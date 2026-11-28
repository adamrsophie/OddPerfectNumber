import OddPerfect.RowCapacity
import OddPerfect.EulerPart
import OddPerfect.IndexColumnLower
import OddPerfect.UniformExponents
import OddPerfect.EqualExponents
import OddPerfect.EulerIndexOmegaSigned

/-!
# Row budget of the Euler index for equal exponents, with extra rows and odd valuations

Let `N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`, and suppose
every ordinary exponent equals `l - 1` for an odd prime `l`. Write `J = eulerIndex q a m`,
`c = v_l(a + 1)`, `R(p) = σ(p ^ (l - 1))`, `S` for the ordinary prime factors that are `1`
modulo `l`, and `P` for the prime factors of `J` other than `l`.

* `padicValNat_eulerIndex_index_add`: `v_l(J) + c = l - 1`.
* `equal_exponents_row_budget`: the rows `R(p) / l` for `p ∈ S`, `R(l)`, and `R(s)` for the
  primes `s` of a set `H` of prime factors of `m` below `l` are `l - c + |H|` distinct numbers
  above `1`, supported on `q` and `P`, whose product divides `σ(m ^ 2) = q ^ a J`. Every
  `t ∈ P` of odd valuation in `J` has `v_t(J) ≤ l - 2`. The weighted row capacity gives
  `T (l - c + |H|) + o ≤ w a + r (l - 1) + capDeficit w T r`, where `o` counts the primes of
  `P` of odd valuation in `J`, whenever `J` has at most `r + 1` prime factors.
* `equal_exponents_row_budget_two`: for `a ≠ 1` and `l ∤ a + 1`, at least two primes of `P`
  have odd valuation, so `T (l + |H|) + 2 ≤ w a + r (l - 1) + capDeficit w T r`.
* `index_le_of_special_eq_five`: for `a = 5` (then `3 ∣ m`) and at most five prime factors of
  `J`, `l ≤ 130`.

These are restricted results for the family where all ordinary exponents equal `l - 1`. The
family is not excluded; the number of prime factors of `J` is not bounded, and `l` is bounded
only through it. The odd perfect number conjecture remains open. Restricted result; no
published source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EqExpRowBudget

/-- The Euler frame: `m ≠ 0`, `v_q(N) = a`, `a` odd, and `v_p(N) = v_p(m ^ 2)` for `p ≠ q`. -/
private lemma frame {N q a m : ℕ} (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
    (hqm : ¬ q ∣ m) :
    m ≠ 0 ∧ N.factorization q = a ∧ Odd a ∧
      ∀ p, p ≠ q → N.factorization p = (m ^ 2).factorization p := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hfac : ∀ p, N.factorization p = (q ^ a).factorization p + (m ^ 2).factorization p := by
    intro p
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply]
  have hqa : N.factorization q = a := by
    rw [hfac, hq.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd)), add_zero]
  refine ⟨hm, hqa, ?_, fun p hp => ?_⟩
  · rcases Nat.even_or_odd a with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  · rw [hfac, hq.factorization_pow, Finsupp.single_apply, ite_eq_right (Ne.symm hp), zero_add]

/-- `v_l(n) = 0` when `l ∤ n`. -/
private lemma padicValNat_eq_zero_of_not_dvd' {l n : ℕ} (hl : l.Prime) (hnd : ¬ l ∣ n) :
    padicValNat l n = 0 := by
  have : Fact l.Prime := ⟨hl⟩
  rw [Nat.padicValNat_def]
  exact multiplicity_eq_zero_of_not_dvd hnd

/-- `p ^ e < σ(p ^ e)` for `e ≠ 0`. -/
private lemma pow_lt_sigma {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) : p ^ e < σ 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  have : p ^ 0 ≤ ∑ i ∈ Finset.range e, p ^ i :=
    Finset.single_le_sum (f := fun i => p ^ i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.pos_of_ne_zero he))
  simp only [pow_zero] at this
  omega

/-- `(L + 1) ^ 2 ≤ L 2 ^ L` for `L ≥ 4`. -/
private lemma sq_le_mul_two_pow {L : ℕ} (hL : 4 ≤ L) : (L + 1) ^ 2 ≤ L * 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 n]
    nlinarith [ih, Nat.zero_le (2 ^ n), hn]

/-- The row of `l` is small: `l σ(l ^ (l - 1)) < σ(p ^ (l - 1))` for `p ≥ 2 l + 1`. -/
private lemma self_row_lt {l p : ℕ} (hl : l.Prime) (hl3 : 3 ≤ l) (hp : p.Prime)
    (hpl : 2 * l + 1 ≤ p) : l * σ 1 (l ^ (l - 1)) < σ 1 (p ^ (l - 1)) := by
  obtain ⟨L, rfl⟩ : ∃ L, l = L + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel, sigma_one_apply_prime_pow hl, sigma_one_apply_prime_pow hp]
  have hgeom : (∑ i ∈ Finset.range (L + 1), (L + 1) ^ i) * L + 1 = (L + 1) ^ (L + 1) :=
    geom_sum_mul_add L (L + 1)
  have hB : p ^ L ≤ ∑ i ∈ Finset.range (L + 1), p ^ i :=
    Finset.single_le_sum (f := fun i => p ^ i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_self L))
  have hkey : (L + 1) * (L + 1) ^ (L + 1) ≤ L * p ^ L := by
    rcases (by omega : L = 2 ∨ L = 3 ∨ 4 ≤ L) with rfl | rfl | hL4
    · have h7 := Nat.pow_le_pow_left (show 7 ≤ p by omega) 2
      norm_num
      nlinarith [h7]
    · have h9 := Nat.pow_le_pow_left (show 9 ≤ p by omega) 3
      norm_num
      nlinarith [h9]
    · have h2 : (2 * (L + 1)) ^ L ≤ p ^ L := Nat.pow_le_pow_left (by omega) L
      rw [mul_pow] at h2
      have h3 := sq_le_mul_two_pow hL4
      calc (L + 1) * (L + 1) ^ (L + 1) = (L + 1) ^ 2 * (L + 1) ^ L := by ring
        _ ≤ (L * 2 ^ L) * (L + 1) ^ L := Nat.mul_le_mul_right _ h3
        _ = L * (2 ^ L * (L + 1) ^ L) := by ring
        _ ≤ L * p ^ L := Nat.mul_le_mul_left _ h2
  have e : L * ((L + 1) * ∑ i ∈ Finset.range (L + 1), (L + 1) ^ i) + (L + 1) =
      (L + 1) * (L + 1) ^ (L + 1) := by
    rw [← hgeom]; ring
  have hL0 : 0 < L := by omega
  have h1 : L * ((L + 1) * ∑ i ∈ Finset.range (L + 1), (L + 1) ^ i) <
      L * ∑ i ∈ Finset.range (L + 1), p ^ i := by
    have := Nat.mul_le_mul_left L hB
    omega
  exact Nat.lt_of_mul_lt_mul_left h1

/-- Rows grow with the prime: `σ(p ^ k) < σ(p' ^ k)` for `p < p'` and `k ≥ 1`. -/
private lemma row_lt_row {p p' k : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hk : 1 ≤ k)
    (h : p < p') : σ 1 (p ^ k) < σ 1 (p' ^ k) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp']
  exact Finset.sum_lt_sum (fun i _ => Nat.pow_le_pow_left h.le i)
    ⟨1, Finset.mem_range.mpr (by omega), by simpa using h⟩

/-- An odd prime `p ≡ 1 (mod l)` with `l` odd satisfies `p ≥ 2 l + 1`. -/
private lemma two_mul_add_one_le {l p : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hp : p.Prime)
    (hp2 : p ≠ 2) (h1 : p % l = 1) : 2 * l + 1 ≤ p := by
  obtain ⟨u, hu⟩ := hl.odd_of_ne_two hl2
  obtain ⟨v, hv⟩ := hp.odd_of_ne_two hp2
  have hd := Nat.div_add_mod p l
  rw [h1] at hd
  obtain ⟨k, hk⟩ : ∃ k, p / l = k := ⟨_, rfl⟩
  rw [hk] at hd
  by_contra hlt
  have hk2 : l * k < l * 2 := by omega
  have hk2' : k < 2 := Nat.lt_of_mul_lt_mul_left hk2
  have := hp.two_le
  interval_cases k
  · omega
  · omega

/-- `v_l(σ(p ^ (l - 1))) = 1` for `p ≡ 1 (mod l)`, as a factorization. -/
private lemma row_factorization {p l : ℕ} (hp : p.Prime) (hl : l.Prime) (hl2 : l ≠ 2)
    (h1 : p % l = 1) : (σ 1 (p ^ (l - 1))).factorization l = 1 := by
  have hv := padicValNat_sigma_of_mod_eq_one hp hl hl2 h1 (a := l - 1)
  rw [Nat.sub_add_cancel hl.one_lt.le, Nat.padicValNat_def, Nat.padicValNat_def] at hv
  rw [Nat.factorization_def _ hl, hv, ← Nat.factorization_def _ hl, hl.factorization_self]

/-- For a prime `s` with `s % l ≠ 1`, `l ∤ σ(s ^ (l - 1))` (geometric sum modulo `l`). -/
private lemma not_dvd_sigma_of_mod_ne_one {l s : ℕ} (hl : l.Prime) (hs : s.Prime)
    (h1 : s % l ≠ 1) : ¬ l ∣ σ 1 (s ^ (l - 1)) := by
  have : Fact l.Prime := ⟨hl⟩
  intro hd
  rw [sigma_one_apply_prime_pow hs, Nat.sub_add_cancel hl.one_lt.le] at hd
  have h0 : ((∑ i ∈ Finset.range l, s ^ i : ℕ) : ZMod l) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at h0
  have hg := geom_sum_mul (s : ZMod l) l
  rw [h0, zero_mul, ZMod.pow_card] at hg
  have h1' : (s : ZMod l) = ((1 : ℕ) : ZMod l) := by
    rw [Nat.cast_one]; exact (sub_eq_zero.mp hg.symm)
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hl.one_lt] at h1'
  exact h1 h1'

/-- The row values: `σ(p ^ (l - 1)) / l` for `p ≡ 1 (mod l)`, and `σ(p ^ (l - 1))` otherwise. -/
private def row (l p : ℕ) : ℕ :=
  if p % l = 1 then σ 1 (p ^ (l - 1)) / l else σ 1 (p ^ (l - 1))

private lemma row_of_mod {l p : ℕ} (h : p % l = 1) : row l p = σ 1 (p ^ (l - 1)) / l := by
  unfold row; exact ite_eq_left h

private lemma row_of_not {l p : ℕ} (h : p % l ≠ 1) : row l p = σ 1 (p ^ (l - 1)) := by
  unfold row; exact ite_eq_right h

/-- `l` is an ordinary prime factor, and the ledger `|S| + v_l(a + 1) = l - 1`. -/
private lemma setup {N q a m l : ℕ} (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
    (hqm : ¬ q ∣ m) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    l ∈ N.primeFactors ∧ l ≠ q ∧ (congrPrimes N q l).card + padicValNat l (a + 1) = l - 1 := by
  obtain ⟨-, hqa, hao, -⟩ := frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => ⟨1, by rw [hexp p hp hpq, hl1, pow_one]⟩
  have hlq := LCol.ne_of_prime_pow_index h hl hodd hidx'
  have hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1 :=
    fun p hp hpq => by rw [hexp p hp hpq, hl1]
  have hlN : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hl,
    (dvd_pow_self l (by norm_num : (4 : ℕ) ≠ 0)).trans (pow_four_dvd_of_dvd_succ h hq hodd hcomp),
    h.ne_zero⟩
  have hcard := card_congrPrimes_add_padicValNat h hq hodd hl hexp hlN hlq
  rw [hqa] at hcard
  exact ⟨hlN, hlq, hcard⟩

/-- The row budget, proved from the weighted row capacity. -/
private lemma budget {N q a m l w T r : ℕ} {H : Finset ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : 0 < w) (hr : (eulerIndex q a m).primeFactors.card ≤ r + 1)
    (hH : ∀ s ∈ H, s.Prime ∧ s ∣ m ∧ s < l) :
    T * (l - padicValNat l (a + 1) + H.card) +
        (((eulerIndex q a m).primeFactors.erase l).filter
          fun t => Odd ((eulerIndex q a m).factorization t)).card ≤
      w * a + r * (l - 1) + capDeficit w T r := by
  obtain ⟨hm, hqa, hao, hfm⟩ := frame h hq hN hqm
  obtain ⟨hlN, hlq, hcard⟩ := setup h hq hN hqm hl hexp
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hthree := two_mul_index_pred_le_three_mul_card_of_equal_exponents h hq hodd hl hl2 hexp
  have hthree' : 2 * (l - 1) ≤ 3 * (congrPrimes N q l).card := hthree
  obtain ⟨u, hu⟩ := hl.odd_of_ne_two hl2
  set S := congrPrimes N q l with hS
  set J := eulerIndex q a m with hJ
  have hσ : σ 1 (m ^ 2) = q ^ a * J := sigma_sq_eq_mul_eulerIndex h hq hN hqm
  have hJm : J ∣ m ^ 2 := eulerIndex_dvd_sq h hq hN hqm
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hJ0 : J ≠ 0 := fun h0 => hm2 (Nat.eq_zero_of_zero_dvd (h0 ▸ hJm))
  have hqJ : ¬ q ∣ J := fun hd => hqm (hq.dvd_of_dvd_pow (hd.trans hJm))
  -- The primes of `S`.
  have hSmem : ∀ p ∈ S, p ∈ N.primeFactors ∧ p ≠ q ∧ p % l = 1 := fun p hp => by
    rw [hS, congrPrimes, Finset.mem_filter] at hp
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  have hSrow : ∀ p ∈ S, l * (σ 1 (p ^ (l - 1)) / l) = σ 1 (p ^ (l - 1)) ∧
      ¬ l ∣ σ 1 (p ^ (l - 1)) / l ∧ 2 * l + 1 ≤ p := by
    intro p hp
    obtain ⟨hpN, -, hp1⟩ := hSmem p hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hp2 : p ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hpN)
    have hR0 : σ 1 (p ^ (l - 1)) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
    have hv := row_factorization hpp hl hl2 hp1
    have hdvd : l ∣ σ 1 (p ^ (l - 1)) := by
      have := (hl.pow_dvd_iff_le_factorization hR0 (k := 1)).mpr (by omega)
      simpa using this
    have hmul := Nat.mul_div_cancel' hdvd
    refine ⟨hmul, fun hd => ?_, two_mul_add_one_le hl hl2 hpp hp2 hp1⟩
    have h2 : l ^ 2 ∣ σ 1 (p ^ (l - 1)) := by
      rw [pow_two]
      exact hmul ▸ Nat.mul_dvd_mul_left l hd
    have := (hl.pow_dvd_iff_le_factorization hR0).mp h2
    omega
  -- The primes of `H`.
  have hHmem : ∀ s ∈ H, s ∈ N.primeFactors ∧ s ≠ q ∧ s.Prime ∧ s < l ∧ s % l ≠ 1 := by
    intro s hs
    obtain ⟨hsp, hsm, hsl⟩ := hH s hs
    have hs2 := hsp.two_le
    refine ⟨Nat.mem_primeFactors.mpr ⟨hsp, ?_, h.ne_zero⟩, fun e => hqm (e ▸ hsm), hsp, hsl,
      by rw [Nat.mod_eq_of_lt hsl]; omega⟩
    rw [hN]
    exact (dvd_pow hsm two_ne_zero).mul_left _
  -- The set `F = H ∪ {l} ∪ S` of ordinary primes carrying a row.
  set F := H ∪ insert l S with hF
  have hFcases : ∀ x ∈ F, x ∈ H ∨ l = x ∨ x ∈ S := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr ((Finset.mem_insert.mp hx).imp_left Eq.symm)
  have hFN : ∀ p ∈ F, p ∈ N.primeFactors ∧ p ≠ q := by
    intro p hp
    rcases hFcases p hp with hp | hpl | hp
    · exact ⟨(hHmem p hp).1, (hHmem p hp).2.1⟩
    · exact ⟨hpl ▸ hlN, hpl ▸ hlq⟩
    · exact ⟨(hSmem p hp).1, (hSmem p hp).2.1⟩
  have hFm : ∀ p ∈ F, (m ^ 2).factorization p = l - 1 := fun p hp => by
    rw [← hfm p (hFN p hp).2, hexp p (hFN p hp).1 (hFN p hp).2]
  have hFprime : ∀ p ∈ F, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hFN p hp).1
  have hFdvd : ∏ p ∈ F, σ 1 (p ^ (l - 1)) ∣ σ 1 (m ^ 2) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hm2, Finsupp.prod,
      Nat.support_factorization]
    have hsub : F ⊆ (m ^ 2).primeFactors := fun p hp => by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff, hFm p hp]
      omega
    calc ∏ p ∈ F, σ 1 (p ^ (l - 1)) = ∏ p ∈ F, σ 1 (p ^ (m ^ 2).factorization p) :=
          Finset.prod_congr rfl fun p hp => by rw [hFm p hp]
      _ ∣ _ := Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have hRF : ∀ p ∈ F, σ 1 (p ^ (l - 1)) ∣ q ^ a * J := fun p hp => by
    rw [← hσ]
    exact (Finset.dvd_prod_of_mem (fun p => σ 1 (p ^ (l - 1))) hp).trans hFdvd
  have hSF : ∀ p ∈ S, p ∈ F := fun p hp =>
    Finset.mem_union_right _ (Finset.mem_insert_of_mem hp)
  -- `l` divides the index.
  obtain ⟨p0, hp0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hlJ : l ∣ J := by
    have hd0 : l ∣ σ 1 (p0 ^ (l - 1)) := Dvd.intro _ (hSrow p0 hp0).1
    rcases (Nat.Prime.dvd_mul hl).mp (hd0.trans (hRF p0 (hSF p0 hp0))) with h' | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hl hq).mp (hl.dvd_of_dvd_pow h')) hlq
    · exact h'
  have hlJmem : l ∈ J.primeFactors := Nat.mem_primeFactors.mpr ⟨hl, hlJ, hJ0⟩
  -- Values of the rows.
  have hll : l % l ≠ 1 := by rw [Nat.mod_self]; omega
  have hrowl : row l l = σ 1 (l ^ (l - 1)) := row_of_not hll
  have hrowH : ∀ x ∈ H, row l x = σ 1 (x ^ (l - 1)) := fun x hx =>
    row_of_not (hHmem x hx).2.2.2.2
  have hrowS : ∀ x ∈ S, l * row l x = σ 1 (x ^ (l - 1)) ∧ ¬ l ∣ row l x ∧
      l * σ 1 (l ^ (l - 1)) < σ 1 (x ^ (l - 1)) := by
    intro x hx
    obtain ⟨hmul, hnd, hx2⟩ := hSrow x hx
    rw [row_of_mod (hSmem x hx).2.2]
    exact ⟨hmul, hnd, self_row_lt hl hl3 (hFprime x (hSF x hx)) hx2⟩
  have hSl : ∀ x ∈ S, l < x := fun x hx => by have := (hSrow x hx).2.2; omega
  -- The rows increase strictly along `F`.
  have hmono : ∀ x ∈ F, ∀ y ∈ F, x < y → row l x < row l y := by
    intro x hx y hy hxy
    have hxp := hFprime x hx
    have hyp := hFprime y hy
    rcases hFcases x hx with hxH | rfl | hxS <;> rcases hFcases y hy with hyH | rfl | hyS
    · rw [hrowH x hxH, hrowH y hyH]
      exact row_lt_row hxp hyp (by omega) hxy
    · rw [hrowH x hxH, hrowl]
      exact row_lt_row hxp hyp (by omega) hxy
    · obtain ⟨hmul, -, hlt⟩ := hrowS y hyS
      rw [hrowH x hxH]
      have h1 := row_lt_row hxp hl (show 1 ≤ l - 1 by omega) (hHmem x hxH).2.2.2.1
      rw [← hmul] at hlt
      have h2 := Nat.lt_of_mul_lt_mul_left hlt
      omega
    · exact absurd hxy (by have := (hHmem y hyH).2.2.2.1; omega)
    · exact absurd hxy (lt_irrefl _)
    · obtain ⟨hmul, -, hlt⟩ := hrowS y hyS
      rw [hrowl]
      rw [← hmul] at hlt
      exact Nat.lt_of_mul_lt_mul_left hlt
    · exact absurd hxy (by have := (hHmem y hyH).2.2.2.1; have := hSl x hxS; omega)
    · exact absurd hxy (by have := hSl x hxS; omega)
    · have h1 := row_lt_row hxp hyp (show 1 ≤ l - 1 by omega) hxy
      rw [← (hrowS x hxS).1, ← (hrowS y hyS).1] at h1
      exact Nat.lt_of_mul_lt_mul_left h1
  have hinj : Set.InjOn (row l) F := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact (hmono x hx y hy hlt).ne hxy
    · exact (hmono y hy x hx hlt).ne hxy.symm
  set V := F.image (row l) with hV
  have hlS : l ∉ S := fun hm' => lt_irrefl _ (hSl l hm')
  have hdisj : Disjoint H (insert l S) := by
    rw [Finset.disjoint_left]
    intro x hxH hx
    have hxl := (hHmem x hxH).2.2.2.1
    rcases Finset.mem_insert.mp hx with hxl' | hxS
    · omega
    · have := hSl x hxS
      omega
  have hVcard : V.card = H.card + (S.card + 1) := by
    rw [hV, Finset.card_image_of_injOn hinj, hF, Finset.card_union_of_disjoint hdisj,
      Finset.card_insert_of_notMem hlS]
  have hrow_dvd : ∀ x ∈ F, row l x ∣ σ 1 (x ^ (l - 1)) := by
    intro x hx
    rcases hFcases x hx with hxH | rfl | hxS
    · simp only [hrowH x hxH, dvd_refl]
    · simp only [hrowl, dvd_refl]
    · exact Dvd.intro_left _ (hrowS x hxS).1
  have hVprop : ∀ x ∈ F, 1 < row l x ∧ ¬ l ∣ row l x := by
    intro x hx
    rcases hFcases x hx with hxH | rfl | hxS
    · obtain ⟨-, -, hxp, -, hx1⟩ := hHmem x hxH
      rw [hrowH x hxH]
      refine ⟨?_, not_dvd_sigma_of_mod_ne_one hl hxp hx1⟩
      have := pow_lt_sigma hxp (show l - 1 ≠ 0 by omega)
      have := pow_pos hxp.pos (l - 1)
      omega
    · rw [hrowl]
      refine ⟨?_, LCol.not_dvd_sigma_self hl _⟩
      have := pow_lt_sigma hl (show l - 1 ≠ 0 by omega)
      have := pow_pos hl.pos (l - 1)
      omega
    · obtain ⟨hmul, hnd, hlt⟩ := hrowS x hxS
      refine ⟨?_, hnd⟩
      rw [← hmul] at hlt
      have := Nat.lt_of_mul_lt_mul_left hlt
      have := pow_lt_sigma hl (show l - 1 ≠ 0 by omega)
      have := pow_pos hl.pos (l - 1)
      omega
  have hVdvd : ∏ n ∈ V, n ∣ q ^ a * J := by
    rw [hV, Finset.prod_image hinj, ← hσ]
    exact (Finset.prod_dvd_prod_of_dvd _ _ hrow_dvd).trans hFdvd
  -- Support of the rows.
  set P := J.primeFactors.erase l with hP
  have hPcard : P.card ≤ r := by
    rw [hP, Finset.card_erase_of_mem hlJmem]
    omega
  have hqP : q ∉ P := fun hm' =>
    hqJ (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hm'))
  have hn_dvd : ∀ n ∈ V, n ∣ q ^ a * J := fun n hn =>
    (Finset.dvd_prod_of_mem (fun n => n) hn).trans hVdvd
  have hVsupp : ∀ n ∈ V, 1 < n ∧ ∀ p ∈ n.primeFactors, p = q ∨ p ∈ P := by
    intro n hn
    obtain ⟨x, hx, hxn⟩ := Finset.mem_image.mp hn
    obtain ⟨h1, hnd⟩ := hVprop x hx
    rw [hxn] at h1 hnd
    refine ⟨h1, fun t ht => ?_⟩
    have htp := Nat.prime_of_mem_primeFactors ht
    have htd := Nat.dvd_of_mem_primeFactors ht
    rcases (Nat.Prime.dvd_mul htp).mp (htd.trans (hn_dvd n hn)) with h' | h'
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq htp hq).mp (htp.dvd_of_dvd_pow h'))
    · exact Or.inr (Finset.mem_erase.mpr
        ⟨fun htl => hnd (htl ▸ htd), Nat.mem_primeFactors.mpr ⟨htp, h', hJ0⟩⟩)
  -- Budgets.
  have hM0 : q ^ a * J ≠ 0 := mul_ne_zero (pow_ne_zero _ hq.ne_zero) hJ0
  have hD0 : ∏ n ∈ V, n ≠ 0 := Finset.prod_ne_zero_iff.mpr fun n hn => by
    have := (hVsupp n hn).1
    omega
  have hbud : ∀ t, ∑ n ∈ V, n.factorization t ≤ (q ^ a * J).factorization t := by
    intro t
    have hle := (Nat.factorization_le_iff_dvd hD0 hM0).mpr hVdvd t
    rw [Nat.factorization_prod (fun n hn => by have := (hVsupp n hn).1; omega),
      Finset.sum_apply'] at hle
    exact hle
  have hMq : (q ^ a * J).factorization q = a := by
    rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hJ0, Finsupp.add_apply,
      hq.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hqJ,
      add_zero]
  have hMt : ∀ t ∈ P, (q ^ a * J).factorization t +
      (if Odd (J.factorization t) then 1 else 0) ≤ l - 1 := by
    intro t ht
    obtain ⟨-, htJ⟩ := Finset.mem_erase.mp ht
    have htq : t ≠ q := fun e => hqP (e ▸ ht)
    have htp := Nat.prime_of_mem_primeFactors htJ
    have htm2 : t ∣ m ^ 2 := (Nat.dvd_of_mem_primeFactors htJ).trans hJm
    have htN : t ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨htp,
      by rw [hN]; exact htm2.mul_left _, h.ne_zero⟩
    rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hJ0, Finsupp.add_apply,
      hq.factorization_pow, Finsupp.single_apply, ite_eq_right (Ne.symm htq), zero_add]
    have hle : J.factorization t ≤ l - 1 :=
      calc J.factorization t ≤ (m ^ 2).factorization t :=
            (Nat.factorization_le_iff_dvd hJ0 hm2).mpr hJm t
        _ = l - 1 := by rw [← hfm t htq, hexp t htN htq]
    split_ifs with ho
    · rw [Nat.odd_iff] at ho
      omega
    · omega
  have hsum : ∑ n ∈ V, (w * n.factorization q + ∑ p ∈ P, n.factorization p) +
      (P.filter fun t => Odd (J.factorization t)).card ≤ w * a + r * (l - 1) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm, Finset.card_filter]
    have h1 : w * ∑ n ∈ V, n.factorization q ≤ w * a :=
      Nat.mul_le_mul_left _ ((hbud q).trans hMq.le)
    have h2 : ∑ p ∈ P, (∑ n ∈ V, n.factorization p +
        (if Odd (J.factorization p) then 1 else 0)) ≤ ∑ _p ∈ P, (l - 1) :=
      Finset.sum_le_sum fun p hp => (Nat.add_le_add_right (hbud p) _).trans (hMt p hp)
    rw [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib] at h2
    have h3 : P.card * (l - 1) ≤ r * (l - 1) := Nat.mul_le_mul_right _ hPcard
    omega
  have hcapV := weighted_row_capacity (q := q) (w := w) (T := T) (r := r) hw hqP hPcard hVsupp
  have hVc : V.card = l - padicValNat l (a + 1) + H.card := by omega
  rw [← hVc]
  omega

/-- For special exponent `5`, `3 ∣ σ(q ^ 5)`, hence `3 ∣ m`. -/
private lemma three_dvd_of_five {N q m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ 5 * m ^ 2) (hqm : ¬ q ∣ m) (hq3 : q ≠ 3) : 3 ∣ m := by
  have hprod := sigma_special_mul_eulerIndex h hq hN hqm
  have hq3' : ¬ 3 ∣ q := fun hd =>
    hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp hd).symm
  have hs : 3 ∣ σ 1 (q ^ 5) := by
    rw [sigma_one_apply_prime_pow hq, ← ZMod.natCast_eq_zero_iff]
    have hx : ((q : ℕ) : ZMod 3) ≠ 0 := fun h0 => hq3' ((ZMod.natCast_eq_zero_iff _ _).mp h0)
    push_cast
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    generalize ((q : ℕ) : ZMod 3) = x at hx ⊢
    revert x
    decide
  have h3 : 3 ∣ 2 * m ^ 2 := by rw [← hprod]; exact hs.mul_right _
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h' | h'
  · norm_num at h'
  · exact Nat.prime_three.dvd_of_dvd_pow h'

end EqExpRowBudget

/-- Valuation of `l` in the Euler index for equal exponents. Let `N = q ^ a * m ^ 2` be an odd
perfect number with special prime `q`, `q ∤ m`, and every ordinary exponent equal to `l - 1`
for an odd prime `l`. Then `v_l(eulerIndex q a m) + v_l(a + 1) = l - 1`. Restricted result;
no published source was checked; novelty not verified. -/
theorem padicValNat_eulerIndex_index_add {N q a m l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    padicValNat l (eulerIndex q a m) + padicValNat l (a + 1) = l - 1 := by
  obtain ⟨hm, hqa, hao, hfm⟩ := EqExpRowBudget.frame h hq hN hqm
  obtain ⟨hlN, hlq, -⟩ := EqExpRowBudget.setup h hq hN hqm hl hexp
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  have hmod := special_mod_eq_one h hq hodd hl hexp hlq
  have hprod := sigma_special_mul_eulerIndex h hq hN hqm
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hJ0 : eulerIndex q a m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    have := Nat.pos_of_ne_zero hm2
    omega
  have hs0 : σ 1 (q ^ a) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
  have hv : (σ 1 (q ^ a) * eulerIndex q a m).factorization l = (2 * m ^ 2).factorization l := by
    rw [hprod]
  rw [Nat.factorization_mul hs0 hJ0, Nat.factorization_mul two_ne_zero hm2, Finsupp.add_apply,
    Finsupp.add_apply, Nat.factorization_def _ hl, ← Nat.padicValNat_def,
    padicValNat_sigma_of_mod_eq_one hq hl hl2 hmod,
    Nat.factorization_eq_zero_of_not_dvd
      (fun hd => hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hd)),
    ← hfm l hlq, hexp l hlN hlq] at hv
  rw [Nat.padicValNat_def (n := eulerIndex q a m), ← Nat.factorization_def _ hl]
  omega

/-- Row budget of the Euler index for equal exponents. Let `N = q ^ a * m ^ 2` be an odd
perfect number with special prime `q`, `q ∤ m`, and every ordinary exponent equal to `l - 1`
for an odd prime `l`. Let `H` be a set of prime factors of `m` below `l`. If the Euler index
`J` has at most `r + 1` prime factors, then for every weight `w > 0` and threshold `T`,
`T (l - v_l(a + 1) + |H|) + o ≤ w a + r (l - 1) + capDeficit w T r`, where `o` is the number
of prime factors `t ≠ l` of `J` with `v_t(J)` odd. Restricted result; no published source was
checked; novelty not verified. -/
theorem equal_exponents_row_budget {N q a m l w T r : ℕ} {H : Finset ℕ} (h : OddPerfect N)
    (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : 0 < w) (hr : (eulerIndex q a m).primeFactors.card ≤ r + 1)
    (hH : ∀ s ∈ H, s.Prime ∧ s ∣ m ∧ s < l) :
    T * (l - padicValNat l (a + 1) + H.card) +
        (((eulerIndex q a m).primeFactors.erase l).filter
          fun t => Odd ((eulerIndex q a m).factorization t)).card ≤
      w * a + r * (l - 1) + capDeficit w T r :=
  EqExpRowBudget.budget h hq hN hqm hl hl2 hexp hw hr hH

/-- Row budget with two odd valuations. Let `N = q ^ a * m ^ 2` be an odd perfect number with
special prime `q`, `q ∤ m`, `a ≠ 1`, and every ordinary exponent equal to `l - 1` for an odd
prime `l` with `l ∤ a + 1`. Let `H` be a set of prime factors of `m` below `l`. If the Euler
index has at most `r + 1` prime factors, then for every weight `w > 0` and threshold `T`,
`T (l + |H|) + 2 ≤ w a + r (l - 1) + capDeficit w T r`. Restricted result; no published source
was checked; novelty not verified. -/
theorem equal_exponents_row_budget_two {N q a m l w T r : ℕ} {H : Finset ℕ} (h : OddPerfect N)
    (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (ha : a ≠ 1) (hla : ¬ l ∣ a + 1)
    (hw : 0 < w) (hr : (eulerIndex q a m).primeFactors.card ≤ r + 1)
    (hH : ∀ s ∈ H, s.Prime ∧ s ∣ m ∧ s < l) :
    T * (l + H.card) + 2 ≤ w * a + r * (l - 1) + capDeficit w T r := by
  obtain ⟨-, -, hao, -⟩ := EqExpRowBudget.frame h hq hN hqm
  have hc : padicValNat l (a + 1) = 0 := EqExpRowBudget.padicValNat_eq_zero_of_not_dvd' hl hla
  have hb := equal_exponents_row_budget (T := T) h hq hN hqm hl hl2 hexp hw hr hH
  rw [hc, Nat.sub_zero] at hb
  have hv := padicValNat_eulerIndex_index_add h hq hN hqm hl hl2 hexp
  rw [hc, add_zero] at hv
  have hcount := cardFactors_add_one_le_card_odd_valuation_eulerIndex h hq hN hqm ha
  have hΩ : 0 < ArithmeticFunction.cardFactors ((a + 1) / 2) := by
    rw [cardFactors_pos_iff_one_lt]
    obtain ⟨j, hj⟩ := hao
    omega
  have hsub : (eulerIndex q a m).primeFactors.filter
        (fun t => Odd ((eulerIndex q a m).factorization t)) ⊆
      ((eulerIndex q a m).primeFactors.erase l).filter
        (fun t => Odd ((eulerIndex q a m).factorization t)) := by
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨Finset.mem_erase.mpr ⟨?_, ht.1⟩, ht.2⟩
    rintro rfl
    have ho := ht.2
    rw [Nat.factorization_def _ hl, ← Nat.padicValNat_def, hv, Nat.odd_iff] at ho
    obtain ⟨u, hu⟩ := hl.odd_of_ne_two hl2
    omega
  have := Finset.card_le_card hsub
  omega

/-- Special exponent `5` with equal exponents. Let `N = q ^ 5 * m ^ 2` be an odd perfect
number with special prime `q`, `q ∤ m`, and every ordinary exponent equal to `l - 1` for a
prime `l ≥ 7`. If the Euler index has at most five prime factors, then `l ≤ 130`. Restricted
result: the family is not excluded. Restricted result; no published source was checked;
novelty not verified. -/
theorem index_le_of_special_eq_five {N q m l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ 5 * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl7 : 7 ≤ l)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hJ : (eulerIndex q 5 m).primeFactors.card ≤ 5) : l ≤ 130 := by
  obtain ⟨-, hqa, hao, -⟩ := EqExpRowBudget.frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  have hq4 := (special_mod_four h hq hodd).1
  have hq3 : q ≠ 3 := by rintro rfl; norm_num at hq4
  have h3m : 3 ∣ m := EqExpRowBudget.three_dvd_of_five h hq hN hqm hq3
  have hl2 : l ≠ 2 := by omega
  have hla : ¬ l ∣ 5 + 1 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hb := equal_exponents_row_budget_two (w := 5) (T := 6) (r := 4) (H := {3}) h hq hN hqm
    hl hl2 hexp (by norm_num) hla (by norm_num) (by omega) (by
      intro s hs
      rw [Finset.mem_singleton] at hs
      subst hs
      exact ⟨Nat.prime_three, h3m, by omega⟩)
  rw [capDeficit_five_six_four, Finset.card_singleton] at hb
  omega

end OddPerfect

#print axioms OddPerfect.padicValNat_eulerIndex_index_add
#print axioms OddPerfect.equal_exponents_row_budget
#print axioms OddPerfect.equal_exponents_row_budget_two
#print axioms OddPerfect.index_le_of_special_eq_five
