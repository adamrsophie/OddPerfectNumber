import OddPerfect.RowCapacity
import OddPerfect.EqualExponentBelow131
import OddPerfect.EulerPart
import OddPerfect.IndexColumnLower
import OddPerfect.UniformExponents
import OddPerfect.EqualExponents

/-!
# Row capacity of the Euler index for equal exponents

Let `N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`, and suppose
every ordinary exponent equals `l - 1` for an odd prime `l`. Write `J = eulerIndex q a m`,
`R(p) = σ(p ^ (l - 1))`, `c = v_l(a + 1)` and `S` for the ordinary prime factors that are `1`
modulo `l`. The rows `R(p) / l` for `p ∈ S` together with `R(l)` are `l - c` distinct numbers
above `1`, supported on `q` and the prime factors of `J` other than `l`, and their product
divides `σ(m ^ 2) = q ^ a J`. The weighted row capacity then gives
`T (l - c) ≤ w a + r (l - 1) + capDeficit w T r` whenever `J` has at most `r + 1` prime
factors (`equal_exponents_row_capacity`).

Consequences:

* `six_le_card_primeFactors_eulerIndex_of_equal_exponents`: for `a = 1`, `J` has at least six
  prime factors.
* `six_le_card_primeFactors_eulerIndex_or_eq_of_special_le_five`: for `a ≤ 5`, `J` has at least
  six prime factors unless `l = 131`; the case `l = 131` is left open.
* `index_le_of_card_primeFactors_eulerIndex_le_six`: for `a = 1`, if `J` has at most six prime
  factors then `l ≤ 457`.

These are restricted results for the family where all ordinary exponents equal `l - 1`. The
prime `l` and the number of prime factors of the Euler index both stay unbounded: the family
is not excluded, and the odd perfect number conjecture remains open. Restricted result; no
published source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EqExpEulerIndex

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

/-- `v_l(n) = 0` for `0 < n < l`. -/
private lemma padicValNat_eq_zero_of_lt {l n : ℕ} (hl : l.Prime) (hn0 : 0 < n) (hn : n < l) :
    padicValNat l n = 0 := by
  have hnd : ¬ l ∣ n := fun hd => absurd (Nat.le_of_dvd hn0 hd) (by omega)
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

/-- The row values: `σ(l ^ (l - 1))` at `l`, and `σ(p ^ (l - 1)) / l` elsewhere. -/
private def row (l p : ℕ) : ℕ := if p = l then σ 1 (l ^ (l - 1)) else σ 1 (p ^ (l - 1)) / l

private lemma row_self (l : ℕ) : row l l = σ 1 (l ^ (l - 1)) := by
  unfold row; exact ite_eq_left rfl

private lemma row_of_ne {l p : ℕ} (h : p ≠ l) : row l p = σ 1 (p ^ (l - 1)) / l := by
  unfold row; exact ite_eq_right h

/-- The bridge with the capacity statement as a hypothesis. -/
private lemma core {N q a m l w T r : ℕ}
    (hcap : ∀ {q w T r : ℕ} {P V : Finset ℕ}, 0 < w → q ∉ P → P.card ≤ r →
      (∀ n ∈ V, 1 < n ∧ ∀ p ∈ n.primeFactors, p = q ∨ p ∈ P) →
      T * V.card ≤
        ∑ n ∈ V, (w * n.factorization q + ∑ p ∈ P, n.factorization p) + capDeficit w T r)
    (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) (hw : 0 < w)
    (hr : (eulerIndex q a m).primeFactors.card ≤ r + 1) :
    T * (l - padicValNat l (a + 1)) ≤ w * a + r * (l - 1) + capDeficit w T r := by
  obtain ⟨hm, hqa, hao, hfm⟩ := frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  -- `l` is an ordinary prime factor of `N`.
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => ⟨1, by rw [hexp p hp hpq, hl1, pow_one]⟩
  have hlq := LCol.ne_of_prime_pow_index h hl hodd hidx'
  have hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1 :=
    fun p hp hpq => by rw [hexp p hp hpq, hl1]
  have hlN : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hl,
    (dvd_pow_self l (by norm_num : (4 : ℕ) ≠ 0)).trans (pow_four_dvd_of_dvd_succ h hq hodd hcomp),
    h.ne_zero⟩
  have hcard := card_congrPrimes_add_padicValNat h hq hodd hl hexp hlN hlq
  have hthree := two_mul_index_pred_le_three_mul_card_of_equal_exponents h hq hodd hl hl2 hexp
  rw [hqa] at hcard
  have hthree' : 2 * (l - 1) ≤ 3 * (congrPrimes N q l).card := hthree
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
  have hlS : l ∉ S := fun hm' => by
    have := (hSmem l hm').2.2
    rw [Nat.mod_self] at this
    omega
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
  -- The set `F = {l} ∪ S` of ordinary primes carrying a row.
  set F := insert l S with hF
  have hFN : ∀ p ∈ F, p ∈ N.primeFactors ∧ p ≠ q := by
    intro p hp
    rcases Finset.mem_insert.mp hp with hpl | hp
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
  -- `l` divides the index.
  obtain ⟨p0, hp0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hlJ : l ∣ J := by
    have hd0 : l ∣ σ 1 (p0 ^ (l - 1)) := Dvd.intro _ (hSrow p0 hp0).1
    rcases (Nat.Prime.dvd_mul hl).mp (hd0.trans (hRF p0 (Finset.mem_insert_of_mem hp0)))
      with h' | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hl hq).mp (hl.dvd_of_dvd_pow h')) hlq
    · exact h'
  have hlJmem : l ∈ J.primeFactors := Nat.mem_primeFactors.mpr ⟨hl, hlJ, hJ0⟩
  -- The row of `l`.
  have hl1lt : 1 < σ 1 (l ^ (l - 1)) := by
    have := pow_lt_sigma hl (show l - 1 ≠ 0 by omega)
    have := pow_pos hl.pos (l - 1)
    omega
  have hlnd : ¬ l ∣ σ 1 (l ^ (l - 1)) := LCol.not_dvd_sigma_self hl _
  -- The rows are distinct.
  have hkey : ∀ x ∈ S, row l x ≠ row l l := by
    intro x hx he
    have hxl : x ≠ l := fun e => hlS (e ▸ hx)
    rw [row_self, row_of_ne hxl] at he
    obtain ⟨hmul, -, hx2⟩ := hSrow x hx
    have hlt := self_row_lt hl hl3 (hFprime x (Finset.mem_insert_of_mem hx)) hx2
    rw [← hmul, he] at hlt
    exact lt_irrefl _ hlt
  have hinj : Set.InjOn (row l) F := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    rcases Finset.mem_insert.mp hx with hxl | hx' <;>
      rcases Finset.mem_insert.mp hy with hyl | hy'
    · rw [hxl, hyl]
    · rw [hxl] at hxy
      exact absurd hxy.symm (hkey y hy')
    · rw [hyl] at hxy
      exact absurd hxy (hkey x hx')
    · have hxl : x ≠ l := fun e => hlS (e ▸ hx')
      have hyl : y ≠ l := fun e => hlS (e ▸ hy')
      rw [row_of_ne hxl, row_of_ne hyl] at hxy
      have e : σ 1 (x ^ (l - 1)) = σ 1 (y ^ (l - 1)) := by
        rw [← (hSrow x hx').1, ← (hSrow y hy').1, hxy]
      have hxp := hFprime x (Finset.mem_insert_of_mem hx')
      have hyp := hFprime y (Finset.mem_insert_of_mem hy')
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact (row_lt_row hxp hyp (by omega) hlt).ne e
      · exact (row_lt_row hyp hxp (by omega) hlt).ne e.symm
  set V := F.image (row l) with hV
  have hVcard : V.card = S.card + 1 := by
    rw [hV, Finset.card_image_of_injOn hinj, hF, Finset.card_insert_of_notMem hlS]
  have hrow_dvd : ∀ x ∈ F, row l x ∣ σ 1 (x ^ (l - 1)) := by
    intro x hx
    by_cases hxl : x = l
    · simp only [hxl, row_self, dvd_refl]
    · have hxS := (Finset.mem_insert.mp hx).resolve_left hxl
      rw [row_of_ne hxl]
      exact Dvd.intro_left _ (hSrow x hxS).1
  have hVprop : ∀ x ∈ F, 1 < row l x ∧ ¬ l ∣ row l x := by
    intro x hx
    by_cases hxl : x = l
    · rw [hxl, row_self]
      exact ⟨hl1lt, hlnd⟩
    · have hxS := (Finset.mem_insert.mp hx).resolve_left hxl
      obtain ⟨hmul, hnd, hx2⟩ := hSrow x hxS
      rw [row_of_ne hxl]
      refine ⟨?_, hnd⟩
      have hlt := self_row_lt hl hl3 (hFprime x hx) hx2
      rw [← hmul] at hlt
      have := Nat.lt_of_mul_lt_mul_left hlt
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
  have hMt : ∀ t ∈ P, (q ^ a * J).factorization t ≤ l - 1 := by
    intro t ht
    obtain ⟨-, htJ⟩ := Finset.mem_erase.mp ht
    have htq : t ≠ q := fun e => hqP (e ▸ ht)
    have htp := Nat.prime_of_mem_primeFactors htJ
    have htm2 : t ∣ m ^ 2 := (Nat.dvd_of_mem_primeFactors htJ).trans hJm
    have htN : t ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨htp,
      by rw [hN]; exact htm2.mul_left _, h.ne_zero⟩
    rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hJ0, Finsupp.add_apply,
      hq.factorization_pow, Finsupp.single_apply, ite_eq_right (Ne.symm htq), zero_add]
    calc J.factorization t ≤ (m ^ 2).factorization t :=
          (Nat.factorization_le_iff_dvd hJ0 hm2).mpr hJm t
      _ = l - 1 := by rw [← hfm t htq, hexp t htN htq]
  have hsum : ∑ n ∈ V, (w * n.factorization q + ∑ p ∈ P, n.factorization p) ≤
      w * a + r * (l - 1) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
    have h1 : w * ∑ n ∈ V, n.factorization q ≤ w * a :=
      Nat.mul_le_mul_left _ ((hbud q).trans hMq.le)
    have h2 : ∑ p ∈ P, ∑ n ∈ V, n.factorization p ≤ ∑ _p ∈ P, (l - 1) :=
      Finset.sum_le_sum fun p hp => (hbud p).trans (hMt p hp)
    rw [Finset.sum_const, smul_eq_mul] at h2
    have h3 : P.card * (l - 1) ≤ r * (l - 1) := Nat.mul_le_mul_right _ hPcard
    omega
  have hcapV := hcap (q := q) (w := w) (T := T) (r := r) hw hqP hPcard hVsupp
  have hVc : V.card = l - padicValNat l (a + 1) := by omega
  rw [← hVc]
  exact le_trans hcapV (Nat.add_le_add_right hsum _)

end EqExpEulerIndex

/-- Row capacity of the Euler index for equal exponents. Let `N = q ^ a * m ^ 2` be an odd
perfect number with special prime `q`, `q ∤ m`, and every ordinary exponent equal to `l - 1`
for an odd prime `l`. If the Euler index has at most `r + 1` prime factors, then for every
weight `w > 0` and threshold `T`,
`T (l - v_l(a + 1)) ≤ w a + r (l - 1) + capDeficit w T r`. Restricted result; no published
source was checked; novelty not verified. -/
theorem equal_exponents_row_capacity {N q a m l w T r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) (hw : 0 < w)
    (hr : (eulerIndex q a m).primeFactors.card ≤ r + 1) :
    T * (l - padicValNat l (a + 1)) ≤ w * a + r * (l - 1) + capDeficit w T r :=
  EqExpEulerIndex.core weighted_row_capacity h hq hN hqm hl hl2 hexp hw hr

/-- For special exponent `1` and equal ordinary exponents `l - 1` (`l` an odd prime), the
Euler index has at least six prime factors. Restricted result: the number of prime factors
stays unbounded and the family is not excluded. Restricted result; no published source was
checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_of_equal_exponents {N q m l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime)
    (hl2 : l ≠ 2) (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q 1 m).primeFactors.card := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  obtain ⟨-, hqa, hao, -⟩ := EqExpEulerIndex.frame h hq hN1 hqm
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  by_contra hk
  have hb := equal_exponents_row_capacity (w := 5) (T := 5) (r := 4) h hq hN1 hqm hl hl2 hexp
    (by norm_num) (by omega)
  rw [capDeficit_five_five_four,
    EqExpEulerIndex.padicValNat_eq_zero_of_lt (n := 1 + 1) hl (by norm_num) (by omega)] at hb
  exact not_all_exponents_eq_pred_of_lt_131 h hq (hqa ▸ hao) hl hl2 (by omega) hexp

/-- For special exponent `a ≤ 5` and equal ordinary exponents `l - 1` (`l` an odd prime), the
Euler index has at least six prime factors, or `l = 131`. The case `l = 131` is left open.
Restricted result: the family is not excluded. Restricted result; no published source was
checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_or_eq_of_special_le_five {N q a m l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (ha : a ≤ 5)
    (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card ∨ l = 131 := by
  obtain ⟨-, hqa, hao, -⟩ := EqExpEulerIndex.frame h hq hN hqm
  rcases Nat.lt_or_ge l 131 with hlt | hge
  · exact (not_all_exponents_eq_pred_of_lt_131 h hq (hqa ▸ hao) hl hl2 hlt hexp).elim
  by_cases hk : 6 ≤ (eulerIndex q a m).primeFactors.card
  · exact Or.inl hk
  right
  have hb := equal_exponents_row_capacity (w := 5) (T := 6) (r := 4) h hq hN hqm hl hl2 hexp
    (by norm_num) (by omega)
  rw [capDeficit_five_six_four,
    EqExpEulerIndex.padicValNat_eq_zero_of_lt (n := a + 1) hl (by omega) (by omega)] at hb
  have hl134 : l ≤ 134 := by omega
  interval_cases l <;> first | rfl | exact absurd hl (by norm_num)

/-- For special exponent `1` and equal ordinary exponents `l - 1` (`l` an odd prime), an Euler
index with at most six prime factors forces `l ≤ 457`. Restricted result: `l` stays unbounded
in general and the family is not excluded. Restricted result; no published source was
checked; novelty not verified. -/
theorem index_le_of_card_primeFactors_eulerIndex_le_six {N q m l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hk : (eulerIndex q 1 m).primeFactors.card ≤ 6) : l ≤ 457 := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hb := equal_exponents_row_capacity (w := 6) (T := 6) (r := 5) h hq hN1 hqm hl hl2 hexp
    (by norm_num) (by omega)
  rw [capDeficit_six_six_five,
    EqExpEulerIndex.padicValNat_eq_zero_of_lt (n := 1 + 1) hl (by norm_num) (by omega)] at hb
  omega

end OddPerfect

#print axioms OddPerfect.equal_exponents_row_capacity
#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_of_equal_exponents
#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_or_eq_of_special_le_five
#print axioms OddPerfect.index_le_of_card_primeFactors_eulerIndex_le_six
