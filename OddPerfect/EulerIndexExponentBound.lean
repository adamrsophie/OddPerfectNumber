import OddPerfect.EulerIndexOmegaSigned
import OddPerfect.Zsigmondy
import OddPerfect.EulerPart
import OddPerfect.UniformExponents

/-!
# The number of prime factors through the exponents of the Euler index

Let `N = q ^ a * m ^ 2` be an odd perfect number in Euler's form, with `q` the special prime and
`q ∤ m`, and let `J = eulerIndex q a m`, so that `σ(m ^ 2) = q ^ a J` and `J ∣ m ^ 2`.

* If every prime factor of `J` has exponent at most `E` in `N` and `ω(J) ≤ k`, then
  `ω(N) ≤ 1 + k (E + 1) + k / 2`. The ordinary primes split into three classes: rows
  `σ(p ^ e_p)` with a prime factor other than `q` (at most `ω(J) E`, by the ledger of each prime
  factor of `J`), rows that are powers of `q` with `p ∣ J` (at most `ω(J)`), and rows that are
  powers of `q` with `p ∤ J` (at most `ω(J) / 2`, by lifting the exponent and the signed count
  of primes of odd valuation in `J`).
* For a prime factor `r` of `J` such that every prime factor of `e_r + 1` is at most `T`:
  `e_r + 1 ≤ T ^ ω(J)`, since the divisors `d ≥ 3` of `e_r + 1` get primitive prime divisors of
  `σ(r ^ e_r)`, all in `{q} ∪ primeFactors J` and distinct from `r`.

These bound the number of prime factors of `N` by quantities of the Euler index; `ω(J)` and the
exponents stay unbounded, and no odd perfect number is excluded. Restricted result; no published
source was checked; novelty not verified. The odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- `σ(p ^ v_p(n))` divides `σ(n)`. -/
private lemma eib_sigma_component_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    σ 1 (p ^ n.factorization p) ∣ σ 1 n := by
  have hcop := (Nat.coprime_ordCompl hp hn).pow_left (n.factorization p)
  calc σ 1 (ordProj[p] n) ∣ σ 1 (ordProj[p] n) * σ 1 (ordCompl[p] n) := dvd_mul_right _ _
    _ = σ 1 (ordProj[p] n * ordCompl[p] n) :=
      (isMultiplicative_sigma.map_mul_of_coprime hcop).symm
    _ = σ 1 n := by rw [Nat.ordProj_mul_ordCompl_eq_self]

/-- `σ(p ^ (j + 1)) = 1 + p σ(p ^ j)`. -/
private lemma eib_sigma_succ_mul {p : ℕ} (hp : p.Prime) (j : ℕ) :
    σ 1 (p ^ (j + 1)) = 1 + p * σ 1 (p ^ j) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
    Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

/-- The `p`-adic valuation is the exponent in the factorization. -/
private lemma eib_pv {p n : ℕ} (hp : p.Prime) : padicValNat p n = n.factorization p := by
  rw [Nat.padicValNat_def, Nat.factorization_def _ hp]

/-- Outside the special prime, the exponent in `N` is the exponent in `m ^ 2`. -/
private lemma eib_fac_ne {N q a m p : ℕ} (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hm : m ≠ 0)
    (hpq : p ≠ q) : N.factorization p = (m ^ 2).factorization p := by
  rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm), Finsupp.add_apply,
    Nat.factorization_pow, hq.factorization]
  simp [Ne.symm hpq]

/-- `1 + ∑ f ≤ ∏ (f + 1)`. -/
private lemma eib_one_add_sum_le_prod (s : Finset ℕ) (f : ℕ → ℕ) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (f i + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have hP : 1 ≤ ∏ i ∈ s, (f i + 1) := by omega
    have h1 : f x ≤ f x * ∏ i ∈ s, (f i + 1) := Nat.le_mul_of_pos_right _ hP
    rw [add_mul, one_mul]
    omega

/-- A number all of whose prime factors are at most `T` is at most `T` to the number of its
divisors above `1`. -/
private lemma eib_le_pow_card_divisors {n T : ℕ} (hn : n ≠ 0) (hT1 : 1 ≤ T)
    (hT : ∀ d ∈ n.primeFactors, d ≤ T) : n ≤ T ^ (n.divisors.card - 1) := by
  have hprod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
  have hle1 : n ≤ T ^ ∑ p ∈ n.primeFactors, n.factorization p := by
    rw [← Finset.prod_pow_eq_pow_sum]
    calc n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := hprod
      _ ≤ ∏ p ∈ n.primeFactors, T ^ n.factorization p :=
        Finset.prod_le_prod fun p hp => Nat.pow_le_pow_left (hT p hp) _
  have hsum := eib_one_add_sum_le_prod n.primeFactors n.factorization
  rw [← Nat.card_divisors hn] at hsum
  exact hle1.trans (Nat.pow_le_pow_right hT1 (by omega))

/-- For every odd perfect number `N = q ^ a * m ^ 2` with special prime `q` and `q ∤ m`: a prime
factor `r` of the Euler index `J` such that every prime factor of `e_r + 1` is at most `T` has
`e_r + 1 ≤ T ^ ω(J)`. A bound through quantities of the Euler index only; nothing is excluded.
Restricted result; no published source was checked; novelty not verified. -/
theorem factorization_succ_le_pow_of_mem_eulerIndex {N q a m r T : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hr : r ∈ (eulerIndex q a m).primeFactors)
    (hT : ∀ d ∈ (N.factorization r + 1).primeFactors, d ≤ T) :
    N.factorization r + 1 ≤ T ^ (eulerIndex q a m).primeFactors.card := by
  classical
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hsig : σ 1 (m ^ 2) = q ^ a * eulerIndex q a m := sigma_sq_eq_mul_eulerIndex h hq hN hqm
  have hJm : eulerIndex q a m ∣ m ^ 2 := eulerIndex_dvd_sq h hq hN hqm
  have hJ0 : eulerIndex q a m ≠ 0 := by
    intro e
    rw [e, mul_zero] at hsig
    exact (sigma_pos 1 _ hm2).ne' hsig
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hrm : r ∣ m := hrp.dvd_of_dvd_pow ((Nat.dvd_of_mem_primeFactors hr).trans hJm)
  have hrq : r ≠ q := by rintro rfl; exact hqm hrm
  have hrN : r ∣ N := hN ▸ (hrm.trans (dvd_pow_self m two_ne_zero)).mul_left _
  have hr2 : r ≠ 2 := by rintro rfl; exact h.not_two_dvd hrN
  have hr3 : 3 ≤ r := by have := hrp.two_le; omega
  have hfm : N.factorization r = (m ^ 2).factorization r := eib_fac_ne hq hN hm hrq
  have hf2 : (m ^ 2).factorization r = 2 * m.factorization r := by simp [Nat.factorization_pow]
  have hpos : 0 < m.factorization r := hrp.factorization_pos_of_dvd hm hrm
  obtain ⟨n, hn⟩ : ∃ n, n = N.factorization r + 1 := ⟨_, rfl⟩
  rw [← hn] at hT ⊢
  have hn3 : 3 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  -- the receivers
  set X := (insert q (eulerIndex q a m).primeFactors).erase r with hXdef
  have hX : X.card ≤ (eulerIndex q a m).primeFactors.card := by
    have h1 := Finset.card_erase_of_mem
      (Finset.mem_insert_of_mem hr : r ∈ insert q (eulerIndex q a m).primeFactors)
    have h2 := Finset.card_insert_le q (eulerIndex q a m).primeFactors
    rw [hXdef, h1]
    omega
  have hbig : (n.divisors.filter (3 ≤ ·)).card ≤ X.card := by
    calc _ ≤ (X.image fun s => orderOf (r : ZMod s)).card := by
          apply Finset.card_le_card
          intro d hd
          rw [Finset.mem_filter, Nat.mem_divisors] at hd
          have hdn : d ∣ N.factorization r + 1 := hn ▸ hd.1.1
          obtain ⟨s, hs, hsd, ho, -⟩ := exists_prime_dvd_sigma_orderOf_eq hrp hr3 hd.2 hdn
          have hsm : s ∣ q ^ a * eulerIndex q a m := by
            rw [← hsig]
            rw [hfm] at hsd
            exact hsd.trans (eib_sigma_component_dvd hm2 hrp)
          refine Finset.mem_image.mpr ⟨s, Finset.mem_erase.mpr ⟨?_, ?_⟩, ho⟩
          · rintro rfl
            have : Fact s.Prime := ⟨hs⟩
            rw [ZMod.natCast_self, orderOf_zero] at ho
            omega
          · rcases (Nat.Prime.dvd_mul hs).mp hsm with e | e
            · rw [(Nat.prime_dvd_prime_iff_eq hs hq).mp (hs.dvd_of_dvd_pow e)]
              exact Finset.mem_insert_self q _
            · exact Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hs, e, hJ0⟩)
      _ ≤ _ := Finset.card_image_le
  have hsmall : n.divisors ⊆ insert 1 (n.divisors.filter (3 ≤ ·)) := by
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    rw [Finset.mem_insert, Finset.mem_filter]
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hdn
      omega
    have hd2 : d ≠ 2 := by
      rintro rfl
      omega
    by_cases h3 : 3 ≤ d
    · exact Or.inr ⟨hd, h3⟩
    · left
      omega
  have hcard : n.divisors.card ≤ (eulerIndex q a m).primeFactors.card + 1 := by
    have := (Finset.card_le_card hsmall).trans (Finset.card_insert_le _ _)
    omega
  have hT1 : 1 ≤ T := by
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    have := hT p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩)
    have := hp.two_le
    omega
  exact (eib_le_pow_card_divisors hn0 hT1 hT).trans (Nat.pow_le_pow_right hT1 (by omega))


/-- Class (c): an ordinary prime `p` with `σ(p ^ e) = q ^ w`, `e ≥ 2` and `v_p(σ(q ^ a)) = e`
divides `L = (a + 1) / 2`, twice or without dividing `q - 1`. -/
private lemma eib_class_c {q a p e w : ℕ} (hq : q.Prime) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q) (ha : Odd a) (he : 2 ≤ e) (hv : (σ 1 (q ^ a)).factorization p = e)
    (hw : q ^ w = σ 1 (p ^ e)) :
    2 ≤ ((a + 1) / 2).factorization p ∨
      (1 ≤ ((a + 1) / 2).factorization p ∧ ¬ p ∣ q - 1) := by
  have hF : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, rfl⟩ := ha
  have hL : (2 * t + 1 + 1) / 2 = t + 1 := by omega
  rw [hL]
  have hL2 : 2 * t + 1 + 1 = 2 * (t + 1) := by ring
  have hfL : (2 * t + 1 + 1).factorization p = (t + 1).factorization p := by
    rw [hL2, Nat.factorization_mul two_ne_zero (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)), zero_add]
  have hdvd : p ∣ σ 1 (q ^ (2 * t + 1)) := Nat.dvd_of_factorization_pos (by omega)
  have hiff := (dvd_sigma_prime_pow_iff hq hp (Ne.symm hpq)).mp hdvd
  by_cases h1 : orderOf (q : ZMod p) = 1
  · left
    have hc : (q : ZMod p) = 1 := orderOf_eq_one_iff.mp h1
    have hqp : q % p = 1 := by
      have := (ZMod.natCast_eq_natCast_iff' q 1 p).mp (by simpa using hc)
      rwa [Nat.mod_eq_of_lt hp.one_lt] at this
    have := padicValNat_sigma_of_mod_eq_one (a := 2 * t + 1) hq hp hp2 hqp
    rw [eib_pv hp, eib_pv hp, hv, hfL] at this
    omega
  · right
    simp only [h1, ↓reduceIte] at hiff
    have hd0 : orderOf (q : ZMod p) ≠ 0 := by
      intro h0
      rw [h0, zero_dvd_iff] at hiff
      omega
    have h1' : 1 < orderOf (q : ZMod p) := by omega
    have key := padicValNat_sigma_prime_pow_of_orderOf_dvd hq hp hp2 (Ne.symm hpq) h1' hiff
    rw [eib_pv hp, eib_pv hp, eib_pv hp, hv] at key
    obtain ⟨j, rfl⟩ : ∃ j, e = j + 2 := ⟨e - 2, by omega⟩
    have hs1 := eib_sigma_succ_mul hp (j + 1)
    have hs2 := eib_sigma_succ_mul hp j
    have hqw : q ^ w - 1 = p * (p * σ 1 (p ^ j) + 1) := by
      rw [hw, hs1, hs2, Nat.add_sub_cancel_left]
      ring
    have hqw0 : q ^ w - 1 ≠ 0 := by
      rw [hqw]
      exact mul_ne_zero hp.ne_zero (by omega)
    have hfw : (q ^ w - 1).factorization p = 1 := by
      rw [hqw, Nat.factorization_mul hp.ne_zero (by omega), Finsupp.add_apply,
        hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd]
      intro hd
      have h0 := Nat.mod_eq_zero_of_dvd hd
      rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt hp.one_lt] at h0
      omega
    have hdw : orderOf (q : ZMod p) ∣ w := by
      apply orderOf_dvd_of_pow_eq_one
      have e1 : q ^ w = p * (p * σ 1 (p ^ j) + 1) + 1 := by omega
      have : ((q ^ w : ℕ) : ZMod p) = 1 := by
        rw [e1]
        push_cast
        rw [ZMod.natCast_self]
        ring
      exact_mod_cast this
    have hdvd2 : q ^ orderOf (q : ZMod p) - 1 ∣ q ^ w - 1 := by
      obtain ⟨c, hc⟩ := hdw
      rw [hc, pow_mul]
      simpa using Nat.sub_dvd_pow_sub_pow (q ^ orderOf (q : ZMod p)) 1 c
    have hqd0 : q ^ orderOf (q : ZMod p) - 1 ≠ 0 := by
      have := Nat.one_lt_pow hd0 hq.one_lt
      omega
    have hle := Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hqd0 hqw0).mpr hdvd2) p
    rw [hfw] at hle
    have hpd : p ∣ 2 * t + 1 + 1 :=
      (Nat.dvd_of_factorization_pos (by omega)).trans (Nat.div_dvd_of_dvd hiff)
    refine ⟨?_, ?_⟩
    · rw [← hfL]
      exact (hp.dvd_iff_one_le_factorization (by omega)).mp hpd
    · intro hpq1
      apply h1
      apply orderOf_eq_one_iff.mpr
      have h0 : ((q - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq1
      rw [Nat.cast_sub hq.one_lt.le, Nat.cast_one, sub_eq_zero] at h0
      exact h0

/-- Theorem A with the signed count of `OddPerfect.EulerIndexOmegaSigned` as a hypothesis. -/
private lemma eib_card_le_core {N q a m k E : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hk : (eulerIndex q a m).primeFactors.card ≤ k)
    (hE : ∀ r ∈ (eulerIndex q a m).primeFactors, N.factorization r ≤ E)
    (hsg : cardFactors ((a + 1) / 2) +
        ∑ p ∈ ((a + 1) / 2).primeFactors.filter (fun p => ¬ p ∣ q - 1),
          ((a + 1) / 2).factorization p ≤
      ((eulerIndex q a m).primeFactors.filter
        fun t => Odd ((eulerIndex q a m).factorization t)).card) :
    N.primeFactors.card ≤ 1 + k * (E + 1) + k / 2 := by
  classical
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hsig : σ 1 (m ^ 2) = q ^ a * eulerIndex q a m := sigma_sq_eq_mul_eulerIndex h hq hN hqm
  have hspec : σ 1 (q ^ a) * eulerIndex q a m = 2 * m ^ 2 :=
    sigma_special_mul_eulerIndex h hq hN hqm
  have hJm : eulerIndex q a m ∣ m ^ 2 := eulerIndex_dvd_sq h hq hN hqm
  have hJ0 : eulerIndex q a m ≠ 0 := by
    intro e
    rw [e, mul_zero] at hsig
    exact (sigma_pos 1 _ hm2).ne' hsig
  have ha : Odd a := by
    rcases Nat.even_or_odd a with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  have hm2N : m ^ 2 ∣ N := by rw [hN]; exact dvd_mul_left _ _
  have hmN : m ∣ N := (dvd_pow_self m two_ne_zero).trans hm2N
  have hord : ∀ p ∈ m.primeFactors, p.Prime ∧ p ≠ 2 ∧ p ≠ q ∧ p ∈ N.primeFactors ∧
      N.factorization p = (m ^ 2).factorization p ∧ 2 ≤ N.factorization p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpm := Nat.dvd_of_mem_primeFactors hp
    have hpq : p ≠ q := by rintro rfl; exact hqm hpm
    have hpN : p ∣ N := hpm.trans hmN
    have hp2 : p ≠ 2 := by rintro rfl; exact h.not_two_dvd hpN
    have hf := eib_fac_ne hq hN hm hpq
    have hf2 : (m ^ 2).factorization p = 2 * m.factorization p := by
      simp [Nat.factorization_pow]
    have hpos : 0 < m.factorization p := hpp.factorization_pos_of_dvd hm hpm
    exact ⟨hpp, hp2, hpq, Nat.mem_primeFactors.mpr ⟨hpp, hpN, h.ne_zero⟩, hf, by omega⟩
  have hNm : N.primeFactors.card ≤ m.primeFactors.card + 1 := by
    have hsub : N.primeFactors ⊆ insert q m.primeFactors := by
      intro x hx
      have hxp := Nat.prime_of_mem_primeFactors hx
      have hxN := Nat.dvd_of_mem_primeFactors hx
      rw [hN] at hxN
      rw [Finset.mem_insert]
      rcases (Nat.Prime.dvd_mul hxp).mp hxN with e | e
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hxp hq).mp (hxp.dvd_of_dvd_pow e))
      · exact Or.inr (Nat.mem_primeFactors.mpr ⟨hxp, hxp.dvd_of_dvd_pow e, hm⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, A = m.primeFactors.filter
      (fun p => ∃ r ∈ (eulerIndex q a m).primeFactors, r ∣ σ 1 (p ^ N.factorization p)) :=
    ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Finset ℕ, R = m.primeFactors.filter
      (fun p => ¬ ∃ r ∈ (eulerIndex q a m).primeFactors, r ∣ σ 1 (p ^ N.factorization p)) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset ℕ, B = R.filter (fun p => p ∈ (eulerIndex q a m).primeFactors) :=
    ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Finset ℕ, C = R.filter (fun p => p ∉ (eulerIndex q a m).primeFactors) :=
    ⟨_, rfl⟩
  have hsplit1 : A.card + R.card = m.primeFactors.card := by
    rw [hA, hR]
    exact Finset.card_filter_add_card_filter_not (s := m.primeFactors)
      (fun p => ∃ r ∈ (eulerIndex q a m).primeFactors, r ∣ σ 1 (p ^ N.factorization p))
  have hsplit2 : B.card + C.card = R.card := by
    rw [hB, hC]
    exact Finset.card_filter_add_card_filter_not (s := R)
      (fun p => p ∈ (eulerIndex q a m).primeFactors)
  -- class (a)
  have hAsub : A ⊆ (eulerIndex q a m).primeFactors.biUnion
      (fun r => (N.primeFactors.erase r).filter (fun p => r ∣ σ 1 (p ^ N.factorization p))) := by
    intro p hp
    rw [hA, Finset.mem_filter] at hp
    obtain ⟨hpm, r, hr, hrd⟩ := hp
    obtain ⟨hpp, -, -, hpN, -, -⟩ := hord p hpm
    refine Finset.mem_biUnion.mpr
      ⟨r, hr, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hpN⟩, hrd⟩⟩
    intro hpr
    subst hpr
    have h0 := padicValNat_sigma_prime_pow_self hpp (N.factorization p)
    rw [eib_pv hpp] at h0
    have := hpp.factorization_pos_of_dvd (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne' hrd
    omega
  have hAcard : A.card ≤ (eulerIndex q a m).primeFactors.card * E := by
    refine (Finset.card_le_card hAsub).trans (Finset.card_biUnion_le.trans ?_)
    calc _ ≤ ∑ r ∈ (eulerIndex q a m).primeFactors, E := by
          apply Finset.sum_le_sum
          intro r hr
          have hrp := Nat.prime_of_mem_primeFactors hr
          have hrN : r ∣ N := (Nat.dvd_of_mem_primeFactors hr).trans (hJm.trans hm2N)
          have hr2 : r ≠ 2 := by rintro rfl; exact h.not_two_dvd hrN
          have hled := factorization_eq_sum_erase h.perfect hrp hr2
          calc _ = ∑ p ∈ (N.primeFactors.erase r).filter
                  (fun p => r ∣ σ 1 (p ^ N.factorization p)), 1 := Finset.card_eq_sum_ones _
            _ ≤ ∑ p ∈ (N.primeFactors.erase r).filter
                  (fun p => r ∣ σ 1 (p ^ N.factorization p)),
                  padicValNat r (σ 1 (p ^ N.factorization p)) := by
                apply Finset.sum_le_sum
                intro p hp
                rw [Finset.mem_filter] at hp
                have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp.1)
                rw [eib_pv hrp]
                exact hrp.factorization_pos_of_dvd
                  (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne' hp.2
            _ ≤ ∑ p ∈ N.primeFactors.erase r, padicValNat r (σ 1 (p ^ N.factorization p)) :=
                Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
            _ = N.factorization r := hled.symm
            _ ≤ E := hE r hr
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  -- class (b)
  have hBcard : B.card ≤ (eulerIndex q a m).primeFactors.card := by
    rw [hB]
    exact Finset.card_le_card fun p hp => (Finset.mem_filter.mp hp).2
  -- class (c)
  have hCg : ∀ p ∈ C, p ∈ ((a + 1) / 2).primeFactors ∧
      2 ≤ ((a + 1) / 2).factorization p +
        (if ¬ p ∣ q - 1 then ((a + 1) / 2).factorization p else 0) := by
    intro p hp
    rw [hC, hR, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨hpm, hnA⟩, hpJ⟩ := hp
    obtain ⟨hpp, hp2, hpq, hpN, hfm, he⟩ := hord p hpm
    have hpJ' : ¬ p ∣ eulerIndex q a m := fun hd => hpJ (Nat.mem_primeFactors.mpr ⟨hpp, hd, hJ0⟩)
    have hp2' : ¬ p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hd)
    have hv : (σ 1 (q ^ a)).factorization p = N.factorization p := by
      have h1 : (σ 1 (q ^ a) * eulerIndex q a m).factorization p =
          (2 * m ^ 2).factorization p := by rw [hspec]
      rw [Nat.factorization_mul (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne' hJ0,
        Nat.factorization_mul two_ne_zero hm2, Finsupp.add_apply, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpJ', Nat.factorization_eq_zero_of_not_dvd hp2'] at h1
      omega
    have hrow0 : σ 1 (p ^ N.factorization p) ≠ 0 :=
      (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hrow0 (p := q) (fun {s} hs hsd => by
      have hsm : s ∣ q ^ a * eulerIndex q a m := by
        rw [← hsig]
        have hsd' : s ∣ σ 1 (p ^ (m ^ 2).factorization p) := by rwa [hfm] at hsd
        exact hsd'.trans (eib_sigma_component_dvd hm2 hpp)
      rcases (Nat.Prime.dvd_mul hs).mp hsm with e | e
      · exact (Nat.prime_dvd_prime_iff_eq hs hq).mp (hs.dvd_of_dvd_pow e)
      · exact absurd ⟨s, Nat.mem_primeFactors.mpr ⟨hs, e, hJ0⟩, hsd⟩ hnA)
    have hcl := eib_class_c hq hpp hp2 hpq ha he hv hpow.symm
    have hL0 : (a + 1) / 2 ≠ 0 := by obtain ⟨t, ht⟩ := ha; omega
    refine ⟨?_, ?_⟩
    · have : 1 ≤ ((a + 1) / 2).factorization p := by rcases hcl with h' | h' <;> omega
      exact Nat.mem_primeFactors.mpr ⟨hpp, Nat.dvd_of_factorization_pos (by omega), hL0⟩
    · rcases hcl with h' | ⟨h', h''⟩
      · split_ifs <;> omega
      · simp only [h'', not_false_eq_true, ↓reduceIte]
        omega
  have hC2 : 2 * C.card ≤ (eulerIndex q a m).primeFactors.card := by
    have hsub : C ⊆ ((a + 1) / 2).primeFactors := fun p hp => (hCg p hp).1
    calc 2 * C.card = ∑ p ∈ C, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ p ∈ C, (((a + 1) / 2).factorization p +
            (if ¬ p ∣ q - 1 then ((a + 1) / 2).factorization p else 0)) :=
          Finset.sum_le_sum fun p hp => (hCg p hp).2
      _ ≤ ∑ p ∈ ((a + 1) / 2).primeFactors, (((a + 1) / 2).factorization p +
            (if ¬ p ∣ q - 1 then ((a + 1) / 2).factorization p else 0)) :=
          Finset.sum_le_sum_of_subset hsub
      _ = cardFactors ((a + 1) / 2) +
            ∑ p ∈ ((a + 1) / 2).primeFactors.filter (fun p => ¬ p ∣ q - 1),
              ((a + 1) / 2).factorization p := by
          rw [Finset.sum_add_distrib, Finset.sum_filter, cardFactors_eq_sum_factorization,
            Finsupp.sum, Nat.support_factorization]
      _ ≤ _ := hsg
      _ ≤ _ := Finset.card_filter_le _ _
  have hkE : (eulerIndex q a m).primeFactors.card * E ≤ k * E := Nat.mul_le_mul_right E hk
  have hexp : k * (E + 1) = k * E + k := by ring
  rw [hexp]
  generalize (eulerIndex q a m).primeFactors.card * E = X at *
  generalize k * E = Y at *
  omega

/-- For every odd perfect number `N = q ^ a * m ^ 2` with special prime `q` and `q ∤ m`: if
every prime factor of the Euler index `J` has exponent at most `E` in `N` and `ω(J) ≤ k`, then
`ω(N) ≤ 1 + k (E + 1) + k / 2`. A bound through quantities of the Euler index only; nothing is
excluded. Restricted result; no published source was checked; novelty not verified. -/
theorem card_primeFactors_le_of_eulerIndex_exponents {N q a m k E : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m)
    (hk : (eulerIndex q a m).primeFactors.card ≤ k)
    (hE : ∀ r ∈ (eulerIndex q a m).primeFactors, N.factorization r ≤ E) :
    N.primeFactors.card ≤ 1 + k * (E + 1) + k / 2 :=
  eib_card_le_core h hq hN hqm hk hE
    (cardFactors_add_signed_le_card_odd_valuation_eulerIndex h hq hN hqm)

end OddPerfect

#print axioms OddPerfect.factorization_succ_le_pow_of_mem_eulerIndex
#print axioms OddPerfect.card_primeFactors_le_of_eulerIndex_exponents
