import OddPerfect.EulerPart
import OddPerfect.SquareRow

/-!
# An Euler index supported on two primes

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and let `J = eulerIndex q 1 m`, so that `σ(m ^ 2) = q J`, `(q + 1) J = 2 m ^ 2` and
`J ∣ m ^ 2`. This module studies the case where `J` has exactly two prime factors `r ≠ s`.

* `eulerIndex_pair_sender`: for a labeling `(t, u)` of `{r, s}`, with `e = v_t(N)` and
  `f = v_u(N)`, we have `σ(t ^ e) = q u ^ v`, `σ(u ^ f) = t ^ j` with `j > 0`, `t ∤ q + 1` and
  `v_t(J) = v_t(N)`.
* `eulerIndex_pair_not_both_odd`: `v_r(J)` and `v_s(J)` are not both odd.
* `eulerIndex_pair_not_both_three_mod_four`: `r` and `s` are not both `≡ 3 (mod 4)`.

These are restricted results (special exponent 1, index supported on two primes). Their
novelty has not been verified, and they do not exclude this family of odd perfect numbers.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPair

/-- `σ(n) = σ(p ^ v_p(n)) σ(n / p ^ v_p(n))`. -/
private lemma sigma_split {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    σ 1 n = σ 1 (p ^ n.factorization p) * σ 1 (ordCompl[p] n) := by
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  exact isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_ordCompl hp hn).pow_left _)

/-- The row of one prime divides `σ(n)`. -/
private lemma row_dvd {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    σ 1 (p ^ n.factorization p) ∣ σ 1 n :=
  ⟨_, sigma_split hp hn⟩

/-- The rows of two distinct primes divide `σ(n)` together. -/
private lemma pair_dvd {n p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hpp : p ≠ p')
    (hn : n ≠ 0) :
    σ 1 (p ^ n.factorization p) * σ 1 (p' ^ n.factorization p') ∣ σ 1 n := by
  rw [sigma_split hp hn]
  have h0 : ordCompl[p] n ≠ 0 := (Nat.ordCompl_pos p hn).ne'
  have hf : (ordCompl[p] n).factorization p' = n.factorization p' := by
    rw [Nat.factorization_ordCompl, Finsupp.erase_ne hpp.symm]
  exact mul_dvd_mul_left _ (hf ▸ row_dvd hp' h0)

/-- `p ^ e < σ(p ^ e)` for `e ≠ 0`. -/
private lemma pow_lt_sigma {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) : p ^ e < σ 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  have : p ^ 0 ≤ ∑ i ∈ Finset.range e, p ^ i :=
    Finset.single_le_sum (f := fun i => p ^ i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.pos_of_ne_zero he))
  simp only [pow_zero] at this
  omega

/-- A prime `p` does not divide `σ(p ^ e)`. -/
private lemma not_dvd_sigma_self {p e : ℕ} (hp : p.Prime) : ¬ p ∣ σ 1 (p ^ e) := fun hd =>
  hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (coprime_sigma_prime_pow hp e).symm hd)

/-- A prime divisor of `q * J` that is not `q` lies in the support of `J`. -/
private lemma mem_of_dvd {q J p : ℕ} (hq : q.Prime) (hp : p.Prime) (hJ : J ≠ 0)
    (hd : p ∣ q * J) (hpq : p ≠ q) : p ∈ J.primeFactors := by
  refine Nat.mem_primeFactors.mpr ⟨hp, ?_, hJ⟩
  rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp h) hpq
  · exact h

/-- Step (iii): a row of `r` not divisible by `q` is at most `s ^ v_s(n)`. -/
private lemma row_le {n q J r s : ℕ} (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hn : n ≠ 0) (hσ : σ 1 n = q * J) (hJn : J ∣ n) (hJ : J.primeFactors = {r, s})
    (hnq : ¬ q ∣ σ 1 (r ^ n.factorization r)) :
    σ 1 (r ^ n.factorization r) ≤ s ^ n.factorization s := by
  set A := σ 1 (r ^ n.factorization r)
  have hJ0 : J ≠ 0 := by
    rintro rfl; simp at hJ; exact Finset.insert_ne_empty _ _ hJ.symm
  have hA0 : A ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hr.ne_zero)).ne'
  have hAJ : A ∣ J :=
    ((hq.coprime_iff_not_dvd.mpr hnq).symm).dvd_of_dvd_mul_left (hσ ▸ row_dvd hr hn)
  have hAs : A = s ^ A.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hA0 fun {d} hd hdA => ?_
    have hmem : d ∈ J.primeFactors := Nat.mem_primeFactors.mpr ⟨hd, hdA.trans hAJ, hJ0⟩
    rw [hJ] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact absurd (h ▸ hdA) (not_dvd_sigma_self hr)
    · exact Finset.mem_singleton.mp h
  have hle : A.primeFactorsList.length ≤ n.factorization s :=
    (hs.pow_dvd_iff_le_factorization hn).mp (hAs ▸ hAJ.trans hJn)
  rw [hAs]
  exact Nat.pow_le_pow_right hs.pos hle

/-- Geometric sums with ratio `≡ -1`: `σ(p ^ e) ≡ 1` for even `e`. -/
private lemma sigma_cast_neg_one {n p e : ℕ} (hp : p.Prime) (he : Even e)
    (hpn : (p : ZMod n) = -1) : ((σ 1 (p ^ e) : ℕ) : ZMod n) = 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  rw [hpn, neg_one_geom_sum, if_neg (by rw [Nat.even_add_one]; exact not_not.mpr he)]

/-- The common setting, stated for `n = m ^ 2`. -/
private structure Setting (q J n : ℕ) : Prop where
  hq : q.Prime
  hn : n ≠ 0
  hσ : σ 1 n = q * J
  hJn : J ∣ n
  hqJ : ¬ q ∣ J
  hJo : Odd J
  hJ2 : (q + 1) * J = 2 * n

/-- The facts of Theorem 1 for an ordered pair `(t, u)` whose `t` row carries `q`. -/
private lemma ordered {q J n t u : ℕ} (H : Setting q J n) (ht : t.Prime) (hu : u.Prime)
    (htu : t ≠ u) (hJ : J.primeFactors = {t, u}) (hfe : Even (n.factorization u))
    (hqt : q ∣ σ 1 (t ^ n.factorization t)) :
    (∃ v, σ 1 (t ^ n.factorization t) = q * u ^ v) ∧
      (∃ j, 0 < j ∧ σ 1 (u ^ n.factorization u) = t ^ j) ∧ ¬ t ∣ q + 1 ∧
      J.factorization t = n.factorization t := by
  obtain ⟨hq, hn, hσ, hJn, hqJ, hJo, hJ2⟩ := H
  set A := σ 1 (t ^ n.factorization t)
  set B := σ 1 (u ^ n.factorization u)
  have hJ0 : J ≠ 0 := by
    rintro rfl; simp at hJ; exact Finset.insert_ne_empty _ _ hJ.symm
  have hA0 : A ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ ht.ne_zero)).ne'
  have hB0 : B ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hu.ne_zero)).ne'
  have htJ : t ∈ J.primeFactors := by rw [hJ]; simp
  have huJ : u ∈ J.primeFactors := by rw [hJ]; simp
  have ht2 : t ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hJo) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors htJ))
  -- `q * q` does not divide `σ(n)`
  have hqq : ¬ q * q ∣ σ 1 n := by
    rw [hσ]; exact fun h => hqJ (Nat.dvd_of_mul_dvd_mul_left hq.pos h)
  have hqB : ¬ q ∣ B := fun h => hqq ((mul_dvd_mul hqt h).trans (pair_dvd ht hu htu hn))
  -- the `t` row
  obtain ⟨X, hX⟩ := hqt
  have hX0 : X ≠ 0 := by rintro rfl; simp at hX; exact hA0 hX
  have hqX : ¬ q ∣ X := fun h => hqq (hX ▸ (mul_dvd_mul_left q h) |>.trans (row_dvd ht hn))
  have hXu : X = u ^ X.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hX0 fun {d} hd hdX => ?_
    have hdq : d ≠ q := by rintro rfl; exact hqX hdX
    have hdA : d ∣ A := hX ▸ dvd_mul_of_dvd_right hdX q
    have hmem := mem_of_dvd hq hd hJ0 (hσ ▸ hdA.trans (row_dvd ht hn)) hdq
    rw [hJ] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact absurd (h ▸ hdA) (not_dvd_sigma_self ht)
    · exact Finset.mem_singleton.mp h
  -- the `u` row
  have hBt : B = t ^ B.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hB0 fun {d} hd hdB => ?_
    have hdq : d ≠ q := by rintro rfl; exact hqB hdB
    have hmem := mem_of_dvd hq hd hJ0 (hσ ▸ hdB.trans (row_dvd hu hn)) hdq
    rw [hJ] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exact absurd (Finset.mem_singleton.mp h ▸ hdB) (not_dvd_sigma_self hu)
  obtain ⟨v, hXv⟩ : ∃ v, X = u ^ v := ⟨_, hXu⟩
  obtain ⟨j, hBj⟩ : ∃ j, B = t ^ j := ⟨_, hBt⟩
  clear hXu hBt
  have hf0 : n.factorization u ≠ 0 :=
    (hu.factorization_pos_of_dvd hn ((Nat.dvd_of_mem_primeFactors huJ).trans hJn)).ne'
  have hj : 0 < j := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h1 : u ^ n.factorization u < B := pow_lt_sigma hu hf0
    have h2 := Nat.one_le_pow (n.factorization u) u hu.pos
    rw [h0, pow_zero] at hBj
    omega
  -- `t ∤ q + 1`
  have hfact : ¬ t ∣ q + 1 := by
    intro hdt
    have : Fact t.Prime := ⟨ht⟩
    set f := n.factorization u
    have hA1 : ((A : ℕ) : ZMod t) = 1 := by
      simp only [A, sigma_one_apply_prime_pow ht]
      rw [Finset.sum_range_succ']
      push_cast
      simp
    have hB1 : ((u : ZMod t)) ^ (f + 1) = 1 := by
      have hg := geom_sum_mul (u : ZMod t) (f + 1)
      have hB : ((B : ℕ) : ZMod t) = 0 := by
        rw [hBj, Nat.cast_pow, ZMod.natCast_self, zero_pow hj.ne']
      simp only [B, sigma_one_apply_prime_pow hu] at hB
      push_cast at hB
      rw [hB, zero_mul] at hg
      exact (sub_eq_zero.mp hg.symm)
    have hqm1 : (q : ZMod t) = -1 := by
      have : ((q + 1 : ℕ) : ZMod t) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdt
      push_cast at this
      exact eq_neg_of_add_eq_zero_left this
    have hAq : (q : ZMod t) * (u : ZMod t) ^ v = 1 := by
      rw [← hA1, hX, hXv]; push_cast; ring
    have hpow : (q : ZMod t) ^ (f + 1) = 1 := by
      calc (q : ZMod t) ^ (f + 1)
          = ((q : ZMod t) * (u : ZMod t) ^ v) ^ (f + 1) := by
            rw [mul_pow, ← pow_mul, mul_comm v, pow_mul, hB1, one_pow, mul_one]
        _ = 1 := by rw [hAq, one_pow]
    rw [hqm1, Odd.neg_one_pow (Even.add_one hfe)] at hpow
    have h2 : ((2 : ℕ) : ZMod t) = 0 := by
      have : (2 : ZMod t) = 1 - -1 := by ring
      push_cast
      rw [this, hpow, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact ht2 ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_two).mp h2)
  refine ⟨⟨v, hX.trans (by rw [hXv])⟩, ⟨j, hj, hBj⟩, hfact, ?_⟩
  -- valuations from `(q + 1) J = 2 n`
  have hv : ((q + 1) * J).factorization t = (2 * n).factorization t := by rw [hJ2]
  rw [Nat.factorization_mul (by omega) hJ0, Nat.factorization_mul two_ne_zero hn,
    Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hfact,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => ht2 ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_two).mp h))] at hv
  omega

/-- The labeling of Theorem 1, together with the `q` row, in the language of `n = m ^ 2`. -/
private lemma labeling {q J n r s : ℕ} (H : Setting q J n) (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (hJ : J.primeFactors = {r, s}) (hev : ∀ p, Even (n.factorization p)) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧ t.Prime ∧ u.Prime ∧
      q ∣ σ 1 (t ^ n.factorization t) ∧
      (∃ v, σ 1 (t ^ n.factorization t) = q * u ^ v) ∧
      (∃ j, 0 < j ∧ σ 1 (u ^ n.factorization u) = t ^ j) ∧ ¬ t ∣ q + 1 ∧
      J.factorization t = n.factorization t := by
  by_cases hqr : q ∣ σ 1 (r ^ n.factorization r)
  · exact ⟨r, s, rfl, hrs, hr, hs, hqr, ordered H hr hs hrs hJ (hev s) hqr⟩
  by_cases hqs : q ∣ σ 1 (s ^ n.factorization s)
  · refine ⟨s, r, Finset.pair_comm s r, hrs.symm, hs, hr, hqs,
      ordered H hs hr hrs.symm (by rw [hJ, Finset.pair_comm]) (hev r) hqs⟩
  exfalso
  have hJn := H.hJn
  have hrJ : r ∣ J := Nat.dvd_of_mem_primeFactors (by rw [hJ]; simp)
  have hsJ : s ∣ J := Nat.dvd_of_mem_primeFactors (by rw [hJ]; simp)
  have h1 := row_le H.hq hr hs H.hn H.hσ hJn hJ hqr
  have h2 := row_le H.hq hs hr H.hn H.hσ hJn (by rw [hJ, Finset.pair_comm]) hqs
  have h3 := pow_lt_sigma hr (hr.factorization_pos_of_dvd H.hn (hrJ.trans hJn)).ne'
  have h4 := pow_lt_sigma hs (hs.factorization_pos_of_dvd H.hn (hsJ.trans hJn)).ne'
  omega

/-- The setting and the exponent bridge for an odd perfect number `q * m ^ 2`. -/
private lemma setting {N q m : ℕ} (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) :
    Setting q (eulerIndex q 1 m) (m ^ 2) ∧ (∀ p, Even ((m ^ 2).factorization p)) ∧
      ∀ p, p ≠ q → N.factorization p = (m ^ 2).factorization p := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hσ := sigma_sq_eq_mul_eulerIndex h hq hN1 hqm
  have hJ2 := sigma_special_mul_eulerIndex h hq hN1 hqm
  rw [pow_one] at hσ
  rw [sigma_one_apply_prime_pow hq] at hJ2
  simp [Finset.sum_range_succ, add_comm] at hJ2
  have hJn := eulerIndex_dvd_sq h hq hN1 hqm
  refine ⟨⟨hq, pow_ne_zero _ hm, hσ, hJn, fun hd => hqm (hq.dvd_of_dvd_pow (hd.trans hJn)),
    odd_eulerIndex h hq hN1 hqm, hJ2⟩, fun p => ?_, fun p hp => ?_⟩
  · rw [Nat.factorization_pow]; exact ⟨m.factorization p, by simp [two_mul]⟩
  · rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
      hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hp), zero_add]

/-- `w ^ 2 + w + 1` divides `∑_{i < 3 k} w ^ i`. -/
private lemma geom_three_dvd (w k : ℕ) :
    w ^ 2 + w + 1 ∣ ∑ i ∈ Finset.range (3 * k), w ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + w ^ (3 * k), ?_⟩
    rw [show 3 * (k + 1) = 3 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, hc]
    ring

/-- No root of `x ^ 2 + x + 1` modulo 11. -/
private lemma no_root_eleven : ∀ x : ZMod 11, x ^ 2 + x + 1 ≠ 0 := by decide

/-- Theorem 3 for an ordered pair `(t, u)` whose `t` row carries `q`. -/
private lemma not_both_three {q J n t u j : ℕ} (H : Setting q J n) (ht : t.Prime)
    (hu : u.Prime) (hJ : J.primeFactors = {t, u}) (hev : ∀ p, Even (n.factorization p))
    (hqt : q ∣ σ 1 (t ^ n.factorization t)) (hj : 0 < j)
    (hB : σ 1 (u ^ n.factorization u) = t ^ j) (ht4 : t % 4 = 3) (hu4 : u % 4 = 3) : False := by
  obtain ⟨hq, hn, hσ, hJn, hqJ, -, -⟩ := H
  have hJ0 : J ≠ 0 := by
    rintro rfl; simp at hJ; exact Finset.insert_ne_empty _ _ hJ.symm
  have huJ : u ∣ J := Nat.dvd_of_mem_primeFactors (by rw [hJ]; simp)
  have hf0 : n.factorization u ≠ 0 := (hu.factorization_pos_of_dvd hn (huJ.trans hJn)).ne'
  have hu2 : u ≠ 2 := by omega
  -- `j` is even, so the `u` row is a square
  have hje : Even j := by
    have h1 : ((σ 1 (u ^ n.factorization u) : ℕ) : ZMod 4) = 1 :=
      sigma_cast_neg_one hu (hev u) (by rw [← ZMod.natCast_mod, hu4]; decide)
    have ht' : (t : ZMod 4) = -1 := by rw [← ZMod.natCast_mod, ht4]; decide
    rw [hB, Nat.cast_pow, ht'] at h1
    rcases Nat.even_or_odd j with he | ho
    · exact he
    · rw [ho.neg_one_pow] at h1; exact absurd h1 (by decide)
  obtain ⟨i, hi⟩ := hje
  have hsq : IsSquare (σ 1 (u ^ n.factorization u)) := ⟨t ^ i, by rw [hB, hi, pow_add]⟩
  obtain ⟨rfl, hf4⟩ := (isSquare_sigma_prime_pow_iff hu hu2 (hev u) hf0).mp hsq
  have h121 : σ 1 (3 ^ 4) = 121 := by
    rw [sigma_one_apply_prime_pow Nat.prime_three]; norm_num [Finset.sum_range_succ]
  rw [hf4, h121] at hB
  have h11 : t = 11 := by
    have hd : t ∣ 11 ^ 2 := by
      rw [show (11 : ℕ) ^ 2 = 121 by norm_num, hB]; exact dvd_pow_self t hj.ne'
    exact (Nat.prime_dvd_prime_iff_eq ht (by norm_num)).mp (ht.dvd_of_dvd_pow hd)
  subst h11
  -- the rows of 3 and 11 carry no factor 3
  have h3A : ¬ 3 ∣ σ 1 (11 ^ n.factorization 11) := by
    intro hd
    have h1 := sigma_cast_neg_one (n := 3) ht (hev 11) (by decide)
    rw [(ZMod.natCast_eq_zero_iff _ 3).mpr hd] at h1
    exact absurd h1 (by decide)
  have h3J : 3 ∣ J := Nat.dvd_of_mem_primeFactors (by rw [hJ]; simp)
  have h3n : 3 ∣ σ 1 n := hσ ▸ dvd_mul_of_dvd_right h3J q
  have hn1 : ordCompl[3] n ≠ 0 := (Nat.ordCompl_pos 3 hn).ne'
  have hM : ordCompl[11] (ordCompl[3] n) ≠ 0 := (Nat.ordCompl_pos 11 hn1).ne'
  have hf11 : (ordCompl[3] n).factorization 11 = n.factorization 11 := by
    rw [Nat.factorization_ordCompl, Finsupp.erase_ne (by norm_num)]
  have hrow3 : σ 1 (3 ^ n.factorization 3) = 121 := by rw [hf4, h121]
  rw [sigma_split Nat.prime_three hn, hrow3, sigma_split ht hn1] at h3n
  set M := ordCompl[11] (ordCompl[3] n)
  have h3M : 3 ∣ σ 1 M := by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3n with h | h
    · exact absurd h (by norm_num)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · rw [hf11] at h; exact absurd h h3A
    · exact h
  -- a third prime `w` whose row carries 3
  rw [IsMultiplicative.multiplicative_factorization (σ 1) isMultiplicative_sigma hM,
    Finsupp.prod] at h3M
  obtain ⟨w, hwM, hw3⟩ := (Nat.prime_three.prime.dvd_finsetProd_iff _).mp h3M
  have hMfac : M.factorization = (n.factorization.erase 3).erase 11 := by
    rw [Nat.factorization_ordCompl, Nat.factorization_ordCompl]
  have hw0 : M.factorization w ≠ 0 := Finsupp.mem_support_iff.mp hwM
  have hw11 : w ≠ 11 := by
    rintro rfl; rw [hMfac, Finsupp.erase_same] at hw0; exact hw0 rfl
  have hw3' : w ≠ 3 := by
    rintro rfl; rw [hMfac, Finsupp.erase_ne (by norm_num), Finsupp.erase_same] at hw0
    exact hw0 rfl
  have hwg : M.factorization w = n.factorization w := by
    rw [hMfac, Finsupp.erase_ne hw11, Finsupp.erase_ne hw3']
  have hw : w.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization M ▸ hwM)
  rw [hwg] at hw3
  -- its row is coprime to `q`, so it divides `J`
  have hqq : ¬ q * q ∣ σ 1 n := by
    rw [hσ]; exact fun h => hqJ (Nat.dvd_of_mul_dvd_mul_left hq.pos h)
  have hqW : ¬ q ∣ σ 1 (w ^ n.factorization w) := fun hd =>
    hqq ((mul_dvd_mul hqt hd).trans (pair_dvd ht hw hw11.symm hn))
  have hWJ : σ 1 (w ^ n.factorization w) ∣ J :=
    ((hq.coprime_iff_not_dvd.mpr hqW).symm).dvd_of_dvd_mul_left (hσ ▸ row_dvd hw hn)
  -- `w ≡ 1 (mod 3)` and `3 ∣ g + 1`
  have h0 : ((σ 1 (w ^ n.factorization w) : ℕ) : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff _ 3).mpr hw3
  have hw1 : w % 3 = 1 ∧ 3 ∣ n.factorization w + 1 := by
    rcases (by omega : w % 3 = 0 ∨ w % 3 = 1 ∨ w % 3 = 2) with hwm | hwm | hwm
    · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hw).mp
        (Nat.dvd_of_mod_eq_zero hwm)).symm hw3'
    · refine ⟨hwm, ?_⟩
      have hc : (w : ZMod 3) = 1 := by rw [← ZMod.natCast_mod, hwm]; rfl
      rw [sigma_one_apply_prime_pow hw] at h0
      push_cast at h0
      rw [hc] at h0
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h0
      exact (ZMod.natCast_eq_zero_iff _ 3).mp h0
    · have hc : (w : ZMod 3) = -1 := by rw [← ZMod.natCast_mod, hwm]; decide
      rw [sigma_cast_neg_one hw (hev w) hc] at h0
      exact absurd h0 (by decide)
  obtain ⟨k, hk⟩ := hw1.2
  have hX : w ^ 2 + w + 1 ∣ σ 1 (w ^ n.factorization w) := by
    rw [sigma_one_apply_prime_pow hw, hk]; exact geom_three_dvd w k
  have hXJ := hX.trans hWJ
  have hX0 : w ^ 2 + w + 1 ≠ 0 := by omega
  have h11X : ¬ 11 ∣ w ^ 2 + w + 1 := by
    intro hd
    apply no_root_eleven (w : ZMod 11)
    have := (ZMod.natCast_eq_zero_iff (w ^ 2 + w + 1) 11).mpr hd
    push_cast at this
    exact this
  obtain ⟨c, hc⟩ : ∃ c, w ^ 2 + w + 1 = 3 ^ c := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hX0 fun {d} hd hdX => ?_⟩
    have hmem : d ∈ J.primeFactors := Nat.mem_primeFactors.mpr ⟨hd, hdX.trans hXJ, hJ0⟩
    rw [hJ] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact absurd (h ▸ hdX) h11X
    · exact Finset.mem_singleton.mp h
  have h9 : (w ^ 2 + w + 1) % 9 = 3 := by
    obtain ⟨a, ha⟩ : ∃ a, w = 3 * a + 1 := ⟨w / 3, by omega⟩
    have : w ^ 2 + w + 1 = 9 * (a ^ 2 + a) + 3 := by rw [ha]; ring
    rw [this]; omega
  have hw2 := hw.two_le
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · have : w ^ 2 + w + 1 ≤ 3 := by rw [hc]; interval_cases c <;> norm_num
    nlinarith
  · have : 9 ∣ w ^ 2 + w + 1 := by rw [hc]; exact (Nat.pow_dvd_pow 3 hc2 : 3 ^ 2 ∣ 3 ^ c)
    omega

end EulerIndexPair

open EulerIndexPair

variable {N q m r s : ℕ}

/-- **Two prime index, sender row.** Let `N = q m ^ 2` be an odd perfect number with special
prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly
the two prime factors `r ≠ s`. Then for a labeling `(t, u)` of `{r, s}`, with `e = v_t(N)` and
`f = v_u(N)`: `σ(t ^ e) = q u ^ v`, `σ(u ^ f) = t ^ j` with `j > 0`, `t ∤ q + 1` and
`v_t(J) = v_t(N)`. This is a restricted result (special exponent 1, index supported on two
primes); its novelty has not been verified, and it does not exclude this family. -/
theorem eulerIndex_pair_sender (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (∃ j, 0 < j ∧ σ 1 (u ^ N.factorization u) = t ^ j) ∧ ¬ t ∣ q + 1 ∧
      (eulerIndex q 1 m).factorization t = N.factorization t := by
  obtain ⟨H, hev, hbr⟩ := setting h hq hN hqm
  obtain ⟨t, u, htu, hne, ht, hu, -, h1, h2, h3, h4⟩ := labeling H hr hs hrs hJ hev
  have hq' (p : ℕ) (hp : p ∈ ({t, u} : Finset ℕ)) : p ≠ q := by
    rintro rfl
    rw [htu, ← hJ] at hp
    exact H.hqJ (Nat.dvd_of_mem_primeFactors hp)
  refine ⟨t, u, htu, hne, ?_⟩
  rw [hbr t (hq' t (by simp)), hbr u (hq' u (by simp))]
  exact ⟨h1, h2, h3, h4⟩

/-- **Two prime index, parity.** In the setting of `eulerIndex_pair_sender`, the exponents of
`r` and `s` in the index are not both odd. This is a restricted result (special exponent 1,
index supported on two primes); its novelty has not been verified, and it does not exclude
this family. -/
theorem eulerIndex_pair_not_both_odd (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ¬ (Odd ((eulerIndex q 1 m).factorization r) ∧ Odd ((eulerIndex q 1 m).factorization s)) := by
  obtain ⟨H, hev, -⟩ := setting h hq hN hqm
  obtain ⟨t, u, htu, -, -, -, -, -, -, -, h4⟩ := labeling H hr hs hrs hJ hev
  rintro ⟨ho1, ho2⟩
  have hmem : t ∈ ({r, s} : Finset ℕ) := by rw [← htu]; simp
  have he : Even ((eulerIndex q 1 m).factorization t) := h4 ▸ hev t
  rcases Finset.mem_insert.mp hmem with rfl | h'
  · exact (Nat.not_even_iff_odd.mpr ho1) he
  · rw [Finset.mem_singleton.mp h'] at he
    exact (Nat.not_even_iff_odd.mpr ho2) he

/-- **Two prime index, residues modulo 4.** In the setting of `eulerIndex_pair_sender`, the
primes `r` and `s` are not both `≡ 3 (mod 4)`. This is a restricted result (special exponent 1,
index supported on two primes); its novelty has not been verified, and it does not exclude
this family. -/
theorem eulerIndex_pair_not_both_three_mod_four (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) : ¬ (r % 4 = 3 ∧ s % 4 = 3) := by
  rintro ⟨hr4, hs4⟩
  obtain ⟨H, hev, -⟩ := setting h hq hN hqm
  obtain ⟨t, u, htu, -, ht, hu, hqt, -, ⟨j, hj, hB⟩, -, -⟩ := labeling H hr hs hrs hJ hev
  have hmod (p : ℕ) (hp : p ∈ ({t, u} : Finset ℕ)) : p % 4 = 3 := by
    rw [htu] at hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hr4
    · rw [Finset.mem_singleton.mp hp]; exact hs4
  exact not_both_three H ht hu (by rw [htu]; exact hJ) hev hqt hj hB (hmod t (by simp))
    (hmod u (by simp))

end OddPerfect

#print axioms OddPerfect.eulerIndex_pair_sender
#print axioms OddPerfect.eulerIndex_pair_not_both_odd
#print axioms OddPerfect.eulerIndex_pair_not_both_three_mod_four
