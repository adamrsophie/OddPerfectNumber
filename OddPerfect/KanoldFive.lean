import OddPerfect.KanoldGeneral

/-!
# Fifth power cases of Kanold's theorem

Let `N` be an odd perfect number with special prime `q`; the other prime factors are ordinary.
`OddPerfect/KanoldGeneral.lean` proves `l ^ (4 a) ∣ N` when `l ^ a` divides `e_p + 1` for
every ordinary `p`, and the fifth power `l ^ (5 a) ∣ N` (a strengthening found in the
literature on Kanold's theorem) outside a few residual cases. This file treats them.

* `succ_le_card_filter_mod_eq_one`: if `s ≡ 1 (mod q)` is a prime factor with
  `q ^ b ∣ e_s + 1`, then at least `b + 1` prime factors of `N` are `≡ 1 (mod q)`: `s` and
  the primitive prime factors of `Φ_{q ^ j}(s)`, `1 ≤ j ≤ b`.
* `factorization_special_ne`: if `q ^ a` (`a ≥ 2`) divides every ordinary `e_p + 1`, then
  `v_q(N) ≠ a (a + 1) + 1`. With `S` the prime factors `≡ 1 (mod q)`, the budget forces
  `|S| = a + 1`; the previous item then makes each `v_q(e_p + 1)` with `p ∈ S` equal to `a`,
  so the components outside `S` supply exactly `1`. But such a component supplies either `0`
  or `v_q(p ^ d - 1) + v_q((e_p + 1) / d) ≥ 1 + a`.
* `seventeen_le_factorization_special`, `pow_five_mul_dvd_of_special_of_ne_two`: the case
  `a = 3` at the special prime.
* `factorization_five_ne_four`, `pow_five_mul_dvd_of_ne_special`: the ordinary case in full.
* `factorization_five_ne_nine_of_special`, `thirteen_le_factorization_five_of_special`,
  `pow_thirteen_dvd_of_five_special`: the special prime `5` with `25` dividing every
  ordinary `e_p + 1`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Many prime factors `≡ 1 (mod q)`. Let `q ≥ 3`, and let `s` be a prime factor of the odd
perfect number `N` with `s ≡ 1 (mod q)` and `q ^ b ∣ v_s(N) + 1`. Then at least `b + 1` prime
factors of `N` are `≡ 1 (mod q)`. -/
theorem succ_le_card_filter_mod_eq_one {N q s b : ℕ} (h : OddPerfect N) (hq3 : 3 ≤ q)
    (hs : s ∈ N.primeFactors) (hs1 : s % q = 1)
    (hb : q ^ b ∣ N.factorization s + 1) :
    b + 1 ≤ (N.primeFactors.filter (fun p => p % q = 1)).card := by
  have hj : ∀ j ∈ Finset.Icc 1 b, ∃ t ∈ N.primeFactors,
      orderOf (s : ZMod t) = q ^ j ∧ t % q ^ j = 1 := by
    intro j hj
    obtain ⟨hj1, hjb⟩ := Finset.mem_Icc.mp hj
    exact exists_primeFactor_modEq_one h hs (le_trans hq3 (Nat.le_self_pow (by omega) q))
      ((pow_dvd_pow q hjb).trans hb)
  choose! f hfN hfo hfm using hj
  have hfS : ∀ j ∈ Finset.Icc 1 b, f j % q = 1 := by
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    have := Nat.mod_mod_of_dvd (f j) (dvd_pow_self q (by omega : j ≠ 0))
    rw [hfm j hj, Nat.mod_eq_of_lt (by omega)] at this
    exact this.symm
  have hsub : insert s ((Finset.Icc 1 b).image f) ⊆
      N.primeFactors.filter (fun p => p % q = 1) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨hs, hs1⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨hfN j hj, hfS j hj⟩
  have hinj : Set.InjOn f (Finset.Icc 1 b : Set ℕ) := by
    intro i hi j hj hij
    have := hfo i hi
    rw [hij, hfo j hj] at this
    exact Nat.pow_right_injective (by omega) this.symm
  have hnot : s ∉ (Finset.Icc 1 b).image f := by
    intro hx
    have : Fact s.Prime := ⟨Nat.prime_of_mem_primeFactors hs⟩
    obtain ⟨j, hj, hfj⟩ := Finset.mem_image.mp hx
    have := hfo j hj
    rw [hfj, ZMod.natCast_self, orderOf_zero] at this
    exact (pow_ne_zero j (by omega : q ≠ 0)) this.symm
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj,
    Nat.card_Icc, Nat.add_sub_cancel] at this

/-- A component outside the residue class `1 (mod q)` supplies either nothing or more than
`a` to `v_q(N)`. Let `q` be an odd prime and `p ≠ q` a prime with `p ≢ 1 (mod q)` and
`q ^ a ∣ e + 1`. If `q ∣ σ(p ^ e)` then `a + 1 ≤ v_q(σ(p ^ e))`. -/
theorem succ_le_padicValNat_sigma_of_not_mod_eq_one {p q a e : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hpq : p ≠ q) (hp1 : p % q ≠ 1) (hqa : q ^ a ∣ e + 1)
    (hdvd : q ∣ σ 1 (p ^ e)) : a + 1 ≤ padicValNat q (σ 1 (p ^ e)) := by
  have : Fact q.Prime := ⟨hq⟩
  rcases (prime_dvd_sigma_prime_pow hp hq hdvd).2 with ⟨h1, -⟩ | ⟨h1, hd, hdq⟩
  · exact absurd h1 hp1
  rw [padicValNat_sigma_prime_pow_of_orderOf_dvd hp hq hq2 hpq h1 hd]
  set d := orderOf (p : ZMod q) with hdd
  have hpd : 1 < p ^ d := Nat.one_lt_pow (by omega) hp.one_lt
  have hA : 1 ≤ padicValNat q (p ^ d - 1) := by
    refine one_le_padicValNat_of_dvd (by omega) ?_
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpd.le, Nat.cast_pow, hdd, pow_orderOf_eq_one,
      Nat.cast_one, sub_self]
  have hq1 := hq.one_lt
  have hdpos : 0 < d := by omega
  have hdle : d ≤ q - 1 := Nat.le_of_dvd (by omega) hdq
  have hcop : Nat.Coprime (q ^ a) d := by
    refine Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun hqd => ?_)
    have := Nat.le_of_dvd hdpos hqd
    omega
  have hm : q ^ a ∣ (e + 1) / d := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [Nat.mul_div_cancel' hd]
    exact hqa
  have hm0 : (e + 1) / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (by omega) hd) hdpos).ne'
  have hB := (padicValNat_dvd_iff_le hm0).mp hm
  omega

/-- The exponent `a (a + 1) + 1` is impossible at the special prime. Let `N` be an odd perfect
number with special prime `q`, `a ≥ 2`, and `q ^ a ∣ e + 1` for every ordinary exponent `e`.
Then `v_q(N) ≠ a (a + 1) + 1`. -/
theorem factorization_special_ne {N q a : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (ha : 2 ≤ a)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → q ^ a ∣ N.factorization p + 1) :
    N.factorization q ≠ a * (a + 1) + 1 := by
  intro heq
  have : Fact q.Prime := ⟨hq⟩
  have hq4 := (mod_four_special h hq hodd).1
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hq2 : q ≠ 2 := by omega
  set S := N.primeFactors.filter (fun p => p % q = 1) with hS
  have hSq : ∀ p ∈ S, p ≠ q := by
    intro p hp hpq
    have := (Finset.mem_filter.mp hp).2
    rw [hpq, Nat.mod_self] at this
    omega
  have hSN : ∀ p ∈ S, p ∈ N.primeFactors := fun p hp => (Finset.mem_filter.mp hp).1
  -- `S` is not empty
  obtain ⟨p₀, hp₀, hp₀q⟩ := exists_ordinary_prime h hq hodd
  obtain ⟨r, hrN, -, hr⟩ := exists_primeFactor_modEq_one h hp₀ (d := q) (by omega)
    ((dvd_pow_self q (by omega)).trans (hexp p₀ hp₀ hp₀q))
  have hrS : r ∈ S := Finset.mem_filter.mpr ⟨hrN, hr⟩
  have hcard1 : a + 1 ≤ S.card :=
    succ_le_card_filter_mod_eq_one h (by omega) hrN hr (hexp r hrN (hSq r hrS))
  -- the contributions of `S`
  let f := fun p => padicValNat q (σ 1 (p ^ N.factorization p))
  have hfS : ∀ p ∈ S, f p = padicValNat q (N.factorization p + 1) := by
    intro p hp
    have hp1 := (Finset.mem_filter.mp hp).2
    refine padicValNat_sigma_prime_pow_of_dvd_pred (Nat.prime_of_mem_primeFactors (hSN p hp))
      hq hq2 ?_
    have := Nat.dvd_sub_mod (n := q) p
    rwa [hp1] at this
  have hlo : ∀ p ∈ S, a ≤ f p := by
    intro p hp
    rw [hfS p hp]
    exact (padicValNat_dvd_iff_le (by omega)).mp (hexp p (hSN p hp) (hSq p hp))
  have hhi : ∀ p ∈ S, f p + 1 ≤ S.card := by
    intro p hp
    rw [hfS p hp]
    exact succ_le_card_filter_mod_eq_one h (by omega) (hSN p hp)
      (Finset.mem_filter.mp hp).2 pow_padicValNat_dvd
  -- the exact ledger, split along `S`
  have hSsub : S ⊆ N.primeFactors.erase q := fun p hp =>
    Finset.mem_erase.mpr ⟨hSq p hp, hSN p hp⟩
  set T := N.primeFactors.erase q \ S with hT
  have hledger : N.factorization q = ∑ p ∈ T, f p + ∑ p ∈ S, f p := by
    rw [hT, Finset.sum_sdiff hSsub]
    exact factorization_eq_sum_erase h.perfect hq hq2
  have hsumS : S.card * a ≤ ∑ p ∈ S, f p := by
    have := Finset.card_nsmul_le_sum S f a hlo
    rwa [smul_eq_mul] at this
  have hSc : S.card = a + 1 := by
    by_contra hne
    have h2 : a + 2 ≤ S.card := by omega
    have h3 : (a + 2) * a ≤ S.card * a := Nat.mul_le_mul_right a h2
    have h4 : ∑ p ∈ S, f p ≤ N.factorization q := by rw [hledger]; omega
    nlinarith
  have hsumS' : ∑ p ∈ S, f p ≤ S.card * a := by
    have := Finset.sum_le_card_nsmul S f a fun p hp => by have := hhi p hp; omega
    rwa [smul_eq_mul] at this
  have hsumT : ∑ p ∈ T, f p = 1 := by
    have e1 : ∑ p ∈ S, f p = (a + 1) * a := by rw [hSc] at hsumS hsumS'; omega
    have e2 : a * (a + 1) = (a + 1) * a := mul_comm _ _
    omega
  -- a component outside `S` supplies `0` or at least `a + 1`
  obtain ⟨p, hpT, hfp⟩ : ∃ p ∈ T, 0 < f p := by
    by_contra hno
    push Not at hno
    rw [Finset.sum_eq_zero fun p hp => by have := hno p hp; omega] at hsumT
    omega
  obtain ⟨hpE, hpS⟩ := Finset.mem_sdiff.mp hpT
  obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hpE
  have hp1 : p % q ≠ 1 := fun h1 => hpS (Finset.mem_filter.mpr ⟨hpN, h1⟩)
  have hbig := succ_le_padicValNat_sigma_of_not_mod_eq_one (Nat.prime_of_mem_primeFactors hpN)
    hq hq2 hpq hp1 (hexp p hpN hpq) (dvd_of_one_le_padicValNat hfp)
  have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hpT
  change a + 1 ≤ f p at hbig
  omega

/-- The case `a = 3` at the special prime. If `q ^ 3 ∣ e + 1` for every ordinary exponent `e`
of the odd perfect number `N` with special prime `q`, then `17 ≤ v_q(N)`. -/
theorem seventeen_le_factorization_special {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → q ^ 3 ∣ N.factorization p + 1) :
    17 ≤ N.factorization q := by
  have h1 := mul_succ_le_factorization_special h hq hodd hexp
  have h2 := factorization_special_ne h hq hodd (by norm_num) hexp
  have h4 := (mod_four_special h hq hodd).2
  norm_num at h1 h2
  omega

/-- The fifth power at the special prime for every `a ≠ 2`: if `q ^ a ∣ e + 1` for every
ordinary exponent `e` of the odd perfect number `N` with special prime `q`, and `a ≠ 2`, then
`q ^ (5 a) ∣ N`. -/
theorem pow_five_mul_dvd_of_special_of_ne_two {N q a : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (ha2 : a ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → q ^ a ∣ N.factorization p + 1) :
    q ^ (5 * a) ∣ N := by
  by_cases ha3 : a = 3
  · subst ha3
    rw [hq.pow_dvd_iff_le_factorization h.ne_zero]
    have := seventeen_le_factorization_special h hq hodd hexp
    omega
  · exact pow_five_mul_dvd_of_special h hq hodd ha2 ha3 hexp

/-- `σ(p ^ 4)` for a prime `p`. -/
private theorem sigma_four {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 4) = 1 + p + p ^ 2 + p ^ 3 + p ^ 4 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

/-! ## Small certified facts for the prime `5` -/

private theorem p5' : Nat.Prime 5 := by norm_num
private theorem p11 : Nat.Prime 11 := by norm_num
private theorem p71 : Nat.Prime 71 := by norm_num
private theorem p211 : Nat.Prime 211 := by norm_num
private theorem p1361 : Nat.Prime 1361 := by norm_num
private theorem p2221 : Nat.Prime 2221 := by norm_num
private theorem p3221 : Nat.Prime 3221 := by norm_num
private theorem d5_11 : 11 ∣ 1 + 5 + 5 ^ 2 + 5 ^ 3 + 5 ^ 4 := by norm_num
private theorem d5_71 : 71 ∣ 1 + 5 + 5 ^ 2 + 5 ^ 3 + 5 ^ 4 := by norm_num
private theorem d11_3221 : 3221 ∣ 1 + 11 + 11 ^ 2 + 11 ^ 3 + 11 ^ 4 := by norm_num
private theorem d71_211 : 211 ∣ 1 + 71 + 71 ^ 2 + 71 ^ 3 + 71 ^ 4 := by norm_num
private theorem d71_2221 : 2221 ∣ 1 + 71 + 71 ^ 2 + 71 ^ 3 + 71 ^ 4 := by norm_num
private theorem d211_1361 : 1361 ∣ 1 + 211 + 211 ^ 2 + 211 ^ 3 + 211 ^ 4 := by norm_num

/-- The ordinary prime `5` with common divisor `5`. If `5` is an ordinary prime of the odd
perfect number `N` with special prime `q` and `5 ∣ e + 1` for every ordinary exponent `e`, then
`v_5(N) ≠ 4`. The primes `11, 71` (from `σ(5 ^ 4)`), `3221` (from `Φ_5(11)`), `211, 2221`
(from `Φ_5(71)`) and `1361` (from `Φ_5(211)`) are all `≡ 1 (mod 5)`; at least five of them are
ordinary, and each supplies a factor `5` to `v_5(N)`. -/
theorem factorization_five_ne_four {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h5q : (5 : ℕ) ≠ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1) :
    N.factorization 5 ≠ 4 := by
  intro e5
  have hq4 := (mod_four_special h hq hodd).1
  have hmem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hpN =>
    Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  have force : ∀ {p r : ℕ}, p.Prime → p ∣ N → p ≠ q → r.Prime → r ≠ 2 →
      r ∣ 1 + p + p ^ 2 + p ^ 3 + p ^ 4 → r ∣ N := by
    intro p r hp hpN hpq hr hr2 hd
    refine OPNStarter.force_prime h.perfect hp rfl hr hr2 ((sigma_four hp ▸ hd).trans ?_)
    exact OPNExample.sigma_prime_pow_dvd hp (hexp p (hmem hp hpN) hpq)
  have n11 : (11 : ℕ) ≠ q := by omega
  have n71 : (71 : ℕ) ≠ q := by omega
  have n211 : (211 : ℕ) ≠ q := by omega
  have h5N : 5 ∣ N := Nat.dvd_of_factorization_pos (by rw [e5]; norm_num)
  have h11 : 11 ∣ N := force p5' h5N h5q p11 (by norm_num) d5_11
  have h71 : 71 ∣ N := force p5' h5N h5q p71 (by norm_num) d5_71
  have h211 : 211 ∣ N := force p71 h71 n71 p211 (by norm_num) d71_211
  have h3221 : 3221 ∣ N := force p11 h11 n11 p3221 (by norm_num) d11_3221
  have h2221 : 2221 ∣ N := force p71 h71 n71 p2221 (by norm_num) d71_2221
  have h1361 : 1361 ∣ N := force p211 h211 n211 p1361 (by norm_num) d211_1361
  set U : Finset ℕ := {11, 71, 211, 1361, 2221, 3221} with hU
  set T := U.erase q with hT
  have hTsub : T ⊆ N.primeFactors.filter (fun p => p % 5 = 1) := by
    intro p hp
    have hpU := Finset.mem_of_mem_erase hp
    simp only [hU, Finset.mem_insert, Finset.mem_singleton] at hpU
    rcases hpU with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hmem p11 h11, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p71 h71, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p211 h211, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p1361 h1361, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p2221 h2221, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p3221 h3221, by norm_num⟩
  clear force h5N h11 h71 h211 h3221 h2221 h1361
  have hTcard : 5 ≤ T.card := by
    have := Finset.pred_card_le_card_erase (s := U) (a := q)
    have hc : U.card = 6 := by rw [hU]; decide
    rw [← hT, hc] at this
    exact this
  have hlo : ∀ p ∈ T, 1 ≤ padicValNat 5 (N.factorization p + 1) := by
    intro p hp
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact one_le_padicValNat_of_dvd (by omega)
      (hexp p (Finset.mem_filter.mp (hTsub hp)).1 (Finset.ne_of_mem_erase hp))
  have hsum := Finset.card_nsmul_le_sum T _ 1 hlo
  have hsub := Finset.sum_le_sum_of_subset (f := fun p => padicValNat 5 (N.factorization p + 1))
    hTsub
  have hled := sum_padicValNat_succ_le h.perfect (l := 5) (by norm_num) (by norm_num)
  rw [smul_eq_mul, mul_one] at hsum
  omega

/-- The fifth power for every prime other than the special prime. Let `N` be an odd perfect
number with special prime `q`, `l ≠ q` a prime, and `l ^ a ∣ e + 1` for every ordinary exponent
`e`. Then `l ^ (5 a) ∣ N`. -/
theorem pow_five_mul_dvd_of_ne_special {N q l a : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hlq : l ≠ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → l ^ a ∣ N.factorization p + 1) :
    l ^ (5 * a) ∣ N := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  by_cases hl2 : l = 2
  · exfalso
    subst hl2
    obtain ⟨p, hp, hpq⟩ := exists_ordinary_prime h hq hodd
    obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd (Nat.prime_of_mem_primeFactors hp) hpq
    have := (dvd_pow_self 2 ha.ne').trans (hexp p hp hpq)
    omega
  by_cases hla : 7 ≤ l ∨ 2 ≤ a
  · exact pow_five_mul_dvd_of_ordinary h hq hodd hl hl2 hlq hla hexp
  push Not at hla
  obtain ⟨hl7, ha2⟩ := hla
  obtain rfl : a = 1 := by omega
  rw [pow_one] at hexp
  by_cases hl3 : l = 3
  · subst hl3
    exact (mcdaniel h hq hodd fun p hp hpq => by have := hexp p hp hpq; omega).elim
  have hl5 : l = 5 := by
    interval_cases l <;> first | rfl | omega | (norm_num at hl)
  subst hl5
  have hlN := dvd_of_dvd_succ h hq hodd hl hl2 hexp
  have hmem : 5 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hl, hlN, h.ne_zero⟩
  have h1 := hexp 5 hmem hlq
  have h2 := Nat.le_of_dvd (by omega) h1
  have h3 := factorization_five_ne_four h hq hodd hlq hexp
  rw [hl.pow_dvd_iff_le_factorization h.ne_zero]
  omega

/-- The special prime `5` with `25` dividing every ordinary `e + 1`: then `v_5(N) ≠ 9`. The
primes `11, 71, 521` divide `σ(5 ^ 9)`, are `≡ 1 (mod 5)` and are not `≡ 1 (mod 25)`. A
primitive prime factor `t` of `Φ_25(11)` and a primitive prime factor of `Φ_25(t)` give two
more prime factors `≡ 1 (mod 25)`. Five components `≡ 1 (mod 5)` each supply at least `2` to
`v_5(N)`. -/
theorem factorization_five_ne_nine_of_special {N : ℕ} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 → 5 ^ 2 ∣ N.factorization p + 1) :
    N.factorization 5 ≠ 9 := by
  intro e9
  have p5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨p5⟩
  have hmem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hpN =>
    Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  have hσ : σ 1 (5 ^ 9) = 2441406 := by
    rw [sigma_one_apply_prime_pow p5]
    simp [Finset.sum_range_succ]
  have force : ∀ {r : ℕ}, r.Prime → r ≠ 2 → r ∣ 2441406 → r ∣ N := fun hr hr2 hd =>
    OPNStarter.force_prime h.perfect p5 e9 hr hr2 (hσ ▸ hd)
  have h11 := hmem (by norm_num) (force (r := 11) (by norm_num) (by norm_num) (by norm_num))
  have h71 := hmem (by norm_num) (force (r := 71) (by norm_num) (by norm_num) (by norm_num))
  have h521 := hmem (by norm_num) (force (r := 521) (by norm_num) (by norm_num) (by norm_num))
  obtain ⟨t, htN, -, ht⟩ := exists_primeFactor_modEq_one h h11 (d := 5 ^ 2) (by norm_num)
    (hexp 11 h11 (by norm_num))
  have ht5 : t ≠ 5 := by rintro rfl; norm_num at ht
  obtain ⟨u, huN, huo, hu⟩ := exists_primeFactor_modEq_one h htN (d := 5 ^ 2) (by norm_num)
    (hexp t htN ht5)
  have hut : u ≠ t := by
    rintro rfl
    have : Fact u.Prime := ⟨Nat.prime_of_mem_primeFactors htN⟩
    rw [ZMod.natCast_self, orderOf_zero] at huo
    norm_num at huo
  norm_num at ht hu
  set T : Finset ℕ := {11, 71, 521, t, u} with hT
  have hTcard : T.card = 5 := by
    rw [hT, Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (Ne.symm hut)]
  have hTsub : T ⊆ N.primeFactors.filter (fun p => p % 5 = 1) := by
    intro p hp
    simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨h11, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨h71, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨h521, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨htN, by omega⟩
    · exact Finset.mem_filter.mpr ⟨huN, by omega⟩
  have hlo : ∀ p ∈ T, 2 ≤ padicValNat 5 (N.factorization p + 1) := by
    intro p hp
    have hpf := Finset.mem_filter.mp (hTsub hp)
    have hp5 : p ≠ 5 := by have := hpf.2; omega
    exact (padicValNat_dvd_iff_le (by omega)).mp (hexp p hpf.1 hp5)
  have hsum := Finset.card_nsmul_le_sum T _ 2 hlo
  have hsub := Finset.sum_le_sum_of_subset (f := fun p => padicValNat 5 (N.factorization p + 1))
    hTsub
  have hled := sum_padicValNat_succ_le h.perfect (l := 5) p5 (by norm_num)
  rw [smul_eq_mul, hTcard] at hsum
  omega

/-- The special prime `5` with `25` dividing every ordinary `e + 1`: then `13 ≤ v_5(N)`. -/
theorem thirteen_le_factorization_five_of_special {N : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 → 5 ^ 2 ∣ N.factorization p + 1) :
    13 ≤ N.factorization 5 := by
  have h1 := mul_succ_le_factorization_special h (by norm_num) hodd hexp
  have h2 := factorization_five_ne_nine_of_special h hexp
  have h4 := (mod_four_special h (by norm_num) hodd).2
  norm_num at h1
  omega

/-- The fifth power for the special prime `5` and `a = 2`: if `5` is the special prime of the
odd perfect number `N` and `25 ∣ e + 1` for every ordinary exponent `e`, then `5 ^ 13 ∣ N`, in
particular `5 ^ (5 * 2) ∣ N`. -/
theorem pow_thirteen_dvd_of_five_special {N : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 → 5 ^ 2 ∣ N.factorization p + 1) :
    5 ^ 13 ∣ N :=
  ((Nat.prime_five).pow_dvd_iff_le_factorization h.ne_zero).mpr
    (thirteen_le_factorization_five_of_special h hodd hexp)

end OddPerfect

#print axioms OddPerfect.succ_le_card_filter_mod_eq_one
#print axioms OddPerfect.succ_le_padicValNat_sigma_of_not_mod_eq_one
#print axioms OddPerfect.factorization_special_ne
#print axioms OddPerfect.seventeen_le_factorization_special
#print axioms OddPerfect.pow_five_mul_dvd_of_special_of_ne_two
#print axioms OddPerfect.factorization_five_ne_four
#print axioms OddPerfect.pow_five_mul_dvd_of_ne_special
#print axioms OddPerfect.factorization_five_ne_nine_of_special
#print axioms OddPerfect.thirteen_le_factorization_five_of_special
#print axioms OddPerfect.pow_thirteen_dvd_of_five_special
