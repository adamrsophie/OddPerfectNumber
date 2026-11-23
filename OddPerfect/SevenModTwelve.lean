import OddPerfect.Phi3
import OddPerfect.SpecialPrime
import OddPerfect.ForcingClosed
import OddPerfect.MixedIndexCheck
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Primes that are 7 modulo 12 cannot feed each other

Write `phi3 t = t ^ 2 + t + 1`. This module proves:

* `exists_seven_mod_twelve_dvd_phi3`: for a prime `p ≡ 5` or `7 (mod 12)`, `phi3 p` has a
  prime factor `r ≡ 7 (mod 12)` with `r ≠ p`;
* `not_mutual_phi3_of_three_mod_four`: two distinct primes `p, r ≡ 3 (mod 4)` never satisfy
  both `r ∣ phi3 p` and `p ∣ phi3 r`;
* `seven_mod_twelve_chain` and `exists_seven_mod_twelve_exception`: an odd perfect number `N`
  with `v_3(N) ≤ 2` and a prime factor `p ≡ 5` or `7 (mod 12)` with `3 ∣ v_p(N) + 1` (the
  special prime allowed) has a prime factor `r ≡ 7 (mod 12)` with `v_r(N) ≥ 4` and
  `3 ∤ v_r(N) + 1`.

Proof idea. The residues of `phi3 p` modulo `4` and `3` force a prime factor that is `3`
modulo `4` and, like every prime factor of `phi3 p` other than `3`, `1` modulo `3`. If
`r ∣ phi3 p` then `p ^ 3 ≡ 1 (mod r)`, so `p ≡ (p ^ 2) ^ 2` is a square modulo `r`, and
quadratic reciprocity for two primes that are `3` modulo `4` rules out the mutual case. Thus a
chain of three primes that are `7` modulo `12` with `3 ∣ v + 1`, each feeding the next, has
three distinct members, each sending a factor `3`, which needs `v_3(N) ≥ 3`.

Whether these statements are in the literature was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace SevenModTwelve

/-- A number that is `3` modulo `4` has a prime factor that is `3` modulo `4`. -/
theorem exists_prime_dvd_mod_four_eq_three (n : ℕ) (hn : n % 4 = 3) :
    ∃ r, r.Prime ∧ r ∣ n ∧ r % 4 = 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn1 : n ≠ 1 := by omega
    have hmp : n.minFac.Prime := Nat.minFac_prime hn1
    obtain ⟨k, hk⟩ := Nat.minFac_dvd n
    by_cases h3 : n.minFac % 4 = 3
    · exact ⟨n.minFac, hmp, ⟨k, hk⟩, h3⟩
    have hm2 : n.minFac ≠ 2 := by
      intro h2
      rw [h2] at hk
      omega
    have hm1 : n.minFac % 4 = 1 := by
      rcases hmp.eq_two_or_odd with h | h
      · exact absurd h hm2
      · omega
    have hk3 : k % 4 = 3 := by
      have := Nat.mul_mod n.minFac k 4
      rw [← hk, hm1] at this
      omega
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk
        omega
      · exact h
    have hklt : k < n := by
      have := hmp.two_le
      nlinarith
    obtain ⟨r, hr, hrk, hr4⟩ := ih k hklt hk3
    exact ⟨r, hr, hrk.trans (Dvd.intro_left _ hk.symm), hr4⟩

/-- `phi3 p` divides the divisor sum of the `p` component when `3 ∣ v_p(N) + 1`. -/
theorem phi3_dvd_sigma {N p : ℕ} (hp : p.Prime) (h3 : 3 ∣ N.factorization p + 1) :
    phi3 p ∣ σ 1 (p ^ N.factorization p) := by
  rw [← sigma_prime_sq hp]
  exact ForcingClosed.sigma_prime_pow_dvd_of_dvd hp h3

/-- A prime factor of `phi3 p` divides `N` when `p` is prime and `3 ∣ v_p(N) + 1`. -/
theorem dvd_of_dvd_phi3 {N p r : ℕ} (h : OddPerfect N) (hp : p.Prime)
    (h3 : 3 ∣ N.factorization p + 1) (hr : r.Prime) (hrd : r ∣ phi3 p) : r ∣ N :=
  OPNStarter.force_prime h.perfect hp rfl hr
    (fun h2 => (phi3_odd p).not_two_dvd_nat (h2 ▸ hrd)) (hrd.trans (phi3_dvd_sigma hp h3))

/-- If `r ∣ phi3 p` then `p` is a square modulo `r`: `p ^ 3 ≡ 1`, so `p ≡ (p ^ 2) ^ 2`. -/
theorem isSquare_of_dvd_phi3 {p r : ℕ} (h : r ∣ phi3 p) : IsSquare (p : ZMod r) := by
  have h0 : ((phi3 p : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  unfold phi3 at h0
  push_cast at h0
  have h3 : (p : ZMod r) ^ 3 = 1 := by linear_combination ((p : ZMod r) - 1) * h0
  exact ⟨(p : ZMod r) ^ 2, by linear_combination (-(p : ZMod r)) * h3⟩

end SevenModTwelve

open SevenModTwelve

/-- Two distinct primes that are `3` modulo `4` cannot each divide `phi3` of the other. -/
theorem not_mutual_phi3_of_three_mod_four {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hp4 : p % 4 = 3) (hr4 : r % 4 = 3) (h1 : r ∣ phi3 p) (h2 : p ∣ phi3 r) : False := by
  have := Fact.mk hp
  have := Fact.mk hr
  exact (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hp4 hr4 hpr).1
    (isSquare_of_dvd_phi3 h2) (isSquare_of_dvd_phi3 h1)

/-- For a prime `p ≡ 5` or `7 (mod 12)`, `phi3 p` has a prime factor `r ≡ 7 (mod 12)`, and
`r ≠ p`. -/
theorem exists_seven_mod_twelve_dvd_phi3 {p : ℕ} (hp : p.Prime)
    (hmod : p % 12 = 5 ∨ p % 12 = 7) :
    ∃ r, r.Prime ∧ r ∣ phi3 p ∧ r % 12 = 7 ∧ r ≠ p := by
  obtain ⟨n, hn, hn4, hn3⟩ : ∃ n, n ∣ phi3 p ∧ n % 4 = 3 ∧ ¬ 3 ∣ n := by
    have hk : p = 12 * (p / 12) + p % 12 := (Nat.div_add_mod p 12).symm
    set k := p / 12
    rcases hmod with h | h
    · refine ⟨phi3 p, dvd_rfl, ?_, fun h3 => by have := (three_dvd_phi3_iff p).1 h3; omega⟩
      have he : phi3 p = 4 * (36 * k ^ 2 + 33 * k + 7) + 3 := by
        rw [hk, h]; unfold phi3; ring
      rw [he, Nat.mul_add_mod]
    · refine ⟨48 * k ^ 2 + 60 * k + 19, ⟨3, ?_⟩, ?_, fun h3 => ?_⟩
      · rw [hk, h]; unfold phi3; ring
      · have he : 48 * k ^ 2 + 60 * k + 19 = 4 * (12 * k ^ 2 + 15 * k + 4) + 3 := by ring
        rw [he, Nat.mul_add_mod]
      · have he : phi3 p = 3 * (48 * k ^ 2 + 60 * k + 19) := by
          rw [hk, h]; unfold phi3; ring
        exact not_nine_dvd_phi3 p (he ▸ (mul_dvd_mul_left 3 h3 : 3 * 3 ∣ _))
  obtain ⟨r, hr, hrn, hr4⟩ := exists_prime_dvd_mod_four_eq_three n hn4
  have hrd : r ∣ phi3 p := hrn.trans hn
  have hr3 : r ≠ 3 := by rintro rfl; exact hn3 hrn
  have h31 := prime_dvd_phi3_mod_three hr hr3 hrd
  refine ⟨r, hr, hrd, by omega, ?_⟩
  rintro rfl
  have hc : Nat.Coprime r r := (phi3_coprime_self r).coprime_dvd_left hrd
  exact hr.one_lt.ne' (Nat.coprime_self r |>.1 hc)

/-- Let `N` be odd perfect and `p ∣ N` a prime with `p ≡ 5` or `7 (mod 12)` and
`3 ∣ v_p(N) + 1` (the special prime is allowed). Then either some prime factor `r ≡ 7 (mod 12)`
of `N` has `3 ∤ v_r(N) + 1`, or at least three prime factors `r ≡ 7 (mod 12)` of `N` have
`3 ∣ v_r(N) + 1`. -/
theorem seven_mod_twelve_chain {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors)
    (hmod : p % 12 = 5 ∨ p % 12 = 7) (h3 : 3 ∣ N.factorization p + 1) :
    (∃ r ∈ N.primeFactors, r % 12 = 7 ∧ ¬ 3 ∣ N.factorization r + 1) ∨
      3 ≤ (N.primeFactors.filter fun r => r % 12 = 7 ∧ 3 ∣ N.factorization r + 1).card := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have mem : ∀ {a r : ℕ}, a.Prime → 3 ∣ N.factorization a + 1 → r.Prime → r ∣ phi3 a →
      r ∈ N.primeFactors := fun ha ha3 hr hd =>
    Nat.mem_primeFactors.2 ⟨hr, dvd_of_dvd_phi3 h ha ha3 hr hd, h.ne_zero⟩
  obtain ⟨r1, hr1, hd1, h1m, -⟩ := exists_seven_mod_twelve_dvd_phi3 hpp hmod
  have m1 := mem hpp h3 hr1 hd1
  by_cases s1 : 3 ∣ N.factorization r1 + 1
  swap
  · exact Or.inl ⟨r1, m1, h1m, s1⟩
  obtain ⟨r2, hr2, hd2, h2m, h21⟩ := exists_seven_mod_twelve_dvd_phi3 hr1 (Or.inr h1m)
  have m2 := mem hr1 s1 hr2 hd2
  by_cases s2 : 3 ∣ N.factorization r2 + 1
  swap
  · exact Or.inl ⟨r2, m2, h2m, s2⟩
  obtain ⟨r3, hr3, hd3, h3m, h32⟩ := exists_seven_mod_twelve_dvd_phi3 hr2 (Or.inr h2m)
  have m3 := mem hr2 s2 hr3 hd3
  by_cases s3 : 3 ∣ N.factorization r3 + 1
  swap
  · exact Or.inl ⟨r3, m3, h3m, s3⟩
  have h31 : r3 ≠ r1 := by
    intro he
    rw [he] at hd3
    exact not_mutual_phi3_of_three_mod_four hr2 hr1 h21 (by omega) (by omega) hd3 hd2
  right
  have hsub : ({r1, r2, r3} : Finset ℕ) ⊆
      N.primeFactors.filter fun r => r % 12 = 7 ∧ 3 ∣ N.factorization r + 1 :=
    Finset.insert_subset_iff.2 ⟨Finset.mem_filter.2 ⟨m1, h1m, s1⟩,
      Finset.insert_subset_iff.2 ⟨Finset.mem_filter.2 ⟨m2, h2m, s2⟩,
        Finset.singleton_subset_iff.2 (Finset.mem_filter.2 ⟨m3, h3m, s3⟩)⟩⟩
  have hc : ({r1, r2, r3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨r1, r2, r3, h21.symm, h31.symm, h32.symm, rfl⟩
  exact (Finset.card_le_card hsub).trans' hc.ge

/-- Let `N` be odd perfect with special prime `q` and `v_3(N) ≤ 2`, and let `p ∣ N` be a prime
with `p ≡ 5` or `7 (mod 12)` and `3 ∣ v_p(N) + 1` (`p = q` allowed). Then some prime factor
`r ≡ 7 (mod 12)` of `N` has `v_r(N) ≥ 4` and `3 ∤ v_r(N) + 1`. -/
theorem exists_seven_mod_twelve_exception {N q p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3N : N.factorization 3 ≤ 2)
    (hp : p ∈ N.primeFactors) (hmod : p % 12 = 5 ∨ p % 12 = 7)
    (h3 : 3 ∣ N.factorization p + 1) :
    ∃ r ∈ N.primeFactors, r % 12 = 7 ∧ 4 ≤ N.factorization r ∧ ¬ 3 ∣ N.factorization r + 1 := by
  rcases seven_mod_twelve_chain h hp hmod h3 with ⟨r, hr, hr7, hr3⟩ | hc
  · refine ⟨r, hr, hr7, ?_, hr3⟩
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hq4 := (special_mod_four h hq hodd).1
    have hrq : r ≠ q := by rintro rfl; omega
    obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hrp hrq
    have h1 := (hrp.dvd_iff_one_le_factorization h.ne_zero).1 (Nat.dvd_of_mem_primeFactors hr)
    omega
  · exfalso
    have hd : ∀ r ∈ N.primeFactors.filter (fun r => r % 12 = 7 ∧ 3 ∣ N.factorization r + 1),
        3 ∣ σ 1 (r ^ N.factorization r) := by
      intro r hr
      obtain ⟨hrN, hr7, hr3⟩ := Finset.mem_filter.1 hr
      exact ((three_dvd_phi3_iff r).2 (by omega)).trans
        (phi3_dvd_sigma (Nat.prime_of_mem_primeFactors hrN) hr3)
    have := MixedIndex.card_le_of_senders h.perfect Nat.prime_three (by decide) _
      (Finset.filter_subset _ _) hd
    omega

/-! ## Concrete instances -/

/-- Step 1 on the chain `7 → 19 → 127`: `19 ∣ phi3 7 = 57` and `127 ∣ phi3 19 = 381`. -/
example : 19 ∣ phi3 7 ∧ 19 % 12 = 7 ∧ 127 ∣ phi3 19 ∧ 127 % 12 = 7 ∧ phi3 19 = 3 * 127 := by
  decide

/-- Step 2 on `7` and `19`: `19 ∣ phi3 7` but `7 ∤ phi3 19`. -/
example : ¬ 7 ∣ phi3 19 := by decide

end OddPerfect

#print axioms OddPerfect.not_mutual_phi3_of_three_mod_four
#print axioms OddPerfect.exists_seven_mod_twelve_dvd_phi3
#print axioms OddPerfect.seven_mod_twelve_chain
#print axioms OddPerfect.exists_seven_mod_twelve_exception
