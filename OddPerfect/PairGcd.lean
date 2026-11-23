import OddPerfect.VietaPairs

/-!
# Common divisors of mutually dividing pairs

The Vieta invariant restricts the common prime divisors of two rows to 3 and 7.
When both members are 1 modulo 3, their row gcd is 3 times a power of 7.
This applies in particular to pairs of primes above 3.

This is Lemma 10 of Bibby, Vyncke and Zelinsky (INTEGERS 21 (2021), A115), stated there for
pairs of primes; the pair `{3, 13}` has coprime rows. Known mathematics. The first theorem
needs no primality of the pair.
-/

namespace OddPerfect

/-- A prime that divides both rows of a mutually dividing pair is 3 or 7. -/
theorem prime_dvd_phi3_pair_eq_three_or_seven {p q k : ℕ} (h1 : p ∣ phi3 q) (h2 : q ∣ phi3 p)
    (hk : k.Prime) (hkp : k ∣ phi3 p) (hkq : k ∣ phi3 q) : k = 3 ∨ k = 7 := by
  by_cases hk3 : k = 3
  · exact Or.inl hk3
  right
  have hkZ : Prime (k : ℤ) := Nat.prime_iff_prime_int.mp hk
  have hnot2 : ¬ (k : ℤ) ∣ 2 := by
    intro hd
    have hd' : k ∣ 2 := Int.natCast_dvd_natCast.mp hd
    have hk2 := (Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).mp hd'
    exact (phi3_odd p).not_two_dvd_nat (hk2 ▸ hkp)
  have hnot3 : ¬ (k : ℤ) ∣ 3 := by
    intro hd
    have hd' : k ∣ 3 := Int.natCast_dvd_natCast.mp hd
    exact hk3 ((Nat.prime_dvd_prime_iff_eq hk Nat.prime_three).mp hd')
  have not_dvd_member (x : ℕ) (hx : k ∣ phi3 x) : ¬ (k : ℤ) ∣ (x : ℤ) := by
    intro hd
    exact hk.ne_one
      (Nat.eq_one_of_dvd_coprimes (phi3_coprime_self x) hx (Int.natCast_dvd_natCast.mp hd))
  have cast_row (x : ℕ) (hx : k ∣ phi3 x) : (k : ℤ) ∣ (x : ℤ) ^ 2 + x + 1 := by
    unfold phi3 at hx
    zify at hx
    exact hx
  have hkpZ := cast_row p hkp
  have hkqZ := cast_row q hkq
  have hinv := invariant_of_dvd_phi3 h1 h2
  zify at hinv
  have hp_row : (p : ℤ) ^ 2 + p + 1 = (q : ℤ) * (5 * (p : ℤ) - q - 1) := by
    linear_combination hinv
  have hq_row : (q : ℤ) ^ 2 + q + 1 = (p : ℤ) * (5 * (q : ℤ) - p - 1) := by
    linear_combination hinv
  have hp_factor : (k : ℤ) ∣ 5 * (p : ℤ) - q - 1 := by
    have hd : (k : ℤ) ∣ (q : ℤ) * (5 * (p : ℤ) - q - 1) := by
      rw [← hp_row]
      exact hkpZ
    exact (hkZ.dvd_or_dvd hd).resolve_left (not_dvd_member q hkq)
  have hq_factor : (k : ℤ) ∣ 5 * (q : ℤ) - p - 1 := by
    have hd : (k : ℤ) ∣ (p : ℤ) * (5 * (q : ℤ) - p - 1) := by
      rw [← hq_row]
      exact hkqZ
    exact (hkZ.dvd_or_dvd hd).resolve_left (not_dvd_member p hkp)
  have hdiff := dvd_sub hp_factor hq_factor
  rw [show (5 * (p : ℤ) - q - 1) - (5 * (q : ℤ) - p - 1) =
    2 * (3 * ((p : ℤ) - q)) by ring] at hdiff
  have htriple := (hkZ.dvd_or_dvd hdiff).resolve_left hnot2
  have hpq := (hkZ.dvd_or_dvd htriple).resolve_left hnot3
  have hp4 := dvd_sub hp_factor hpq
  rw [show 5 * (p : ℤ) - q - 1 - ((p : ℤ) - q) = 4 * (p : ℤ) - 1 by ring] at hp4
  have hprod := dvd_add hkpZ hp4
  rw [show (p : ℤ) ^ 2 + p + 1 + (4 * (p : ℤ) - 1) =
    (p : ℤ) * ((p : ℤ) + 5) by ring] at hprod
  have hp5 := (hkZ.dvd_or_dvd hprod).resolve_left (not_dvd_member p hkp)
  have h21 := dvd_add hkpZ (dvd_mul_of_dvd_left hp5 (4 - (p : ℤ)))
  rw [show (p : ℤ) ^ 2 + p + 1 + ((p : ℤ) + 5) * (4 - (p : ℤ)) = 21 by ring] at h21
  have h21_nat : k ∣ 21 := Int.natCast_dvd_natCast.mp h21
  have h37 : k ∣ 3 * 7 := h21_nat
  have h7 := (hk.dvd_mul.mp h37).resolve_left fun h =>
    hk3 ((Nat.prime_dvd_prime_iff_eq hk Nat.prime_three).mp h)
  exact (Nat.prime_dvd_prime_iff_eq hk Nat.prime_seven).mp h7

/-- For a mutually dividing pair with both members 1 modulo 3, the greatest common divisor of
the two rows is 3 times a power of 7. -/
theorem gcd_phi3_pair_of_mod_three {p q : ℕ} (h1 : p ∣ phi3 q) (h2 : q ∣ phi3 p)
    (hp : p % 3 = 1) (hq : q % 3 = 1) : ∃ m, Nat.gcd (phi3 p) (phi3 q) = 3 * 7 ^ m := by
  obtain ⟨c, hc⟩ := Nat.dvd_gcd ((three_dvd_phi3_iff p).2 hp) ((three_dvd_phi3_iff q).2 hq)
  have hnot3 : ¬ 3 ∣ c := by
    intro hd
    have h9 : 9 ∣ 3 * c := mul_dvd_mul_left 3 hd
    rw [← hc] at h9
    exact not_nine_dvd_phi3 p (h9.trans (Nat.gcd_dvd_left _ _))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hnot3 (dvd_zero 3)
  have hprimes {k : ℕ} (hk : k.Prime) (hd : k ∣ c) : k = 7 := by
    have hdg : k ∣ Nat.gcd (phi3 p) (phi3 q) := by
      rw [hc]
      exact dvd_mul_of_dvd_right hd 3
    have hkp := hdg.trans (Nat.gcd_dvd_left _ _)
    have hkq := hdg.trans (Nat.gcd_dvd_right _ _)
    exact (prime_dvd_phi3_pair_eq_three_or_seven h1 h2 hk hkp hkq).resolve_left
      (fun h => hnot3 (h ▸ hd))
  have hc7 := Nat.eq_prime_pow_of_unique_prime_dvd (p := 7) hc0 (@hprimes)
  exact ⟨c.primeFactorsList.length, hc.trans (congrArg (fun n => 3 * n) hc7)⟩

/-- For two primes above 3 that divide each other's rows, the greatest common divisor of the
rows is 3 times a power of 7. -/
theorem gcd_phi3_prime_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq3 : 3 < q)
    (h1 : p ∣ phi3 q) (h2 : q ∣ phi3 p) : ∃ m, Nat.gcd (phi3 p) (phi3 q) = 3 * 7 ^ m := by
  exact gcd_phi3_pair_of_mod_three h1 h2
    (prime_dvd_phi3_mod_three hp (by omega) h1) (prime_dvd_phi3_mod_three hq (by omega) h2)

end OddPerfect

#print axioms OddPerfect.prime_dvd_phi3_pair_eq_three_or_seven
#print axioms OddPerfect.gcd_phi3_pair_of_mod_three
#print axioms OddPerfect.gcd_phi3_prime_pair
