import OddPerfect.ThreeRowParts
import OddPerfect.NagellPrime
import OddPerfect.ClassicalInputs

/-!
# The equation `p ^ 2 + p + 1 = 3 * r ^ a` for primes `p` and `r`

This is the classical theorem of Nagell (1921) for prime `p` and a prime power on the right: if
`p` and `r` are primes and `p ^ 2 + p + 1 = 3 * r ^ a`, then `a ≤ 2`. The name of the definition
`LjunggrenThreePrimePower` is historical. The cube case rests on mathlib's Fermat theorem for
exponent 3; the fourth power case is an elementary descent; an exponent with a prime factor
`n ≥ 5` is excluded in the Eisenstein integers by `eis_not_pow_add_twist`. The value
`Φ₃(313) = 3 * 181 ^ 2` shows that the exponent 2 occurs (313 and 181 are prime).

The hypothesis `LjunggrenThreePrimePower` used elsewhere in the library is thereby proved
(`ljunggrenThreePrimePower`). This is known mathematics and decides nothing about odd perfect
numbers.
-/

open QuadraticAlgebra

namespace OddPerfect

namespace ThreeRowPrime

open Eis

private lemma nrm_pow' (z : Eis) (k : ℕ) : nrm (z ^ k) = nrm z ^ k := by
  induction k with
  | zero => simp [nrm_one]
  | succ k ih => rw [pow_succ, nrm_mul, ih, pow_succ]

/-- A unit has order dividing `6`. -/
private lemma pow_six_of_nrm_one {u : Eis} (h : nrm u = 1) : u ^ 6 = 1 := by
  rcases eq_of_nrm_eq_one h with rfl | rfl | rfl | rfl | rfl | rfl <;> ext <;> norm_num [pow_succ]

private lemma pow_mod_six {u : Eis} (h : u ^ 6 = 1) (n : ℕ) : u ^ n = u ^ (n % 6) := by
  conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul, h, one_pow, one_mul]

/-- An element of norm `3` is `λ = 1 - ω` times a unit. -/
private lemma eq_lam_mul {θ : Eis} (h : nrm θ = 3) : ∃ u : Eis, nrm u = 1 ∧ θ = ⟨1, -1⟩ * u := by
  rcases eq_of_nrm_eq_three h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨0, 1⟩, by rw [nrm_mk]; norm_num, by ext <;> norm_num⟩
  · exact ⟨⟨0, -1⟩, by rw [nrm_mk]; norm_num, by ext <;> norm_num⟩
  · exact ⟨⟨-1, -1⟩, by rw [nrm_mk]; norm_num, by ext <;> norm_num⟩
  · exact ⟨⟨1, 1⟩, by rw [nrm_mk]; norm_num, by ext <;> norm_num⟩
  · exact ⟨⟨1, 0⟩, by rw [nrm_mk]; norm_num, by ext <;> norm_num⟩
  · exact ⟨⟨-1, 0⟩, by rw [nrm_mk]; norm_num, by ext <;> norm_num⟩

/-- A positive exponent all of whose prime factors are below `5`, with `3 ∤ a` and `4 ∤ a`, is
at most `2`. -/
private lemma le_two_of_small_primes {a : ℕ} (ha : a ≠ 0) (h3 : ¬ 3 ∣ a) (h4 : ¬ 4 ∣ a)
    (hs : ∀ n, n.Prime → n ∣ a → n < 5) : a ≤ 2 := by
  have h2 : ∀ {d : ℕ}, d.Prime → d ∣ a → d = 2 := by
    intro d hd hda
    have hd5 := hs d hd hda
    have hd2 := hd.two_le
    interval_cases d
    · rfl
    · exact (h3 hda).elim
    · exact absurd hd (by norm_num)
  have he := Nat.eq_prime_pow_of_unique_prime_dvd ha h2
  generalize a.primeFactorsList.length = L at he
  subst he
  rcases (show L = 0 ∨ L = 1 ∨ 2 ≤ L by omega) with rfl | rfl | hge
  · norm_num
  · norm_num
  · exact (h4 (by simpa using (pow_dvd_pow 2 hge : 2 ^ 2 ∣ 2 ^ L))).elim

/-- The case of an exponent with a prime factor `n ≥ 5`. -/
private lemma not_of_prime_factor {p r a n : ℕ} (hr : r.Prime) (h : p ^ 2 + p + 1 = 3 * r ^ a)
    (hn : n.Prime) (hn5 : 5 ≤ n) (hna : n ∣ a) (ha : 1 ≤ a) : False := by
  obtain ⟨j', rfl⟩ := hna
  have hj' : 1 ≤ j' := by
    rcases Nat.eq_zero_or_pos j' with h0 | h0
    · rw [h0, mul_zero] at ha; omega
    · exact h0
  have hn6 : n % 6 = 1 ∨ n % 6 = 5 := by
    have h2 : ¬ 2 ∣ n := fun hd => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hn).1 hd; omega
    have h3 : ¬ 3 ∣ n := fun hd => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hn).1 hd; omega
    omega
  have hr3 : r ≠ 3 := by
    rintro rfl
    apply not_nine_dvd_phi3 p
    unfold phi3
    rw [h]
    obtain ⟨c, hc⟩ : ∃ c, n * j' = c + 1 := ⟨n * j' - 1, by omega⟩
    rw [hc, pow_succ]
    exact ⟨3 ^ c, by ring⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨c, hc⟩ : ∃ c, n * j' = c + 1 := ⟨n * j' - 1, by omega⟩
    rw [hc, pow_succ 2 c] at h
    obtain ⟨t, ht⟩ := Nat.even_mul_succ_self p
    have : p ^ 2 + p = t + t := by rw [← ht]; ring
    omega
  have hr5 : 5 ≤ r := by
    have := hr.two_le
    have h4 : r ≠ 4 := by rintro rfl; exact absurd hr (by norm_num)
    omega
  have hrow : nrm ⟨(p : ℤ), -1⟩ = 3 * (r : ℤ) ^ (n * j') := by
    have : ((p ^ 2 + p + 1 : ℕ) : ℤ) = ((3 * r ^ (n * j') : ℕ) : ℤ) := by rw [h]
    push_cast at this
    rw [nrm_mk]
    linear_combination this
  obtain ⟨ρ, θ, hρ, hθ, hx⟩ := exists_root_pow_mul_of_row hr hr3 p (n * j') ha 3 hrow
  obtain ⟨u, hu, rfl⟩ := eq_lam_mul hθ
  have h6 := pow_six_of_nrm_one hu
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (u ^ k) ^ n = u := by
    rcases hn6 with h1 | h5
    · exact ⟨1, by rw [pow_one, pow_mod_six h6, h1, pow_one]⟩
    · exact ⟨5, by rw [← pow_mul, pow_mod_six h6, show 5 * n % 6 = 1 by omega, pow_one]⟩
  set β := u ^ k * ρ ^ j' with hβdef
  have hβ : (⟨(p : ℤ), -1⟩ : Eis) = ⟨1, -1⟩ * β ^ n := by
    rw [hx, hβdef, mul_pow, hk, ← pow_mul, mul_comm j' n]; ring
  have hs : (⟨(p : ℤ) + 1, 1⟩ : Eis) = ⟨2, 1⟩ * (star β) ^ n := by
    have e := congrArg star hβ
    rw [star_mul', star_pow] at e
    have e1 : star (⟨(p : ℤ), -1⟩ : Eis) = ⟨(p : ℤ) + 1, 1⟩ := by ext <;> simp
    have e2 : star (⟨1, -1⟩ : Eis) = ⟨2, 1⟩ := by ext <;> norm_num
    rw [e1, e2] at e
    exact e
  have c1 : (⟨1, -1⟩ : Eis) * ⟨-1, -1⟩ = -⟨2, 1⟩ := by ext <;> norm_num
  have c2 : (⟨(p : ℤ), -1⟩ : Eis) - ⟨(p : ℤ) + 1, 1⟩ = ⟨1, -1⟩ * ⟨0, -1⟩ := by
    ext <;> norm_num
  have hlam : (⟨1, -1⟩ : Eis) ≠ 0 := fun h0 => by
    have := congrArg QuadraticAlgebra.re h0
    simp at this
  have hmul : (⟨1, -1⟩ : Eis) * (β ^ n + ⟨-1, -1⟩ * (star β) ^ n - ⟨0, -1⟩) = 0 := by
    linear_combination (-1 : Eis) * hβ + (star β) ^ n * c1 + hs + c2
  have heq : β ^ n + (⟨-1, -1⟩ : Eis) * (star β) ^ n = ⟨0, -1⟩ :=
    sub_eq_zero.1 ((mul_eq_zero.1 hmul).resolve_left hlam)
  have hρp : Prime ρ := prime_of_nrm_prime (by rw [hρ, Int.natAbs_natCast]; exact hr)
  have hρn : 5 ≤ nrm ρ := by rw [hρ]; exact_mod_cast hr5
  have hd : ρ ∣ β := dvd_mul_of_dvd_right (dvd_pow_self ρ (by omega)) _
  exact eis_not_pow_add_twist (by omega) hn6 hρp hρn hd heq

end ThreeRowPrime

open ThreeRowPrime in
/-- If `p` and `r` are primes and `p ^ 2 + p + 1 = 3 * r ^ a`, then `a ≤ 2`. -/
theorem three_mul_prime_pow_exponent_le_two {p r a : ℕ} (hp : p.Prime) (hr : r.Prime)
    (h : p ^ 2 + p + 1 = 3 * r ^ a) : a ≤ 2 := by
  by_contra ha
  have hp2 := hp.two_le
  have h3 : ¬ 3 ∣ a := by
    rintro ⟨k, rfl⟩
    exact not_phi3_eq_three_mul_cube hp2 (by rw [h, pow_mul'])
  have h4 : ¬ 4 ∣ a := by
    rintro ⟨k, rfl⟩
    exact not_phi3_eq_three_mul_pow_four hp2 (by rw [h, pow_mul'])
  by_cases hex : ∃ n, n.Prime ∧ n ∣ a ∧ 5 ≤ n
  · obtain ⟨n, hn, hna, hn5⟩ := hex
    exact not_of_prime_factor hr h hn hn5 hna (by omega)
  · exact ha (le_two_of_small_primes (by omega) h3 h4 fun n hn hna => by
      by_contra hc
      exact hex ⟨n, hn, hna, by omega⟩)

/-- The hypothesis `LjunggrenThreePrimePower` used elsewhere in the library holds: this is the
classical theorem of Nagell (1921) for prime `p` and a prime power on the right. It is known
mathematics; nothing here decides the odd perfect number conjecture. -/
theorem ljunggrenThreePrimePower : LjunggrenThreePrimePower := by
  intro p r a hp hr _ h
  exact three_mul_prime_pow_exponent_le_two hp hr h

end OddPerfect

#print axioms OddPerfect.three_mul_prime_pow_exponent_le_two
#print axioms OddPerfect.ljunggrenThreePrimePower
