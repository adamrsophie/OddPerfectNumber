import OddPerfect.SupportBridges
import OddPerfect.EqualExponentsBound
import OddPerfect.Phi3

/-!
# Five small classical lemmas

Textbook size facts; no novelty is claimed.

* `dvd_pow_self_sub_one_of_mutual_rows` (the argument, for `ℓ = 5`, is in the proof of
  Proposition 6.2 of Hagis, Math. Comp. 35 (1980), 1027 to 1032): if
  `F(p) = ℓ q ^ α` and `F(q) = ℓ p ^ β` with `β ≥ 1`, where `F(x) = 1 + x + ... + x ^ (ℓ - 1)`,
  then `p ∣ ℓ ^ ℓ - 1`. For `ℓ = 3`: `no_mutual_phi3_eq_three_mul_pow`.
* `factorization_sigma_prime_pow_sub_one` (compare Pomerance, Math. Comp. 29 (1975),
  Lemma 3): the prime `p` divides `σ(p ^ a) - 1` exactly once when `a ≥ 1`.
* `sigma_div_gcd_dvd_of_unitary`: for a unitary factorization `N = X Y` of a perfect number,
  `σ(X) / gcd(σ(X), 2 X)` divides `Y`.
* `dvd_geom_sum_iff_modEq`: `ℓ ∣ 1 + r + ... + r ^ j` iff `r ^ (j + 1) ≡ 1` modulo
  `ℓ (r - 1)`.
* `mod_three_eq_one_of_dvd_geom_sum_three`: a prime `q ≡ 1 (mod 4)` dividing
  `1 + 3 + ... + 3 ^ e` with `e` even is `1` modulo `3`; for an odd perfect number,
  `special_mod_twelve_of_dvd_sigma_three`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Item 1: mutual rows -/

/-- Mutual rows. The argument, for `ℓ = 5`, is in the proof of Proposition 6.2 of Hagis,
Math. Comp. 35 (1980). Let `ℓ` and `p` be primes. If
`∑ i < ℓ, p ^ i = ℓ q ^ α` and `∑ i < ℓ, q ^ i = ℓ p ^ β` with `1 ≤ β`, then
`p ∣ ℓ ^ ℓ - 1`. -/
theorem dvd_pow_self_sub_one_of_mutual_rows {l p q α β : ℕ} (hl : l.Prime) (hp : p.Prime)
    (hpq : ∑ i ∈ Finset.range l, p ^ i = l * q ^ α)
    (hqp : ∑ i ∈ Finset.range l, q ^ i = l * p ^ β) (hβ : 1 ≤ β) : p ∣ l ^ l - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := (q : ZMod p) with hx
  have h0 : ∑ i ∈ Finset.range l, x ^ i = 0 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hqp
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul, ZMod.natCast_self] at h
    rw [h, zero_pow (by omega), mul_zero]
  have hxl : x ^ l = 1 := by
    have := geom_sum_mul x l
    rw [h0, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  have h1 : (l : ZMod p) * x ^ α = 1 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hpq
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul, ZMod.natCast_self] at h
    obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := ⟨l - 1, by have := hl.one_lt; omega⟩
    rw [hk, Finset.sum_range_succ', pow_zero] at h
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, zero_add] at h
    rw [← hk] at h
    exact h.symm
  have h2 : ((l ^ l : ℕ) : ZMod p) = 1 := by
    have := congrArg (· ^ l) h1
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm α l, pow_mul, hxl, one_pow, mul_one] at this
    push_cast
    exact this
  have hle : 1 ≤ l ^ l := Nat.one_le_pow _ _ hl.pos
  apply (ZMod.natCast_eq_zero_iff _ p).mp
  rw [Nat.cast_sub hle, h2, Nat.cast_one, sub_self]

/-- `phi3 x` is the sum `∑ i < 3, x ^ i`. -/
theorem phi3_eq_geom_sum (x : ℕ) : phi3 x = ∑ i ∈ Finset.range 3, x ^ i := by
  simp [phi3, Finset.sum_range_succ]
  ring

private theorem eq_two_or_thirteen {p : ℕ} (hp : p.Prime) (h : p ∣ 3 ^ 3 - 1) :
    p = 2 ∨ p = 13 := by
  have h26 : p ∣ 2 * 13 := by simpa using h
  rcases (Nat.Prime.dvd_mul hp).mp h26 with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)

private theorem ne_two_of_phi3_eq {p q α : ℕ} (hα : 1 ≤ α) (h : phi3 p = 3 * q ^ α) :
    q ≠ 2 := by
  rintro rfl
  have ho := Nat.odd_iff.mp (phi3_odd p)
  obtain ⟨a, rfl⟩ : ∃ a, α = a + 1 := ⟨α - 1, by omega⟩
  rw [h, pow_succ] at ho
  omega

/-- The case `ℓ = 3` of the mutual rows lemma: there are no primes `p`,
`q` and exponents `α, β ≥ 1` with `phi3 p = 3 q ^ α` and `phi3 q = 3 p ^ β`. -/
theorem no_mutual_phi3_eq_three_mul_pow {p q α β : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hα : 1 ≤ α) (hβ : 1 ≤ β) (hpq : phi3 p = 3 * q ^ α) (hqp : phi3 q = 3 * p ^ β) :
    False := by
  have hp' := dvd_pow_self_sub_one_of_mutual_rows Nat.prime_three hp
    ((phi3_eq_geom_sum p).symm.trans hpq) ((phi3_eq_geom_sum q).symm.trans hqp) hβ
  have hq' := dvd_pow_self_sub_one_of_mutual_rows Nat.prime_three hq
    ((phi3_eq_geom_sum q).symm.trans hqp) ((phi3_eq_geom_sum p).symm.trans hpq) hα
  have hp2 := ne_two_of_phi3_eq hβ hqp
  have hq2 := ne_two_of_phi3_eq hα hpq
  have hp13 := (eq_two_or_thirteen hp hp').resolve_left hp2
  have hq13 := (eq_two_or_thirteen hq hq').resolve_left hq2
  subst hp13 hq13
  have h13 : 13 ∣ 13 ^ α := dvd_pow_self 13 (by omega)
  rw [← Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3), ← hpq] at h13
  norm_num [phi3] at h13

/-! ## Item 2: the exponent of `p` in `σ(p ^ a) - 1` -/

/-- Compare Pomerance 1975, Lemma 3: for a prime `p` and `1 ≤ a`, the exponent of `p` in
`σ(p ^ a) - 1 = p (1 + p + ... + p ^ (a - 1))` is exactly one. -/
theorem factorization_sigma_prime_pow_sub_one {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (σ 1 (p ^ a) - 1).factorization p = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  have hs : σ 1 (p ^ (k + 1)) = 1 + p * σ 1 (p ^ k) := by
    rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
      Finset.mul_sum, pow_zero, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hnd : ¬ p ∣ σ 1 (p ^ k) := by
    intro hd
    have := sigma_prime_pow_mod_self hp k
    rw [Nat.mod_eq_zero_of_dvd hd] at this
    exact absurd this (by norm_num)
  have h0 : σ 1 (p ^ k) ≠ 0 := (sigma_pos 1 _ (pow_pos hp.pos k).ne').ne'
  rw [hs, Nat.add_sub_cancel_left, Nat.factorization_mul hp.ne_zero h0, Finsupp.add_apply,
    hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hnd]

/-- Compare Pomerance 1975, Lemma 3: if `σ(p ^ a) = q ^ b` for a prime `p` and `1 ≤ a`, then
`p` divides `q ^ b - 1` exactly once. -/
theorem factorization_pow_sub_one_of_sigma_eq {p q a b : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (h : σ 1 (p ^ a) = q ^ b) : (q ^ b - 1).factorization p = 1 := by
  rw [← h]
  exact factorization_sigma_prime_pow_sub_one hp ha

/-! ## Item 3: forced divisor of a unitary divisor -/

/-- For a perfect number `N = X Y` with `X` and `Y` coprime, `σ(X) / gcd(σ(X), 2 X)` divides
`Y`. -/
theorem sigma_div_gcd_dvd_of_unitary {N X Y : ℕ} (hN : σ 1 N = 2 * N) (hN0 : 0 < N)
    (hXY : N = X * Y) (hcop : Nat.Coprime X Y) :
    σ 1 X / Nat.gcd (σ 1 X) (2 * X) ∣ Y := by
  have hX0 : 0 < X := Nat.pos_of_ne_zero (by rintro rfl; simp at hXY; omega)
  have hmul : σ 1 X * σ 1 Y = 2 * X * Y := by
    rw [← (isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop, ← hXY, hN, hXY,
      Nat.mul_assoc]
  set g := Nat.gcd (σ 1 X) (2 * X) with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
  have hcd := Nat.coprime_div_gcd_div_gcd (m := σ 1 X) (n := 2 * X) hg0
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left (σ 1 X) (2 * X)
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right (σ 1 X) (2 * X)
  rw [← hg] at ha hb hcd
  have hda : σ 1 X / g = a := by rw [ha, Nat.mul_div_cancel_left _ hg0]
  have hdb : 2 * X / g = b := by rw [hb, Nat.mul_div_cancel_left _ hg0]
  rw [hda, hdb] at hcd
  rw [hda]
  have hdiv : g * a ∣ g * (b * Y) := by
    rw [← ha, ← Nat.mul_assoc, ← hb, ← hmul]
    exact dvd_mul_right _ _
  exact hcd.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hg0 hdiv)

/-! ## Item 4: divisibility of a geometric sum -/

private theorem geom_sum_mul_add_one (s j : ℕ) :
    (∑ i ∈ Finset.range (j + 1), (s + 1) ^ i) * s + 1 = (s + 1) ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, pow_succ (s + 1) (j + 1), ← ih]
    ring

/-- For `2 ≤ r`: `ℓ ∣ ∑ i ≤ j, r ^ i` if and only if `r ^ (j + 1) ≡ 1 (mod ℓ (r - 1))`. -/
theorem dvd_geom_sum_iff_modEq {r l j : ℕ} (hr : 2 ≤ r) :
    l ∣ ∑ i ∈ Finset.range (j + 1), r ^ i ↔ r ^ (j + 1) ≡ 1 [MOD l * (r - 1)] := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hs : 0 < s := by omega
  have key := geom_sum_mul_add_one s j
  rw [Nat.add_sub_cancel, Nat.ModEq.comm, Nat.modEq_iff_dvd' (by omega), ← key,
    Nat.add_sub_cancel]
  exact (Nat.mul_dvd_mul_iff_right hs).symm

/-! ## Item 5: a prime `1 (mod 4)` in the row of `3` -/

private theorem not_isSquare_two_zmod_three : ¬ IsSquare ((2 : ℕ) : ZMod 3) := by
  rintro ⟨y, hy⟩
  fin_cases y <;> revert hy <;> decide

/-- A prime `q ≡ 1 (mod 4)` dividing `∑ i ≤ e, 3 ^ i` with `e` even satisfies
`q ≡ 1 (mod 3)`: `3` is a square modulo `q`, so by reciprocity `q` is a square modulo `3`. -/
theorem mod_three_eq_one_of_dvd_geom_sum_three {q e : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    (he : Even e) (hdvd : q ∣ ∑ i ∈ Finset.range (e + 1), 3 ^ i) : q % 3 = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hdvd' : q ∣ σ 1 (3 ^ e) := by rwa [sigma_one_apply_prime_pow Nat.prime_three]
  have hq3 : q ≠ 3 := (prime_dvd_sigma_prime_pow Nat.prime_three hq hdvd').1
  have hq2 : q ≠ 2 := by rintro rfl; omega
  have hL := legendreSym_eq_one_of_dvd_sigma_even Nat.prime_three he hdvd'
  have h30 : ((3 : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h)
  have hsq : IsSquare ((3 : ℕ) : ZMod q) := (legendreSym.eq_one_iff' q h30).mp hL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsq3 : IsSquare ((q : ℕ) : ZMod 3) :=
    (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := q) (q := 3) hq4 (by norm_num)).mp hsq
  have hne0 : q % 3 ≠ 0 := by
    intro h0
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
      (Nat.dvd_of_mod_eq_zero h0)).symm
  by_contra h1
  have h2 : q % 3 = 2 := by omega
  rw [← ZMod.natCast_mod, h2] at hsq3
  exact not_isSquare_two_zmod_three hsq3

/-- For an odd perfect number `N` with special prime `s`, if `s ∣ σ(3 ^ v_3(N))` then
`s ≡ 1 (mod 12)`. -/
theorem special_mod_twelve_of_dvd_sigma_three {N s : ℕ} (h : OddPerfect N) (hs : s.Prime)
    (hodd : Odd (N.factorization s)) (hdvd : s ∣ σ 1 (3 ^ N.factorization 3)) :
    s % 12 = 1 := by
  have h3 := special_mod_three_of_dvd_sigma_three h hs hodd hdvd
  have h4 := (special_mod_four h hs hodd).1
  omega

end OddPerfect

#print axioms OddPerfect.dvd_pow_self_sub_one_of_mutual_rows
#print axioms OddPerfect.phi3_eq_geom_sum
#print axioms OddPerfect.no_mutual_phi3_eq_three_mul_pow
#print axioms OddPerfect.factorization_sigma_prime_pow_sub_one
#print axioms OddPerfect.factorization_pow_sub_one_of_sigma_eq
#print axioms OddPerfect.sigma_div_gcd_dvd_of_unitary
#print axioms OddPerfect.dvd_geom_sum_iff_modEq
#print axioms OddPerfect.mod_three_eq_one_of_dvd_geom_sum_three
#print axioms OddPerfect.special_mod_twelve_of_dvd_sigma_three
