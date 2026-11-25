import OddPerfect.EulerIndexPairPalette

/-!
# Two prime Euler index: small values of the first label

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly two prime factors.
`eulerIndex_pair_pure_exponent_odd` labels them `(t, u)` with `σ(u ^ f) = t ^ j`, `j` odd,
`f = v_u(N)`, `ℓ = f + 1` prime and `t ≡ 1 (mod 2 ℓ)`. So
`1 + u + ⋯ + u ^ (ℓ - 1) = t ^ j` with `u` an odd prime and `ℓ` an odd prime dividing `t - 1`.

Arithmetic lemmas (no odd perfect number), with `S = ∑ i ∈ range ℓ, u ^ i`:

* `geom_sum_mod_four_of_three`, `geom_sum_mod_four_of_one`, `geom_sum_eq_pow_mod_four`:
  for odd `u` and odd `ℓ`, `S ≡ 1 (mod 4)` if `u ≡ 3` and `S ≡ ℓ (mod 4)` if `u ≡ 1`. So
  `S = t ^ j` with `t ≡ 3 (mod 4)` and `j` odd forces `u ≡ 1` and `ℓ ≡ 3 (mod 4)`.
* `geom_sum_seven_mod_three`, `geom_sum_seven_ne_twentynine_pow`: for `ℓ = 7`, `S ≡ 1 (mod 3)`,
  so `S ≠ 29 ^ j` for odd `j`.
* `geom_sum_five_mod_seven`, `geom_sum_five_ne_fortyone_pow`: for `ℓ = 5`, `S mod 7` lies in
  `{1, 2, 3, 4, 5}`, so `S ≠ 41 ^ j` for odd `j`.
* `geom_sum_eleven_ne_twentythree_pow`: for `ℓ = 11`, `S ≠ 23 ^ j` for odd `j` (modulo 41).
* `geom_sum_twentythree_ne_fortyseven_pow`: for `ℓ = 23`, `S ≠ 47 ^ j` for odd `j` (moduli 7,
  19, 181, 271, 631 and 1153).

The last three are residue certificates checked by `decide +kernel` through one checker
(`EulerIndexPairEmitters.certOK`) and one soundness lemma.

Family result `eulerIndex_pair_emitter_small`: in the two prime setting, either
`(t, u) = (13, 3)`, or `(t, u) = (31, 5)`, or `t = 43` with `v_u(N) = 6`, or `t ≥ 53`.

These are restricted results (special exponent 1, Euler index supported on exactly two
primes). The case is not excluded: `t = 43` and infinitely many values `t ≥ 53` remain (the
two small pairs are removed in `EulerIndexPairSmallPairs`). Their novelty has not been
verified.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairEmitters

/-- Horner value of `∑ i < n, x ^ i` modulo `M`. -/
def geomMod (M x : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (geomMod M x n * x + 1) % M

/-- `∑ i < n + 1, x ^ i = (∑ i < n, x ^ i) * x + 1`. -/
private lemma sum_succ_horner (x n : ℕ) :
    ∑ i ∈ range (n + 1), x ^ i = (∑ i ∈ range n, x ^ i) * x + 1 := by
  rw [sum_range_succ', sum_mul]
  simp [pow_succ]

/-- The Horner value is the sum modulo `M`. -/
private lemma geomMod_eq (M x n : ℕ) : geomMod M x n = (∑ i ∈ range n, x ^ i) % M := by
  induction n with
  | zero => simp [geomMod]
  | succ n ih =>
    rw [geomMod.eq_2, ih, sum_succ_horner]
    exact ((Nat.mod_modEq _ M).mul_right x).add_right 1

/-- The Horner value only depends on `x % M`. -/
private lemma geomMod_mod (M x n : ℕ) : geomMod M (x % M) n = geomMod M x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [geomMod.eq_2, geomMod.eq_2, ih]
    exact ((Nat.mod_modEq x M).mul_left _).add_right 1

/-- The sum modulo `M` through the residue of `x`. -/
private lemma sum_mod_eq (M x n : ℕ) : (∑ i ∈ range n, x ^ i) % M = geomMod M (x % M) n := by
  rw [geomMod_mod, geomMod_eq]

/-- With base `1` the Horner value is `n % M`. -/
private lemma geomMod_one (M n : ℕ) : geomMod M 1 n = n % M := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [geomMod.eq_2, ih, mul_one]
    exact (Nat.mod_modEq n M).add_right 1

/-- Modulus `4`, base `3`, odd length: the Horner value is `1`. -/
private lemma geomMod_four_three (k : ℕ) : geomMod 4 3 (2 * k + 1) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, geomMod.eq_2, geomMod.eq_2, ih]

/-- The certificate checker: every modulus `M` is positive with `t ^ P ≡ 1 (mod M)`, no
value of `∑ i < n, x ^ i` modulo `M` lies in the list `F` of `M`, and for every odd `r < P`
some pair has `t ^ r % M ∈ F`. -/
def certOK (n t P : ℕ) (cs : List (ℕ × List ℕ)) : Bool :=
  cs.all (fun c => decide (0 < c.1 ∧ t ^ P % c.1 = 1 % c.1) &&
    (List.range c.1).all (fun x => !decide (geomMod c.1 x n ∈ c.2))) &&
  (List.range P).all (fun r => decide (r % 2 = 0) ||
    cs.any (fun c => decide (t ^ r % c.1 ∈ c.2)))

/-- Soundness of the checker. -/
private lemma ne_pow_of_certOK {n t : ℕ} (P : ℕ) (cs : List (ℕ × List ℕ)) (hP0 : 0 < P)
    (hP : 2 ∣ P) (hc : certOK n t P cs = true) (u : ℕ) {j : ℕ} (hj : Odd j) :
    ∑ i ∈ range n, u ^ i ≠ t ^ j := by
  intro h
  simp only [certOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.any_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, List.mem_range] at hc
  obtain ⟨hA, hB⟩ := hc
  have hr : j % P < P := Nat.mod_lt _ hP0
  have hro : ¬ j % P % 2 = 0 := by
    rw [Nat.mod_mod_of_dvd _ hP, Nat.odd_iff.mp hj]; norm_num
  obtain ⟨c, hcs, hcF⟩ := (hB (j % P) hr).resolve_left hro
  obtain ⟨⟨hM, hper⟩, hmiss⟩ := hA c hcs
  have hmod : t ^ j ≡ t ^ (j % P) [MOD c.1] := by
    have := ((show t ^ P ≡ 1 [MOD c.1] from hper).pow (j / P)).mul_right (t ^ (j % P))
    rwa [one_pow, one_mul, ← pow_mul, ← pow_add, Nat.div_add_mod] at this
  apply hmiss (u % c.1) (Nat.mod_lt _ hM)
  unfold Nat.ModEq at hmod
  rw [← sum_mod_eq, h, hmod]
  exact hcF

/-- `t ^ j % 4 = 3` for `t % 4 = 3` and odd `j`. -/
private lemma pow_mod_four {t j : ℕ} (ht : t % 4 = 3) (hj : Odd j) : t ^ j % 4 = 3 := by
  obtain ⟨k, rfl⟩ := hj
  rw [Nat.pow_mod, ht]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

/-- `σ(u ^ f)` as a geometric sum. -/
private lemma sigma_eq_sum {u f : ℕ} (hu : u.Prime) :
    σ 1 (u ^ f) = ∑ i ∈ range (f + 1), u ^ i := sigma_one_apply_prime_pow hu

end EulerIndexPairEmitters

open EulerIndexPairEmitters

/-- **Geometric sum modulo 4, base `3 (mod 4)`.** If `u ≡ 3 (mod 4)` and `ℓ` is odd, then
`∑ i < ℓ, u ^ i ≡ 1 (mod 4)`. -/
theorem geom_sum_mod_four_of_three {u ℓ : ℕ} (hu : u % 4 = 3) (hl : Odd ℓ) :
    (∑ i ∈ range ℓ, u ^ i) % 4 = 1 := by
  obtain ⟨k, rfl⟩ := hl
  rw [sum_mod_eq, hu, geomMod_four_three]

/-- **Geometric sum modulo 4, base `1 (mod 4)`.** If `u ≡ 1 (mod 4)`, then
`∑ i < ℓ, u ^ i ≡ ℓ (mod 4)`. -/
theorem geom_sum_mod_four_of_one {u ℓ : ℕ} (hu : u % 4 = 1) :
    (∑ i ∈ range ℓ, u ^ i) % 4 = ℓ % 4 := by
  rw [sum_mod_eq, hu, geomMod_one]

/-- **Geometric sum equal to a power of a prime `≡ 3 (mod 4)`.** If `u` and `ℓ` are odd,
`t ≡ 3 (mod 4)`, `j` is odd and `∑ i < ℓ, u ^ i = t ^ j`, then `u ≡ 1` and
`ℓ ≡ 3 (mod 4)`. -/
theorem geom_sum_eq_pow_mod_four {u ℓ t j : ℕ} (hu : Odd u) (hl : Odd ℓ) (ht : t % 4 = 3)
    (hj : Odd j) (h : ∑ i ∈ range ℓ, u ^ i = t ^ j) : u % 4 = 1 ∧ ℓ % 4 = 3 := by
  have h3 := pow_mod_four ht hj
  rw [← h] at h3
  have hu4 : u % 4 = 1 ∨ u % 4 = 3 := by have := Nat.odd_iff.mp hu; omega
  rcases hu4 with hu4 | hu4
  · rw [geom_sum_mod_four_of_one hu4] at h3
    exact ⟨hu4, h3⟩
  · rw [geom_sum_mod_four_of_three hu4 hl] at h3
    omega

/-- **Length 7 modulo 3.** `∑ i < 7, u ^ i ≡ 1 (mod 3)` for every `u`. -/
theorem geom_sum_seven_mod_three (u : ℕ) : (∑ i ∈ range 7, u ^ i) % 3 = 1 := by
  rw [sum_mod_eq]
  have hx := Nat.mod_lt u (by norm_num : 0 < 3)
  generalize u % 3 = x at hx ⊢
  interval_cases x <;> rfl

/-- **Length 7 against powers of 29.** `∑ i < 7, u ^ i ≠ 29 ^ j` for odd `j`. -/
theorem geom_sum_seven_ne_twentynine_pow (u : ℕ) {j : ℕ} (hj : Odd j) :
    ∑ i ∈ range 7, u ^ i ≠ 29 ^ j :=
  ne_pow_of_certOK 2 [(3, [2])] (by norm_num) (by norm_num) (by decide +kernel) u hj

/-- **Length 5 modulo 7.** `∑ i < 5, u ^ i` modulo 7 lies in `{1, 2, 3, 4, 5}`. -/
theorem geom_sum_five_mod_seven (u : ℕ) :
    1 ≤ (∑ i ∈ range 5, u ^ i) % 7 ∧ (∑ i ∈ range 5, u ^ i) % 7 ≤ 5 := by
  rw [sum_mod_eq]
  have hx := Nat.mod_lt u (by norm_num : 0 < 7)
  generalize u % 7 = x at hx ⊢
  interval_cases x <;> decide

/-- **Length 5 against powers of 41.** `∑ i < 5, u ^ i ≠ 41 ^ j` for odd `j`. -/
theorem geom_sum_five_ne_fortyone_pow (u : ℕ) {j : ℕ} (hj : Odd j) :
    ∑ i ∈ range 5, u ^ i ≠ 41 ^ j :=
  ne_pow_of_certOK 2 [(7, [6])] (by norm_num) (by norm_num) (by decide +kernel) u hj

/-- **Length 11 against powers of 23.** `∑ i < 11, u ^ i ≠ 23 ^ j` for odd `j`: modulo 41 the
order of 23 is 10, and no odd power of 23 is a value of `∑ i < 11, x ^ i` modulo 41. -/
theorem geom_sum_eleven_ne_twentythree_pow (u : ℕ) {j : ℕ} (hj : Odd j) :
    ∑ i ∈ range 11, u ^ i ≠ 23 ^ j :=
  ne_pow_of_certOK 10 [(41, [4, 23, 25, 31, 40])] (by norm_num) (by norm_num)
    (by decide +kernel) u hj

/-- **Length 23 against powers of 47.** `∑ i < 23, u ^ i ≠ 47 ^ j` for odd `j`: for every odd
residue of `j` modulo 360 one of the moduli 7, 19, 181, 271, 631, 1153 puts `47 ^ j` outside
the values of `∑ i < 23, x ^ i`. -/
theorem geom_sum_twentythree_ne_fortyseven_pow (u : ℕ) {j : ℕ} (hj : Odd j) :
    ∑ i ∈ range 23, u ^ i ≠ 47 ^ j :=
  ne_pow_of_certOK 360
    [(7, [6]), (19, [5, 6, 17]),
     (181, [2, 6, 8, 21, 28, 30, 35, 40, 41, 53, 54, 57, 61, 63, 69, 71, 76, 89, 90, 93, 95,
       98, 103, 107, 112, 113, 120, 123, 127, 130, 140, 149, 153, 157, 171, 179]),
     (271, [19, 24, 84, 86, 93, 104, 123, 165, 171, 192, 202, 216, 232, 240, 261]),
     (631, [16, 57, 128, 155, 172, 310, 337, 456, 485, 558, 562]),
     (1153, [47, 368, 529, 572, 1106])]
    (by norm_num) (by norm_num) (by decide +kernel) u hj

namespace EulerIndexPairEmitters

/-- The pairs `(ℓ, t)` with `ℓ` an odd prime, `t < 53` a prime and `t ≡ 1 (mod 2 ℓ)`. -/
private lemma small_cases {t ℓ : ℕ} (ht : t.Prime) (hl : ℓ.Prime) (hl2 : ℓ % 2 = 1)
    (hmod : t % (2 * ℓ) = 1) (h53 : t < 53) :
    ℓ = 3 ∨ (ℓ = 5 ∧ (t = 11 ∨ t = 31 ∨ t = 41)) ∨
      (ℓ = 7 ∧ (t = 29 ∨ t = 43)) ∨
      (ℓ = 11 ∧ t = 23) ∨ (ℓ = 23 ∧ t = 47) := by
  have ht2 := ht.two_le
  have hl3 : 3 ≤ ℓ := by have := hl.two_le; omega
  have hk : t = 2 * ℓ * (t / (2 * ℓ)) + 1 := by
    have := Nat.div_add_mod t (2 * ℓ); omega
  have hk1 : 1 ≤ t / (2 * ℓ) := by
    rcases Nat.eq_zero_or_pos (t / (2 * ℓ)) with h0 | h0
    · rw [h0] at hk; omega
    · exact h0
  have hl25 : ℓ ≤ 25 := by
    have : 2 * ℓ * 1 ≤ 2 * ℓ * (t / (2 * ℓ)) := Nat.mul_le_mul_left _ hk1
    omega
  generalize t / (2 * ℓ) = k at hk hk1
  subst hk
  interval_cases ℓ <;> norm_num at hl <;>
    (have : k ≤ 8 := by omega) <;> interval_cases k <;> first | omega | norm_num at ht

end EulerIndexPairEmitters

variable {N q m r s : ℕ}

/-- **Two prime index, small first labels.** Let `N = q m ^ 2` be an odd perfect number with
special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has
exactly the two prime factors `r ≠ s`. For the labeling `(t, u)` of
`eulerIndex_pair_pure_exponent_odd` (with `σ(u ^ v_u(N)) = t ^ j`, `j` odd), either
`(t, u) = (13, 3)`, or `(t, u) = (31, 5)`, or `t = 43` and `v_u(N) = 6`, or `t ≥ 53`.
This is a restricted result (special exponent 1, index supported on exactly two primes); it
does not exclude this case, and infinitely many values of `t` remain. Its novelty has not been
verified. -/
theorem eulerIndex_pair_emitter_small (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (∃ j, 0 < j ∧ Odd j ∧ σ 1 (u ^ N.factorization u) = t ^ j) ∧ ¬ t ∣ q + 1 ∧
      (N.factorization u + 1).Prime ∧ t % (2 * (N.factorization u + 1)) = 1 ∧
      ((t = 13 ∧ u = 3) ∨ (t = 31 ∧ u = 5) ∨ (t = 43 ∧ N.factorization u = 6) ∨
        53 ≤ t) := by
  obtain ⟨t, u, htu, hne, hA, ⟨j, hj, hjo, hB⟩, h3, -, hf1, -, hmod, -⟩ :=
    eulerIndex_pair_pure_exponent_odd h hq hN hqm hr hs hrs hJ
  refine ⟨t, u, htu, hne, hA, ⟨j, hj, hjo, hB⟩, h3, hf1, hmod, ?_⟩
  have hprime (p : ℕ) (hp : p ∈ ({t, u} : Finset ℕ)) : p.Prime := by
    rw [htu] at hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hr
    · rw [Finset.mem_singleton.mp hp]; exact hs
  have ht : t.Prime := hprime t (by simp)
  have hu : u.Prime := hprime u (by simp)
  set f := N.factorization u with hfdef
  have hf0 : f ≠ 0 := by rintro hf; rw [hf] at hf1; norm_num at hf1
  have huo : Odd u := Odd.of_dvd_nat h.1 (Nat.dvd_of_factorization_pos hf0)
  rw [sigma_eq_sum hu] at hB
  have ht2 : t % 2 = 1 := by
    rw [← Nat.mod_mod_of_dvd t (dvd_mul_right 2 (f + 1)), hmod]
  have hl2 : (f + 1) % 2 = 1 := by
    have h2 := congrArg (· % 2) hB
    rw [sum_mod_eq, Nat.odd_iff.mp huo, geomMod_one, Nat.pow_mod, ht2, one_pow] at h2
    omega
  by_cases h53 : 53 ≤ t
  · exact Or.inr (Or.inr (Or.inr h53))
  push Not at h53
  rcases EulerIndexPairEmitters.small_cases ht hf1 hl2 hmod h53 with
    hl | ⟨hl, ht'⟩ | ⟨hl, ht'⟩ | ⟨hl, ht'⟩ | ⟨hl, ht'⟩
  · -- `ℓ = 3`: Nagell gives `j = 1`, then `u ^ 2 + u + 1 = t < 53`
    rw [hl] at hB
    have hphi : phi3 u = t ^ j := by
      rw [← hB, phi3]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
      ring
    have hj1 := phi3_eq_prime_pow_exponent ht hu hj hphi
    rw [hj1, pow_one] at hphi
    unfold phi3 at hphi
    have hu8 : u < 8 := by nlinarith
    have hu2 := Nat.odd_iff.mp huo
    interval_cases u <;> first | omega | (norm_num at hphi; omega) | norm_num at hu
  · rw [hl] at hB
    rcases ht' with rfl | rfl | rfl
    · exact absurd (geom_sum_eq_pow_mod_four huo ⟨2, by norm_num⟩ (by norm_num) hjo hB).2
        (by norm_num)
    · exact absurd (geom_sum_eq_pow_mod_four huo ⟨2, by norm_num⟩ (by norm_num) hjo hB).2
        (by norm_num)
    · exact absurd hB (geom_sum_five_ne_fortyone_pow u hjo)
  · rw [hl] at hB
    rcases ht' with rfl | rfl
    · exact absurd hB (geom_sum_seven_ne_twentynine_pow u hjo)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
  · rw [hl] at hB; subst ht'
    exact absurd hB (geom_sum_eleven_ne_twentythree_pow u hjo)
  · rw [hl] at hB; subst ht'
    exact absurd hB (geom_sum_twentythree_ne_fortyseven_pow u hjo)

end OddPerfect

#print axioms OddPerfect.geom_sum_mod_four_of_three
#print axioms OddPerfect.geom_sum_mod_four_of_one
#print axioms OddPerfect.geom_sum_eq_pow_mod_four
#print axioms OddPerfect.geom_sum_seven_mod_three
#print axioms OddPerfect.geom_sum_seven_ne_twentynine_pow
#print axioms OddPerfect.geom_sum_five_mod_seven
#print axioms OddPerfect.geom_sum_five_ne_fortyone_pow
#print axioms OddPerfect.geom_sum_eleven_ne_twentythree_pow
#print axioms OddPerfect.geom_sum_twentythree_ne_fortyseven_pow
#print axioms OddPerfect.eulerIndex_pair_emitter_small
