import OddPerfect.LargestPrimeSigned

/-!
# Sharper signed capacity of the largest prime factor

This module refines `factorization_largest_le_signedCap`. Let `N` be an odd perfect number with
largest prime factor `P`, and write `P - 1 = 2 ^ a · m` with `m` odd. The senders into `P` are
odd primes `u < P`, and a sender of weight at least `j` has `u ^ (2 m) ≡ 1 (mod P ^ j)`.

* `card_le_of_two_signed_primes`: two senders `u ≠ v` at level `j ≥ 1` and any finite set of
  exponent vectors `(a, b, c, e)` with `a + b ≤ j / 2`, `c + e ≤ (j + 1) / 2`, `a c = 0`,
  `b e = 0` give that many distinct reduced pairs `(u ^ a v ^ b, u ^ c v ^ e)`, so the set has
  at most `m` elements.
* Level four and level five: at most one sender when `m ≤ 18`, respectively `m ≤ 26`.
* `card_le_two_of_signed_primes_cube`: three senders at level three give `28` reduced pairs,
  so at most two senders when `m ≤ 27`.
* `factorization_largest_le_signedCapFine`: `e_P ≤ signedCapFine m`, where the number of
  senders of weight at least `j` is bounded by the minimum of the level bounds at `1, …, j`.
  In particular `e_P ≤ 25, 23, 35, 47` for `m = 13, 15, 21, 25`, against the values
  `signedCap m = 42, 32, 60, 96` of the landed capacity.

These hold for every odd perfect number, with no hypothesis on the exponents. They bound
`e_P` only for the listed odd parts; the odd part itself is not bounded and no contradiction
follows. Novelty was not verified.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Products of prime powers -/

private theorem coprime_prime_pow {p q a c : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p = q → a * c = 0) : Nat.Coprime (p ^ a) (q ^ c) := by
  by_cases hpq : p = q
  · rcases Nat.mul_eq_zero.mp (h hpq) with h0 | h0 <;> simp [h0]
  · exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)

private theorem factorization_prod2 {u v : ℕ} (hu : u.Prime) (hv : v.Prime) (a b r : ℕ) :
    (u ^ a * v ^ b).factorization r = (if u = r then a else 0) + (if v = r then b else 0) := by
  rw [Nat.factorization_mul (pow_ne_zero _ hu.ne_zero) (pow_ne_zero _ hv.ne_zero)]
  simp [Nat.factorization_pow, hu.factorization, hv.factorization, Finsupp.single_apply]

private theorem factorization_prod3 {u v w : ℕ} (hu : u.Prime) (hv : v.Prime) (hw : w.Prime)
    (a b c r : ℕ) : (u ^ a * v ^ b * w ^ c).factorization r =
      (if u = r then a else 0) + (if v = r then b else 0) + (if w = r then c else 0) := by
  rw [Nat.factorization_mul (mul_ne_zero (pow_ne_zero _ hu.ne_zero) (pow_ne_zero _ hv.ne_zero))
    (pow_ne_zero _ hw.ne_zero), Finsupp.add_apply, factorization_prod2 hu hv]
  simp [Nat.factorization_pow, hw.factorization, Finsupp.single_apply]

private theorem odd_prod {u v : ℕ} (hu : u % 2 = 1) (hv : v % 2 = 1) (a b : ℕ) :
    u ^ a * v ^ b % 2 = 1 :=
  Nat.odd_iff.mp ((Nat.odd_iff.mpr hu).pow.mul (Nat.odd_iff.mpr hv).pow)

private theorem pow_modEq_prod {u v k n : ℕ} (hu : u ^ k ≡ 1 [MOD n]) (hv : v ^ k ≡ 1 [MOD n])
    (a b : ℕ) : (u ^ a * v ^ b) ^ k ≡ 1 [MOD n] := by
  have e : (u ^ a * v ^ b) ^ k = (u ^ k) ^ a * (v ^ k) ^ b := by ring
  rw [e]
  simpa using (hu.pow a).mul (hv.pow b)

private theorem prod_le_pow {u v n : ℕ} (hu : u ≤ n) (hv : v ≤ n) (a b : ℕ) :
    u ^ a * v ^ b ≤ n ^ (a + b) := by
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hu a) (Nat.pow_le_pow_left hv b)

/-! ## Two senders at level `j` -/

/-- Two senders at level `j`. Let `P` be prime with `P ∤ 2 m` and `j ≥ 1`, and let `u ≠ v` be
odd primes below `P` with `u ^ (2 m) ≡ v ^ (2 m) ≡ 1 (mod P ^ j)`. A finite set `V` of exponent
vectors `(a, b, c, e)` with `a + b ≤ j / 2`, `c + e ≤ (j + 1) / 2`, `a c = 0` and `b e = 0` has
`#V ≤ m`: the pairs `(u ^ a v ^ b, u ^ c v ^ e)` are distinct reduced pairs to which
`card_le_of_signed_reduced_pairs` applies. -/
theorem card_le_of_two_signed_primes {P m j u v : ℕ} (hP : P.Prime) (hPm : ¬ P ∣ 2 * m)
    (hj : 1 ≤ j) (hu : u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ j])
    (hv : v.Prime ∧ v % 2 = 1 ∧ v < P ∧ v ^ (2 * m) ≡ 1 [MOD P ^ j]) (huv : u ≠ v)
    (V : Finset (ℕ × ℕ × ℕ × ℕ))
    (hV : ∀ x ∈ V, x.1 + x.2.1 ≤ j / 2 ∧ x.2.2.1 + x.2.2.2 ≤ (j + 1) / 2 ∧
      x.1 * x.2.2.1 = 0 ∧ x.2.1 * x.2.2.2 = 0) : #V ≤ m := by
  obtain ⟨hup, hu2, huP, hud⟩ := hu
  obtain ⟨hvp, hv2, hvP, hvd⟩ := hv
  have hvu : v ≠ u := fun h => huv h.symm
  let A : ℕ × ℕ × ℕ × ℕ → ℕ := fun x => u ^ x.1 * v ^ x.2.1
  let B : ℕ × ℕ × ℕ × ℕ → ℕ := fun x => u ^ x.2.2.1 * v ^ x.2.2.2
  have hle : ∀ a b : ℕ, u ^ a * v ^ b ≤ (P - 1) ^ (a + b) :=
    prod_le_pow (by omega) (by omega)
  refine card_le_of_signed_reduced_pairs hP hPm hj V A B ?_ ?_
    (fun x _ => odd_prod hu2 hv2 _ _) (fun x _ => odd_prod hu2 hv2 _ _)
    (fun x _ => pow_modEq_prod hud hvd _ _) (fun x _ => pow_modEq_prod hud hvd _ _) ?_
  · intro x _ y _ hxy
    simp only [A, B, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have f1u := congrArg (fun n => n.factorization u) h1
    have f1v := congrArg (fun n => n.factorization v) h1
    have f2u := congrArg (fun n => n.factorization u) h2
    have f2v := congrArg (fun n => n.factorization v) h2
    simp only [factorization_prod2 hup hvp, huv, hvu, if_true, if_false] at f1u f1v f2u f2v
    ext <;> omega
  · intro x hx
    obtain ⟨-, -, h1, h2⟩ := hV x hx
    exact Nat.Coprime.mul_left
      (Nat.Coprime.mul_right (coprime_prime_pow hup hup fun _ => h1)
        (coprime_prime_pow hup hvp fun h => absurd h huv))
      (Nat.Coprime.mul_right (coprime_prime_pow hvp hup fun h => absurd h hvu)
        (coprime_prime_pow hvp hvp fun _ => h2))
  · intro x hx y hy
    have hx' := hV x hx
    have hy' := hV y hy
    have hP1 : 1 ≤ P - 1 := by have := hup.two_le; omega
    calc A x * B y ≤ (P - 1) ^ (x.1 + x.2.1) * (P - 1) ^ (y.2.2.1 + y.2.2.2) :=
          Nat.mul_le_mul (hle _ _) (hle _ _)
      _ = (P - 1) ^ (x.1 + x.2.1 + (y.2.2.1 + y.2.2.2)) := (pow_add _ _ _).symm
      _ ≤ (P - 1) ^ j := Nat.pow_le_pow_right hP1 (by omega)
      _ < P ^ j := Nat.pow_lt_pow_left (by omega) (by omega)

/-- The exponent vectors `(a, b, c, e)` with `a + b ≤ A`, `c + e ≤ C`, `a c = 0`, `b e = 0`. -/
private def signedVectors (A C : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (range (A + 1) ×ˢ range (A + 1) ×ˢ range (C + 1) ×ˢ range (C + 1)).filter fun x =>
    x.1 + x.2.1 ≤ A ∧ x.2.2.1 + x.2.2.2 ≤ C ∧ x.1 * x.2.2.1 = 0 ∧ x.2.1 * x.2.2.2 = 0

private theorem signedVectors_two_two : #(signedVectors 2 2) = 19 := by decide

private theorem signedVectors_two_three : #(signedVectors 2 3) = 27 := by decide

private theorem card_le_one_of_vectors {P m j A C : ℕ} (hP : P.Prime) (hPm : ¬ P ∣ 2 * m)
    (hj : 1 ≤ j) (hA : A ≤ j / 2) (hC : C ≤ (j + 1) / 2) (hm : m < #(signedVectors A C))
    (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ j]) : #s ≤ 1 := by
  by_contra hc
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < #s by omega)
  have := card_le_of_two_signed_primes hP hPm hj (hs u hu) (hs v hv) huv (signedVectors A C)
    fun x hx => by
      obtain ⟨-, h1, h2, h3, h4⟩ := Finset.mem_filter.mp hx
      exact ⟨by omega, by omega, h3, h4⟩
  omega

/-- Signed layer four: if `P ∤ 2 m` and `m ≤ 18`, at most one odd prime `u < P` has
`u ^ (2 m) ≡ 1 (mod P ^ 4)`. Two such primes give `19` reduced pairs. -/
theorem card_le_one_of_signed_primes_four {P m : ℕ} (hP : P.Prime) (hPm : ¬ P ∣ 2 * m)
    (hm : m ≤ 18) (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ 4]) : #s ≤ 1 :=
  card_le_one_of_vectors (A := 2) (C := 2) hP hPm (by norm_num) (by norm_num) (by norm_num)
    (by rw [signedVectors_two_two]; omega) s hs

/-- Signed layer five: if `P ∤ 2 m` and `m ≤ 26`, at most one odd prime `u < P` has
`u ^ (2 m) ≡ 1 (mod P ^ 5)`. Two such primes give `27` reduced pairs. -/
theorem card_le_one_of_signed_primes_five {P m : ℕ} (hP : P.Prime) (hPm : ¬ P ∣ 2 * m)
    (hm : m ≤ 26) (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ 5]) : #s ≤ 1 :=
  card_le_one_of_vectors (A := 2) (C := 3) hP hPm (by norm_num) (by norm_num) (by norm_num)
    (by rw [signedVectors_two_three]; omega) s hs

/-! ## Three senders at level three -/

/-- The exponent vectors `(a₁, a₂, a₃, c₁, c₂, c₃)` with `a₁ + a₂ + a₃ ≤ 1`,
`c₁ + c₂ + c₃ ≤ 2` and `aᵢ cᵢ = 0`. -/
private def tripleVectors : Finset (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (range 2 ×ˢ range 2 ×ˢ range 2 ×ˢ range 3 ×ˢ range 3 ×ˢ range 3).filter fun x =>
    x.1 + x.2.1 + x.2.2.1 ≤ 1 ∧ x.2.2.2.1 + x.2.2.2.2.1 + x.2.2.2.2.2 ≤ 2 ∧
      x.1 * x.2.2.2.1 = 0 ∧ x.2.1 * x.2.2.2.2.1 = 0 ∧ x.2.2.1 * x.2.2.2.2.2 = 0

private theorem tripleVectors_card : #tripleVectors = 28 := by decide

/-- Signed layer three with three senders: if `P ∤ 2 m` and `m ≤ 27`, at most two odd primes
`u < P` have `u ^ (2 m) ≡ 1 (mod P ^ 3)`. Three such primes `u, v, w` give `28` reduced pairs
`(u ^ a₁ v ^ a₂ w ^ a₃, u ^ c₁ v ^ c₂ w ^ c₃)` with numerator of at most one factor and
denominator of at most two. -/
theorem card_le_two_of_signed_primes_cube {P m : ℕ} (hP : P.Prime) (hPm : ¬ P ∣ 2 * m)
    (hm : m ≤ 27) (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ 3]) : #s ≤ 2 := by
  by_contra hc
  obtain ⟨u, hu, v, hv, w, hw, huv, huw, hvw⟩ := Finset.two_lt_card.mp (show 2 < #s by omega)
  obtain ⟨hup, hu2, huP, hud⟩ := hs u hu
  obtain ⟨hvp, hv2, hvP, hvd⟩ := hs v hv
  obtain ⟨hwp, hw2, hwP, hwd⟩ := hs w hw
  have hvu : v ≠ u := fun h => huv h.symm
  have hwu : w ≠ u := fun h => huw h.symm
  have hwv : w ≠ v := fun h => hvw h.symm
  let A : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → ℕ := fun x => u ^ x.1 * v ^ x.2.1 * w ^ x.2.2.1
  let B : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → ℕ := fun x =>
    u ^ x.2.2.2.1 * v ^ x.2.2.2.2.1 * w ^ x.2.2.2.2.2
  have hodd : ∀ a b c : ℕ, u ^ a * v ^ b * w ^ c % 2 = 1 := fun a b c =>
    Nat.odd_iff.mp (((Nat.odd_iff.mpr hu2).pow.mul (Nat.odd_iff.mpr hv2).pow).mul
      (Nat.odd_iff.mpr hw2).pow)
  have hpow : ∀ a b c : ℕ, (u ^ a * v ^ b * w ^ c) ^ (2 * m) ≡ 1 [MOD P ^ 3] := fun a b c => by
    have := pow_modEq_prod (pow_modEq_prod hud hvd a b) hwd 1 c
    rwa [pow_one] at this
  have hle : ∀ a b c : ℕ, u ^ a * v ^ b * w ^ c ≤ (P - 1) ^ (a + b + c) := fun a b c => by
    rw [pow_add]
    exact Nat.mul_le_mul (prod_le_pow (by omega) (by omega) a b) (Nat.pow_le_pow_left (by omega) c)
  have hcard := card_le_of_signed_reduced_pairs hP hPm (by norm_num) tripleVectors A B ?_ ?_
    (fun x _ => hodd _ _ _) (fun x _ => hodd _ _ _) (fun x _ => hpow _ _ _)
    (fun x _ => hpow _ _ _) ?_
  · rw [tripleVectors_card] at hcard
    omega
  · intro x _ y _ hxy
    simp only [A, B, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have f1u := congrArg (fun n => n.factorization u) h1
    have f1v := congrArg (fun n => n.factorization v) h1
    have f1w := congrArg (fun n => n.factorization w) h1
    have f2u := congrArg (fun n => n.factorization u) h2
    have f2v := congrArg (fun n => n.factorization v) h2
    have f2w := congrArg (fun n => n.factorization w) h2
    simp only [factorization_prod3 hup hvp hwp, huv, hvu, huw, hwu, hvw, hwv, if_true,
      if_false] at f1u f1v f1w f2u f2v f2w
    ext <;> omega
  · intro x hx
    obtain ⟨-, -, -, h1, h2, h3⟩ := Finset.mem_filter.mp hx
    have k : ∀ {p a : ℕ}, p.Prime → (p = u → a * x.2.2.2.1 = 0) →
        (p = v → a * x.2.2.2.2.1 = 0) → (p = w → a * x.2.2.2.2.2 = 0) →
        Nat.Coprime (p ^ a) (B x) := fun hp hpu hpv hpw =>
      Nat.Coprime.mul_right (Nat.Coprime.mul_right (coprime_prime_pow hp hup hpu)
        (coprime_prime_pow hp hvp hpv)) (coprime_prime_pow hp hwp hpw)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_left
      (k hup (fun _ => h1) (fun h => absurd h huv) (fun h => absurd h huw))
      (k hvp (fun h => absurd h hvu) (fun _ => h2) (fun h => absurd h hvw)))
      (k hwp (fun h => absurd h hwu) (fun h => absurd h hwv) (fun _ => h3))
  · intro x hx y hy
    obtain ⟨-, hx1, -⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, -, hy2, -⟩ := Finset.mem_filter.mp hy
    have hP1 : 1 ≤ P - 1 := by have := hup.two_le; omega
    calc A x * B y ≤ (P - 1) ^ (x.1 + x.2.1 + x.2.2.1) *
            (P - 1) ^ (y.2.2.2.1 + y.2.2.2.2.1 + y.2.2.2.2.2) :=
          Nat.mul_le_mul (hle _ _ _) (hle _ _ _)
      _ = (P - 1) ^ (x.1 + x.2.1 + x.2.2.1 + (y.2.2.2.1 + y.2.2.2.2.1 + y.2.2.2.2.2)) :=
          (pow_add _ _ _).symm
      _ ≤ (P - 1) ^ 3 := Nat.pow_le_pow_right hP1 (by omega)
      _ < P ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)

/-! ## The refined layer capacity -/

/-- The bound on the number of senders of weight at least `j` from level `j` alone: `m - 1` at
`j = 1`; `sqCap m` at `j = 2`; at `j = 3`, `1` when `m ≤ 11` and `2` when `m ≤ 27`; `1` at
`j = 4` when `m ≤ 18`; `1` at `j ≥ 5` when `m ≤ 26`; `sqCap m` otherwise. -/
def signedLevelCap (m j : ℕ) : ℕ :=
  if j = 1 then m - 1 else if j = 2 then sqCap m
  else if j = 3 ∧ m ≤ 11 then 1 else if j = 3 ∧ m ≤ 27 then 2
  else if j = 4 ∧ m ≤ 18 then 1 else if 5 ≤ j ∧ m ≤ 26 then 1 else sqCap m

/-- The monotone layer bound: the minimum of `signedLevelCap m i` over `1 ≤ i ≤ j` (and of `m`). -/
def signedLayerFine (m : ℕ) : ℕ → ℕ
  | 0 => m
  | j + 1 => min (signedLayerFine m j) (signedLevelCap m (j + 1))

/-- The refined signed capacity: `∑ j ∈ [1, φ(m) - 1], signedLayerFine m j`. -/
def signedCapFine (m : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 (m.totient - 1), signedLayerFine m j

/-- The value `signedCapFine 13 = 25`. -/
theorem signedCapFine_thirteen : signedCapFine 13 = 25 := by decide
/-- The value `signedCapFine 15 = 23`. -/
theorem signedCapFine_fifteen : signedCapFine 15 = 23 := by decide
/-- The value `signedCapFine 21 = 35`. -/
theorem signedCapFine_twentyone : signedCapFine 21 = 35 := by decide
/-- The value `signedCapFine 25 = 47`. -/
theorem signedCapFine_twentyfive : signedCapFine 25 = 47 := by decide

/-- The level bound: if `P ∤ 2 m` and `j ≥ 1`, a finite set of odd primes `u < P` with
`u ^ (2 m) ≡ 1 (mod P ^ j)` has at most `signedLevelCap m j` elements. -/
theorem card_le_signedLevelCap {P m j : ℕ} (hP : P.Prime) (hPm : ¬ P ∣ 2 * m) (hj : 1 ≤ j)
    (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ j]) :
    #s ≤ signedLevelCap m j := by
  have hw : ∀ i, i ≤ j →
      ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ i] :=
    fun i hi u hu => ⟨(hs u hu).1, (hs u hu).2.1, (hs u hu).2.2.1,
      (hs u hu).2.2.2.of_dvd (Nat.pow_dvd_pow P hi)⟩
  unfold signedLevelCap
  split_ifs with h1 h2 h3 h4 h5 h6
  · subst h1
    have := card_add_one_le_of_signed_primes hP hPm s fun u hu => by
      have h := hs u hu
      rwa [pow_one] at h
    omega
  · subst h2
    exact le_sqCap (sq_add_add_one_le_of_signed_primes hP hPm s hs)
  · obtain ⟨rfl, h⟩ := h3
    exact card_le_one_of_signed_primes_cube hP hPm h s hs
  · obtain ⟨rfl, h⟩ := h4
    exact card_le_two_of_signed_primes_cube hP hPm h s hs
  · obtain ⟨rfl, h⟩ := h5
    exact card_le_one_of_signed_primes_four hP hPm h s hs
  · exact card_le_one_of_signed_primes_five hP hPm h6.2 s (hw 5 h6.1)
  · exact le_sqCap (sq_add_add_one_le_of_signed_primes hP hPm s (hw 2 (by omega)))

/-! ## Senders into the largest prime factor -/

variable {N : ℕ}

private theorem layer_cake_fine {f n : ℕ} (h : f ≤ n) :
    f = ∑ j ∈ Finset.Icc 1 n, if j ≤ f then 1 else 0 := by
  rw [← Finset.card_filter]
  have : (Finset.Icc 1 n).filter (fun j => j ≤ f) = Finset.Icc 1 f := by
    ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]
  omega

private theorem sum_senders_fine (h : OddPerfect N) {P : ℕ} (hP : P ∈ N.primeFactors) :
    N.factorization P = ∑ p ∈ (N.primeFactors.erase P).filter
      (fun p => P ∣ σ 1 (p ^ N.factorization p)), padicValNat P (σ 1 (p ^ N.factorization p)) := by
  have hP2 : P ≠ 2 := by
    have := Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hP))
    omega
  rw [factorization_eq_sum_erase h.perfect (Nat.prime_of_mem_primeFactors hP) hP2,
    Finset.sum_filter_of_ne]
  intro p _ hne
  by_contra hd
  exact hne (padicValNat.eq_zero_of_not_dvd hd)

/-- A sender `u` into the largest prime factor `P` with `P - 1 = 2 ^ a · m`, `m` odd, is an odd
prime below `P` of weight at most `φ(m) - 1`, with `u ^ (2 m) ≡ 1 (mod P ^ j)` for every `j`
up to its weight. -/
private theorem sender_signed_fine (h : OddPerfect N) {P a m : ℕ} (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hm : P - 1 = 2 ^ a * m) (hmo : Odd m)
    {u : ℕ} (hu : u ∈ N.primeFactors) (huP : u ≠ P) (hd : P ∣ σ 1 (u ^ N.factorization u)) :
    u.Prime ∧ u % 2 = 1 ∧ u < P ∧
      padicValNat P (σ 1 (u ^ N.factorization u)) ≤ m.totient - 1 ∧
      ∀ j, j ≤ padicValNat P (σ 1 (u ^ N.factorization u)) → u ^ (2 * m) ≡ 1 [MOD P ^ j] := by
  obtain ⟨hlt, hu2, ht, h4, hw⟩ := sender_largest_data h hP hmax hu huP hd
  have hup := Nat.prime_of_mem_primeFactors hu
  have hPp := Nat.prime_of_mem_primeFactors hP
  have : Fact P.Prime := ⟨hPp⟩
  have hu0 : (u : ZMod P) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hh
    have := Nat.le_of_dvd hup.pos hh
    omega
  have htP : orderOf (u : ZMod P) ∣ 2 ^ a * m := hm ▸ ZMod.orderOf_dvd_card_sub_one hu0
  have ht2m : orderOf (u : ZMod P) ∣ 2 * m := by
    rcases Nat.even_or_odd (orderOf (u : ZMod P)) with ⟨k, hk⟩ | hto
    · have hko : Odd k := Nat.odd_iff.mpr (by omega)
      have hkm : k ∣ m :=
        (Nat.Coprime.pow_right a ((Nat.coprime_two_right).mpr hko)).dvd_of_dvd_mul_left
          (Nat.dvd_trans ⟨2, by omega⟩ htP)
      rw [hk, ← two_mul]
      exact Nat.mul_dvd_mul_left 2 hkm
    · exact ((Nat.Coprime.pow_right a ((Nat.coprime_two_right).mpr hto)).dvd_of_dvd_mul_left
        htP).trans (dvd_mul_left m 2)
  refine ⟨hup, hu2, hlt, ?_, fun j hj => ?_⟩
  · have h1 := padicValNat_pow_orderOf_sub_one_lt_totient hup hPp hlt ht
    have h2 : (orderOf (u : ZMod P)).totient ≤ m.totient := by
      rw [← Nat.totient_two_mul_of_odd hmo]
      exact Nat.le_of_dvd (Nat.totient_pos.mpr (by have := hmo.pos; omega))
        (Nat.totient_dvd_of_dvd ht2m)
    rw [hw]
    omega
  · rw [hw] at hj
    have hpt : 1 ≤ u ^ orderOf (u : ZMod P) := Nat.one_le_pow _ _ hup.pos
    have hdvd : P ^ j ∣ u ^ orderOf (u : ZMod P) - 1 :=
      (pow_dvd_pow P hj).trans pow_padicValNat_dvd
    have hmod : u ^ orderOf (u : ZMod P) ≡ 1 [MOD P ^ j] :=
      ((Nat.modEq_iff_dvd' hpt).mpr hdvd).symm
    obtain ⟨k, hk⟩ := ht2m
    rw [hk, pow_mul]
    simpa using hmod.pow k

/-- Refined signed capacity of the largest prime factor. Let `P` be the largest prime factor of
an odd perfect number `N` and `P - 1 = 2 ^ a · m` with `m` odd. Then
`v_P(N) ≤ signedCapFine m`: the senders of weight at least `j` number at most
`signedLayerFine m j`. Unconditional; it gives no contradiction. -/
theorem factorization_largest_le_signedCapFine (h : OddPerfect N) {P a m : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * m) (hmo : Odd m) : N.factorization P ≤ signedCapFine m := by
  classical
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hPm : ¬ P ∣ 2 * m := by
    intro hd
    have hmpos := hmo.pos
    have ha : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have hmP : m < P := by
      have := Nat.le_mul_of_pos_left m ha
      have := hPp.two_le
      omega
    rcases (Nat.Prime.dvd_mul hPp).mp hd with h2 | h2
    · have := Nat.le_of_dvd two_pos h2
      have hPodd : P % 2 = 1 :=
        Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hP))
      have := hPp.two_le
      omega
    · have := Nat.le_of_dvd hmpos h2
      omega
  rw [sum_senders_fine h hP]
  set S := (N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p)) with hS
  set w : ℕ → ℕ := fun u => padicValNat P (σ 1 (u ^ N.factorization u)) with hwdef
  have hdat : ∀ u ∈ S, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ w u ≤ m.totient - 1 ∧
      ∀ j, j ≤ w u → u ^ (2 * m) ≡ 1 [MOD P ^ j] := by
    intro u hu
    rw [hS, Finset.mem_filter, Finset.mem_erase] at hu
    exact sender_signed_fine h hP hmax hm hmo hu.1.2 hu.1.1 hu.2
  have hlevel : ∀ j, 1 ≤ j → #(S.filter (fun u => j ≤ w u)) ≤ signedLevelCap m j := by
    intro j hj
    refine card_le_signedLevelCap hPp hPm hj _ fun u hu => ?_
    obtain ⟨huS, hju⟩ := Finset.mem_filter.mp hu
    obtain ⟨h1, h2, h3, -, h5⟩ := hdat u huS
    exact ⟨h1, h2, h3, h5 j hju⟩
  have hfine : ∀ n, #(S.filter (fun u => n + 1 ≤ w u)) ≤ signedLayerFine m (n + 1) := by
    intro n
    induction n with
    | zero =>
      have := hlevel 1 le_rfl
      simp only [signedLevelCap, if_true] at this
      simp only [zero_add, signedLayerFine, signedLevelCap, if_true]
      omega
    | succ n ih =>
      refine le_min (le_trans (Finset.card_le_card fun u hu => ?_) ih) (hlevel _ (by omega))
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨h1, by omega⟩
  calc ∑ u ∈ S, w u
      = ∑ u ∈ S, ∑ j ∈ Finset.Icc 1 (m.totient - 1), (if j ≤ w u then 1 else 0) :=
        Finset.sum_congr rfl fun u hu => layer_cake_fine (hdat u hu).2.2.2.1
    _ = ∑ j ∈ Finset.Icc 1 (m.totient - 1), #(S.filter (fun u => j ≤ w u)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
    _ ≤ signedCapFine m := by
        unfold signedCapFine
        refine Finset.sum_le_sum fun j hj => ?_
        obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by have := (Finset.mem_Icc.mp hj).1; omega⟩
        exact hfine n

/-- If the odd part of `P - 1` is `13`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 25`. -/
theorem factorization_largest_le_twentyfive_of_odd_part_thirteen (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 13) : N.factorization P ≤ 25 :=
  signedCapFine_thirteen ▸ factorization_largest_le_signedCapFine h hP hmax hm (by decide)

/-- If the odd part of `P - 1` is `15`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 23`. -/
theorem factorization_largest_le_twentythree_of_odd_part_fifteen (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 15) : N.factorization P ≤ 23 :=
  signedCapFine_fifteen ▸ factorization_largest_le_signedCapFine h hP hmax hm (by decide)

/-- If the odd part of `P - 1` is `21`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 35`. -/
theorem factorization_largest_le_thirtyfive_of_odd_part_twentyone (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 21) : N.factorization P ≤ 35 :=
  signedCapFine_twentyone ▸ factorization_largest_le_signedCapFine h hP hmax hm (by decide)

/-- If the odd part of `P - 1` is `25`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 47`. -/
theorem factorization_largest_le_fortyseven_of_odd_part_twentyfive (h : OddPerfect N)
    {P a : ℕ} (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 25) : N.factorization P ≤ 47 :=
  signedCapFine_twentyfive ▸ factorization_largest_le_signedCapFine h hP hmax hm (by decide)

end OddPerfect

#print axioms OddPerfect.card_le_of_two_signed_primes
#print axioms OddPerfect.card_le_one_of_signed_primes_four
#print axioms OddPerfect.card_le_one_of_signed_primes_five
#print axioms OddPerfect.card_le_two_of_signed_primes_cube
#print axioms OddPerfect.signedCapFine_thirteen
#print axioms OddPerfect.signedCapFine_fifteen
#print axioms OddPerfect.signedCapFine_twentyone
#print axioms OddPerfect.signedCapFine_twentyfive
#print axioms OddPerfect.card_le_signedLevelCap
#print axioms OddPerfect.factorization_largest_le_signedCapFine
#print axioms OddPerfect.factorization_largest_le_twentyfive_of_odd_part_thirteen
#print axioms OddPerfect.factorization_largest_le_twentythree_of_odd_part_fifteen
#print axioms OddPerfect.factorization_largest_le_thirtyfive_of_odd_part_twentyone
#print axioms OddPerfect.factorization_largest_le_fortyseven_of_odd_part_twentyfive
