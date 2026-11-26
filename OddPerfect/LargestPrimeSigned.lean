import OddPerfect.LargestPrimeCapacity
import OddPerfect.PrimeCap

/-!
# Signed packing of the senders into the largest prime factor

Let `N` be an odd perfect number with largest prime factor `P`, and write `P - 1 = 2 ^ a · m`
with `m` odd. A sender is a prime factor `u ≠ P` with `P ∣ σ(u ^ e_u)`; its weight is
`w_u = v_P(σ(u ^ e_u))`, and `e_P = Σ_u w_u`. By `sender_largest_data` every sender is odd,
lies below `P`, and has order `t` modulo `P` with `4 ∤ t`, so `t ∣ 2 m` and
`u ^ (2 m) ≡ 1 (mod P ^ j)` for every `j ≤ w_u`. Senders of order `d` and of order `2 d` are
counted in one pool.

* `eq_of_sq_modEq_of_pow_two_mul_modEq_one`: the signed lifting lemma. Odd `X, Y < P ^ j`
  whose `2 m`-th powers are `1` modulo `P ^ j` and whose squares agree modulo `P` are equal:
  the case `X ≡ -Y (mod P)` would give `X + Y = P ^ j`, even equal to odd.
* `card_le_of_signed_reduced_pairs`: reduced pairs `(A i, B i)` of odd integers as above give
  distinct values `(A i / B i) ^ 2` modulo `P`, all `m`-th roots of unity; so at most `m` pairs.
* Layers of prime senders: `#s + 1 ≤ m` at level `1`, `#s ^ 2 + #s + 1 ≤ m` at level `2`, and
  `#s ≤ 1` at level `3` when `m ≤ 11`.
* `factorization_largest_le_signedCap`: `e_P ≤ signedCap m`, the layer sum over the levels
  `1, …, φ(m) - 1`; in particular `e_P ≤ 6, 11, 13, 19` for `m = 5, 7, 9, 11`.

These are unconditional statements about every odd perfect number (no hypothesis on the
exponents; the special prime is included). They give no contradiction. Counting small fractions
in multiplicative subgroups is related to work in the literature (Bourgain, Konyagin,
Shparlinski, IMRN 2012); novelty was not verified.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## The signed lifting lemma -/

private theorem not_dvd_of_pow_two_mul_modEq_one {P m j Z : ℕ} (hP : P.Prime) (hm : m ≠ 0)
    (hj : 1 ≤ j) (hZ : Z ^ (2 * m) ≡ 1 [MOD P ^ j]) : ¬ P ∣ Z := by
  have : Fact P.Prime := ⟨hP⟩
  intro hPZ
  have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (hZ.of_dvd (dvd_pow_self P (by omega : j ≠ 0)))
  push_cast at h1
  rw [(ZMod.natCast_eq_zero_iff Z P).mpr hPZ, zero_pow (by omega)] at h1
  exact zero_ne_one h1

/-- Signed lifting lemma. Let `P` be prime with `P ∤ 2 m` and `j ≥ 1`. Let `X, Y < P ^ j` be
odd with `X ^ (2 m) ≡ Y ^ (2 m) ≡ 1 (mod P ^ j)` and `X ^ 2 ≡ Y ^ 2 (mod P)`. Then `X = Y`. -/
theorem eq_of_sq_modEq_of_pow_two_mul_modEq_one {P m j X Y : ℕ} (hP : P.Prime)
    (hPm : ¬ P ∣ 2 * m) (hj : 1 ≤ j) (hX : X < P ^ j) (hY : Y < P ^ j)
    (hXo : X % 2 = 1) (hYo : Y % 2 = 1)
    (hXm : X ^ (2 * m) ≡ 1 [MOD P ^ j]) (hYm : Y ^ (2 * m) ≡ 1 [MOD P ^ j])
    (hXY : X ^ 2 ≡ Y ^ 2 [MOD P]) : X = Y := by
  have : Fact P.Prime := ⟨hP⟩
  have hm0 : m ≠ 0 := by rintro rfl; simp at hPm
  have hP2 : P ≠ 2 := fun h => hPm (h ▸ dvd_mul_right 2 m)
  have hPodd : P % 2 = 1 := hP.eq_two_or_odd.resolve_left hP2
  have hPj : P ^ j % 2 = 1 := by rw [Nat.pow_mod, hPodd, one_pow]; norm_num
  have hsq : ((X : ZMod P) - Y) * ((X : ZMod P) + Y) = 0 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hXY
    push_cast at this
    linear_combination this
  have hpow : X ^ (2 * m) ≡ Y ^ (2 * m) [MOD P ^ j] := hXm.trans hYm.symm
  have hndX := not_dvd_of_pow_two_mul_modEq_one hP hm0 hj hXm
  rcases mul_eq_zero.mp hsq with h | h
  · exact eq_of_modEq_of_pow_modEq hP hPm hX hY hndX
      ((ZMod.natCast_eq_natCast_iff _ _ _).mp (sub_eq_zero.mp h)) hpow
  · exfalso
    obtain ⟨Y', hY'⟩ : ∃ Y', Y' + Y = P ^ j := ⟨P ^ j - Y, by omega⟩
    have hY'lt : Y' < P ^ j := by omega
    have hcast : (X : ZMod P) = Y' := by
      have e := congrArg (Nat.cast : ℕ → ZMod P) hY'
      rw [Nat.cast_add, Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega)] at e
      linear_combination h - e
    have hY'pow : Y' ^ (2 * m) ≡ Y ^ (2 * m) [MOD P ^ j] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      have e := congrArg (Nat.cast : ℕ → ZMod (P ^ j)) hY'
      rw [Nat.cast_add, ZMod.natCast_self] at e
      have e' : (Y' : ZMod (P ^ j)) = -Y := eq_neg_of_add_eq_zero_left e
      push_cast
      rw [e', Even.neg_pow ⟨m, by ring⟩]
    have hXY' := eq_of_modEq_of_pow_modEq hP hPm hX hY'lt hndX
      ((ZMod.natCast_eq_natCast_iff _ _ _).mp hcast) (hpow.trans hY'pow.symm)
    omega

/-- The injection lemma for signed reduced fractions. Let `P` be prime with `P ∤ 2 m` and
`j ≥ 1`. Let `T` index distinct pairs `(A i, B i)` of coprime odd integers with
`A i ^ (2 m) ≡ B i ^ (2 m) ≡ 1 (mod P ^ j)` and `A i * B k < P ^ j` for all `i, k ∈ T`. Then
`#T ≤ m`: the squares `(A i / B i) ^ 2` modulo `P` are distinct roots of `x ^ m = 1`. -/
theorem card_le_of_signed_reduced_pairs {ι : Type*} {P m j : ℕ} (hP : P.Prime)
    (hPm : ¬ P ∣ 2 * m) (hj : 1 ≤ j) (T : Finset ι) (A B : ι → ℕ)
    (hinj : Set.InjOn (fun i => (A i, B i)) T) (hcop : ∀ i ∈ T, Nat.Coprime (A i) (B i))
    (hAo : ∀ i ∈ T, A i % 2 = 1) (hBo : ∀ i ∈ T, B i % 2 = 1)
    (hA : ∀ i ∈ T, A i ^ (2 * m) ≡ 1 [MOD P ^ j]) (hB : ∀ i ∈ T, B i ^ (2 * m) ≡ 1 [MOD P ^ j])
    (hlt : ∀ i ∈ T, ∀ k ∈ T, A i * B k < P ^ j) : #T ≤ m := by
  classical
  have : Fact P.Prime := ⟨hP⟩
  have hm0 : m ≠ 0 := by rintro rfl; simp at hPm
  have hcast : ∀ Z, Z ^ (2 * m) ≡ 1 [MOD P ^ j] → (Z : ZMod P) ^ (2 * m) = 1 := by
    intro Z hZ
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (hZ.of_dvd (dvd_pow_self P (by omega : j ≠ 0)))
    push_cast at this
    exact this
  have hBne : ∀ i ∈ T, (B i : ZMod P) ≠ 0 := fun i hi h0 => by
    have := hcast _ (hB i hi)
    rw [h0, zero_pow (by omega)] at this
    exact zero_ne_one this
  set φ : ι → ZMod P := fun i => ((A i : ZMod P) / (B i : ZMod P)) ^ 2 with hφ
  have hprod : ∀ i ∈ T, ∀ k ∈ T, (A i * B k) ^ (2 * m) ≡ 1 [MOD P ^ j] := by
    intro i hi k hk
    rw [mul_pow]
    simpa using (hA i hi).mul (hB k hk)
  have hodd : ∀ i ∈ T, ∀ k ∈ T, A i * B k % 2 = 1 := by
    intro i hi k hk
    rw [Nat.mul_mod, hAo i hi, hBo k hk]
  have hinjφ : Set.InjOn φ T := by
    intro i hi k hk h
    simp only [hφ, div_pow] at h
    rw [div_eq_div_iff (pow_ne_zero _ (hBne i hi)) (pow_ne_zero _ (hBne k hk))] at h
    have hXY : (A i * B k) ^ 2 ≡ (A k * B i) ^ 2 [MOD P] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      linear_combination h
    have hX := eq_of_sq_modEq_of_pow_two_mul_modEq_one hP hPm hj (hlt i hi k hk)
      (hlt k hk i hi) (hodd i hi k hk) (hodd k hk i hi) (hprod i hi k hk) (hprod k hk i hi) hXY
    have hpos : 0 < A i := by have := hAo i hi; omega
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul_of_coprime hpos (hcop i hi) (hcop k hk)
      (by rw [hX, mul_comm])
    exact hinj hi hk (Prod.ext h1 h2)
  have hsub : T.image φ ⊆ (Polynomial.nthRoots m (1 : ZMod P)).toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hm0)]
    show (((A i : ZMod P) / B i) ^ 2) ^ m = 1
    rw [← pow_mul, div_pow, hcast _ (hA i hi), hcast _ (hB i hi), div_one]
  have c1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinjφ] at c1
  exact c1.trans ((Multiset.toFinset_card_le _).trans
    (Polynomial.card_nthRoots m (1 : ZMod P)))

/-! ## Layers of prime senders -/

private theorem mem_insert_one' {P m j : ℕ} (hP : P.Prime) {s : Finset ℕ}
    (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ j]) {v : ℕ}
    (hv : v ∈ insert 1 s) : v % 2 = 1 ∧ v < P ∧ v ^ (2 * m) ≡ 1 [MOD P ^ j] := by
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact ⟨rfl, hP.one_lt, by rw [one_pow]⟩
  · exact (hs v hv).2

private theorem coprime_of_mem_insert_one' {s : Finset ℕ} (hs : ∀ u ∈ s, u.Prime) {a b : ℕ}
    (ha : a ∈ insert 1 s) (hb : b ∈ insert 1 s) (hab : a ≠ b) : Nat.Coprime a b := by
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact Nat.coprime_one_left _
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact Nat.coprime_one_right _
  exact (Nat.coprime_primes (hs a ha) (hs b hb)).mpr hab

private theorem one_notMem_of_primes' {s : Finset ℕ} (hs : ∀ u ∈ s, u.Prime) : 1 ∉ s :=
  fun h => Nat.not_prime_one (hs 1 h)

private theorem injOn_pair' (T : Finset (ℕ × ℕ)) :
    Set.InjOn (fun i : ℕ × ℕ => (i.1, i.2)) T :=
  fun _ _ _ _ h => Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Signed layer one: a finite set `s` of odd primes below the prime `P` with
`u ^ (2 m) ≡ 1 (mod P)`, where `P ∤ 2 m`, has `#s + 1 ≤ m`. -/
theorem card_add_one_le_of_signed_primes {P m : ℕ} (hP : P.Prime) (hPm : ¬ P ∣ 2 * m)
    (s : Finset ℕ) (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P]) :
    #s + 1 ≤ m := by
  have hs' : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ 1] := by
    simpa only [pow_one] using hs
  have hc := card_le_of_signed_reduced_pairs hP hPm le_rfl ((insert 1 s) ×ˢ {1}) Prod.fst
    Prod.snd (injOn_pair' _)
    (fun i hi => by rw [Finset.mem_singleton.mp (Finset.mem_product.mp hi).2]; exact
      Nat.coprime_one_right _)
    (fun i hi => (mem_insert_one' hP hs' (Finset.mem_product.mp hi).1).1)
    (fun i hi => by rw [Finset.mem_singleton.mp (Finset.mem_product.mp hi).2])
    (fun i hi => (mem_insert_one' hP hs' (Finset.mem_product.mp hi).1).2.2)
    (fun i hi => by rw [Finset.mem_singleton.mp (Finset.mem_product.mp hi).2, one_pow])
    (fun i hi k hk => by
      rw [Finset.mem_singleton.mp (Finset.mem_product.mp hk).2, mul_one, pow_one]
      exact (mem_insert_one' hP hs' (Finset.mem_product.mp hi).1).2.1)
  rwa [Finset.card_product, Finset.card_singleton, mul_one,
    Finset.card_insert_of_notMem (one_notMem_of_primes' fun u hu => (hs u hu).1)] at hc

/-- Signed layer two: a finite set `s` of odd primes below the prime `P` with
`u ^ (2 m) ≡ 1 (mod P ^ 2)`, where `P ∤ 2 m`, has `#s ^ 2 + #s + 1 ≤ m`. -/
theorem sq_add_add_one_le_of_signed_primes {P m : ℕ} (hP : P.Prime) (hPm : ¬ P ∣ 2 * m)
    (s : Finset ℕ) (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ 2]) :
    #s ^ 2 + #s + 1 ≤ m := by
  classical
  set s' := insert 1 s with hs'def
  have hsp : ∀ u ∈ s, u.Prime := fun u hu => (hs u hu).1
  have h1s : ((1 : ℕ), (1 : ℕ)) ∉ s'.offDiag := by
    simp [Finset.mem_offDiag]
  have hmem : ∀ x ∈ insert (1, 1) s'.offDiag,
      x.1 ∈ s' ∧ x.2 ∈ s' ∧ Nat.Coprime x.1 x.2 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, Nat.coprime_one_left _⟩
    · obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hx
      exact ⟨ha, hb, coprime_of_mem_insert_one' hsp ha hb hab⟩
  have hc := card_le_of_signed_reduced_pairs hP hPm (by norm_num) (insert (1, 1) s'.offDiag)
    Prod.fst Prod.snd (injOn_pair' _)
    (fun i hi => (hmem i hi).2.2)
    (fun i hi => (mem_insert_one' hP hs (hmem i hi).1).1)
    (fun i hi => (mem_insert_one' hP hs (hmem i hi).2.1).1)
    (fun i hi => (mem_insert_one' hP hs (hmem i hi).1).2.2)
    (fun i hi => (mem_insert_one' hP hs (hmem i hi).2.1).2.2)
    (fun i hi k hk => by
      rw [sq]
      exact Nat.mul_lt_mul'' (mem_insert_one' hP hs (hmem i hi).1).2.1
        (mem_insert_one' hP hs (hmem k hk).2.1).2.1)
  rw [Finset.card_insert_of_notMem h1s, Finset.offDiag_card, hs'def,
    Finset.card_insert_of_notMem (one_notMem_of_primes' hsp)] at hc
  have e : (#s + 1) * (#s + 1) - (#s + 1) = #s ^ 2 + #s := by
    rw [Nat.sub_eq_of_eq_add]
    ring
  omega

/-- The twelve exponent vectors `(a, b, c, e)` of the reduced pairs
`(u ^ a * v ^ b, u ^ c * v ^ e)` used in signed layer three. -/
private def cubeVectors' : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {(0, 0, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (0, 0, 2, 0), (0, 0, 1, 1), (0, 0, 0, 2),
   (1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 0, 2), (0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 2, 0)}

private theorem cubeVectors'_card : #cubeVectors' = 12 := by decide

private theorem cubeVectors'_prop : ∀ x ∈ cubeVectors', x.1 + x.2.1 ≤ 1 ∧
    x.2.2.1 + x.2.2.2 ≤ 2 ∧ x.1 * x.2.2.1 = 0 ∧ x.2.1 * x.2.2.2 = 0 := by decide

private theorem factorization_pow_mul_pow' {u v : ℕ} (hu : u.Prime) (hv : v.Prime)
    (huv : u ≠ v) (a b : ℕ) :
    (u ^ a * v ^ b).factorization u = a ∧ (u ^ a * v ^ b).factorization v = b := by
  rw [Nat.factorization_mul (pow_ne_zero _ hu.ne_zero) (pow_ne_zero _ hv.ne_zero),
    Nat.factorization_pow, Nat.factorization_pow, hu.factorization, hv.factorization]
  simp [huv, huv.symm]

private theorem coprime_pow_mul_pow' {u v : ℕ} (hu : u.Prime) (hv : v.Prime) (huv : u ≠ v)
    {a b c e : ℕ} (h1 : a * c = 0) (h2 : b * e = 0) :
    Nat.Coprime (u ^ a * v ^ b) (u ^ c * v ^ e) := by
  have h : Nat.Coprime u v := (Nat.coprime_primes hu hv).mpr huv
  refine Nat.coprime_mul_iff_left.mpr ⟨Nat.Coprime.mul_right ?_ (h.pow _ _),
    Nat.Coprime.mul_right (h.symm.pow _ _) ?_⟩
  · rcases Nat.mul_eq_zero.mp h1 with h0 | h0 <;> simp [h0]
  · rcases Nat.mul_eq_zero.mp h2 with h0 | h0 <;> simp [h0]

private theorem pow_mul_pow_le' {u v n : ℕ} (hu : u ≤ n) (hv : v ≤ n) (a b : ℕ) :
    u ^ a * v ^ b ≤ n ^ (a + b) := by
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hu a) (Nat.pow_le_pow_left hv b)

private theorem pow_mul_pow_odd {u v : ℕ} (hu : u % 2 = 1) (hv : v % 2 = 1) (a b : ℕ) :
    u ^ a * v ^ b % 2 = 1 :=
  Nat.odd_iff.mp ((Nat.odd_iff.mpr hu).pow.mul (Nat.odd_iff.mpr hv).pow)

/-- Signed layer three: if `P ∤ 2 m` and `m ≤ 11`, at most one odd prime `u < P` has
`u ^ (2 m) ≡ 1 (mod P ^ 3)`. Two such primes `u ≠ v` give twelve reduced pairs: numerators
`1, u, v` and denominators of at most two factors. -/
theorem card_le_one_of_signed_primes_cube {P m : ℕ} (hP : P.Prime) (hPm : ¬ P ∣ 2 * m)
    (hm : m ≤ 11) (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ 3]) : #s ≤ 1 := by
  by_contra hc
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < #s by omega)
  obtain ⟨hup, hu2, huP, hud⟩ := hs u hu
  obtain ⟨hvp, hv2, hvP, hvd⟩ := hs v hv
  let A : ℕ × ℕ × ℕ × ℕ → ℕ := fun x => u ^ x.1 * v ^ x.2.1
  let B : ℕ × ℕ × ℕ × ℕ → ℕ := fun x => u ^ x.2.2.1 * v ^ x.2.2.2
  have hpow : ∀ a b : ℕ, (u ^ a * v ^ b) ^ (2 * m) ≡ 1 [MOD P ^ 3] := by
    intro a b
    have e : (u ^ a * v ^ b) ^ (2 * m) = (u ^ (2 * m)) ^ a * (v ^ (2 * m)) ^ b := by ring
    rw [e]
    simpa using (hud.pow a).mul (hvd.pow b)
  have hle : ∀ a b : ℕ, u ^ a * v ^ b ≤ (P - 1) ^ (a + b) :=
    pow_mul_pow_le' (by omega) (by omega)
  have hc12 := card_le_of_signed_reduced_pairs hP hPm (by norm_num) cubeVectors' A B
    (by
      intro x _ y _ hxy
      simp only [A, B, Prod.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      have f1 := factorization_pow_mul_pow' hup hvp huv x.1 x.2.1
      have f2 := factorization_pow_mul_pow' hup hvp huv x.2.2.1 x.2.2.2
      rw [h1] at f1
      rw [h2] at f2
      have g1 := factorization_pow_mul_pow' hup hvp huv y.1 y.2.1
      have g2 := factorization_pow_mul_pow' hup hvp huv y.2.2.1 y.2.2.2
      ext <;> omega)
    (fun x hx => coprime_pow_mul_pow' hup hvp huv (cubeVectors'_prop x hx).2.2.1
      (cubeVectors'_prop x hx).2.2.2)
    (fun x _ => pow_mul_pow_odd hu2 hv2 _ _) (fun x _ => pow_mul_pow_odd hu2 hv2 _ _)
    (fun x _ => hpow _ _) (fun x _ => hpow _ _)
    (by
      intro x hx y hy
      have hx' := cubeVectors'_prop x hx
      have hy' := cubeVectors'_prop y hy
      have hP1 : 1 ≤ P - 1 := by have := hup.two_le; omega
      calc A x * B y ≤ (P - 1) ^ (x.1 + x.2.1) * (P - 1) ^ (y.2.2.1 + y.2.2.2) :=
            Nat.mul_le_mul (hle _ _) (hle _ _)
        _ = (P - 1) ^ (x.1 + x.2.1 + (y.2.2.1 + y.2.2.2)) := (pow_add _ _ _).symm
        _ ≤ (P - 1) ^ 3 := Nat.pow_le_pow_right hP1 (by omega)
        _ < P ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num))
  rw [cubeVectors'_card] at hc12
  omega

/-! ## The layer capacity -/

/-- The largest `s` with `s ^ 2 + s + 1 ≤ m` (and `0` if there is none), computed as one less
than the number of `s < m` with `s ^ 2 + s + 1 ≤ m`. -/
def sqCap (m : ℕ) : ℕ := #((Finset.range m).filter (fun s => s ^ 2 + s + 1 ≤ m)) - 1

/-- Every `s` with `s ^ 2 + s + 1 ≤ m` is at most `sqCap m`. -/
theorem le_sqCap {m s : ℕ} (h : s ^ 2 + s + 1 ≤ m) : s ≤ sqCap m := by
  have hsub : Finset.range (s + 1) ⊆ (Finset.range m).filter (fun s => s ^ 2 + s + 1 ≤ m) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have : i ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by nlinarith), by omega⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  unfold sqCap
  omega

/-- The bound on the number of senders of weight at least `j`: `m - 1` at `j = 1`, `sqCap m`
at `j = 2` (and at every `j ≥ 2` when `m > 11`), and `1` at `j ≥ 3` when `m ≤ 11`. -/
def signedLayerCap (m j : ℕ) : ℕ :=
  if j = 1 then m - 1 else if j = 2 ∨ 11 < m then sqCap m else 1

/-- The signed capacity: `∑ j ∈ [1, φ(m) - 1], signedLayerCap m j`. -/
def signedCap (m : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 (m.totient - 1), signedLayerCap m j

/-- The value `signedCap 5 = 6`. -/
theorem signedCap_five : signedCap 5 = 6 := by decide
/-- The value `signedCap 7 = 11`. -/
theorem signedCap_seven : signedCap 7 = 11 := by decide
/-- The value `signedCap 9 = 13`. -/
theorem signedCap_nine : signedCap 9 = 13 := by decide
/-- The value `signedCap 11 = 19`. -/
theorem signedCap_eleven : signedCap 11 = 19 := by decide

/-! ## Senders into the largest prime factor -/

variable {N : ℕ}

private theorem layer_cake' {f n : ℕ} (h : f ≤ n) :
    f = ∑ j ∈ Finset.Icc 1 n, if j ≤ f then 1 else 0 := by
  rw [← Finset.card_filter]
  have : (Finset.Icc 1 n).filter (fun j => j ≤ f) = Finset.Icc 1 f := by
    ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]
  omega

private theorem sum_senders (h : OddPerfect N) {P : ℕ} (hP : P ∈ N.primeFactors) :
    N.factorization P = ∑ p ∈ (N.primeFactors.erase P).filter
      (fun p => P ∣ σ 1 (p ^ N.factorization p)), padicValNat P (σ 1 (p ^ N.factorization p)) := by
  have hP2 : P ≠ 2 := by
    have := Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hP))
    omega
  rw [factorization_eq_sum_erase h.perfect (Nat.prime_of_mem_primeFactors hP) hP2,
    Finset.sum_filter_of_ne]
  intro p _ hne
  by_contra hd
  exact hne (by rw [Nat.padicValNat_def]; exact padicValNat.eq_zero_of_not_dvd hd)

/-- A sender `u` into the largest prime factor `P` with `P - 1 = 2 ^ a · m`, `m` odd: `u` is an
odd prime below `P`, its weight is at most `φ(m) - 1`, and `u ^ (2 m) ≡ 1 (mod P ^ j)` for every
`j` up to its weight. -/
private theorem sender_signed (h : OddPerfect N) {P a m : ℕ} (hP : P ∈ N.primeFactors)
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
    have hdvd : P ^ j ∣ u ^ orderOf (u : ZMod P) - 1 := (pow_dvd_pow P hj).trans
      (by rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _)
    have hmod : u ^ orderOf (u : ZMod P) ≡ 1 [MOD P ^ j] := ((Nat.modEq_iff_dvd' hpt).mpr hdvd).symm
    obtain ⟨k, hk⟩ := ht2m
    rw [hk, pow_mul]
    simpa using hmod.pow k

/-- Signed capacity of the largest prime factor. Let `P` be the largest prime factor of an odd
perfect number `N` and `P - 1 = 2 ^ a · m` with `m` odd. Then `v_P(N) ≤ signedCap m`, where the
senders of weight at least `j` number at most `signedLayerCap m j`. Unconditional; it gives no
contradiction. -/
theorem factorization_largest_le_signedCap (h : OddPerfect N) {P a m : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * m) (hmo : Odd m) : N.factorization P ≤ signedCap m := by
  classical
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hPodd : P % 2 = 1 := Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hP))
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
      have := hPp.two_le
      omega
    · have := Nat.le_of_dvd hmpos h2
      omega
  rw [sum_senders h hP]
  set S := (N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p)) with hS
  set w : ℕ → ℕ := fun u => padicValNat P (σ 1 (u ^ N.factorization u)) with hwdef
  have hdat : ∀ u ∈ S, u.Prime ∧ u % 2 = 1 ∧ u < P ∧ w u ≤ m.totient - 1 ∧
      ∀ j, j ≤ w u → u ^ (2 * m) ≡ 1 [MOD P ^ j] := by
    intro u hu
    rw [hS, Finset.mem_filter, Finset.mem_erase] at hu
    exact sender_signed h hP hmax hm hmo hu.1.2 hu.1.1 hu.2
  have hlayer : ∀ j, ∀ u ∈ S.filter (fun u => j ≤ w u),
      u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ j] := by
    intro j u hu
    obtain ⟨huS, hju⟩ := Finset.mem_filter.mp hu
    obtain ⟨h1, h2, h3, -, h5⟩ := hdat u huS
    exact ⟨h1, h2, h3, h5 j hju⟩
  have hweak : ∀ j, 2 ≤ j → ∀ u ∈ S.filter (fun u => j ≤ w u),
      u.Prime ∧ u % 2 = 1 ∧ u < P ∧ u ^ (2 * m) ≡ 1 [MOD P ^ 2] := by
    intro j hj u hu
    obtain ⟨h1, h2, h3, h4⟩ := hlayer j u hu
    exact ⟨h1, h2, h3, h4.of_dvd (Nat.pow_dvd_pow P hj)⟩
  calc ∑ u ∈ S, w u
      = ∑ u ∈ S, ∑ j ∈ Finset.Icc 1 (m.totient - 1), (if j ≤ w u then 1 else 0) :=
        Finset.sum_congr rfl fun u hu => layer_cake' (hdat u hu).2.2.2.1
    _ = ∑ j ∈ Finset.Icc 1 (m.totient - 1), #(S.filter (fun u => j ≤ w u)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
    _ ≤ signedCap m := by
        unfold signedCap
        refine Finset.sum_le_sum fun j hj => ?_
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        unfold signedLayerCap
        split_ifs with ha hb
        · subst ha
          have := card_add_one_le_of_signed_primes hPp hPm _ fun u hu => by
            have h := hlayer 1 u hu
            rwa [pow_one] at h
          omega
        · exact le_sqCap (sq_add_add_one_le_of_signed_primes hPp hPm _
            (hweak j (by omega)))
        · push Not at hb
          exact card_le_one_of_signed_primes_cube hPp hPm hb.2 _ fun u hu => by
            obtain ⟨a, b, c, e⟩ := hlayer j u hu
            exact ⟨a, b, c, e.of_dvd (Nat.pow_dvd_pow P (by omega))⟩

/-- If the odd part of `P - 1` is `5`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 6`. -/
theorem factorization_largest_le_six_of_odd_part_five (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 5) : N.factorization P ≤ 6 :=
  signedCap_five ▸ factorization_largest_le_signedCap h hP hmax hm (by decide)

/-- If the odd part of `P - 1` is `7`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 11`. -/
theorem factorization_largest_le_eleven_of_odd_part_seven (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 7) : N.factorization P ≤ 11 :=
  signedCap_seven ▸ factorization_largest_le_signedCap h hP hmax hm (by decide)

/-- If the odd part of `P - 1` is `9`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 13`. -/
theorem factorization_largest_le_thirteen_of_odd_part_nine (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 9) : N.factorization P ≤ 13 :=
  signedCap_nine ▸ factorization_largest_le_signedCap h hP hmax hm (by decide)

/-- If the odd part of `P - 1` is `11`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 19`. -/
theorem factorization_largest_le_nineteen_of_odd_part_eleven (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 11) : N.factorization P ≤ 19 :=
  signedCap_eleven ▸ factorization_largest_le_signedCap h hP hmax hm (by decide)

end OddPerfect

#print axioms OddPerfect.eq_of_sq_modEq_of_pow_two_mul_modEq_one
#print axioms OddPerfect.card_le_of_signed_reduced_pairs
#print axioms OddPerfect.card_add_one_le_of_signed_primes
#print axioms OddPerfect.sq_add_add_one_le_of_signed_primes
#print axioms OddPerfect.card_le_one_of_signed_primes_cube
#print axioms OddPerfect.le_sqCap
#print axioms OddPerfect.signedCap_five
#print axioms OddPerfect.signedCap_seven
#print axioms OddPerfect.signedCap_nine
#print axioms OddPerfect.signedCap_eleven
#print axioms OddPerfect.factorization_largest_le_signedCap
#print axioms OddPerfect.factorization_largest_le_six_of_odd_part_five
#print axioms OddPerfect.factorization_largest_le_eleven_of_odd_part_seven
#print axioms OddPerfect.factorization_largest_le_thirteen_of_odd_part_nine
#print axioms OddPerfect.factorization_largest_le_nineteen_of_odd_part_eleven
