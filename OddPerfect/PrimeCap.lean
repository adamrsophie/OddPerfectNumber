import OddPerfect.LargestPrimeCapGen

/-!
# Capacity of the largest prime for prime senders, by reduced fractions

Restricted result; no novelty is claimed, and whether it is in the literature was not verified.

Let `P` be a prime, `d` an integer with `P ∤ d`, and `j ≥ 1`. The capacity bound of
`OddPerfect.LargestPrimeCapGen` counts integers `1 < u < P` with `P ^ j ∣ ∑ i < l, u ^ i`. When
the senders `u` are distinct primes the bound improves, because quotients of products of
senders can be compared as well.

* `eq_of_modEq_of_pow_modEq`: reduction from `P ^ j` to `P` is injective on integers below
  `P ^ j`, prime to `P`, with equal `d`-th powers modulo `P ^ j`.
* `card_le_of_reduced_pairs`: the injection lemma. Let `(A_i, B_i)` be distinct pairs of
  coprime positive integers whose `d`-th powers are `1` modulo `P ^ j`, with every product
  `A_i * B_k` below `P ^ j`. Then the residues `A_i / B_i` modulo `P` are distinct roots of
  `x ^ d = 1`, so there are at most `d` pairs.
* Layers: for a finite set `s` of primes below `P` with `u ^ d ≡ 1 (mod P ^ j)`:
  `#s + 1 ≤ d` for `j = 1` (`card_add_one_le_of_primes`), `#s ^ 2 + #s + 1 ≤ d` for `j = 2`
  (`sq_add_add_one_le_of_primes`), and `#s ≤ 1` for `j = 3` when `d ≤ 11`
  (`card_le_one_of_primes_cube`, by twelve reduced pairs built from two senders).
* `sum_factorization_geom_sum_le_primeSenderCap`: for `3 ≤ l ≤ 11` with `P ∤ l` and a finite
  set `U` of primes below `P`, `∑ u ∈ U, v_P(∑ i < l, u ^ i) ≤ primeSenderCap l`, with the
  values `2, 6, 11, 19` at `l = 3, 5, 7, 11` (compare `primeIndexCap`: `2, 7, 13, 26`).
-/

open Finset Polynomial

namespace OddPerfect

/-! ## The injection lemma -/

/-- Lifting lemma. Let `P` be prime with `P ∤ d`, and let `X, Y < P ^ j` with `P ∤ X`,
`X ≡ Y (mod P)` and `X ^ d ≡ Y ^ d (mod P ^ j)`. Then `X = Y`. -/
theorem eq_of_modEq_of_pow_modEq {P d j X Y : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d)
    (hX : X < P ^ j) (hY : Y < P ^ j) (hPX : ¬ P ∣ X) (hXY : X ≡ Y [MOD P])
    (hpow : X ^ d ≡ Y ^ d [MOD P ^ j]) : X = Y := by
  have : Fact P.Prime := ⟨hP⟩
  refine Nat.ModEq.eq_of_lt_of_lt ?_ hX hY
  rw [Nat.modEq_iff_dvd] at hpow ⊢
  have hfac := geom_sum₂_mul (Y : ℤ) (X : ℤ) d
  set S : ℤ := ∑ i ∈ range d, (Y : ℤ) ^ i * (X : ℤ) ^ (d - 1 - i) with hSdef
  have hS : ¬ (P : ℤ) ∣ S := by
    intro h
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd S P).mpr h
    have hxy : (Y : ZMod P) = (X : ZMod P) :=
      ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hXY).symm
    rw [hSdef] at h0
    push_cast at h0
    rw [hxy] at h0
    have hsum : ∑ i ∈ range d, (X : ZMod P) ^ i * (X : ZMod P) ^ (d - 1 - i) =
        (d : ZMod P) * (X : ZMod P) ^ (d - 1) := by
      rw [Finset.sum_congr rfl (g := fun _ => (X : ZMod P) ^ (d - 1)), sum_const, card_range,
        nsmul_eq_mul]
      intro i hi
      rw [← pow_add]
      congr 1
      have := mem_range.mp hi
      omega
    rw [hsum] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hPd ((ZMod.natCast_eq_zero_iff _ _).mp h1)
    · exact hPX ((ZMod.natCast_eq_zero_iff _ _).mp (by
        by_contra hx0
        exact pow_ne_zero _ hx0 h1))
  have hPj : IsCoprime ((P : ℤ) ^ j) S :=
    (((Nat.prime_iff_prime_int.mp hP).coprime_iff_not_dvd).mpr hS).pow_left
  push_cast at hpow ⊢
  rw [← hfac] at hpow
  exact hPj.dvd_of_dvd_mul_left hpow

/-- Unique factorization for coprime pairs: `a * e = b * c` with `a` prime to `b`, `c` prime
to `e` and `0 < a` gives `a = c` and `b = e`. -/
theorem eq_of_mul_eq_mul_of_coprime {a b c e : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b)
    (hce : Nat.Coprime c e) (h : a * e = b * c) : a = c ∧ b = e := by
  have h1 : a ∣ c := hab.dvd_of_dvd_mul_left ⟨e, by rw [← h]⟩
  have h2 : c ∣ a := hce.dvd_of_dvd_mul_right ⟨b, by rw [h]; ring⟩
  have hac := Nat.dvd_antisymm h1 h2
  subst hac
  exact ⟨rfl, (Nat.eq_of_mul_eq_mul_left ha (by rw [h]; ring)).symm⟩

private theorem not_dvd_of_pow_modEq_one {P d j x : ℕ} (hP : P.Prime) (hd : 0 < d)
    (hj : 1 ≤ j) (hx : x ^ d ≡ 1 [MOD P ^ j]) : ¬ P ∣ x := by
  have : Fact P.Prime := ⟨hP⟩
  intro hPx
  have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (hx.of_dvd (dvd_pow_self P (by omega : j ≠ 0)))
  push_cast at h1
  rw [(ZMod.natCast_eq_zero_iff x P).mpr hPx, zero_pow hd.ne'] at h1
  exact zero_ne_one h1

/-- The injection lemma for reduced fractions. Let `P` be prime with `P ∤ d` and `j ≥ 1`. Let
`T` index distinct pairs `(A i, B i)` of coprime integers with `A i > 0`, with
`A i ^ d ≡ B i ^ d ≡ 1 (mod P ^ j)`, and with `A i * B k < P ^ j` for all `i, k ∈ T`. Then
`#T ≤ d`: the residues `A i / B i` modulo `P` are distinct `d`-th roots of unity. -/
theorem card_le_of_reduced_pairs {ι : Type*} {P d j : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d)
    (hj : 1 ≤ j) (T : Finset ι) (A B : ι → ℕ) (hinj : Set.InjOn (fun i => (A i, B i)) T)
    (hpos : ∀ i ∈ T, 0 < A i) (hcop : ∀ i ∈ T, Nat.Coprime (A i) (B i))
    (hA : ∀ i ∈ T, A i ^ d ≡ 1 [MOD P ^ j]) (hB : ∀ i ∈ T, B i ^ d ≡ 1 [MOD P ^ j])
    (hlt : ∀ i ∈ T, ∀ k ∈ T, A i * B k < P ^ j) : #T ≤ d := by
  classical
  have : Fact P.Prime := ⟨hP⟩
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => hPd (h ▸ dvd_zero P)
  have hBne : ∀ i ∈ T, (B i : ZMod P) ≠ 0 := fun i hi h0 =>
    not_dvd_of_pow_modEq_one hP hd0 hj (hB i hi) ((ZMod.natCast_eq_zero_iff _ _).mp h0)
  set φ : ι → ZMod P := fun i => (A i : ZMod P) / (B i : ZMod P) with hφ
  have hprod : ∀ i ∈ T, ∀ k ∈ T, (A i * B k) ^ d ≡ 1 [MOD P ^ j] := by
    intro i hi k hk
    rw [mul_pow]
    simpa using (hA i hi).mul (hB k hk)
  have hinjφ : Set.InjOn φ T := by
    intro i hi k hk h
    simp only [hφ] at h
    rw [div_eq_div_iff (hBne i hi) (hBne k hk)] at h
    have hXY : A i * B k ≡ A k * B i [MOD P] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      exact h
    have hX := eq_of_modEq_of_pow_modEq hP hPd (hlt i hi k hk) (hlt k hk i hi)
      (not_dvd_of_pow_modEq_one hP hd0 hj (hprod i hi k hk)) hXY
      ((hprod i hi k hk).trans (hprod k hk i hi).symm)
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul_of_coprime (hpos i hi) (hcop i hi) (hcop k hk)
      (by rw [hX, mul_comm])
    exact hinj hi hk (Prod.ext h1 h2)
  have hsub : T.image φ ⊆ (nthRoots d (1 : ZMod P)).toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_nthRoots hd0]
    have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((hA i hi).of_dvd
      (dvd_pow_self P (by omega : j ≠ 0)))
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((hB i hi).of_dvd
      (dvd_pow_self P (by omega : j ≠ 0)))
    push_cast at h1 h2
    simp only [hφ, div_pow, h1, h2, div_one]
  have c1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinjφ] at c1
  exact c1.trans ((Multiset.toFinset_card_le _).trans (card_nthRoots d (1 : ZMod P)))

/-! ## Layers of prime senders -/

private theorem mem_insert_one {P d j : ℕ} (hP : P.Prime) {s : Finset ℕ}
    (hs : ∀ u ∈ s, u.Prime ∧ u < P ∧ u ^ d ≡ 1 [MOD P ^ j]) {v : ℕ} (hv : v ∈ insert 1 s) :
    0 < v ∧ v < P ∧ v ^ d ≡ 1 [MOD P ^ j] := by
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact ⟨one_pos, hP.one_lt, by rw [one_pow]⟩
  · obtain ⟨h1, h2, h3⟩ := hs v hv
    exact ⟨h1.pos, h2, h3⟩

private theorem coprime_of_mem_insert_one {s : Finset ℕ} (hs : ∀ u ∈ s, u.Prime) {a b : ℕ}
    (ha : a ∈ insert 1 s) (hb : b ∈ insert 1 s) (hab : a ≠ b) : Nat.Coprime a b := by
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact Nat.coprime_one_left _
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact Nat.coprime_one_right _
  exact (Nat.coprime_primes (hs a ha) (hs b hb)).mpr hab

private theorem one_notMem_of_primes {s : Finset ℕ} (hs : ∀ u ∈ s, u.Prime) : 1 ∉ s :=
  fun h => Nat.not_prime_one (hs 1 h)

private theorem injOn_pair (T : Finset (ℕ × ℕ)) :
    Set.InjOn (fun i : ℕ × ℕ => (i.1, i.2)) T :=
  fun _ _ _ _ h => Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Layer one: a finite set `s` of primes below the prime `P` with `u ^ d ≡ 1 (mod P)`, where
`P ∤ d`, has `#s + 1 ≤ d` (pairs `(1, 1)` and `(u, 1)`). -/
theorem card_add_one_le_of_primes {P d : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d) (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u < P ∧ u ^ d ≡ 1 [MOD P]) : #s + 1 ≤ d := by
  have hs' : ∀ u ∈ s, u.Prime ∧ u < P ∧ u ^ d ≡ 1 [MOD P ^ 1] := by
    simpa only [pow_one] using hs
  have hc := card_le_of_reduced_pairs hP hPd le_rfl ((insert 1 s) ×ˢ {1}) Prod.fst Prod.snd
    (injOn_pair _)
    (fun i hi => (mem_insert_one hP hs' (Finset.mem_product.mp hi).1).1)
    (fun i hi => by rw [Finset.mem_singleton.mp (Finset.mem_product.mp hi).2]; exact
      Nat.coprime_one_right _)
    (fun i hi => (mem_insert_one hP hs' (Finset.mem_product.mp hi).1).2.2)
    (fun i hi => by rw [Finset.mem_singleton.mp (Finset.mem_product.mp hi).2, one_pow])
    (fun i hi k hk => by
      rw [Finset.mem_singleton.mp (Finset.mem_product.mp hk).2, mul_one, pow_one]
      exact (mem_insert_one hP hs' (Finset.mem_product.mp hi).1).2.1)
  rwa [Finset.card_product, Finset.card_singleton, mul_one,
    Finset.card_insert_of_notMem (one_notMem_of_primes fun u hu => (hs u hu).1)] at hc

/-- Layer two: a finite set `s` of primes below the prime `P` with `u ^ d ≡ 1 (mod P ^ 2)`,
where `P ∤ d`, has `#s ^ 2 + #s + 1 ≤ d` (pairs `(1, 1)`, `(u, 1)`, `(1, u)` and `(u, v)` with
`u ≠ v`). -/
theorem sq_add_add_one_le_of_primes {P d : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d) (s : Finset ℕ)
    (hs : ∀ u ∈ s, u.Prime ∧ u < P ∧ u ^ d ≡ 1 [MOD P ^ 2]) : #s ^ 2 + #s + 1 ≤ d := by
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
      exact ⟨ha, hb, coprime_of_mem_insert_one hsp ha hb hab⟩
  have hc := card_le_of_reduced_pairs hP hPd (by norm_num) (insert (1, 1) s'.offDiag)
    Prod.fst Prod.snd (injOn_pair _)
    (fun i hi => (mem_insert_one hP hs (hmem i hi).1).1)
    (fun i hi => (hmem i hi).2.2)
    (fun i hi => (mem_insert_one hP hs (hmem i hi).1).2.2)
    (fun i hi => (mem_insert_one hP hs (hmem i hi).2.1).2.2)
    (fun i hi k hk => by
      rw [sq]
      exact Nat.mul_lt_mul'' (mem_insert_one hP hs (hmem i hi).1).2.1
        (mem_insert_one hP hs (hmem k hk).2.1).2.1)
  rw [Finset.card_insert_of_notMem h1s, Finset.offDiag_card, hs'def,
    Finset.card_insert_of_notMem (one_notMem_of_primes hsp)] at hc
  have e : (#s + 1) * (#s + 1) - (#s + 1) = #s ^ 2 + #s := by
    rw [Nat.sub_eq_of_eq_add]
    ring
  omega

/-- The twelve exponent vectors `(a, b, c, e)` of the reduced pairs
`(u ^ a * v ^ b, u ^ c * v ^ e)` used in layer three. -/
private def cubeVectors : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {(0, 0, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (0, 0, 2, 0), (0, 0, 1, 1), (0, 0, 0, 2),
   (1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 0, 2), (0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 2, 0)}

private theorem cubeVectors_card : #cubeVectors = 12 := by decide

private theorem cubeVectors_prop : ∀ x ∈ cubeVectors, x.1 + x.2.1 ≤ 1 ∧
    x.2.2.1 + x.2.2.2 ≤ 2 ∧ x.1 * x.2.2.1 = 0 ∧ x.2.1 * x.2.2.2 = 0 := by decide

private theorem factorization_pow_mul_pow {u v : ℕ} (hu : u.Prime) (hv : v.Prime)
    (huv : u ≠ v) (a b : ℕ) :
    (u ^ a * v ^ b).factorization u = a ∧ (u ^ a * v ^ b).factorization v = b := by
  rw [Nat.factorization_mul (pow_ne_zero _ hu.ne_zero) (pow_ne_zero _ hv.ne_zero),
    Nat.factorization_pow, Nat.factorization_pow, hu.factorization, hv.factorization]
  simp [huv, huv.symm]

private theorem coprime_pow_mul_pow {u v : ℕ} (hu : u.Prime) (hv : v.Prime) (huv : u ≠ v)
    {a b c e : ℕ} (h1 : a * c = 0) (h2 : b * e = 0) :
    Nat.Coprime (u ^ a * v ^ b) (u ^ c * v ^ e) := by
  have h : Nat.Coprime u v := (Nat.coprime_primes hu hv).mpr huv
  refine Nat.coprime_mul_iff_left.mpr ⟨Nat.Coprime.mul_right ?_ (h.pow _ _),
    Nat.Coprime.mul_right (h.symm.pow _ _) ?_⟩
  · rcases Nat.mul_eq_zero.mp h1 with h0 | h0 <;> simp [h0]
  · rcases Nat.mul_eq_zero.mp h2 with h0 | h0 <;> simp [h0]

private theorem pow_mul_pow_le {u v m : ℕ} (hu : u ≤ m) (hv : v ≤ m) (a b : ℕ) :
    u ^ a * v ^ b ≤ m ^ (a + b) := by
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left hu a) (Nat.pow_le_pow_left hv b)

/-- Layer three: if `P ∤ d` and `d ≤ 11`, at most one prime `u < P` has
`u ^ d ≡ 1 (mod P ^ 3)`. Two such primes `u ≠ v` give twelve reduced pairs: numerators
`1, u, v` and denominators of at most two factors. -/
theorem card_le_one_of_primes_cube {P d : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d) (hd : d ≤ 11)
    (s : Finset ℕ) (hs : ∀ u ∈ s, u.Prime ∧ u < P ∧ u ^ d ≡ 1 [MOD P ^ 3]) : #s ≤ 1 := by
  by_contra hc
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (show 1 < #s by omega)
  obtain ⟨hup, huP, hud⟩ := hs u hu
  obtain ⟨hvp, hvP, hvd⟩ := hs v hv
  let A : ℕ × ℕ × ℕ × ℕ → ℕ := fun x => u ^ x.1 * v ^ x.2.1
  let B : ℕ × ℕ × ℕ × ℕ → ℕ := fun x => u ^ x.2.2.1 * v ^ x.2.2.2
  have hpow : ∀ a b : ℕ, (u ^ a * v ^ b) ^ d ≡ 1 [MOD P ^ 3] := by
    intro a b
    have e : (u ^ a * v ^ b) ^ d = (u ^ d) ^ a * (v ^ d) ^ b := by ring
    rw [e]
    simpa using (hud.pow a).mul (hvd.pow b)
  have hle : ∀ a b : ℕ, u ^ a * v ^ b ≤ (P - 1) ^ (a + b) :=
    pow_mul_pow_le (by omega) (by omega)
  have hc12 := card_le_of_reduced_pairs hP hPd (by norm_num) cubeVectors A B
    (by
      intro x _ y _ hxy
      simp only [A, B, Prod.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      have f1 := factorization_pow_mul_pow hup hvp huv x.1 x.2.1
      have f2 := factorization_pow_mul_pow hup hvp huv x.2.2.1 x.2.2.2
      rw [h1] at f1
      rw [h2] at f2
      have g1 := factorization_pow_mul_pow hup hvp huv y.1 y.2.1
      have g2 := factorization_pow_mul_pow hup hvp huv y.2.2.1 y.2.2.2
      ext <;> omega)
    (fun x _ => Nat.mul_pos (pow_pos hup.pos _) (pow_pos hvp.pos _))
    (fun x hx => coprime_pow_mul_pow hup hvp huv (cubeVectors_prop x hx).2.2.1
      (cubeVectors_prop x hx).2.2.2)
    (fun x _ => hpow _ _) (fun x _ => hpow _ _)
    (by
      intro x hx y hy
      have hx' := cubeVectors_prop x hx
      have hy' := cubeVectors_prop y hy
      have hP1 : 1 ≤ P - 1 := by have := hup.two_le; omega
      calc A x * B y ≤ (P - 1) ^ (x.1 + x.2.1) * (P - 1) ^ (y.2.2.1 + y.2.2.2) :=
            Nat.mul_le_mul (hle _ _) (hle _ _)
        _ = (P - 1) ^ (x.1 + x.2.1 + (y.2.2.1 + y.2.2.2)) := (pow_add _ _ _).symm
        _ ≤ (P - 1) ^ 3 := Nat.pow_le_pow_right hP1 (by omega)
        _ < P ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num))
  rw [cubeVectors_card] at hc12
  omega

/-! ## The capacity for prime senders -/

/-- The bound on the number of prime senders in layer `j` for the index `l`: `l - 1` for
`j = 1`, then `1` or `2` for `j = 2` (from `r ^ 2 + r + 1 ≤ l` with `l ≤ 11`), and `1` for
`j ≥ 3`. -/
def primeLayerCap (l j : ℕ) : ℕ :=
  if j = 1 then l - 1 else if j = 2 then (if l < 7 then 1 else 2) else 1

/-- The capacity for prime senders: `∑ j ∈ [1, l - 2], primeLayerCap l j`. -/
def primeSenderCap (l : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 (l - 2), primeLayerCap l j

/-- The value `primeSenderCap 3 = 2`. -/
theorem primeSenderCap_three : primeSenderCap 3 = 2 := by decide
/-- The value `primeSenderCap 5 = 6`. -/
theorem primeSenderCap_five : primeSenderCap 5 = 6 := by decide
/-- The value `primeSenderCap 7 = 11`. -/
theorem primeSenderCap_seven : primeSenderCap 7 = 11 := by decide
/-- The value `primeSenderCap 11 = 19`. -/
theorem primeSenderCap_eleven : primeSenderCap 11 = 19 := by decide

private theorem layer_cake {f n : ℕ} (h : f ≤ n) :
    f = ∑ j ∈ Finset.Icc 1 n, if j ≤ f then 1 else 0 := by
  rw [← Finset.card_filter]
  have : (Finset.Icc 1 n).filter (fun j => j ≤ f) = Finset.Icc 1 f := by
    ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]
  omega

/-- The capacity bound for prime senders. Let `P` be prime, `3 ≤ l ≤ 11` with `P ∤ l`, and `U`
a finite set of primes below `P`. Then `∑ u ∈ U, v_P(∑ i < l, u ^ i) ≤ primeSenderCap l`. -/
theorem sum_factorization_geom_sum_le_primeSenderCap {P l : ℕ} (hP : P.Prime)
    (hPl : ¬ P ∣ l) (hl3 : 3 ≤ l) (hl11 : l ≤ 11) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u.Prime ∧ u < P) :
    ∑ u ∈ U, (∑ i ∈ Finset.range l, u ^ i).factorization P ≤ primeSenderCap l := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 3 := ⟨l - 3, by omega⟩
  set f : ℕ → ℕ := fun u => (∑ i ∈ Finset.range (m + 3), u ^ i).factorization P with hfdef
  have hne : ∀ u, ∑ i ∈ Finset.range (m + 3), u ^ i ≠ 0 := by
    intro u; rw [Finset.sum_range_succ']; simp
  have hdvd : ∀ {u j : ℕ}, j ≤ f u → P ^ j ∣ ∑ i ∈ Finset.range (m + 3), u ^ i := fun h =>
    (hP.pow_dvd_iff_le_factorization (hne _)).mpr h
  have hfle : ∀ u ∈ U, f u ≤ m + 3 - 2 := by
    intro u hu
    obtain ⟨hup, huP⟩ := hU u hu
    have hu1 := hup.one_lt
    by_contra hc
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero (hne u)) (hdvd (show m + 2 ≤ f u by omega))
    have h2 := geom_sum_lt_succ_pow (u := u) (by omega) m
    have h3 : (u + 1) ^ (m + 2) ≤ P ^ (m + 2) := Nat.pow_le_pow_left (by omega) _
    omega
  have hlayer : ∀ j, ∀ u ∈ U.filter (fun u => j ≤ f u),
      u.Prime ∧ u < P ∧ u ^ (m + 3) ≡ 1 [MOD P ^ j] := by
    intro j u hu
    obtain ⟨huU, hju⟩ := Finset.mem_filter.mp hu
    obtain ⟨hup, huP⟩ := hU u huU
    exact ⟨hup, huP, pow_modEq_one_of_dvd_geom_sum hup.one_lt.le (hdvd hju)⟩
  have h7 : ∀ r : ℕ, 2 ≤ r → 7 ≤ r ^ 2 + r + 1 := fun r hr => by nlinarith
  have h13 : ∀ r : ℕ, 3 ≤ r → 13 ≤ r ^ 2 + r + 1 := fun r hr => by nlinarith
  calc ∑ u ∈ U, f u
      = ∑ u ∈ U, ∑ j ∈ Finset.Icc 1 (m + 3 - 2), (if j ≤ f u then 1 else 0) :=
        Finset.sum_congr rfl fun u hu => layer_cake (hfle u hu)
    _ = ∑ j ∈ Finset.Icc 1 (m + 3 - 2), #(U.filter (fun u => j ≤ f u)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
    _ ≤ primeSenderCap (m + 3) := by
        unfold primeSenderCap
        refine Finset.sum_le_sum fun j hj => ?_
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        unfold primeLayerCap
        split_ifs with ha hb hc
        · subst ha
          have := card_add_one_le_of_primes hP hPl _ fun u hu => by
            have h := hlayer 1 u hu
            rwa [pow_one] at h
          omega
        · subst hb
          have := sq_add_add_one_le_of_primes hP hPl _ (hlayer 2)
          rcases Nat.lt_or_ge #(U.filter (fun u => 2 ≤ f u)) 2 with h | h
          · omega
          · have := h7 _ h
            omega
        · subst hb
          have := sq_add_add_one_le_of_primes hP hPl _ (hlayer 2)
          rcases Nat.lt_or_ge #(U.filter (fun u => 2 ≤ f u)) 3 with h | h
          · omega
          · have := h13 _ h
            omega
        · have h3 : 3 ≤ j := by omega
          exact card_le_one_of_primes_cube hP hPl hl11 _ fun u hu => by
            obtain ⟨a, b, c⟩ := hlayer j u hu
            exact ⟨a, b, c.of_dvd (Nat.pow_dvd_pow P h3)⟩

private theorem not_dvd_of_prime_ne {P l : ℕ} (hP : P.Prime) (hl : l.Prime) (hlP : l ≠ P) :
    ¬ P ∣ l := fun h => hlP ((Nat.prime_dvd_prime_iff_eq hP hl).mp h).symm

/-- Index `3`: for a prime `P ≠ 3` and a finite set `U` of primes below `P`,
`∑ u ∈ U, v_P(1 + u + u ^ 2) ≤ 2`. -/
theorem sum_factorization_geom_sum_three_le_two_of_primes {P : ℕ} (hP : P.Prime) (hP3 : P ≠ 3)
    (U : Finset ℕ) (hU : ∀ u ∈ U, u.Prime ∧ u < P) :
    ∑ u ∈ U, (∑ i ∈ Finset.range 3, u ^ i).factorization P ≤ 2 := by
  have := sum_factorization_geom_sum_le_primeSenderCap hP
    (not_dvd_of_prime_ne hP Nat.prime_three hP3.symm) (by norm_num) (by norm_num) U hU
  rwa [primeSenderCap_three] at this

/-- Index `5`: for a prime `P ≠ 5` and a finite set `U` of primes below `P`,
`∑ u ∈ U, v_P(∑ i < 5, u ^ i) ≤ 6`. -/
theorem sum_factorization_geom_sum_five_le_six_of_primes {P : ℕ} (hP : P.Prime) (hP5 : P ≠ 5)
    (U : Finset ℕ) (hU : ∀ u ∈ U, u.Prime ∧ u < P) :
    ∑ u ∈ U, (∑ i ∈ Finset.range 5, u ^ i).factorization P ≤ 6 := by
  have := sum_factorization_geom_sum_le_primeSenderCap hP
    (not_dvd_of_prime_ne hP Nat.prime_five hP5.symm) (by norm_num) (by norm_num) U hU
  rwa [primeSenderCap_five] at this

/-- Index `7`: for a prime `P ≠ 7` and a finite set `U` of primes below `P`,
`∑ u ∈ U, v_P(∑ i < 7, u ^ i) ≤ 11`. -/
theorem sum_factorization_geom_sum_seven_le_eleven_of_primes {P : ℕ} (hP : P.Prime)
    (hP7 : P ≠ 7) (U : Finset ℕ) (hU : ∀ u ∈ U, u.Prime ∧ u < P) :
    ∑ u ∈ U, (∑ i ∈ Finset.range 7, u ^ i).factorization P ≤ 11 := by
  have := sum_factorization_geom_sum_le_primeSenderCap hP
    (not_dvd_of_prime_ne hP (by decide : Nat.Prime 7) hP7.symm) (by norm_num) (by norm_num) U hU
  rwa [primeSenderCap_seven] at this

/-- Index `11`: for a prime `P ≠ 11` and a finite set `U` of primes below `P`,
`∑ u ∈ U, v_P(∑ i < 11, u ^ i) ≤ 19`. -/
theorem sum_factorization_geom_sum_eleven_le_nineteen_of_primes {P : ℕ} (hP : P.Prime)
    (hP11 : P ≠ 11) (U : Finset ℕ) (hU : ∀ u ∈ U, u.Prime ∧ u < P) :
    ∑ u ∈ U, (∑ i ∈ Finset.range 11, u ^ i).factorization P ≤ 19 := by
  have := sum_factorization_geom_sum_le_primeSenderCap hP
    (not_dvd_of_prime_ne hP (by decide : Nat.Prime 11) hP11.symm) (by norm_num) (by norm_num) U hU
  rwa [primeSenderCap_eleven] at this

end OddPerfect

#print axioms OddPerfect.eq_of_modEq_of_pow_modEq
#print axioms OddPerfect.eq_of_mul_eq_mul_of_coprime
#print axioms OddPerfect.card_le_of_reduced_pairs
#print axioms OddPerfect.card_add_one_le_of_primes
#print axioms OddPerfect.sq_add_add_one_le_of_primes
#print axioms OddPerfect.card_le_one_of_primes_cube
#print axioms OddPerfect.primeSenderCap_three
#print axioms OddPerfect.primeSenderCap_five
#print axioms OddPerfect.primeSenderCap_seven
#print axioms OddPerfect.primeSenderCap_eleven
#print axioms OddPerfect.sum_factorization_geom_sum_le_primeSenderCap
#print axioms OddPerfect.sum_factorization_geom_sum_three_le_two_of_primes
#print axioms OddPerfect.sum_factorization_geom_sum_five_le_six_of_primes
#print axioms OddPerfect.sum_factorization_geom_sum_seven_le_eleven_of_primes
#print axioms OddPerfect.sum_factorization_geom_sum_eleven_le_nineteen_of_primes
