import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Capacity of the largest prime for prime indices

Let `P` be a prime and `l ≠ P` an odd prime. For a finite set `U` of integers `u` with
`1 < u < P` this file proves

    ∑ u ∈ U, v_P(∑ i < l, u ^ i) ≤ primeIndexCap l = ∑ j ∈ [1, l - 2], (l - 1) / j

(`sum_factorization_geom_sum_le_primeIndexCap`). The cases `l = 3` and `l = 5` were proved by
hand in `OddPerfect.LargestPrimeCap`; here one argument covers every odd prime index. No
novelty is claimed; whether the bound is in the literature was not verified. The argument needs the index `l`
to be prime (the residues are then in a group of prime order); composite indices need another
argument and are not treated.

* `mul_card_le_of_no_short_prod`: a zero sum lemma in multiplicative form. In a commutative
  group of exponent dividing the prime `l` and of order at most `l`, a set `A` such that no
  product of `1` to `j` elements of `A` (repetition allowed) is `1` has `j * #A ≤ l - 1`. The
  proof iterates the theorem of Cauchy and Davenport (`cauchy_davenport_minOrder_mul`).
* `prod_not_modEq_one_of_dvd_geom_sum`: the product lemma. A nonempty list of at most `j`
  integers `u` with `1 < u < P` and `P ^ j ∣ ∑ i < l, u ^ i` has product not `1` modulo `P`,
  when `P ∤ l`.
* `sum_factorization_geom_sum_le_primeIndexCap`: the capacity bound.
-/

open Finset
open scoped Pointwise

namespace OddPerfect

/-! ## Step 1: the zero sum lemma -/

private theorem cauchy_davenport_of_pow_eq_one {G : Type*} [Group G] [DecidableEq G] {l : ℕ}
    (hl : l.Prime) (hpow : ∀ g : G, g ^ l = 1) {s t : Finset G} (hs : s.Nonempty)
    (ht : t.Nonempty) : min l (#s + #t - 1) ≤ #(s * t) := by
  have : Fact l.Prime := ⟨hl⟩
  have hmin : (l : ℕ∞) ≤ Monoid.minOrder G :=
    Monoid.le_minOrder.2 fun a ha _ => by rw [orderOf_eq_prime (hpow a) ha]
  have h1 := cauchy_davenport_minOrder_mul hs ht
  rcases le_total l (#s + #t - 1) with hc | hc
  · rw [min_eq_left hc]
    have : (l : ℕ∞) ≤ ((#(s * t) : ℕ) : ℕ∞) := (le_min hmin (by exact_mod_cast hc)).trans h1
    exact_mod_cast this
  · rw [min_eq_right hc]
    have hc' : ((#s + #t - 1 : ℕ) : ℕ∞) ≤ l := by exact_mod_cast hc
    have : ((#s + #t - 1 : ℕ) : ℕ∞) ≤ ((#(s * t) : ℕ) : ℕ∞) :=
      (le_min (hc'.trans hmin) le_rfl).trans h1
    exact_mod_cast this

/-- Zero sum lemma, multiplicative and indexed form. Let `G` be a finite commutative group with
`g ^ l = 1` for every `g`, where `l` is prime, and with at most `l` elements. Let `φ` be
injective on a finite set `s`. If no product `∏ φ (i_k)` of `1` to `j` indices from `s`
(repetition allowed) is `1`, then `j * #s ≤ l - 1`. -/
theorem mul_card_le_of_no_short_prod {G ι : Type*} [CommGroup G] [Finite G] {l : ℕ}
    (hl : l.Prime) (hpow : ∀ g : G, g ^ l = 1) (hcard : Nat.card G ≤ l) (φ : ι → G)
    (s : Finset ι) (hinj : Set.InjOn φ s) (j : ℕ)
    (hprod : ∀ L : List ι, L ≠ [] → L.length ≤ j → (∀ i ∈ L, i ∈ s) → (L.map φ).prod ≠ 1) :
    j * #s ≤ l - 1 := by
  classical
  obtain _ | k := j
  · simp
  set A := s.image φ with hAdef
  have hA1 : (1 : G) ∉ A := by
    intro h1
    obtain ⟨i, hi, hφ⟩ := Finset.mem_image.mp h1
    exact hprod [i] (by simp) (by simp) (by simpa using hi) (by simpa using hφ)
  have hAcard : #A = #s := Finset.card_image_of_injOn hinj
  set B := insert 1 A with hBdef
  have hBcard : #B = #s + 1 := by rw [Finset.card_insert_of_notMem hA1, hAcard]
  have hgrow : ∀ m : ℕ, ∃ S : Finset G, S.Nonempty ∧
      (∀ x ∈ S, ∃ L : List ι, L.length ≤ m ∧ (∀ i ∈ L, i ∈ s) ∧ (L.map φ).prod = x) ∧
      min l (m * #s + 1) ≤ #S := by
    intro m
    induction m with
    | zero =>
      refine ⟨{1}, by simp, fun x hx => ⟨[], by simp, by simp, ?_⟩, ?_⟩
      · rw [Finset.mem_singleton.mp hx]; simp
      simp
    | succ m ih =>
      obtain ⟨S, hS, hSmem, hScard⟩ := ih
      have hB : B.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
      refine ⟨S * B, hS.mul hB, ?_, ?_⟩
      · intro x hx
        obtain ⟨y, hy, b, hb, rfl⟩ := Finset.mem_mul.mp hx
        obtain ⟨L, hLm, hLs, hLp⟩ := hSmem y hy
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact ⟨L, by omega, hLs, by rw [hLp, mul_one]⟩
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
          refine ⟨L ++ [i], by simp; omega, fun a ha => ?_, by simp [hLp]⟩
          rcases List.mem_append.mp ha with ha | ha
          · exact hLs a ha
          · rw [List.mem_singleton.mp ha]; exact hi
      · have hcd := cauchy_davenport_of_pow_eq_one hl hpow hS hB
        rw [hBcard] at hcd
        rw [Nat.succ_mul]
        generalize m * #s = t at hScard ⊢
        simp only [min_le_iff] at hScard hcd ⊢
        omega
  obtain ⟨S, -, hSmem, hScard⟩ := hgrow k
  have hdisj : Disjoint S A⁻¹ := by
    rw [Finset.disjoint_left]
    intro x hx hxA
    obtain ⟨L, hLm, hLs, hLp⟩ := hSmem x hx
    obtain ⟨i, hi, hφ⟩ := Finset.mem_image.mp (Finset.mem_inv'.mp hxA)
    refine hprod (L ++ [i]) (by simp) (by simp; omega) (fun a ha => ?_) ?_
    · rcases List.mem_append.mp ha with ha | ha
      · exact hLs a ha
      · rw [List.mem_singleton.mp ha]; exact hi
    · simp [hLp, hφ]
  have := Fintype.ofFinite G
  have hU := Finset.card_le_univ (S ∪ A⁻¹)
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_inv, hAcard, ← Nat.card_eq_fintype_card]
    at hU
  rcases Nat.eq_zero_or_pos #s with h0 | hpos
  · rw [h0]; omega
  rw [Nat.succ_mul]
  generalize k * #s = t at hScard ⊢
  simp only [min_le_iff] at hScard
  omega

/-! ## Step 2: the product lemma -/

/-- Core of the product lemma: if `1 < v < P ^ j` and `v ^ l ≡ 1 (mod P ^ j)` for a prime
`P` not dividing `l`, then `v ≢ 1 (mod P)`. -/
theorem not_modEq_one_of_pow_modEq_one {P l j v : ℕ} (hP : P.Prime) (hPl : ¬ P ∣ l)
    (hv1 : 1 < v) (hvj : v < P ^ j) (hvl : v ^ l ≡ 1 [MOD P ^ j]) : ¬ v ≡ 1 [MOD P] := by
  intro hv
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  have hPw : P ∣ w := by
    have := (Nat.modEq_iff_dvd' (by omega)).mp hv.symm
    simpa using this
  have he := geom_sum_mul_add w l
  set g := ∑ i ∈ Finset.range l, (w + 1) ^ i with hg
  have hd : P ^ j ∣ g * w := by
    have := (Nat.modEq_iff_dvd' (by rw [← he]; omega)).mp hvl.symm
    rwa [← he, Nat.add_sub_cancel] at this
  have hcop : Nat.Coprime (P ^ j) g := by
    refine Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hP).mpr fun hgP => hPl ?_)
    have h0 := (ZMod.natCast_eq_zero_iff _ _).mpr hgP
    have hw0 := (ZMod.natCast_eq_zero_iff _ _).mpr hPw
    rw [hg] at h0
    push_cast at h0
    simp [hw0] at h0
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  have hw := hcop.dvd_of_dvd_mul_left hd
  have := Nat.le_of_dvd (by omega) hw
  omega

/-- If `M ∣ ∑ i < l, u ^ i` then `u ^ l ≡ 1 (mod M)`. -/
theorem pow_modEq_one_of_dvd_geom_sum {M l u : ℕ} (hu : 1 ≤ u)
    (h : M ∣ ∑ i ∈ Finset.range l, u ^ i) : u ^ l ≡ 1 [MOD M] := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
  have he := geom_sum_mul_add w l
  refine ((Nat.modEq_iff_dvd' (by rw [← he]; omega)).mpr ?_).symm
  rw [← he, Nat.add_sub_cancel]
  exact Dvd.dvd.mul_right h w

private theorem list_prod_bounds {P : ℕ} :
    ∀ L : List ℕ, (∀ u ∈ L, 1 < u ∧ u < P) → L ≠ [] → 1 < L.prod ∧ L.prod < P ^ L.length
  | [], _, h => absurd rfl h
  | [a], hl, _ => by
      have := hl a (by simp)
      simp only [List.prod_cons, List.prod_nil, mul_one, List.length_singleton, pow_one]
      exact this
  | a :: b :: t, hl, _ => by
      obtain ⟨h1, h2⟩ := list_prod_bounds (b :: t) (fun u hu => hl u (List.mem_cons_of_mem a hu))
        (List.cons_ne_nil b t)
      have ha := hl a List.mem_cons_self
      rw [List.prod_cons, List.length_cons, pow_succ]
      constructor
      · nlinarith
      · calc a * (b :: t).prod < P * P ^ (b :: t).length :=
            Nat.mul_lt_mul'' ha.2 h2
          _ = P ^ (b :: t).length * P := by ring

private theorem list_prod_pow_modEq {M l : ℕ} :
    ∀ L : List ℕ, (∀ u ∈ L, u ^ l ≡ 1 [MOD M]) → L.prod ^ l ≡ 1 [MOD M]
  | [], _ => by simp; rfl
  | a :: t, hl => by
      rw [List.prod_cons, mul_pow]
      have := (hl a List.mem_cons_self).mul
        (list_prod_pow_modEq t fun u hu => hl u (List.mem_cons_of_mem a hu))
      simpa using this

/-- The product lemma for every index `l` with `P ∤ l`. Let `P` be prime and let `L` be a
nonempty list of at most `j` integers `u` with `1 < u < P` and `P ^ j ∣ ∑ i < l, u ^ i`
(repetition allowed). Then the product of `L` is not `1` modulo `P`. -/
theorem prod_not_modEq_one_of_dvd_geom_sum {P l j : ℕ} (hP : P.Prime) (hPl : ¬ P ∣ l)
    {L : List ℕ} (hL : L ≠ []) (hLj : L.length ≤ j) (hlt : ∀ u ∈ L, 1 < u ∧ u < P)
    (hd : ∀ u ∈ L, P ^ j ∣ ∑ i ∈ Finset.range l, u ^ i) : ¬ L.prod ≡ 1 [MOD P] := by
  obtain ⟨h1, h2⟩ := list_prod_bounds L hlt hL
  exact not_modEq_one_of_pow_modEq_one hP hPl h1
    (lt_of_lt_of_le h2 (Nat.pow_le_pow_right hP.pos hLj))
    (list_prod_pow_modEq L fun u hu =>
      pow_modEq_one_of_dvd_geom_sum (hlt u hu).1.le (hd u hu))

/-! ## Step 3: the capacity -/

/-- The capacity `C l = ∑ j ∈ [1, l - 2], (l - 1) / j` of an odd prime index `l`. -/
def primeIndexCap (l : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 (l - 2), (l - 1) / j

/-- The value `primeIndexCap 3 = 2`. -/
theorem primeIndexCap_three : primeIndexCap 3 = 2 := by decide
/-- The value `primeIndexCap 5 = 7`. -/
theorem primeIndexCap_five : primeIndexCap 5 = 7 := by decide
/-- The value `primeIndexCap 7 = 13`. -/
theorem primeIndexCap_seven : primeIndexCap 7 = 13 := by decide
/-- The value `primeIndexCap 11 = 26`. -/
theorem primeIndexCap_eleven : primeIndexCap 11 = 26 := by decide

/-- For `u ≥ 1`: `∑ i < m + 3, u ^ i < (u + 1) ^ (m + 2)`. -/
theorem geom_sum_lt_succ_pow {u : ℕ} (hu : 1 ≤ u) :
    ∀ m : ℕ, ∑ i ∈ Finset.range (m + 3), u ^ i < (u + 1) ^ (m + 2)
  | 0 => by
      show ∑ i ∈ Finset.range 3, u ^ i < (u + 1) ^ 2
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
      nlinarith
  | m + 1 => by
      have ih := geom_sum_lt_succ_pow hu m
      have key : ∑ i ∈ Finset.range (m + 3), u ^ (i + 1) =
          (∑ i ∈ Finset.range (m + 3), u ^ i) * u := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => pow_succ u i
      rw [Finset.sum_range_succ', key, pow_zero, show m + 1 + 2 = m + 2 + 1 by omega,
        pow_succ (u + 1) (m + 2)]
      set X := ∑ i ∈ Finset.range (m + 3), u ^ i
      set Y := (u + 1) ^ (m + 2)
      nlinarith

private theorem layer_cake {f n : ℕ} (h : f ≤ n) :
    f = ∑ j ∈ Finset.Icc 1 n, if j ≤ f then 1 else 0 := by
  rw [← Finset.card_filter]
  have : (Finset.Icc 1 n).filter (fun j => j ≤ f) = Finset.Icc 1 f := by
    ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]
  omega

/-- The capacity bound. Let `P` be prime, `l ≠ P` an odd prime, and `U` a finite set of
integers `u` with `1 < u < P`. Then `∑ u ∈ U, v_P(∑ i < l, u ^ i) ≤ primeIndexCap l`. The
index `l` must be prime: composite indices are not covered by this argument. -/
theorem sum_factorization_geom_sum_le_primeIndexCap {P l : ℕ} (hP : P.Prime) (hl : l.Prime)
    (hl2 : l ≠ 2) (hlP : l ≠ P) (U : Finset ℕ) (hU : ∀ u ∈ U, 1 < u ∧ u < P) :
    ∑ u ∈ U, (∑ i ∈ Finset.range l, u ^ i).factorization P ≤ primeIndexCap l := by
  classical
  have : Fact P.Prime := ⟨hP⟩
  have : NeZero l := ⟨hl.ne_zero⟩
  have hPl : ¬ P ∣ l := fun h => hlP ((Nat.prime_dvd_prime_iff_eq hP hl).mp h).symm
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 3 := ⟨l - 3, by have := hl.two_le; omega⟩
  set f : ℕ → ℕ := fun u => (∑ i ∈ Finset.range (m + 3), u ^ i).factorization P with hfdef
  have hne : ∀ u, ∑ i ∈ Finset.range (m + 3), u ^ i ≠ 0 := by
    intro u; rw [Finset.sum_range_succ']; simp
  have hdvd : ∀ {u j : ℕ}, j ≤ f u → P ^ j ∣ ∑ i ∈ Finset.range (m + 3), u ^ i := fun h =>
    (hP.pow_dvd_iff_le_factorization (hne _)).mpr h
  have hfle : ∀ u ∈ U, f u ≤ m + 3 - 2 := by
    intro u hu
    obtain ⟨hu1, huP⟩ := hU u hu
    by_contra hc
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero (hne u)) (hdvd (show m + 2 ≤ f u by omega))
    have h2 := geom_sum_lt_succ_pow (u := u) (by omega) m
    have h3 : (u + 1) ^ (m + 2) ≤ P ^ (m + 2) := Nat.pow_le_pow_left (by omega) _
    omega
  calc ∑ u ∈ U, f u
      = ∑ u ∈ U, ∑ j ∈ Finset.Icc 1 (m + 3 - 2), (if j ≤ f u then 1 else 0) :=
        Finset.sum_congr rfl fun u hu => layer_cake (hfle u hu)
    _ = ∑ j ∈ Finset.Icc 1 (m + 3 - 2), #(U.filter (fun u => j ≤ f u)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
    _ ≤ primeIndexCap (m + 3) := by
        unfold primeIndexCap
        refine Finset.sum_le_sum fun j hj => ?_
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
        set s := U.filter (fun u => j ≤ f u) with hsdef
        have hmem : ∀ u ∈ s, u ∈ U ∧ P ^ j ∣ ∑ i ∈ Finset.range (m + 3), u ^ i := fun u hu =>
          ⟨(Finset.mem_filter.mp hu).1, hdvd (Finset.mem_filter.mp hu).2⟩
        have hroot : ∀ u ∈ s, (u : ZMod P) ^ (m + 3) = 1 := by
          intro u hu
          obtain ⟨huU, hd⟩ := hmem u hu
          have h1 := (pow_modEq_one_of_dvd_geom_sum (hU u huU).1.le hd).of_dvd
            (dvd_pow_self P (by omega))
          have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
          push_cast at this
          exact this
        let φ : ℕ → rootsOfUnity (m + 3) (ZMod P) := fun u =>
          if h : (u : ZMod P) ^ (m + 3) = 1 then rootsOfUnity.mkOfPowEq _ h else 1
        let ψ : rootsOfUnity (m + 3) (ZMod P) →* ZMod P :=
          (Units.coeHom (ZMod P)).comp (Subgroup.subtype _)
        have hψφ : ∀ u ∈ s, ψ (φ u) = (u : ZMod P) := by
          intro u hu
          simp only [φ, ψ, dif_pos (hroot u hu), MonoidHom.coe_comp, Function.comp_apply,
            Subgroup.coe_subtype, Units.coeHom_apply, rootsOfUnity.coe_mkOfPowEq]
        have hinj : Set.InjOn φ s := by
          intro a ha b hb hab
          have h := congrArg ψ hab
          rw [hψφ a ha, hψφ b hb, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt
            (hU a (hmem a ha).1).2, Nat.mod_eq_of_lt (hU b (hmem b hb).1).2] at h
          exact h
        refine mul_card_le_of_no_short_prod hl (fun g => ?_)
          (card_rootsOfUnity (ZMod P) (m + 3)) φ s hinj j ?_
        · exact Subtype.ext (by
            rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
            exact (mem_rootsOfUnity _ _).mp g.2)
        · intro L hL hLj hLs h1
          refine prod_not_modEq_one_of_dvd_geom_sum hP hPl hL hLj
            (fun u hu => hU u (hmem u (hLs u hu)).1) (fun u hu => (hmem u (hLs u hu)).2) ?_
          have h2 := congrArg ψ h1
          rw [map_list_prod, List.map_map, map_one] at h2
          have h3 : L.map (⇑ψ ∘ φ) = L.map (fun u : ℕ => (u : ZMod P)) :=
            List.map_congr_left fun u hu => hψφ u (hLs u hu)
          rw [h3, ← Nat.cast_list_prod] at h2
          rw [← ZMod.natCast_eq_natCast_iff, h2, Nat.cast_one]

end OddPerfect

#print axioms OddPerfect.mul_card_le_of_no_short_prod
#print axioms OddPerfect.not_modEq_one_of_pow_modEq_one
#print axioms OddPerfect.pow_modEq_one_of_dvd_geom_sum
#print axioms OddPerfect.prod_not_modEq_one_of_dvd_geom_sum
#print axioms OddPerfect.primeIndexCap_three
#print axioms OddPerfect.primeIndexCap_five
#print axioms OddPerfect.primeIndexCap_seven
#print axioms OddPerfect.primeIndexCap_eleven
#print axioms OddPerfect.geom_sum_lt_succ_pow
#print axioms OddPerfect.sum_factorization_geom_sum_le_primeIndexCap
