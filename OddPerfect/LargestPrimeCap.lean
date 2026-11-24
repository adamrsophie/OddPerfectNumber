import OddPerfect.Network
import OddPerfect.Phi3
import OddPerfect.SpecialPrime

/-!
# The exponent of the largest prime factor in a mixed family

Restricted family result; whether this is in the literature was not verified.

Let `N` be an odd perfect number with special prime `q` and largest prime factor `P ≠ q`.
Assume `e_q = 1` and that every other prime factor `p ∉ {q, P}` has `e_p = 2` or `e_p = 4`.
Then `e_P ≤ 8` (`factorization_largest_le_eight`). This bounds one exponent in a narrow
family; it does not bound the total excess of an odd perfect number in general.

The proof reads the ledger `e_P = Σ_p v_P(σ(p ^ e_p))`.

* The special row gives `v_P(q + 1) = 0`, since `q + 1` is even and at most `P`.
* Square rows: `sum_factorization_phi3_le_two`. For `u < P` the value `u ^ 2 + u + 1` is below
  `P ^ 2`, and `x ^ 2 + x + 1` has at most two roots modulo `P`, so the total is at most `2`.
* Fourth power rows: `sum_factorization_phi5_le_seven`. For `u < P` and `P ≠ 5` the total
  of `v_P(u ^ 4 + u ^ 3 + u ^ 2 + u + 1)` is at most `7`. Each weight is at most `3`; the
  residues of the sources are nontrivial fifth roots of unity; by the product lemma
  `prod_not_modEq_one_of_dvd_phi5` no product of at most `j` sources of weight at least `j`
  is `1` modulo `P`. So there are at most `4` sources of weight at least `1`, at most `2` of
  weight at least `2` (no inverse pairs) and at most `1` of weight at least `3`.
* So `e_P ≤ 9`, and `e_P` is even.
-/

open ArithmeticFunction Polynomial
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## The product lemma -/

/-- Core of the product lemma: if `1 < v < P ^ j` and `v ^ 5 ≡ 1 (mod P ^ j)` for a prime
`P ≠ 5`, then `v ≢ 1 (mod P)`. -/
theorem not_modEq_one_of_pow_five_modEq {P j v : ℕ} (hP : P.Prime) (hP5 : P ≠ 5)
    (hv1 : 1 < v) (hvj : v < P ^ j) (hv5 : v ^ 5 ≡ 1 [MOD P ^ j]) : ¬ v ≡ 1 [MOD P] := by
  intro hv
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
  have hPw : P ∣ w := by
    have := (Nat.modEq_iff_dvd' (by omega)).mp hv.symm
    simpa using this
  have he : (w + 1) ^ 5 = w * ((w + 1) ^ 4 + (w + 1) ^ 3 + (w + 1) ^ 2 + (w + 1) + 1) + 1 := by
    ring
  have hf : (w + 1) ^ 4 + (w + 1) ^ 3 + (w + 1) ^ 2 + (w + 1) + 1 =
      w * (w ^ 3 + 5 * w ^ 2 + 10 * w + 10) + 5 := by ring
  have hd : P ^ j ∣ w * ((w + 1) ^ 4 + (w + 1) ^ 3 + (w + 1) ^ 2 + (w + 1) + 1) := by
    have := (Nat.modEq_iff_dvd' (by rw [he]; omega)).mp hv5.symm
    rwa [he, Nat.add_sub_cancel] at this
  have hcop : Nat.Coprime (P ^ j)
      ((w + 1) ^ 4 + (w + 1) ^ 3 + (w + 1) ^ 2 + (w + 1) + 1) := by
    refine Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hP).mpr fun h5 => hP5 ?_)
    rw [hf] at h5
    have h5' : P ∣ 5 := (Nat.dvd_add_right (dvd_mul_of_dvd_left hPw _)).mp h5
    exact (Nat.prime_dvd_prime_iff_eq hP (by norm_num)).mp h5'
  have hw := hcop.dvd_of_dvd_mul_right hd
  have := Nat.le_of_dvd (by omega) hw
  omega

private theorem pow_five_modEq_one_of_dvd {M u : ℕ} (h : M ∣ u ^ 4 + u ^ 3 + u ^ 2 + u + 1) :
    u ^ 5 ≡ 1 [MOD M] := by
  obtain ⟨c, hc⟩ := h
  have hc' := congrArg (Nat.cast : ℕ → ℤ) hc
  push_cast at hc'
  rw [Nat.modEq_iff_dvd]
  push_cast
  exact ⟨-((u : ℤ) - 1) * c, by linear_combination (-((u : ℤ) - 1)) * hc'⟩

private theorem list_prod_bounds {P : ℕ} :
    ∀ l : List ℕ, (∀ u ∈ l, 1 < u ∧ u < P) → l ≠ [] → 1 < l.prod ∧ l.prod < P ^ l.length
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

private theorem list_prod_pow_five {M : ℕ} :
    ∀ l : List ℕ, (∀ u ∈ l, u ^ 5 ≡ 1 [MOD M]) → l.prod ^ 5 ≡ 1 [MOD M]
  | [], _ => by simp; rfl
  | a :: t, hl => by
      rw [List.prod_cons, mul_pow]
      have := (hl a List.mem_cons_self).mul
        (list_prod_pow_five t fun u hu => hl u (List.mem_cons_of_mem a hu))
      simpa using this

/-- The product lemma. Let `P ≠ 5` be prime and let `l` be a nonempty list of at most `j`
integers `u` with `1 < u < P` and `P ^ j ∣ u ^ 4 + u ^ 3 + u ^ 2 + u + 1` (repetitions
allowed). Then the product of `l` is not `1` modulo `P`. -/
theorem prod_not_modEq_one_of_dvd_phi5 {P j : ℕ} (hP : P.Prime) (hP5 : P ≠ 5) {l : List ℕ}
    (hl : l ≠ []) (hlj : l.length ≤ j) (hlt : ∀ u ∈ l, 1 < u ∧ u < P)
    (hd : ∀ u ∈ l, P ^ j ∣ u ^ 4 + u ^ 3 + u ^ 2 + u + 1) : ¬ l.prod ≡ 1 [MOD P] := by
  obtain ⟨h1, h2⟩ := list_prod_bounds l hlt hl
  exact not_modEq_one_of_pow_five_modEq hP hP5 h1
    (lt_of_lt_of_le h2 (Nat.pow_le_pow_right hP.pos hlj))
    (list_prod_pow_five l fun u hu => pow_five_modEq_one_of_dvd (hd u hu))

/-! ## Counting roots modulo a prime -/

section Field

variable {P : ℕ} [Fact P.Prime]

private theorem card_le_four (T : Finset (ZMod P)) (hT : ∀ x ∈ T, x ^ 5 = 1 ∧ x ≠ 1) :
    T.card ≤ 4 := by
  have hsub : insert 1 T ⊆ (nthRoots 5 (1 : ZMod P)).toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_nthRoots (by norm_num)]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact one_pow _
    · exact (hT x hx).1
  have h1 : (1 : ZMod P) ∉ T := fun h => (hT 1 h).2 rfl
  have a := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem h1] at a
  have b := Multiset.toFinset_card_le (nthRoots 5 (1 : ZMod P))
  have c := Polynomial.card_nthRoots 5 (1 : ZMod P)
  omega

private theorem card_le_two_of_no_inverse (T : Finset (ZMod P))
    (hT : ∀ x ∈ T, x ^ 5 = 1 ∧ x ≠ 1) (hprod : ∀ x ∈ T, ∀ y ∈ T, x * y ≠ 1) :
    T.card ≤ 2 := by
  have hinj : Set.InjOn (fun x : ZMod P => x ^ 4) (T : Set (ZMod P)) := by
    intro x hx y hy hxy
    have hx5 := (hT x hx).1
    have hy5 := (hT y hy).1
    simp only at hxy
    calc x = (x ^ 5) ^ 3 * x := by rw [hx5]; ring
      _ = (x ^ 4) ^ 4 := by ring
      _ = (y ^ 4) ^ 4 := by rw [hxy]
      _ = (y ^ 5) ^ 3 * y := by ring
      _ = y := by rw [hy5]; ring
  have hdisj : Disjoint T (T.image (fun x : ZMod P => x ^ 4)) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz'
    exact hprod _ hz y hy (by rw [← (hT y hy).1]; ring)
  have hall : ∀ x ∈ T ∪ T.image (fun x : ZMod P => x ^ 4), x ^ 5 = 1 ∧ x ≠ 1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hT x hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hy5, hy1⟩ := hT y hy
      refine ⟨by rw [← pow_mul, mul_comm, pow_mul, hy5, one_pow], fun h4 => hy1 ?_⟩
      calc y = y * y ^ 4 := by rw [h4, mul_one]
        _ = y ^ 5 := by ring
        _ = 1 := hy5
  have := card_le_four _ hall
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj] at this
  omega

private theorem card_le_one_of_no_small_product (T : Finset (ZMod P))
    (hT : ∀ x ∈ T, x ^ 5 = 1 ∧ x ≠ 1) (hprod : ∀ x ∈ T, ∀ y ∈ T, x * y ≠ 1)
    (hprod3 : ∀ x ∈ T, ∀ y ∈ T, x * x * y ≠ 1) : T.card ≤ 1 := by
  by_contra hc
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  obtain ⟨hx5, hx1⟩ := hT x hx
  obtain ⟨hy5, hy1⟩ := hT y hy
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have hprim : IsPrimitiveRoot x 5 := hord ▸ IsPrimitiveRoot.orderOf x
  obtain ⟨i, hi, hxi⟩ := hprim.eq_pow_of_pow_eq_one hy5
  interval_cases i
  · exact hy1 (by rw [← hxi, pow_zero])
  · exact hxy (by rw [← hxi, pow_one])
  · exact hprod3 y hy x hx (by rw [← hxi]; linear_combination hx5)
  · exact hprod3 x hx y hy (by rw [← hxi]; linear_combination hx5)
  · exact hprod x hx y hy (by rw [← hxi]; linear_combination hx5)

private theorem card_le_two_of_quadratic (T : Finset (ZMod P))
    (hT : ∀ x ∈ T, x ^ 2 + x + 1 = 0) : T.card ≤ 2 := by
  by_contra hc
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp (show 2 < T.card by omega)
  have key : ∀ {x z : ZMod P}, x ^ 2 + x + 1 = 0 → z ^ 2 + z + 1 = 0 → x ≠ z →
      x + z + 1 = 0 := by
    intro x z hx hz hxz
    have h0 : (x - z) * (x + z + 1) = 0 := by linear_combination hx - hz
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) hxz
    · exact h
  have h1 := key (hT a ha) (hT b hb) hab
  have h2 := key (hT a ha) (hT c hc') hac
  exact hbc (by linear_combination h1 - h2)

end Field

/-! ## Weight bounds into a prime from sources below it -/

private theorem natCast_injOn_lt {P : ℕ} (s : Finset ℕ) (hs : ∀ u ∈ s, u < P) :
    Set.InjOn (fun u : ℕ => (u : ZMod P)) (s : Set ℕ) := by
  intro a ha b hb hab
  simp only at hab
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hs a ha),
    Nat.mod_eq_of_lt (hs b hb)] at hab

/-- Square rows: for a prime `P` and a finite set of integers `u < P`, the total
`Σ v_P(u ^ 2 + u + 1)` is at most `2`. -/
theorem sum_factorization_phi3_le_two {P : ℕ} (hP : P.Prime) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u < P) : ∑ u ∈ U, (phi3 u).factorization P ≤ 2 := by
  have : Fact P.Prime := ⟨hP⟩
  have hpt : ∀ u ∈ U, (phi3 u).factorization P ≤
      if 1 ≤ (phi3 u).factorization P then 1 else 0 := by
    intro u hu
    have hlt : phi3 u < P ^ 2 := by
      have := hU u hu
      have := hP.two_le
      unfold phi3
      nlinarith
    have hle : (phi3 u).factorization P ≤ 1 := by
      by_contra h2
      have hd := (hP.pow_dvd_iff_le_factorization (by unfold phi3; omega)).mpr
        (show 2 ≤ (phi3 u).factorization P by omega)
      have := Nat.le_of_dvd (by unfold phi3; omega) hd
      omega
    split_ifs <;> omega
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.card_filter]
  set B := U.filter (fun u => 1 ≤ (phi3 u).factorization P)
  have hBU : ∀ u ∈ B, u < P := fun u hu => hU u (Finset.mem_filter.mp hu).1
  rw [← Finset.card_image_of_injOn (natCast_injOn_lt B hBU)]
  refine card_le_two_of_quadratic _ fun x hx => ?_
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  have h1 := (Finset.mem_filter.mp hu).2
  have hd := (hP.pow_dvd_iff_le_factorization (by unfold phi3; omega)).mpr h1
  rw [pow_one] at hd
  have := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  unfold phi3 at this
  push_cast at this
  exact this

private theorem phi5_ne_zero (u : ℕ) : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 ≠ 0 := by omega

/-- Data of a source of weight at least `j ≥ 1` into `P`. -/
private theorem source_data {P j u : ℕ} [Fact P.Prime] (hP5 : P ≠ 5) (hj : 1 ≤ j)
    (hd : P ^ j ∣ u ^ 4 + u ^ 3 + u ^ 2 + u + 1) :
    1 < u ∧ (u : ZMod P) ^ 5 = 1 ∧ (u : ZMod P) ≠ 1 := by
  have hP : P.Prime := Fact.out
  have hd1 : P ∣ u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := (dvd_pow_self P (by omega)).trans
    ((Nat.pow_dvd_pow P hj).trans hd)
  have h0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd1
  push_cast at h0
  have hne : (u : ZMod P) ≠ 1 := by
    intro h1
    rw [h1] at h0
    have h5 : ((5 : ℕ) : ZMod P) = 0 := by push_cast; linear_combination h0
    exact hP5 ((Nat.prime_dvd_prime_iff_eq hP (by norm_num)).mp
      ((ZMod.natCast_eq_zero_iff _ _).mp h5))
  refine ⟨?_, by linear_combination ((u : ZMod P) - 1) * h0, hne⟩
  rcases Nat.lt_or_ge 1 u with h | h
  · exact h
  · interval_cases u
    · simp at hd1
      exact absurd hd1 hP.one_lt.ne'
    · exact absurd (by push_cast; rfl) hne

/-- Fourth power rows: for a prime `P ≠ 5` and a finite set of integers `u < P`, the total
`Σ v_P(u ^ 4 + u ^ 3 + u ^ 2 + u + 1)` is at most `7`. -/
theorem sum_factorization_phi5_le_seven {P : ℕ} (hP : P.Prime) (hP5 : P ≠ 5) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u < P) :
    ∑ u ∈ U, (u ^ 4 + u ^ 3 + u ^ 2 + u + 1).factorization P ≤ 7 := by
  have : Fact P.Prime := ⟨hP⟩
  set f : ℕ → ℕ := fun u => (u ^ 4 + u ^ 3 + u ^ 2 + u + 1).factorization P with hfdef
  have hdvd : ∀ {u j : ℕ}, j ≤ f u → P ^ j ∣ u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := fun h =>
    (hP.pow_dvd_iff_le_factorization (phi5_ne_zero _)).mpr h
  have hpt : ∀ u ∈ U, f u ≤ ((if 1 ≤ f u then 1 else 0) + (if 2 ≤ f u then 1 else 0)) +
      (if 3 ≤ f u then 1 else 0) := by
    intro u hu
    have hlt : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 < P ^ 4 := by
      have := hU u hu
      have := hP.two_le
      have h4 : (u + 1) ^ 4 ≤ P ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have e : (u + 1) ^ 4 = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 + (3 * u ^ 3 + 5 * u ^ 2 + 3 * u) := by
        ring
      rcases Nat.eq_zero_or_pos u with rfl | hu0
      · simpa using Nat.one_lt_pow (by norm_num : 4 ≠ 0) hP.one_lt
      · have := Nat.zero_le (3 * u ^ 3)
        have := Nat.zero_le (5 * u ^ 2)
        linarith
    have hle : f u ≤ 3 := by
      by_contra h4
      have := Nat.le_of_dvd (by omega) (hdvd (show 4 ≤ f u by omega))
      omega
    split_ifs <;> omega
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.card_filter,
    ← Finset.card_filter, ← Finset.card_filter]
  have hcard : ∀ j, (U.filter (fun u => j ≤ f u)).card =
      ((U.filter (fun u => j ≤ f u)).image (fun u : ℕ => (u : ZMod P))).card := fun j =>
    (Finset.card_image_of_injOn (natCast_injOn_lt _
      fun u hu => hU u (Finset.mem_filter.mp hu).1)).symm
  have hmem : ∀ {j : ℕ} {x : ZMod P},
      x ∈ (U.filter (fun u => j ≤ f u)).image (fun u : ℕ => (u : ZMod P)) →
      ∃ u, u ∈ U ∧ j ≤ f u ∧ (u : ZMod P) = x := by
    intro j x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨u, (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2, rfl⟩
  have hroot : ∀ {j : ℕ}, 1 ≤ j → ∀ x ∈ (U.filter (fun u => j ≤ f u)).image
      (fun u : ℕ => (u : ZMod P)), x ^ 5 = 1 ∧ x ≠ 1 := by
    intro j hj x hx
    obtain ⟨u, -, hju, rfl⟩ := hmem hx
    exact (source_data hP5 hj (hdvd hju)).2
  have hlist : ∀ {j : ℕ} (l : List ℕ), l ≠ [] → l.length ≤ j → (∀ u ∈ l, u ∈ U ∧ j ≤ f u) →
      ((l.prod : ℕ) : ZMod P) ≠ 1 := by
    intro j l hl hlj hall h1
    have hj : 1 ≤ j := by
      have := List.length_pos_of_ne_nil hl
      omega
    refine prod_not_modEq_one_of_dvd_phi5 hP hP5 hl hlj (fun u hu => ?_)
      (fun u hu => hdvd (hall u hu).2) ?_
    · exact ⟨(source_data hP5 hj (hdvd (hall u hu).2)).1, hU u (hall u hu).1⟩
    · rw [← ZMod.natCast_eq_natCast_iff, h1, Nat.cast_one]
  have hpair : ∀ {j : ℕ}, 2 ≤ j → ∀ x ∈ (U.filter (fun u => j ≤ f u)).image
      (fun u : ℕ => (u : ZMod P)), ∀ y ∈ (U.filter (fun u => j ≤ f u)).image
      (fun u : ℕ => (u : ZMod P)), x * y ≠ 1 := by
    intro j hj x hx y hy
    obtain ⟨u, hu, hju, rfl⟩ := hmem hx
    obtain ⟨u', hu', hju', rfl⟩ := hmem hy
    have := hlist (j := j) [u, u'] (by simp) (by simp; omega) (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨hu, hju⟩
      · exact ⟨hu', hju'⟩)
    simpa using this
  have htriple : ∀ x ∈ (U.filter (fun u => 3 ≤ f u)).image (fun u : ℕ => (u : ZMod P)),
      ∀ y ∈ (U.filter (fun u => 3 ≤ f u)).image (fun u : ℕ => (u : ZMod P)),
      x * x * y ≠ 1 := by
    intro x hx y hy
    obtain ⟨u, hu, hju, rfl⟩ := hmem hx
    obtain ⟨u', hu', hju', rfl⟩ := hmem hy
    have := hlist (j := 3) [u, u, u'] (by simp) (by simp) (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨hu, hju⟩
      · exact ⟨hu, hju⟩
      · exact ⟨hu', hju'⟩)
    simpa [mul_assoc] using this
  have c1 := card_le_four _ (hroot (le_refl 1))
  have c2 := card_le_two_of_no_inverse _ (hroot (by norm_num : 1 ≤ 2))
    (hpair (le_refl 2))
  have c3 := card_le_one_of_no_small_product _ (hroot (by norm_num : 1 ≤ 3))
    (hpair (by norm_num)) htriple
  rw [hcard 1, hcard 2, hcard 3]
  omega

/-! ## The mixed family -/

private theorem sigma_prime_four {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  ring

/-- Mixed family. Let `N` be an odd perfect number with special prime `q`, `e_q = 1`, and
largest prime factor `P ≠ q`. If every prime factor other than `q` and `P` has exponent `2`
or `4`, then `e_P ≤ 8`. Restricted family result; whether this is in the literature was not
verified. -/
theorem factorization_largest_le_eight {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization P ≤ 8 := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hodd : ∀ p ∈ N.primeFactors, p % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by rw [hq1]; norm_num)
  have hP2 : P ≠ 2 := fun h2 => by have := hodd P hP; omega
  have hP5 : P ≠ 5 := by
    have h4 := (special_mod_four h hq (by rw [hq1]; exact odd_one)).1
    have := hq.two_le
    have := lt_of_le_of_ne (hmax q hqmem) hPq.symm
    omega
  have hsum := sigmaWeight_sum_eq h.2 hPp hP2
  rw [← Finset.sum_erase N.primeFactors (f := fun p => sigmaWeight N p P)
    (sigmaWeight_self hPp)] at hsum
  have hpt : ∀ p ∈ N.primeFactors.erase P, sigmaWeight N p P ≤
      (if N.factorization p = 2 then (phi3 p).factorization P else 0) +
      (if N.factorization p = 4 then (p ^ 4 + p ^ 3 + p ^ 2 + p + 1).factorization P
        else 0) := by
    intro p hp
    obtain ⟨hpP, hp'⟩ := Finset.mem_erase.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hp'
    by_cases hpq : p = q
    · subst hpq
      have hs : σ 1 (p ^ N.factorization p) = p + 1 := by
        rw [hq1, sigma_one_apply_prime_pow hpp]
        simp [Finset.sum_range_succ, add_comm]
      have hlt : p < P := lt_of_le_of_ne (hmax p hp') hpP
      have := hodd p hp'
      have := hodd P hP
      have hnd : ¬ P ∣ p + 1 := fun hd => by
        have := Nat.le_of_dvd (by omega) hd
        omega
      unfold sigmaWeight
      rw [hs, Nat.factorization_eq_zero_of_not_dvd hnd]
      omega
    · rcases hexp p hp' hpq hpP with hf | hf
      · rw [if_pos hf, if_neg (by omega), add_zero]
        unfold sigmaWeight
        rw [hf, sigma_prime_sq hpp]
      · rw [if_neg (by omega), if_pos hf, zero_add]
        unfold sigmaWeight
        rw [hf, sigma_prime_four hpp]
  have hle := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, hsum] at hle
  have hlt : ∀ s : Finset ℕ, s ⊆ N.primeFactors.erase P → ∀ u ∈ s, u < P := by
    intro s hs u hu
    obtain ⟨huP, hu'⟩ := Finset.mem_erase.mp (hs hu)
    exact lt_of_le_of_ne (hmax u hu') huP
  have h2 := sum_factorization_phi3_le_two hPp
    ((N.primeFactors.erase P).filter (fun p => N.factorization p = 2))
    (hlt _ (Finset.filter_subset _ _))
  have h4 := sum_factorization_phi5_le_seven hPp hP5
    ((N.primeFactors.erase P).filter (fun p => N.factorization p = 4))
    (hlt _ (Finset.filter_subset _ _))
  obtain ⟨k, hk⟩ := even_factorization_of_ne h hq (by rw [hq1]; exact odd_one) hPp hPq
  omega

end OddPerfect

#print axioms OddPerfect.not_modEq_one_of_pow_five_modEq
#print axioms OddPerfect.prod_not_modEq_one_of_dvd_phi5
#print axioms OddPerfect.sum_factorization_phi3_le_two
#print axioms OddPerfect.sum_factorization_phi5_le_seven
#print axioms OddPerfect.factorization_largest_le_eight
