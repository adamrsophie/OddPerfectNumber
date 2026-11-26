import OddPerfect.PureRows
import OddPerfect.KanoldGeneral
import OddPerfect.AbundancyTail

/-!
# Packing for primes whose row is a prime power from a small set

Write `R(x) = ∑ i < l, x ^ i` and `H(x) = x / (x - 1)`. Let `S` be a finite set of odd primes and
`X` a set of at most `K` numbers such that every `p ∈ S` outside `X` has `R(p) = r ^ w` for a
prime `r ∈ X`. Then a set `C ⊆ S` of at most `K` centers exists that contains every `p ∈ S` with
`p % l ≠ 1` and `p ≤ 3 ^ (l - 1)`, and the product of `H` over `S \ C` is bounded by a product
over the first `K` numbers `1` modulo `2 l` times the factor
`(3 ^ (l - 1) - 1) / (3 ^ (l - 1) - 1 - K)`.

* `card_mul_le_of_one_mod`: a set of numbers `> 1`, each `1` modulo `m`, all at most `B`,
  has `card * m ≤ B - 1`.
* `prod_div_pred_le_range`: the product of `H` over such a set is at most the product of `H`
  over the first `card` numbers `> 1` that are `1` modulo `m`.
* `exists_centers_of_pure_cover`: the packing statement.

No odd perfect number appears: this is a statement on finite sets of odd primes.
Restricted result; no published source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- A finite set of numbers `> 1`, each `1` modulo `m > 0` and all at most `B`, has
`card * m ≤ B - 1`. -/
theorem card_mul_le_of_one_mod {T : Finset ℕ} {m B : ℕ} (hm : 0 < m)
    (hT : ∀ t ∈ T, 1 < t ∧ m ∣ t - 1) (hB : ∀ t ∈ T, t ≤ B) : T.card * m ≤ B - 1 := by
  have hmaps : Set.MapsTo (fun t => (t - 1) / m) (T : Set ℕ)
      (Finset.Icc 1 ((B - 1) / m) : Set ℕ) := by
    intro t ht
    simp only [Finset.mem_coe, Finset.mem_Icc] at ht ⊢
    obtain ⟨h1, k, hk⟩ := hT t ht
    have htB := hB t ht
    rw [hk, Nat.mul_div_cancel_left _ hm]
    refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hk; omega), ?_⟩
    rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm, ← hk]
    omega
  have hinj : Set.InjOn (fun t => (t - 1) / m) (T : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    have hab' : (a - 1) / m = (b - 1) / m := hab
    have h1 := Nat.div_mul_cancel (hT a ha).2
    have h2 := Nat.div_mul_cancel (hT b hb).2
    rw [hab'] at h1
    have h3 : a - 1 = b - 1 := h1.symm.trans h2
    have := (hT a ha).1
    have := (hT b hb).1
    omega
  have hc := Finset.card_le_card_of_injOn _ hmaps hinj
  have hc' : T.card ≤ (B - 1) / m := by
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at hc
  calc T.card * m ≤ (B - 1) / m * m := Nat.mul_le_mul_right m hc'
    _ ≤ B - 1 := Nat.div_mul_le_self _ _

/-- `H` is antitone on `x > 1`. -/
theorem div_pred_le_div_pred {a b : ℚ} (hb : 1 < b) (hab : b ≤ a) :
    a / (a - 1) ≤ b / (b - 1) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `H(x) ≥ 1` for `x > 1`. -/
theorem one_le_div_pred {a : ℚ} (ha : 1 < a) : 1 ≤ a / (a - 1) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The product of `H` over a finite set of numbers `> 1`, each `1` modulo `m > 0`, is at most
the product of `H((j + 1) m + 1)` over `j < card`. -/
theorem prod_div_pred_le_range {m : ℕ} (hm : 0 < m) : ∀ (T : Finset ℕ),
    (∀ t ∈ T, 1 < t ∧ m ∣ t - 1) →
    ∏ t ∈ T, ((t : ℚ) / ((t : ℚ) - 1)) ≤
      ∏ j ∈ Finset.range T.card, (((m * (j + 1) + 1 : ℕ) : ℚ) / ((m * (j + 1) : ℕ) : ℚ)) := by
  intro T
  induction T using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a S ha ih =>
    intro hT
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    have hS : ∀ t ∈ S, 1 < t ∧ m ∣ t - 1 := fun t ht => hT t (Finset.mem_insert_of_mem ht)
    have hcard := card_mul_le_of_one_mod hm hT (B := a) (fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact le_rfl
      · exact (ha t ht).le)
    rw [Finset.card_insert_of_notMem haS, Nat.mul_comm] at hcard
    have hpos : 0 < m * (S.card + 1) := Nat.mul_pos hm (Nat.succ_pos _)
    have h2 : m * (S.card + 1) + 1 ≤ a := by omega
    have hA : (a : ℚ) / ((a : ℚ) - 1) ≤
        ((m * (S.card + 1) + 1 : ℕ) : ℚ) / ((m * (S.card + 1) : ℕ) : ℚ) := by
      have hc : ((m * (S.card + 1) : ℕ) : ℚ) = ((m * (S.card + 1) + 1 : ℕ) : ℚ) - 1 := by
        push_cast; ring
      rw [hc]
      exact div_pred_le_div_pred (by exact_mod_cast (by omega : 1 < m * (S.card + 1) + 1))
        (by exact_mod_cast h2)
    rw [Finset.prod_insert haS, Finset.card_insert_of_notMem haS, Finset.prod_range_succ]
    refine (mul_le_mul hA (ih hS) ?_ (by positivity)).trans (le_of_eq (mul_comm _ _))
    exact Finset.prod_nonneg fun t ht =>
      zero_le_one.trans (one_le_div_pred (by exact_mod_cast (hS t ht).1))

/-- **Packing for pure covers.** Let `l` be an odd prime, `S` a finite set of odd primes and `X`
a set of at most `K` numbers, `K + 1 < 3 ^ (l - 1)`, such that every `p ∈ S` outside `X` has
`∑ i < l, p ^ i = r ^ w` for a prime `r ∈ X`. Then some `C ⊆ S` with at most `K` elements
contains every `p ∈ S` with `p % l ≠ 1` and `p ≤ 3 ^ (l - 1)`, and the product of `p / (p - 1)`
over `S \ C` is at most `∏ j < K, H(2 (j + 1) l + 1)` times
`(3 ^ (l - 1) - 1) / (3 ^ (l - 1) - 1 - K)`.
Restricted result; no published source was checked; novelty not verified. -/
theorem exists_centers_of_pure_cover {l K : ℕ} {S X : Finset ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hX : X.card ≤ K) (hK : K + 1 < 3 ^ (l - 1))
    (hcov : ∀ p ∈ S, p ∉ X →
      ∃ r ∈ X, ∃ w, r.Prime ∧ ∑ i ∈ Finset.range l, p ^ i = r ^ w) :
    ∃ C : Finset ℕ, C ⊆ S ∧ C.card ≤ K ∧
      (∀ p ∈ S, p % l ≠ 1 → p ≤ 3 ^ (l - 1) → p ∈ C) ∧
      ∏ p ∈ S \ C, ((p : ℚ) / ((p : ℚ) - 1)) ≤
        (∏ j ∈ Finset.range K,
            (((2 * (j + 1) * l + 1 : ℕ) : ℚ) / ((2 * (j + 1) * l : ℕ) : ℚ))) *
          (((3 : ℚ) ^ (l - 1) - 1) / ((3 : ℚ) ^ (l - 1) - 1 - (K : ℚ))) := by
  classical
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  set A := 3 ^ (l - 1) with hA
  have hA9 : 9 ≤ A := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (l - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hS3 : ∀ p ∈ S, 3 ≤ p := fun p hp => by
    have := (hS p hp).1.two_le; have := (hS p hp).2; omega
  -- the row is at least its top term
  have hrow_ge : ∀ p, p ^ (l - 1) ≤ ∑ i ∈ Finset.range l, p ^ i := fun p =>
    Finset.single_le_sum (f := fun i => p ^ i) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  have hrowA : ∀ p, 3 ≤ p → A ≤ ∑ i ∈ Finset.range l, p ^ i := fun p hp =>
    (Nat.pow_le_pow_left hp _).trans (hrow_ge p)
  -- facts on a receiver
  have hrecv : ∀ p r w, p.Prime → p ≠ 2 → r.Prime → ∑ i ∈ Finset.range l, p ^ i = r ^ w →
      r % l = 1 ∧ r ≠ 2 ∧ 2 * l ∣ r - 1 := by
    intro p r w hp hp2 hr hrw
    have hσ : σ 1 (p ^ (l - 1)) = r ^ w := by
      rw [sigma_one_apply_prime_pow hp, Nat.sub_add_cancel hl.one_lt.le]; exact hrw
    have h1 : r % (l - 1 + 1) = 1 := receiver_mod_index_of_pure hp hp2 (by omega) hr hσ
    rw [Nat.sub_add_cancel hl.one_lt.le] at h1
    have hr2 : r ≠ 2 := by
      rintro rfl
      rw [Nat.mod_eq_of_lt (by omega)] at h1
      omega
    have hro : r % 2 = 1 := Nat.odd_iff.mp (hr.odd_of_ne_two hr2)
    have hdl : l ∣ r - 1 := ⟨r / l, by have := Nat.div_add_mod r l; omega⟩
    have hd2 : 2 ∣ r - 1 := ⟨r / 2, by have := Nat.div_add_mod r 2; omega⟩
    have hcop : Nat.Coprime 2 l := (Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2)
    exact ⟨h1, hr2, Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hd2 hdl⟩
  -- choice of one receiver for each parent
  have hcov' : ∀ p, ∃ r, (p ∈ S → p ∉ X →
      r ∈ X ∧ ∃ w, r.Prime ∧ ∑ i ∈ Finset.range l, p ^ i = r ^ w) := by
    intro p
    by_cases h : p ∈ S ∧ p ∉ X
    · obtain ⟨r, hr, w, hrp, hrw⟩ := hcov p h.1 h.2
      exact ⟨r, fun _ _ => ⟨hr, w, hrp, hrw⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose f hf using hcov'
  set P := S.filter (fun p => p ∉ X) with hP
  set T := P.image f with hT
  have hPmem : ∀ p, p ∈ P ↔ p ∈ S ∧ p ∉ X := fun p => Finset.mem_filter
  have hfX : ∀ p ∈ P, f p ∈ X := fun p hp =>
    (hf p ((hPmem p).1 hp).1 ((hPmem p).1 hp).2).1
  have hTX : T ⊆ X := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    exact hfX p hp
  have hTprop : ∀ t ∈ T, t % l = 1 ∧ 1 < t ∧ 2 * l ∣ t - 1 := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hpS, hpX⟩ := (hPmem p).1 hp
    obtain ⟨-, w, hrp, hrw⟩ := hf p hpS hpX
    obtain ⟨h1, -, h3⟩ := hrecv p (f p) w (hS p hpS).1 (hS p hpS).2 hrp hrw
    exact ⟨h1, hrp.one_lt, h3⟩
  -- growth inside one target
  have hgrow : ∀ p ∈ P, ∀ p' ∈ P, p < p' → f p = f p' →
      ∑ i ∈ Finset.range l, p ^ i < p' := by
    intro p hp p' hp' hlt heq
    obtain ⟨hpS, hpX⟩ := (hPmem p).1 hp
    obtain ⟨hpS', hpX'⟩ := (hPmem p').1 hp'
    obtain ⟨-, w, hrp, hrw⟩ := hf p hpS hpX
    obtain ⟨hr', w', hrp', hrw'⟩ := hf p' hpS' hpX'
    obtain ⟨-, hr2, -⟩ := hrecv p' (f p') w' (hS p' hpS').1 (hS p' hpS').2 hrp' hrw'
    rw [heq] at hrw
    exact lt_of_geom_eq_pow hl hrp' hr2 (hS p hpS).1 (hS p' hpS').1 hlt
      (fun h => hpX' (by rw [h]; exact hr')) hrw hrw'
  -- least parents and the centers
  set L := P.filter (fun p => ∀ p' ∈ P, f p' = f p → p ≤ p') with hL
  set D := (S.filter (fun p => p ∈ X)) \ T with hD
  refine ⟨L ∪ D, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact ((hPmem p).1 (Finset.mem_filter.mp h).1).1
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
  · have hLT : L.card ≤ T.card := by
      refine Finset.card_le_card_of_injOn f ?_ ?_
      · intro p hp
        exact Finset.mem_image_of_mem f (Finset.mem_filter.mp hp).1
      · intro a ha b hb hab
        have ha' := Finset.mem_filter.mp ha
        have hb' := Finset.mem_filter.mp hb
        exact le_antisymm (ha'.2 b hb'.1 hab.symm) (hb'.2 a ha'.1 hab)
    have hDX : D.card ≤ (X \ T).card := by
      refine Finset.card_le_card ?_
      intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hp
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp h1).2, h2⟩
    have hXT := Finset.card_sdiff_add_card_eq_card hTX
    have hU := Finset.card_union_le L D
    omega
  · intro p hpS hpl hpA
    by_cases hpX : p ∈ X
    · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hpS, hpX⟩,
        fun ht => hpl (hTprop p ht).1⟩)
    · have hpP : p ∈ P := (hPmem p).2 ⟨hpS, hpX⟩
      refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpP, fun p' hp' heq => ?_⟩)
      by_contra hlt
      push Not at hlt
      have h1 := hgrow p' hp' p hpP hlt heq
      have h2 := hrowA p' (hS3 p' ((hPmem p').1 hp').1)
      omega
  · -- the non least parents
    set P' := (S \ (L ∪ D)) \ T with hP'
    have hP'P : ∀ p ∈ P', p ∈ P ∧ ∃ p' ∈ P, f p' = f p ∧ p' < p := by
      intro p hp
      obtain ⟨h1, hpT⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hpS, hpC⟩ := Finset.mem_sdiff.mp h1
      have hpX : p ∉ X := fun hpX => hpC (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hpS, hpX⟩, hpT⟩))
      have hpP : p ∈ P := (hPmem p).2 ⟨hpS, hpX⟩
      refine ⟨hpP, ?_⟩
      by_contra hno
      push Not at hno
      exact hpC (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpP, hno⟩))
    have hP'A : ∀ p ∈ P', A < p := by
      intro p hp
      obtain ⟨hpP, p', hp', heq, hlt⟩ := hP'P p hp
      have h1 := hgrow p' hp' p hpP hlt heq
      have h2 := hrowA p' (hS3 p' ((hPmem p').1 hp').1)
      omega
    have hP'3 : ∀ p ∈ P', (3 : ℚ) ≤ p := fun p hp => by
      exact_mod_cast hS3 p ((hPmem p).1 (hP'P p hp).1).1
    -- at most `K` elements of `P'` in each block
    have hblock : ∀ j, 1 ≤ j →
        (P'.filter (fun p => A ^ j < p ∧ p ≤ A ^ (j + 1))).card ≤ K := by
      intro j hj
      set F := P'.filter (fun p => A ^ j < p ∧ p ≤ A ^ (j + 1)) with hF
      have key : ∀ a ∈ F, ∀ b ∈ F, a < b → f a = f b → False := by
        intro a ha b hb hab heq
        obtain ⟨haP', haj, -⟩ := Finset.mem_filter.mp ha
        obtain ⟨hbP', -, hbj⟩ := Finset.mem_filter.mp hb
        have h1 := hgrow a (hP'P a haP').1 b (hP'P b hbP').1 hab heq
        have h2 := hrow_ge a
        have h3 : a ^ 2 ≤ a ^ (l - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have h4 : (A ^ j) ^ 2 < a ^ 2 := Nat.pow_lt_pow_left haj two_ne_zero
        have h5 : (A ^ j) ^ 2 = A ^ (j * 2) := (pow_mul A j 2).symm
        have h6 : A ^ (j + 1) ≤ A ^ (j * 2) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      calc F.card ≤ X.card := by
            refine Finset.card_le_card_of_injOn f ?_ ?_
            · intro p hp
              exact hfX p (hP'P p (Finset.mem_filter.mp hp).1).1
            · intro a ha b hb hab
              rcases lt_trichotomy a b with h | h | h
              · exact (key a ha b hb h hab).elim
              · exact h
              · exact (key b hb a ha h hab.symm).elim
        _ ≤ K := hX
    have hsum := sum_inv_pred_le_of_interval_card (by omega : 2 ≤ A) hP'A hblock
    have hAq : ((A : ℕ) : ℚ) = (3 : ℚ) ^ (l - 1) := by simp [hA]
    have hKq : (K : ℚ) + 1 < (A : ℚ) := by exact_mod_cast hK
    have hA1 : (0 : ℚ) < (A : ℚ) - 1 := by linarith
    have hKA : (K : ℚ) / ((A : ℚ) - 1) < 1 := by
      rw [div_lt_one hA1]; linarith
    have hprod := prod_one_add_le_inv_one_sub P' (fun p => (1 : ℚ) / ((p : ℚ) - 1))
      (fun p hp => div_nonneg zero_le_one (by linarith [hP'3 p hp])) (hsum.trans_lt hKA)
    beta_reduce at hprod
    have hP'bound : ∏ p ∈ P', ((p : ℚ) / ((p : ℚ) - 1)) ≤
        ((3 : ℚ) ^ (l - 1) - 1) / ((3 : ℚ) ^ (l - 1) - 1 - (K : ℚ)) := by
      have hcongr : ∏ p ∈ P', ((p : ℚ) / ((p : ℚ) - 1)) =
          ∏ p ∈ P', (1 + (1 : ℚ) / ((p : ℚ) - 1)) := by
        refine Finset.prod_congr rfl fun p hp => ?_
        have hne : (p : ℚ) - 1 ≠ 0 := by linarith [hP'3 p hp]
        rw [one_add_div hne, sub_add_cancel]
      rw [hcongr]
      refine hprod.trans ?_
      refine (one_div_le_one_div_of_le (sub_pos.mpr hKA) (by linarith)).trans (le_of_eq ?_)
      rw [one_sub_div hA1.ne', one_div_div, hAq]
    -- the targets
    have hm : 0 < 2 * l := by omega
    have hTbound : ∏ t ∈ T, ((t : ℚ) / ((t : ℚ) - 1)) ≤
        ∏ j ∈ Finset.range K,
          (((2 * (j + 1) * l + 1 : ℕ) : ℚ) / ((2 * (j + 1) * l : ℕ) : ℚ)) := by
      have h1 := prod_div_pred_le_range hm T (fun t ht => ⟨(hTprop t ht).2.1, (hTprop t ht).2.2⟩)
      have hTK : T.card ≤ K := (Finset.card_le_card hTX).trans hX
      have hg1 : ∀ j, (1 : ℚ) ≤
          ((2 * l * (j + 1) + 1 : ℕ) : ℚ) / ((2 * l * (j + 1) : ℕ) : ℚ) := by
        intro j
        have hpos : (0 : ℚ) < ((2 * l * (j + 1) : ℕ) : ℚ) := by
          exact_mod_cast Nat.mul_pos hm (Nat.succ_pos j)
        rw [le_div_iff₀ hpos]
        push_cast
        linarith
      have h2 := Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.range_subset_range.mpr hTK)
        (f := fun j => ((2 * l * (j + 1) + 1 : ℕ) : ℚ) / ((2 * l * (j + 1) : ℕ) : ℚ))
        (fun j _ => zero_le_one.trans (hg1 j)) (fun j _ _ => hg1 j)
      refine (h1.trans h2).trans (le_of_eq (Finset.prod_congr rfl fun j _ => ?_))
      rw [show 2 * (j + 1) * l = 2 * l * (j + 1) by ring]
    have hTnonneg : ∀ t ∈ T, (0 : ℚ) ≤ (t : ℚ) / ((t : ℚ) - 1) := fun t ht =>
      zero_le_one.trans (one_le_div_pred (by exact_mod_cast (hTprop t ht).2.1))
    have hIT : ∏ p ∈ (S \ (L ∪ D)) ∩ T, ((p : ℚ) / ((p : ℚ) - 1)) ≤
        ∏ t ∈ T, ((t : ℚ) / ((t : ℚ) - 1)) :=
      Finset.prod_le_prod_of_subset_of_one_le₀ Finset.inter_subset_right
        (fun t ht => hTnonneg t (Finset.mem_inter.mp ht).2)
        (fun t ht _ => one_le_div_pred (by exact_mod_cast (hTprop t ht).2.1))
    rw [← Finset.prod_inter_mul_prod_sdiff (S \ (L ∪ D)) T]
    refine mul_le_mul (hIT.trans hTbound) hP'bound ?_ ?_
    · exact Finset.prod_nonneg fun p hp => div_nonneg (by positivity)
        (by linarith [hP'3 p hp])
    · exact Finset.prod_nonneg fun j _ => by positivity

#print axioms card_mul_le_of_one_mod
#print axioms div_pred_le_div_pred
#print axioms one_le_div_pred
#print axioms prod_div_pred_le_range
#print axioms exists_centers_of_pure_cover

end OddPerfect
