import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Prime.Basic

/-!
# Restrained odd perfect numbers: the sieve checker

A certified sieve over the odd numbers of a range. For every odd `n` the data carries a witness
`w < 2 ^ 18`:

* `w ≠ 0` with `2 ≤ w < n` and `w ∣ n`: `n` is not prime;
* `w ≠ 0` with `2 ≤ w < 132257`, `w` odd, `3 ∤ w` and `w ∣ n * n + n + 1`: then `n` is not
  `Good` (see below);
* `w = 0`: `n` belongs to the leftover set `T`, and the checker multiplies a fixed point
  accumulator by `n X / ((n - 1) (X + 1))`, rounding up.

`Cert X lo hi a b` says that there is a finite set `T ⊆ [lo, hi)` that contains every prime
`Good` number of `[lo, hi)`, with `a * ∏_{n ∈ T} n X / ((n - 1) (X + 1)) ≤ b`. The checker
`runL` is sound for `Cert` (`runL_sound`), and certificates of adjacent ranges combine
(`cert_trans`). The number theory that makes the members of the family `Good` is in
`OddPerfect.RestrainedEleven`.
-/

namespace OddPerfect

namespace RestrainedElevenCheck

/-- A number `m` is `Good` when no `w` with `2 ≤ w < 132257`, `w` odd and `3 ∤ w`, divides
`m * m + m + 1`. -/
def Good (m : ℕ) : Prop :=
  ∀ w, 2 ≤ w → w < 132257 → w % 2 = 1 → w % 3 ≠ 0 → ¬ w ∣ m * m + m + 1

/-- The factor of a leftover number: `n X / ((n - 1) (X + 1))`. -/
noncomputable def fac (X n : ℕ) : ℚ := ((n * X : ℕ) : ℚ) / (((n - 1) * (X + 1) : ℕ) : ℚ)

theorem fac_nonneg (X n : ℕ) : 0 ≤ fac X n := by
  unfold fac
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The certificate of a range: a finite set of leftovers in `[lo, hi)` that contains every prime
`Good` number of the range, with the product of the factors bounded by `b / a`. -/
def Cert (X lo hi : ℕ) (a b : ℕ) : Prop :=
  lo ≤ hi ∧ ∃ T : Finset ℕ, (∀ m ∈ T, lo ≤ m ∧ m < hi) ∧
    (∀ m, lo ≤ m → m < hi → m.Prime → Good m → m ∈ T) ∧
    (a : ℚ) * ∏ m ∈ T, fac X m ≤ b

/-- Certificates of adjacent ranges combine. -/
theorem cert_trans {X lo mid hi a b c : ℕ} (h₁ : Cert X lo mid a b) (h₂ : Cert X mid hi b c) :
    Cert X lo hi a c := by
  classical
  obtain ⟨hl₁, T₁, hT₁, hc₁, hp₁⟩ := h₁
  obtain ⟨hl₂, T₂, hT₂, hc₂, hp₂⟩ := h₂
  have hdis : Disjoint T₁ T₂ := Finset.disjoint_left.mpr fun m h1 h2 => by
    have := hT₁ m h1
    have := hT₂ m h2
    omega
  refine ⟨by omega, T₁ ∪ T₂, fun m hm => ?_, fun m hlo hhi hp hg => ?_, ?_⟩
  · rcases Finset.mem_union.mp hm with h | h
    · have := hT₁ m h
      omega
    · have := hT₂ m h
      omega
  · rcases Nat.lt_or_ge m mid with h' | h'
    · exact Finset.mem_union_left _ (hc₁ m hlo h' hp hg)
    · exact Finset.mem_union_right _ (hc₂ m h' hhi hp hg)
  · rw [Finset.prod_union hdis, ← mul_assoc]
    have h0 : 0 ≤ ∏ m ∈ T₂, fac X m := Finset.prod_nonneg fun m _ => fac_nonneg X m
    calc (a : ℚ) * (∏ m ∈ T₁, fac X m) * ∏ m ∈ T₂, fac X m
        ≤ (b : ℚ) * ∏ m ∈ T₂, fac X m := mul_le_mul_of_nonneg_right hp₁ h0
      _ ≤ c := hp₂

/-! ## The checker -/

/-- A witness `w` for the odd number `n`: a proper divisor, or a divisor of `n * n + n + 1`
below `132257` that is prime to `6`. -/
def wit (n w : ℕ) : Bool :=
  (decide (2 ≤ w) && decide (w < n) && n % w == 0) ||
    (decide (2 ≤ w) && decide (w < 132257) && w % 2 == 1 && w % 3 != 0 &&
      (n * n + n + 1) % w == 0)

theorem wit_sound {n w : ℕ} (h : wit n w = true) (hp : n.Prime) (hg : Good n) : False := by
  simp only [wit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨h2, hlt⟩, hd⟩ | ⟨⟨⟨⟨h2, hlt⟩, h2'⟩, h3⟩, hd⟩
  · rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hd) with rfl | rfl <;> omega
  · exact hg w h2 hlt h2' h3 (Nat.dvd_of_mod_eq_zero hd)

/-- Rounded up division. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

theorem div_le_cdiv {a b : ℕ} (hb : 0 < b) : (a : ℚ) / b ≤ (cdiv a b : ℕ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  unfold cdiv
  have : a ≤ (a + b - 1) / b * b := by
    rw [Nat.mul_comm]
    omega
  exact_mod_cast this

/-- The digits of one limb, `c` witnesses in base `2 ^ 18`, starting at the odd number `n`.
Returns the accumulator after the limb, or `none` when a witness fails. -/
def runLimb (X : ℕ) : ℕ → ℕ → ℕ → ℕ → Option ℕ
  | 0, _, W, acc => if W == 0 then some acc else none
  | c + 1, n, W, acc =>
    let w := W % 262144
    if w == 0 then runLimb X c (n + 2) (W / 262144) (cdiv (acc * n * X) ((n - 1) * (X + 1)))
    else if wit n w then runLimb X c (n + 2) (W / 262144) acc else none

/-- The limbs of a block, sixteen witnesses each, from the odd number `n` to `hi`, with the
accumulator running from `acc` to at most `b`. -/
def runL (X : ℕ) : List ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | [], n, acc, hi, b => n == hi && decide (acc ≤ b)
  | W :: L, n, acc, hi, b =>
    n % 2 == 1 && decide (3 ≤ n) &&
      match runLimb X 16 n W acc with
      | some a => runL X L (n + 32) a hi b
      | none => false

theorem fac_step {X n acc : ℕ} (hn : 3 ≤ n) :
    (acc : ℚ) * fac X n ≤ (cdiv (acc * n * X) ((n - 1) * (X + 1)) : ℕ) := by
  have hb : 0 < (n - 1) * (X + 1) := Nat.mul_pos (by omega) (by omega)
  refine le_trans (le_of_eq ?_) (div_le_cdiv hb)
  unfold fac
  push_cast
  ring

theorem runLimb_sound {X : ℕ} : ∀ (c n W acc a : ℕ), runLimb X c n W acc = some a →
    n % 2 = 1 → 3 ≤ n → Cert X n (n + 2 * c) acc a
  | 0, n, W, acc, a, h, _, _ => by
    simp only [runLimb, beq_iff_eq] at h
    split_ifs at h
    cases h
    exact ⟨by omega, ∅, by simp, fun m h1 h2 => by omega, by simp⟩
  | c + 1, n, W, acc, a, h, hodd, h3 => by
    have hnext : ∀ m, n ≤ m → m < n + 2 * (c + 1) → m ≠ n → m.Prime → n + 2 ≤ m := by
      intro m h1 h2 hmn hp
      rcases (by omega : m = n + 1 ∨ n + 2 ≤ m) with rfl | h'
      · exact absurd ((Nat.Prime.even_iff hp).mp (by
          rw [Nat.even_add_one, Nat.not_even_iff_odd]; exact Nat.odd_iff.mpr hodd)) (by omega)
      · exact h'
    simp only [runLimb] at h
    split_ifs at h with hw hwit
    · obtain ⟨-, T, hT, hc, hp⟩ := runLimb_sound c (n + 2) _ _ a h (by omega) (by omega)
      have hnT : n ∉ T := fun hm => by have := hT n hm; omega
      refine ⟨by omega, insert n T, fun m hm => ?_, fun m h1 h2 hpm hg => ?_, ?_⟩
      · rcases Finset.mem_insert.mp hm with rfl | hm
        · omega
        · have := hT m hm; omega
      · by_cases hmn : m = n
        · exact hmn ▸ Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hc m (hnext m h1 h2 hmn hpm) (by omega) hpm hg)
      · rw [Finset.prod_insert hnT, ← mul_assoc]
        have h0 : 0 ≤ ∏ m ∈ T, fac X m := Finset.prod_nonneg fun m _ => fac_nonneg X m
        exact le_trans (mul_le_mul_of_nonneg_right (fac_step h3) h0) hp
    · obtain ⟨-, T, hT, hc, hp⟩ := runLimb_sound c (n + 2) _ _ a h (by omega) (by omega)
      refine ⟨by omega, T, fun m hm => ?_, fun m h1 h2 hpm hg => ?_, hp⟩
      · have := hT m hm; omega
      · by_cases hmn : m = n
        · subst hmn
          exact (wit_sound hwit hpm hg).elim
        · exact hc m (hnext m h1 h2 hmn hpm) (by omega) hpm hg

/-- **Soundness of the checker.** -/
theorem runL_sound {X : ℕ} : ∀ {L : List ℕ} {n acc hi b : ℕ}, runL X L n acc hi b = true →
    Cert X n hi acc b
  | [], n, acc, hi, b, h => by
    simp only [runL, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨rfl, hb⟩ := h
    refine ⟨le_rfl, ∅, by simp, fun m h1 h2 => by omega, ?_⟩
    simpa using (Nat.cast_le (α := ℚ)).mpr hb
  | W :: L, n, acc, hi, b, h => by
    simp only [runL, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hodd, h3⟩, h⟩ := h
    split at h
    · rename_i a ha
      have c1 := runLimb_sound 16 n W acc a ha hodd h3
      exact cert_trans c1 (runL_sound h)
    · exact absurd h (by simp)

/-- Positive twin of `runL_reject`: the odd number `132259` is `19 * 6961`, and a limb with the
witness `19` for it (and no witness for the next fifteen odd numbers) is accepted. -/
theorem runL_accept : runL 1000000 [19] 132259 1 132291 (2 ^ 64) = true := by decide +kernel

/-- Negative control: the same limb with the witness `5`, which divides neither `132259` nor
`132259 ^ 2 + 132259 + 1`, is rejected. -/
theorem runL_reject : runL 1000000 [5] 132259 1 132291 (2 ^ 64) = false := by decide +kernel

end RestrainedElevenCheck

end OddPerfect

#print axioms OddPerfect.RestrainedElevenCheck.fac_nonneg
#print axioms OddPerfect.RestrainedElevenCheck.cert_trans
#print axioms OddPerfect.RestrainedElevenCheck.wit_sound
#print axioms OddPerfect.RestrainedElevenCheck.div_le_cdiv
#print axioms OddPerfect.RestrainedElevenCheck.fac_step
#print axioms OddPerfect.RestrainedElevenCheck.runLimb_sound
#print axioms OddPerfect.RestrainedElevenCheck.runL_sound
#print axioms OddPerfect.RestrainedElevenCheck.runL_accept
#print axioms OddPerfect.RestrainedElevenCheck.runL_reject
