import OddPerfect.Phi3

/-!
# Values `13^a · r^b` of `t^2 + t + 1`

For every `r < 144` with `r ≡ 1 (mod 3)`, `r ≠ 13` and `r ≠ 133`, and every `a < 18`, `b < 24`
with `13^a · r^b < 10^20`, the number `4 · 13^a · r^b - 3` is not the square of `2t + 1` for any
`t ≥ 10` except when `t` is even, `5 ∣ t` or `t = 29`. The check computes an integer square root
by Newton iteration and verifies it; the table is decided by the kernel.

Whether this statement is new was not verified.
-/

namespace OddPerfect

namespace TwoExceptionFourCheck

/-- Newton iteration for the integer square root, with fuel. -/
def rootFuel : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | f + 1, n, x => if (x + n / x) / 2 < x then rootFuel f n ((x + n / x) / 2) else x

/-- A candidate integer square root. -/
def isq (n : ℕ) : ℕ := rootFuel 200 n n

/-- `z` is not `(2t+1)^2` with `t ≥ 10` unless `t` is even, `5 ∣ t` or `t = 29`. -/
def okZ (z : ℕ) : Bool :=
  let s := isq z
  s * s ≤ z && z < (s + 1) * (s + 1) &&
    (s * s != z || s < 21 || ((s - 1) / 2) % 2 == 0 || ((s - 1) / 2) % 5 == 0 || s == 59)

/-- One entry of the table. -/
def entry (r a b : ℕ) : Bool :=
  decide (10 ^ 20 ≤ 13 ^ a * r ^ b) || okZ (4 * (13 ^ a * r ^ b) - 3)

/-- The admissible values of `r`. -/
def rOK (r : ℕ) : Bool := 7 ≤ r && r < 144 && r % 3 == 1 && r != 13 && r != 133

/-- The table. -/
def tab : Bool :=
  (List.range 144).all fun r => !rOK r ||
    (List.range 18).all fun a => (List.range 24).all fun b => entry r a b

set_option maxRecDepth 100000 in
/-- The table holds. Whether this statement is new was not verified. -/
theorem tab_true : tab = true := by decide +kernel

/-- Soundness of the square test. Whether this statement is new was not verified. -/
theorem okZ_sound {t : ℕ} (ht : 10 ≤ t) (h : okZ ((2 * t + 1) * (2 * t + 1)) = true) :
    t % 2 = 0 ∨ t % 5 = 0 ∨ t = 29 := by
  unfold okZ at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  set s := isq ((2 * t + 1) * (2 * t + 1))
  have e1 : s ≤ 2 * t + 1 := Nat.mul_self_le_mul_self_iff.mp h1
  have e2 : 2 * t + 1 < s + 1 := Nat.mul_self_lt_mul_self_iff.mp h2
  have hs : s = 2 * t + 1 := by omega
  rw [hs] at h3
  have hd : (2 * t + 1 - 1) / 2 = t := by omega
  rw [hd] at h3
  omega

/-- The table, read off: a value `t^2 + t + 1 = 13^a · r^b` with `t ≥ 10` and admissible `r`
has `t` even, `5 ∣ t`, `t = 29` or `t^2 + t + 1 ≥ 10^20`. Whether this statement is new was not
verified. -/
theorem root_table {r t a b : ℕ} (hr : rOK r = true) (ht : 10 ≤ t) (ha : a < 18) (hb : b < 24)
    (hz : phi3 t = 13 ^ a * r ^ b) : t % 2 = 0 ∨ t % 5 = 0 ∨ t = 29 ∨ 10 ^ 20 ≤ phi3 t := by
  have hT := tab_true
  simp only [tab, List.all_eq_true, List.mem_range] at hT
  have hr' : r < 144 := by
    simp only [rOK, Bool.and_eq_true, decide_eq_true_eq] at hr
    omega
  have h := hT r hr'
  simp only [hr, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h
  have he := h a ha b hb
  unfold entry at he
  rw [← hz] at he
  simp only [Bool.or_eq_true, decide_eq_true_eq] at he
  rcases he with he | he
  · exact Or.inr (Or.inr (Or.inr he))
  · have hsq : 4 * phi3 t - 3 = (2 * t + 1) * (2 * t + 1) := by
      apply Nat.sub_eq_of_eq_add
      unfold phi3
      ring
    rw [hsq] at he
    rcases okZ_sound ht he with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

end TwoExceptionFourCheck

end OddPerfect

#print axioms OddPerfect.TwoExceptionFourCheck.tab_true
#print axioms OddPerfect.TwoExceptionFourCheck.okZ_sound
#print axioms OddPerfect.TwoExceptionFourCheck.root_table
