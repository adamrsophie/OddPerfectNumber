import OddPerfect.ThreeFreeThreeCore

/-!
# A certificate checker for three exceptional primes

This file defines a Boolean checker, in natural number arithmetic, for case analysis
certificates in the setting of `OddPerfect.ThreeFreeThreeCore`, and proves it sound: a tree of
constraints on `(q, r₁, r₂, r₃)` that passes `treeOK` has no core configuration `Ctx4`
satisfying its root constraints. It also proves that every core configuration, after
relabeling `r₁, r₂, r₃`, satisfies the root constraints of one of 102 class triples.

The final theorem `three_dvd_of_three_exceptions_of_check` is conditional on a Boolean check
`allOK trees = true` for a list of trees supplied by a later data module. This file contains no
certificate data, and the statement with three exceptional primes is not proved here; it is
proved only once a data module establishes the check.

* Constraints. A slot is pinned to a value or free with a residue kind, a lower bound and a
  list of excluded values. A node has four slots for `q, r₁, r₂, r₃`; the class of each `rᵢ`
  is fixed along a tree.
* Leaves. The checker computes least values, the set of small ordinary primes allowed by the
  constraints, a box sum with an exact part decided by an integer square root test, the
  geometric tail, and tests the closing inequality of `Ctx4.close` with `cap = 300`, where the
  tail factor `tailF 300` equals `178802/178801`.
* Trees. A binary split pins one free slot to a value or excludes that value.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace ThreeFreeThree

/-! ## Constraints -/

/-- Residue kinds of a free slot: `q` (`1` modulo 12), `n2` (`2` modulo 3), `big`
(`1` modulo 3). -/
inductive Kind
  | q
  | n2
  | big
  deriving DecidableEq

/-- The residue test of a kind. -/
def Kind.test : Kind → ℕ → Bool
  | .q, x => decide (x % 12 = 1)
  | .n2, x => decide (x % 3 = 2)
  | .big, x => decide (x % 3 = 1)

/-- A slot: pinned to a value, or free with a kind, a lower bound and excluded values. -/
inductive Slot
  | pin (p : ℕ)
  | free (k : Kind) (lb : ℕ) (excl : List ℕ)

/-- The nine classes of the primes `rᵢ`, in class order. -/
inductive Cls
  | c5
  | c7
  | c13
  | c19
  | c31
  | c37
  | c43
  | n2
  | big
  deriving DecidableEq

/-- Classes whose members are sorted by value: `n2` and `big`. -/
def Cls.sortable : Cls → Bool
  | .n2 => true
  | .big => true
  | _ => false

/-- Two `r` slots whose values must increase in slot order. -/
def same (a b : Cls) : Bool := a.sortable && decide (a = b)

/-- The classes of `r₁, r₂, r₃`. -/
abbrev ClassTriple := Cls × Cls × Cls

/-- The constraints of a node, for `q, r₁, r₂, r₃`. -/
structure Node where
  s0 : Slot
  s1 : Slot
  s2 : Slot
  s3 : Slot

/-- The pinned value of a slot, as a list. -/
def Slot.pv : Slot → List ℕ
  | .pin p => [p]
  | .free _ _ _ => []

/-- The pinned values of a node. -/
def Node.pins (nd : Node) : List ℕ := nd.s0.pv ++ nd.s1.pv ++ nd.s2.pv ++ nd.s3.pv

/-- Satisfaction of one slot. -/
def Slot.Sat : Slot → ℕ → Prop
  | .pin p, x => x = p
  | .free k lb ex, x => k.test x = true ∧ lb ≤ x ∧ x ∉ ex

/-- Satisfaction of a node by `(q, r₁, r₂, r₃)`, including the order inside `n2` and `big`. -/
def Sat (cl : ClassTriple) (nd : Node) (q r₁ r₂ r₃ : ℕ) : Prop :=
  nd.s0.Sat q ∧ nd.s1.Sat r₁ ∧ nd.s2.Sat r₂ ∧ nd.s3.Sat r₃ ∧
    (same cl.1 cl.2.1 = true → r₁ < r₂) ∧ (same cl.2.1 cl.2.2 = true → r₂ < r₃) ∧
    (same cl.1 cl.2.2 = true → r₁ < r₃)

/-! ## Least values -/

/-- Upward scan for the first value passing the residue test, not excluded and not pinned;
returns `start` when the fuel runs out. -/
def scan (k : Kind) (ex P : List ℕ) (start : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => start
  | f + 1, x => if k.test x && !decide (x ∈ ex) && !decide (x ∈ P) then x
      else scan k ex P start f (x + 1)

/-- The fuel of the least value scan. -/
def fuelLV : ℕ := 1000

/-- The least value of a slot, given the start forced by an earlier slot of the same class. -/
def Slot.lv (P : List ℕ) : Slot → ℕ → ℕ
  | .pin p, _ => p
  | .free k lb ex, st => scan k ex P (max lb st) fuelLV (max lb st)

/-- The least values of the four slots, in slot order. -/
def leastVals (cl : ClassTriple) (nd : Node) : ℕ × ℕ × ℕ × ℕ :=
  let P := nd.pins
  let m1 := nd.s1.lv P 0
  let m2 := nd.s2.lv P (if same cl.1 cl.2.1 then m1 + 1 else 0)
  (nd.s0.lv P 0, m1, m2,
    nd.s3.lv P (if same cl.2.1 cl.2.2 then m2 + 1 else if same cl.1 cl.2.2 then m1 + 1 else 0))

/-! ## Small ordinary primes -/

/-- Acceptance of a number `f` by a slot with least value `m`. -/
def Slot.acc (P : List ℕ) (m f : ℕ) : Slot → Bool
  | .pin p => decide (f = p)
  | .free k _ ex => k.test f && decide (m ≤ f) && !decide (f ∈ ex) && !decide (f ∈ P)

/-- Acceptance by at least one slot of the node. -/
def anyAcc (nd : Node) (m : ℕ × ℕ × ℕ × ℕ) (f : ℕ) : Bool :=
  nd.s0.acc nd.pins m.1 f || nd.s1.acc nd.pins m.2.1 f || nd.s2.acc nd.pins m.2.2.1 f ||
    nd.s3.acc nd.pins m.2.2.2 f

/-- The primes `s ≡ 2 (mod 3)` with `5 ≤ s < 300`, each with the prime factors of
`1 + s + s^2`. -/
def table : List (ℕ × List ℕ) :=
  [(5, [31]), (11, [7, 19]), (17, [307]), (23, [7, 79]), (29, [13, 67]), (41, [1723]),
    (47, [37, 61]), (53, [7, 409]), (59, [3541]), (71, [5113]), (83, [19, 367]),
    (89, [8011]), (101, [10303]), (107, [7, 13, 127]), (113, [13, 991]), (131, [17293]),
    (137, [7, 37, 73]), (149, [7, 31, 103]), (167, [28057]), (173, [30103]),
    (179, [7, 4603]), (191, [7, 13, 31]), (197, [19, 2053]), (227, [73, 709]),
    (233, [7, 7789]), (239, [19, 3019]), (251, [43, 1471]), (257, [61, 1087]),
    (263, [7, 13, 109]), (269, [13, 37, 151]), (281, [109, 727]), (293, [86143])]

/-- The small set of a node: table primes that are not pinned and all of whose factors are
accepted by some slot. -/
def smallList (nd : Node) (m : ℕ × ℕ × ℕ × ℕ) : List ℕ :=
  (table.filter fun e => !decide (e.1 ∈ nd.pins) && e.2.all (anyAcc nd m)).map Prod.fst

/-! ## Weights and the box -/

/-- The four weights of a leaf, as numerator and denominator pairs. -/
structure Wts where
  w0 : ℕ × ℕ
  w1 : ℕ × ℕ
  w2 : ℕ × ℕ
  w3 : ℕ × ℕ

/-- A slot known to have value `2` modulo 3. -/
def Slot.known2 : Slot → Bool
  | .pin p => decide (p % 3 = 2)
  | .free .n2 _ _ => true
  | .free _ _ _ => false

/-- Admissibility of a weight `n/d` for a slot with least value `m`. -/
def admissible (s : Slot) (m : ℕ) (w : ℕ × ℕ) : Bool :=
  (decide (w.1 = 0) && decide (0 < w.2) && s.known2) ||
    (decide (0 < w.1) && decide (w.1 < w.2) && decide (w.2 * w.2 ≤ w.1 * w.1 * m))

/-- Whether a slot is pinned. -/
def Slot.isPin : Slot → Bool
  | .pin _ => true
  | .free _ _ _ => false

/-- The pinned value of a slot, or 1. -/
def Slot.pinv : Slot → ℕ
  | .pin p => p
  | .free _ _ _ => 1

/-- A coordinate of an exact vector: zero, or at a pinned slot of positive weight. -/
def exOK (s : Slot) (w : ℕ × ℕ) (e : ℕ) : Bool := decide (e = 0) || (s.isPin && decide (w.1 ≠ 0))

/-- Newton iteration for a candidate integer square root, with fuel. -/
def nsqrt : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | f + 1, m, x => if (x + m / x) / 2 < x then nsqrt f m ((x + m / x) / 2) else x

/-- The fuel of the square root iteration. -/
def fuelSq : ℕ := 200

/-- The capped weight factor `n^e * d^(4 - e)` of one coordinate. -/
def capF (w : ℕ × ℕ) (e : ℕ) : ℕ := w.1 ^ e * w.2 ^ (4 - e)

/-- The common denominator part `∏ dᵢ^4`. -/
def Wts.D4 (w : Wts) : ℕ := w.w0.2 ^ 4 * w.w1.2 ^ 4 * w.w2.2 ^ 4 * w.w3.2 ^ 4

/-- The square root test for `m = 4 n - 3`, starting the iteration at `g`: a square `(2s + 1)^2`
gives `(s + 1)/s^2` when `s ≥ 300` and `0` otherwise; a certified non square gives `0`; any
other outcome gives `none`. -/
def sqStep (m g : ℕ) : Option (ℕ × ℕ) :=
  let r := nsqrt fuelSq m g
  if r * r = m then
    if (r - 1) / 2 < 300 then some (0, 1) else some ((r - 1) / 2 + 1, (r - 1) / 2 * ((r - 1) / 2))
  else if r * r < m ∧ m < (r + 1) * (r + 1) then some (0, 1) else none

/-- The bound for one box vector, as a fraction; `none` when the square root test fails. -/
def step (nd : Node) (w : Wts) (D4 : ℕ) (v : ℕ × ℕ × ℕ × ℕ) : Option (ℕ × ℕ) :=
  if v.1 % 2 = 0 ∧ v.2.1 % 2 = 0 ∧ v.2.2.1 % 2 = 0 ∧ v.2.2.2 % 2 = 0 then some (0, 1)
  else if exOK nd.s0 w.w0 v.1 && exOK nd.s1 w.w1 v.2.1 && exOK nd.s2 w.w2 v.2.2.1 &&
      exOK nd.s3 w.w3 v.2.2.2 then
    sqStep (4 * (nd.s0.pinv ^ v.1 * nd.s1.pinv ^ v.2.1 * nd.s2.pinv ^ v.2.2.1 *
      nd.s3.pinv ^ v.2.2.2) - 3)
      (2 * (nd.s0.pinv ^ ((v.1 + 1) / 2) * nd.s1.pinv ^ ((v.2.1 + 1) / 2) *
        nd.s2.pinv ^ ((v.2.2.1 + 1) / 2) * nd.s3.pinv ^ ((v.2.2.2 + 1) / 2)))
  else some (90601 * min D4 (300 * (capF w.w0 v.1 * capF w.w1 v.2.1 * capF w.w2 v.2.2.1 *
    capF w.w3 v.2.2.2)), 27000000 * D4)

/-- The box `[0, 5)^4` as a list. -/
def box : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range 5).flatMap fun a => (List.range 5).flatMap fun b =>
    (List.range 5).flatMap fun c => (List.range 5).map fun d => (a, b, c, d)

/-- Addition of fractions, keeping a common denominator when there is one. -/
def padd (x y : ℕ × ℕ) : ℕ × ℕ :=
  if x.2 = y.2 then (x.1 + y.1, x.2)
  else if x.1 = 0 then y
  else if y.1 = 0 then x
  else (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

/-- The sum of the bounds over a list of vectors, or `none` if one test fails. -/
def accum (f : ℕ × ℕ × ℕ × ℕ → Option (ℕ × ℕ)) : List (ℕ × ℕ × ℕ × ℕ) → Option (ℕ × ℕ)
  | [] => some (0, 1)
  | v :: l => match f v, accum f l with
    | some x, some y => some (padd x y)
    | _, _ => none

/-- The tail `kk 300 * tl4 α β γ δ 5` as a fraction. -/
def tailP (w : Wts) : ℕ × ℕ :=
  (90601 * (w.w0.1 ^ 5 * (w.w1.2 ^ 5 * w.w2.2 ^ 5 * w.w3.2 ^ 5) +
      w.w1.1 ^ 5 * (w.w0.2 ^ 5 * w.w2.2 ^ 5 * w.w3.2 ^ 5) +
      w.w2.1 ^ 5 * (w.w0.2 ^ 5 * w.w1.2 ^ 5 * w.w3.2 ^ 5) +
      w.w3.1 ^ 5 * (w.w0.2 ^ 5 * w.w1.2 ^ 5 * w.w2.2 ^ 5)) * (w.w0.2 * w.w1.2 * w.w2.2 * w.w3.2),
    90000 * (w.w0.2 ^ 5 * w.w1.2 ^ 5 * w.w2.2 ^ 5 * w.w3.2 ^ 5) *
      ((w.w0.2 - w.w0.1) * (w.w1.2 - w.w1.1) * (w.w2.2 - w.w2.1) * (w.w3.2 - w.w3.1)))

/-- The closing test `ρ₀ ρ₁ ρ₂ ρ₃ (∏ s/(s - 1)) (178802/178801) / (1 - X) ≤ 2` in natural
numbers. -/
def finalOK (m : ℕ × ℕ × ℕ × ℕ) (C : List ℕ) (X : ℕ × ℕ) : Bool :=
  decide (m.1 * m.2.1 * m.2.2.1 * m.2.2.2 * C.prod * X.2 * 178802 ≤
    2 * ((m.1 - 1) * (m.2.1 - 1) * (m.2.2.1 - 1) * (m.2.2.2 - 1)) *
      (C.map fun s => s - 1).prod * (X.2 - X.1) * 178801)

/-- The check of one leaf. -/
def leafOK (cl : ClassTriple) (nd : Node) (w : Wts) : Bool :=
  let m := leastVals cl nd
  admissible nd.s0 m.1 w.w0 && admissible nd.s1 m.2.1 w.w1 && admissible nd.s2 m.2.2.1 w.w2 &&
    admissible nd.s3 m.2.2.2 w.w3 && decide (2 ≤ m.1 ∧ 2 ≤ m.2.1 ∧ 2 ≤ m.2.2.1 ∧ 2 ≤ m.2.2.2) &&
    match accum (step nd w w.D4) box with
    | none => false
    | some B => decide ((padd B (tailP w)).1 < (padd B (tailP w)).2) &&
        finalOK m (smallList nd m) (padd B (tailP w))

/-! ## Trees -/

/-- A binary split tree. -/
inductive Tree
  | leaf (w : Wts)
  | split (i p : ℕ) (pinned rest : Tree)

/-- Raising the lower bound of a free slot above `p`. -/
def Slot.bump (p : ℕ) : Slot → Slot
  | .pin a => .pin a
  | .free k lb ex => .free k (max lb (p + 1)) ex

/-- Excluding `p` from a free slot. -/
def Slot.addEx (p : ℕ) : Slot → Slot
  | .pin a => .pin a
  | .free k lb ex => .free k lb (p :: ex)

/-- Whether a slot is free. -/
def Slot.isFree : Slot → Bool
  | .pin _ => false
  | .free _ _ _ => true

/-- The slot with a given index. -/
def Node.get (nd : Node) : ℕ → Slot
  | 0 => nd.s0
  | 1 => nd.s1
  | 2 => nd.s2
  | _ => nd.s3

/-- The child where slot `i` is pinned to `p`; later slots of the same sorted class get the
lower bound `p + 1`. -/
def pinChild (cl : ClassTriple) (nd : Node) (p : ℕ) : ℕ → Node
  | 0 => ⟨.pin p, nd.s1, nd.s2, nd.s3⟩
  | 1 => ⟨nd.s0, .pin p, if same cl.1 cl.2.1 then nd.s2.bump p else nd.s2,
      if same cl.1 cl.2.2 then nd.s3.bump p else nd.s3⟩
  | 2 => ⟨nd.s0, nd.s1, .pin p, if same cl.2.1 cl.2.2 then nd.s3.bump p else nd.s3⟩
  | _ => ⟨nd.s0, nd.s1, nd.s2, .pin p⟩

/-- The child where `p` is excluded from slot `i`. -/
def restChild (nd : Node) (p : ℕ) : ℕ → Node
  | 0 => ⟨nd.s0.addEx p, nd.s1, nd.s2, nd.s3⟩
  | 1 => ⟨nd.s0, nd.s1.addEx p, nd.s2, nd.s3⟩
  | 2 => ⟨nd.s0, nd.s1, nd.s2.addEx p, nd.s3⟩
  | _ => ⟨nd.s0, nd.s1, nd.s2, nd.s3.addEx p⟩

/-- The check of a tree from the constraints of its root. -/
def treeOK (cl : ClassTriple) (nd : Node) : Tree → Bool
  | .leaf w => leafOK cl nd w
  | .split i p t₁ t₂ => decide (i < 4) && (nd.get i).isFree && treeOK cl (pinChild cl nd p i) t₁ &&
      treeOK cl (restChild nd p i) t₂

/-- The root slot of a class. -/
def Cls.root : Cls → Slot
  | .c5 => .pin 5
  | .c7 => .pin 7
  | .c13 => .pin 13
  | .c19 => .pin 19
  | .c31 => .pin 31
  | .c37 => .pin 37
  | .c43 => .pin 43
  | .n2 => .free .n2 11 []
  | .big => .free .big 61 []

/-- The root constraints of a class triple. -/
def rootNode (cl : ClassTriple) : Node :=
  ⟨.free .q 13 [], cl.1.root, cl.2.1.root, cl.2.2.root⟩

/-! ## Soundness: fractions and sums -/

/-- The rational value of a fraction pair. -/
def val (x : ℕ × ℕ) : ℚ := (x.1 : ℚ) / x.2

/-- Fraction values are nonnegative. -/
theorem val_nonneg (x : ℕ × ℕ) : 0 ≤ val x := by unfold val; positivity

private theorem padd_pos {x y : ℕ × ℕ} (hx : 0 < x.2) (hy : 0 < y.2) : 0 < (padd x y).2 := by
  unfold padd
  split_ifs <;> simp only [hx, hy, Nat.mul_pos hx hy]

private theorem val_padd {x y : ℕ × ℕ} (hx : 0 < x.2) (hy : 0 < y.2) :
    val (padd x y) = val x + val y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only at hx hy
  have hb : (b : ℚ) ≠ 0 := by positivity
  have hd : (d : ℚ) ≠ 0 := by positivity
  unfold padd val
  split_ifs with h1 h2 h3
  · simp only at h1; subst h1; push_cast; ring
  · simp only at h2; subst h2; simp
  · simp only at h3; subst h3; simp
  · push_cast; field_simp

private theorem accum_spec (f : ℕ × ℕ × ℕ × ℕ → Option (ℕ × ℕ))
    (hf : ∀ v x, f v = some x → 0 < x.2) :
    ∀ (l : List (ℕ × ℕ × ℕ × ℕ)) (P : ℕ × ℕ), accum f l = some P →
      0 < P.2 ∧ val P = (l.map fun v => val ((f v).getD (0, 1))).sum ∧
        ∀ v ∈ l, ∃ x, f v = some x
  | [], P, h => by
    simp only [accum, Option.some.injEq] at h
    subst h
    simp [val]
  | v :: l, P, h => by
    simp only [accum] at h
    rcases hv : f v with _ | x <;> rcases hl : accum f l with _ | y <;>
      simp only [hv, hl, reduceCtorEq, Option.some.injEq] at h
    subst h
    obtain ⟨h1, h2, h3⟩ := accum_spec f hf l y hl
    refine ⟨padd_pos (hf v x hv) h1, ?_, ?_⟩
    · rw [val_padd (hf v x hv) h1, List.map_cons, List.sum_cons, hv, ← h2]
      rfl
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨x, hv⟩
      · exact h3 u hu

private theorem sum_range_list (n : ℕ) (f : ℕ → ℚ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

private theorem sum_flatMap_map {α β : Type} (l : List α) (F : α → List β) (G : β → ℚ) :
    ((l.flatMap F).map G).sum = (l.map fun a => ((F a).map G).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih]; simp

private theorem gsum_box (g : ℕ × ℕ × ℕ × ℕ → ℚ)
    (hz : ∀ v : ℕ × ℕ × ℕ × ℕ, v.1 % 2 = 0 → v.2.1 % 2 = 0 → v.2.2.1 % 2 = 0 → v.2.2.2 % 2 = 0 →
      g v = 0) :
    gsum g 5 = (box.map g).sum := by
  have h : ∀ a b c d : ℕ,
      (if Even a ∧ Even b ∧ Even c ∧ Even d then 0 else g (a, b, c, d)) = g (a, b, c, d) := by
    intro a b c d
    split_ifs with hv
    · simp only [Nat.even_iff] at hv
      exact (hz (a, b, c, d) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2).symm
    · rfl
  simp only [gsum, h, sum_range_list, box, sum_flatMap_map, List.map_map, Function.comp_def]

private theorem mem_box {v : ℕ × ℕ × ℕ × ℕ} (h1 : v.1 < 5) (h2 : v.2.1 < 5) (h3 : v.2.2.1 < 5)
    (h4 : v.2.2.2 < 5) : v ∈ box := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [box, List.mem_flatMap, List.mem_map, List.mem_range] at *
  exact ⟨a, h1, b, h2, c, h3, d, h4, rfl⟩

/-! ## Soundness: the table -/

private theorem table_factors : ∀ e ∈ table, ∀ f ∈ e.2, f.Prime ∧ f ∣ 1 + e.1 + e.1 ^ 2 := by
  simp only [table, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

private theorem table_keys : ∀ e ∈ table, 5 ≤ e.1 := by decide

private theorem table_cover : ∀ s < 300, s % 3 = 2 → 5 ≤ s →
    s ∈ table.map Prod.fst ∨ ∃ d ∈ [2, 5, 7, 11, 13, 17], d < s ∧ s % d = 0 := by
  decide +kernel

private theorem table_complete {s : ℕ} (hs : s.Prime) (h3 : s % 3 = 2) (h5 : 5 ≤ s)
    (h300 : s < 300) : ∃ fs, (s, fs) ∈ table := by
  rcases table_cover s h300 h3 h5 with h | ⟨d, hd, hds, hmod⟩
  · obtain ⟨⟨a, fs⟩, he, rfl⟩ := List.mem_map.mp h
    exact ⟨fs, he⟩
  · have h2 : 2 ≤ d := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega
    rcases hs.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

/-! ## Soundness: least values and acceptance -/

private theorem scan_le (k : Kind) (ex P : List ℕ) (start : ℕ) :
    ∀ (f x y : ℕ), start ≤ x → x ≤ y → k.test y = true → y ∉ ex → y ∉ P →
      scan k ex P start f x ≤ y
  | 0, x, y, h1, h2, _, _, _ => h1.trans h2
  | f + 1, x, y, h1, h2, ht, he, hP => by
    unfold scan
    split_ifs with hc
    · exact h2
    · have hxy : x ≠ y := by
        rintro rfl
        simp [ht, he, hP] at hc
      exact scan_le k ex P start f (x + 1) y (by omega) (by omega) ht he hP

private theorem pv_free {s : Slot} (h : s.isFree = true) : s.pv = [] := by
  cases s <;> simp_all [Slot.isFree, Slot.pv]

private theorem mem_pv {s : Slot} {x y : ℕ} (hy : y ∈ s.pv) (hs : s.Sat x) : y = x := by
  cases s with
  | pin p => simp only [Slot.pv, List.mem_singleton] at hy; simp only [Slot.Sat] at hs; omega
  | free k lb ex => simp [Slot.pv] at hy

private theorem lv_le {s : Slot} {P : List ℕ} {st x : ℕ} (hs : s.Sat x) (hst : st ≤ x)
    (hP : s.isFree = true → x ∉ P) : s.lv P st ≤ x := by
  cases s with
  | pin p => simp only [Slot.Sat] at hs; simp [Slot.lv, hs]
  | free k lb ex =>
    obtain ⟨ht, hlb, hex⟩ := hs
    exact scan_le k ex P _ _ _ x le_rfl (max_le hlb hst) ht hex (hP rfl)

/-- Pairwise distinct values of the four slots. -/
private def Dist (a0 a1 a2 a3 : ℕ) : Prop :=
  a0 ≠ a1 ∧ a0 ≠ a2 ∧ a0 ≠ a3 ∧ a1 ≠ a2 ∧ a1 ≠ a3 ∧ a2 ≠ a3

private theorem mem_pins {nd : Node} {a0 a1 a2 a3 y : ℕ} (h0 : nd.s0.Sat a0) (h1 : nd.s1.Sat a1)
    (h2 : nd.s2.Sat a2) (h3 : nd.s3.Sat a3) (hy : y ∈ nd.pins) :
    (y = a0 ∧ nd.s0.isFree = false) ∨ (y = a1 ∧ nd.s1.isFree = false) ∨
      (y = a2 ∧ nd.s2.isFree = false) ∨ (y = a3 ∧ nd.s3.isFree = false) := by
  have key : ∀ (s : Slot) (x : ℕ), s.Sat x → y ∈ s.pv → y = x ∧ s.isFree = false :=
    fun s x hs hm => ⟨mem_pv hm hs, by cases s <;> simp_all [Slot.pv, Slot.isFree]⟩
  simp only [Node.pins, List.mem_append] at hy
  rcases hy with ((hy | hy) | hy) | hy
  · exact Or.inl (key _ _ h0 hy)
  · exact Or.inr (Or.inl (key _ _ h1 hy))
  · exact Or.inr (Or.inr (Or.inl (key _ _ h2 hy)))
  · exact Or.inr (Or.inr (Or.inr (key _ _ h3 hy)))

private theorem not_mem_pins {cl : ClassTriple} {nd : Node} {a0 a1 a2 a3 : ℕ}
    (hS : Sat cl nd a0 a1 a2 a3) (hd : Dist a0 a1 a2 a3) :
    (nd.s0.isFree = true → a0 ∉ nd.pins) ∧ (nd.s1.isFree = true → a1 ∉ nd.pins) ∧
      (nd.s2.isFree = true → a2 ∉ nd.pins) ∧ (nd.s3.isFree = true → a3 ∉ nd.pins) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := hS
  obtain ⟨d01, d02, d03, d12, d13, d23⟩ := hd
  refine ⟨fun hf hm => ?_, fun hf hm => ?_, fun hf hm => ?_, fun hf hm => ?_⟩ <;>
  · rcases mem_pins h0 h1 h2 h3 hm with ⟨e, f⟩ | ⟨e, f⟩ | ⟨e, f⟩ | ⟨e, f⟩ <;>
      first | (rw [hf] at f; exact absurd f (by decide)) | omega

private theorem least_le {cl : ClassTriple} {nd : Node} {a0 a1 a2 a3 : ℕ}
    (hS : Sat cl nd a0 a1 a2 a3) (hd : Dist a0 a1 a2 a3) :
    (leastVals cl nd).1 ≤ a0 ∧ (leastVals cl nd).2.1 ≤ a1 ∧ (leastVals cl nd).2.2.1 ≤ a2 ∧
      (leastVals cl nd).2.2.2 ≤ a3 := by
  have hP := not_mem_pins hS hd
  obtain ⟨h0, h1, h2, h3, o12, o23, o13⟩ := hS
  have m1 : nd.s1.lv nd.pins 0 ≤ a1 := lv_le h1 (Nat.zero_le _) hP.2.1
  have m2 : nd.s2.lv nd.pins (if same cl.1 cl.2.1 then nd.s1.lv nd.pins 0 + 1 else 0) ≤ a2 := by
    refine lv_le h2 ?_ hP.2.2.1
    split_ifs with h
    · have := o12 h; omega
    · exact Nat.zero_le _
  refine ⟨lv_le h0 (Nat.zero_le _) hP.1, m1, m2, lv_le h3 ?_ hP.2.2.2⟩
  by_cases h : same cl.2.1 cl.2.2 = true
  · rw [if_pos h]; have := o23 h; omega
  · rw [if_neg h]
    by_cases h' : same cl.1 cl.2.2 = true
    · rw [if_pos h']; have := o13 h'; omega
    · rw [if_neg h']; exact Nat.zero_le _

private theorem acc_of {s : Slot} {P : List ℕ} {m x : ℕ} (hs : s.Sat x) (hm : m ≤ x)
    (hP : s.isFree = true → x ∉ P) : s.acc P m x = true := by
  cases s with
  | pin p => simpa [Slot.acc, Slot.Sat] using hs
  | free k lb ex =>
    obtain ⟨ht, -, hex⟩ := hs
    simp [Slot.acc, ht, hm, hex, hP rfl]

/-! ## Soundness: the small set -/

private theorem mem_smallList {cl : ClassTriple} {nd : Node} {N q r₁ r₂ r₃ : ℕ}
    (c : Ctx4 N q r₁ r₂ r₃) (hS : Sat cl nd q r₁ r₂ r₃) {s : ℕ} (hs : s ∈ ord4 N q r₁ r₂ r₃)
    (h300 : s < 300) : s ∈ smallList nd (leastVals cl nd) := by
  have hd : Dist q r₁ r₂ r₃ := ⟨c.h1q.symm, c.h2q.symm, c.h3q.symm, c.h12, c.h13, c.h23⟩
  have hP := not_mem_pins hS hd
  have hm := least_le hS hd
  obtain ⟨h0, h1, h2, h3, -⟩ := hS
  obtain ⟨hsp, -, h5, hs3⟩ := c.ord_facts hs
  obtain ⟨fs, hfs⟩ := table_complete hsp hs3 h5 h300
  obtain ⟨-, hne0, hne1, hne2, hne3⟩ := mem_ord4.mp hs
  simp only [smallList, List.mem_map, List.mem_filter]
  refine ⟨(s, fs), ⟨hfs, ?_⟩, rfl⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
  refine ⟨fun hm' => ?_, fun f hf => ?_⟩
  · rcases mem_pins h0 h1 h2 h3 hm' with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> contradiction
  · obtain ⟨hfp, hfd⟩ := table_factors _ hfs f hf
    rcases (c.tgt hs hfp hfd).1 with rfl | rfl | rfl | rfl
    · simp [anyAcc, acc_of h0 hm.1 hP.1]
    · simp [anyAcc, acc_of h1 hm.2.1 hP.2.1]
    · simp [anyAcc, acc_of h2 hm.2.2.1 hP.2.2.1]
    · simp [anyAcc, acc_of h3 hm.2.2.2 hP.2.2.2]

private theorem smallList_ge {nd : Node} {m : ℕ × ℕ × ℕ × ℕ} : ∀ s ∈ smallList nd m, 5 ≤ s := by
  intro s hs
  simp only [smallList, List.mem_map, List.mem_filter] at hs
  obtain ⟨e, ⟨he, -⟩, rfl⟩ := hs
  exact table_keys e he

private theorem prod_toFinset_le (l : List ℕ) (hl : ∀ s ∈ l, 2 ≤ s) :
    ∏ s ∈ l.toFinset, rv s ≤ (l.map rv).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun s hs => hl s (List.mem_cons_of_mem a hs))
    have ha := one_le_rv (hl a (by simp))
    have h0 : 0 ≤ ∏ s ∈ l.toFinset, rv s := Finset.prod_nonneg fun s hs =>
      zero_le_one.trans (one_le_rv (hl s (List.mem_cons_of_mem a (List.mem_toFinset.mp hs))))
    rw [List.toFinset_cons, List.map_cons, List.prod_cons]
    by_cases hm : a ∈ l.toFinset
    · rw [Finset.insert_eq_of_mem hm]; nlinarith
    · rw [Finset.prod_insert hm]; exact mul_le_mul_of_nonneg_left ih' (by linarith)

private theorem prod_rv_list (l : List ℕ) (hl : ∀ s ∈ l, 1 ≤ s) : (l.map rv).prod =
    ((l.prod : ℕ) : ℚ) / (((l.map fun s => s - 1).prod : ℕ) : ℚ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : 1 ≤ a := hl a (by simp)
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul,
      ih (fun s hs => hl s (List.mem_cons_of_mem a hs)), rv, Nat.cast_sub ha, Nat.cast_one]
    rw [div_mul_div_comm]

/-! ## Soundness: weights and the box terms -/

private theorem weight_ok {s : Slot} {m x : ℕ} {w : ℕ × ℕ} (hs : s.Sat x) (hm : m ≤ x)
    (ha : admissible s m w = true) :
    0 < w.2 ∧ w.1 < w.2 ∧ 0 ≤ (w.1 : ℚ) / w.2 ∧ (w.1 : ℚ) / w.2 < 1 ∧
      (1 ≤ ((w.1 : ℚ) / w.2) ^ 2 * x ∨ x % 3 = 2) := by
  obtain ⟨n, d⟩ := w
  simp only [admissible, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
  rcases ha with ⟨⟨hn, hd⟩, hk⟩ | ⟨⟨hn, hnd⟩, hsq⟩
  · subst hn
    refine ⟨hd, hd, by simp, by simp, Or.inr ?_⟩
    cases s with
    | pin p => simp only [Slot.known2, decide_eq_true_eq] at hk; simp only [Slot.Sat] at hs; omega
    | free k lb ex =>
      cases k <;> simp_all [Slot.known2, Slot.Sat, Kind.test]
  · have hd : 0 < d := by omega
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    refine ⟨hd, hnd, by positivity, ?_, Or.inl ?_⟩
    · rw [div_lt_one hdq]; exact_mod_cast hnd
    · have h1 : d * d ≤ n * n * x := hsq.trans (Nat.mul_le_mul_left _ hm)
      have h1' : (d : ℚ) * d ≤ n * n * x := by exact_mod_cast h1
      rw [div_pow, div_mul_eq_mul_div, one_le_div (by positivity)]
      nlinarith

private theorem rho_le {m x : ℕ} (hm : 2 ≤ m) (hx : m ≤ x) :
    (x : ℚ) / (x - 1) ≤ (m : ℚ) / (m - 1) := by
  have h1 : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have h2 : (m : ℚ) ≤ x := by exact_mod_cast hx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private theorem capF_cast {w : ℕ × ℕ} {e : ℕ} (he : e ≤ 4) (hd : 0 < w.2) :
    (capF w e : ℚ) = ((w.1 : ℚ) / w.2) ^ e * (w.2 : ℚ) ^ 4 := by
  have hd' : (w.2 : ℚ) ≠ 0 := by positivity
  have h4 : (w.2 : ℚ) ^ 4 = (w.2 : ℚ) ^ e * (w.2 : ℚ) ^ (4 - e) := by
    rw [← pow_add]; congr 1; omega
  unfold capF
  push_cast
  rw [h4, div_pow]
  field_simp

private theorem val_cap (w : Wts) (v : ℕ × ℕ × ℕ × ℕ) (h1 : v.1 ≤ 4) (h2 : v.2.1 ≤ 4)
    (h3 : v.2.2.1 ≤ 4) (h4 : v.2.2.2 ≤ 4) (d0 : 0 < w.w0.2) (d1 : 0 < w.w1.2) (d2 : 0 < w.w2.2)
    (d3 : 0 < w.w3.2) :
    val (90601 * min w.D4 (300 * (capF w.w0 v.1 * capF w.w1 v.2.1 * capF w.w2 v.2.2.1 *
      capF w.w3 v.2.2.2)), 27000000 * w.D4) =
    kk 300 * min (1 / ((300 : ℕ) : ℚ)) (wt4 ((w.w0.1 : ℚ) / w.w0.2) ((w.w1.1 : ℚ) / w.w1.2)
      ((w.w2.1 : ℚ) / w.w2.2) ((w.w3.1 : ℚ) / w.w3.2) v) := by
  have hDe : (w.D4 : ℚ) = (w.w0.2 : ℚ) ^ 4 * (w.w1.2 : ℚ) ^ 4 * (w.w2.2 : ℚ) ^ 4 *
      (w.w3.2 : ℚ) ^ 4 := by
    unfold Wts.D4; push_cast; ring
  have hD : (0 : ℚ) < w.D4 := by rw [hDe]; positivity
  unfold val
  simp only
  push_cast
  rw [capF_cast h1 d0, capF_cast h2 d1, capF_cast h3 d2, capF_cast h4 d3]
  set wt := wt4 ((w.w0.1 : ℚ) / w.w0.2) ((w.w1.1 : ℚ) / w.w1.2) ((w.w2.1 : ℚ) / w.w2.2)
    ((w.w3.1 : ℚ) / w.w3.2) v with hwt
  have e0 : 300 * (((w.w0.1 : ℚ) / w.w0.2) ^ v.1 * (w.w0.2 : ℚ) ^ 4 *
      (((w.w1.1 : ℚ) / w.w1.2) ^ v.2.1 * (w.w1.2 : ℚ) ^ 4) *
      (((w.w2.1 : ℚ) / w.w2.2) ^ v.2.2.1 * (w.w2.2 : ℚ) ^ 4) *
      (((w.w3.1 : ℚ) / w.w3.2) ^ v.2.2.2 * (w.w3.2 : ℚ) ^ 4)) = 300 * (w.D4 : ℚ) * wt := by
    rw [hDe, hwt]; unfold wt4; ring
  have e1 : min (w.D4 : ℚ) (300 * (w.D4 : ℚ) * wt) = 300 * w.D4 * min (1 / 300) wt := by
    rw [mul_min_of_nonneg _ _ (by positivity)]
    congr 1
    field_simp
  rw [e0, e1, kk]
  field_simp
  ring

private theorem val_tail (w : Wts) (h0 : w.w0.1 < w.w0.2) (h1 : w.w1.1 < w.w1.2)
    (h2 : w.w2.1 < w.w2.2) (h3 : w.w3.1 < w.w3.2) :
    0 < (tailP w).2 ∧ val (tailP w) = kk 300 * tl4 ((w.w0.1 : ℚ) / w.w0.2)
      ((w.w1.1 : ℚ) / w.w1.2) ((w.w2.1 : ℚ) / w.w2.2) ((w.w3.1 : ℚ) / w.w3.2) 5 := by
  obtain ⟨⟨n0, d0⟩, ⟨n1, d1⟩, ⟨n2, d2⟩, ⟨n3, d3⟩⟩ := w
  simp only at h0 h1 h2 h3 ⊢
  refine ⟨?_, ?_⟩
  · unfold tailP
    simp only
    have a0 := Nat.sub_pos_of_lt h0
    have a1 := Nat.sub_pos_of_lt h1
    have a2 := Nat.sub_pos_of_lt h2
    have a3 := Nat.sub_pos_of_lt h3
    have p0 : 0 < d0 := by omega
    have p1 : 0 < d1 := by omega
    have p2 : 0 < d2 := by omega
    have p3 : 0 < d3 := by omega
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by positivity))
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos a0 a1) a2) a3)
  have e0 : (0 : ℚ) < (d0 : ℚ) - n0 := by
    have : (n0 : ℚ) < d0 := by exact_mod_cast h0
    linarith
  have e1 : (0 : ℚ) < (d1 : ℚ) - n1 := by
    have : (n1 : ℚ) < d1 := by exact_mod_cast h1
    linarith
  have e2 : (0 : ℚ) < (d2 : ℚ) - n2 := by
    have : (n2 : ℚ) < d2 := by exact_mod_cast h2
    linarith
  have e3 : (0 : ℚ) < (d3 : ℚ) - n3 := by
    have : (n3 : ℚ) < d3 := by exact_mod_cast h3
    linarith
  have f0 : (0 : ℚ) < d0 := by exact_mod_cast (show 0 < d0 by omega)
  have f1 : (0 : ℚ) < d1 := by exact_mod_cast (show 0 < d1 by omega)
  have f2 : (0 : ℚ) < d2 := by exact_mod_cast (show 0 < d2 by omega)
  have f3 : (0 : ℚ) < d3 := by exact_mod_cast (show 0 < d3 by omega)
  have g0 : (1 : ℚ) - n0 / d0 = (d0 - n0) / d0 := by field_simp
  have g1 : (1 : ℚ) - n1 / d1 = (d1 - n1) / d1 := by field_simp
  have g2 : (1 : ℚ) - n2 / d2 = (d2 - n2) / d2 := by field_simp
  have g3 : (1 : ℚ) - n3 / d3 = (d3 - n3) / d3 := by field_simp
  unfold val tailP tl4 kk
  simp only
  rw [g0, g1, g2, g3]
  push_cast [Nat.cast_sub h0.le, Nat.cast_sub h1.le, Nat.cast_sub h2.le, Nat.cast_sub h3.le]
  field_simp
  ring

private theorem sqStep_spec {n g s : ℕ} {x : ℕ × ℕ} (h : sqStep (4 * n - 3) g = some x)
    (hn : n = 1 + s + s ^ 2) (hs : 300 ≤ s) : x = (s + 1, s * s) := by
  have hm : 4 * n - 3 = (2 * s + 1) * (2 * s + 1) := by
    subst hn
    have : (2 * s + 1) * (2 * s + 1) + 3 = 4 * (1 + s + s ^ 2) := by ring
    omega
  rw [hm] at h
  simp only [sqStep] at h
  generalize nsqrt fuelSq ((2 * s + 1) * (2 * s + 1)) g = r at h
  split_ifs at h with h1 h2 h3
  · have := Nat.mul_self_inj.mp h1; omega
  · have := Nat.mul_self_inj.mp h1
    subst this
    have hs' : (2 * s + 1 - 1) / 2 = s := by omega
    simp only [hs', Option.some.injEq] at h
    exact h.symm
  · have a := Nat.mul_self_lt_mul_self_iff.mp h3.1
    have b := Nat.mul_self_lt_mul_self_iff.mp h3.2
    omega

private theorem exOK_pow {s : Slot} {w : ℕ × ℕ} {e x : ℕ} (h : exOK s w e = true)
    (hs : s.Sat x) : x ^ e = s.pinv ^ e := by
  cases s with
  | pin p => simp only [Slot.Sat] at hs; simp [Slot.pinv, hs]
  | free k lb ex => simp [exOK, Slot.isPin] at h; simp [h]

private theorem step_pos {nd : Node} {w : Wts} {D4 : ℕ} (hD : 0 < D4) :
    ∀ v x, step nd w D4 v = some x → 0 < x.2 := by
  intro v x h
  unfold step at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq] at h; subst h; simp
  · simp only [sqStep] at h
    split_ifs at h with a b c <;> simp only [Option.some.injEq] at h <;> subst h
    · simp
    · simp only; exact Nat.mul_pos (by omega) (by omega)
    · simp
  · simp only [Option.some.injEq] at h; subst h; simp only; positivity

/-! ## Soundness of a leaf -/

private theorem tailF_300 : tailF 300 = 178802 / 178801 := by
  unfold tailF; norm_num

private theorem final_bound {m0 m1 m2 m3 : ℕ} {C : List ℕ} {X : ℕ × ℕ}
    (h0 : 2 ≤ m0) (h1 : 2 ≤ m1) (h2 : 2 ≤ m2) (h3 : 2 ≤ m3) (hC : ∀ s ∈ C, 5 ≤ s)
    (hX : X.1 < X.2) (h : finalOK (m0, m1, m2, m3) C X = true) :
    (m0 : ℚ) / (m0 - 1) * ((m1 : ℚ) / (m1 - 1)) * ((m2 : ℚ) / (m2 - 1)) *
      ((m3 : ℚ) / (m3 - 1)) * (∏ s ∈ C.toFinset, rv s) * tailF 300 / (1 - val X) ≤ 2 := by
  obtain ⟨X1, X2⟩ := X
  simp only at hX
  simp only [finalOK, decide_eq_true_eq] at h
  set Pn := C.prod
  set Pd := (C.map fun s => s - 1).prod
  have hPd : 0 < Pd := List.prod_pos fun x hx => by
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    have := hC s hs
    omega
  have hfvC := prod_toFinset_le C fun s hs => le_trans (by norm_num) (hC s hs)
  rw [prod_rv_list C fun s hs => le_trans (by norm_num) (hC s hs)] at hfvC
  have q0 : (1 : ℚ) < m0 := by exact_mod_cast h0
  have q1 : (1 : ℚ) < m1 := by exact_mod_cast h1
  have q2 : (1 : ℚ) < m2 := by exact_mod_cast h2
  have q3 : (1 : ℚ) < m3 := by exact_mod_cast h3
  have hX2 : (0 : ℚ) < X2 := by exact_mod_cast (show 0 < X2 by omega)
  have hX12 : (X1 : ℚ) < X2 := by exact_mod_cast hX
  have hPdq : (0 : ℚ) < Pd := by exact_mod_cast hPd
  have h1X : 0 < 1 - val (X1, X2) := by
    unfold val; simp only; rw [sub_pos, div_lt_one hX2]; exact hX12
  have key : (m0 : ℚ) * m1 * m2 * m3 * Pn * X2 * 178802 ≤
      2 * (((m0 : ℚ) - 1) * (m1 - 1) * (m2 - 1) * (m3 - 1)) * Pd * (X2 - X1) * 178801 := by
    have := h
    rw [← Nat.cast_le (α := ℚ)] at this
    push_cast [Nat.cast_sub (show 1 ≤ m0 by omega), Nat.cast_sub (show 1 ≤ m1 by omega),
      Nat.cast_sub (show 1 ≤ m2 by omega), Nat.cast_sub (show 1 ≤ m3 by omega),
      Nat.cast_sub hX.le] at this
    exact this
  have hA : 0 < (m0 : ℚ) / (m0 - 1) * ((m1 : ℚ) / (m1 - 1)) * ((m2 : ℚ) / (m2 - 1)) *
      ((m3 : ℚ) / (m3 - 1)) := by
    have a0 : 0 < (m0 : ℚ) / (m0 - 1) := div_pos (by linarith) (by linarith)
    have a1 : 0 < (m1 : ℚ) / (m1 - 1) := div_pos (by linarith) (by linarith)
    have a2 : 0 < (m2 : ℚ) / (m2 - 1) := div_pos (by linarith) (by linarith)
    have a3 : 0 < (m3 : ℚ) / (m3 - 1) := div_pos (by linarith) (by linarith)
    positivity
  rw [tailF_300]
  calc _ ≤ (m0 : ℚ) / (m0 - 1) * ((m1 : ℚ) / (m1 - 1)) * ((m2 : ℚ) / (m2 - 1)) *
        ((m3 : ℚ) / (m3 - 1)) * ((Pn : ℚ) / Pd) * (178802 / 178801) / (1 - val (X1, X2)) := by
        gcongr
    _ = (m0 : ℚ) * m1 * m2 * m3 * Pn * X2 * 178802 /
        ((((m0 : ℚ) - 1) * (m1 - 1) * (m2 - 1) * (m3 - 1)) * Pd * (X2 - X1) * 178801) := by
        have e0 : (m0 : ℚ) - 1 ≠ 0 := by linarith
        have e1 : (m1 : ℚ) - 1 ≠ 0 := by linarith
        have e2 : (m2 : ℚ) - 1 ≠ 0 := by linarith
        have e3 : (m3 : ℚ) - 1 ≠ 0 := by linarith
        have e4 : (X2 : ℚ) - X1 ≠ 0 := by linarith
        have e5 : (X2 : ℚ) ≠ 0 := by linarith
        have e6 : (Pd : ℚ) ≠ 0 := by linarith
        have e7 : (1 : ℚ) - X1 / X2 = (X2 - X1) / X2 := by field_simp
        unfold val
        simp only
        rw [e7]
        field_simp
    _ ≤ 2 := by
        rw [div_le_iff₀ (by
          have : (0 : ℚ) < X2 - X1 := by linarith
          have : (0 : ℚ) < ((m0 : ℚ) - 1) * (m1 - 1) * (m2 - 1) * (m3 - 1) := by
            have := mul_pos (mul_pos (mul_pos (sub_pos.mpr q0) (sub_pos.mpr q1))
              (sub_pos.mpr q2)) (sub_pos.mpr q3)
            exact this
          positivity)]
        linarith

/-- Soundness of the check of one leaf: no core configuration satisfies the constraints of a
leaf that passes `leafOK`. -/
theorem leafOK_sound {cl : ClassTriple} {nd : Node} {w : Wts} (h : leafOK cl nd w = true)
    {N q r₁ r₂ r₃ : ℕ} (c : Ctx4 N q r₁ r₂ r₃) (hS : Sat cl nd q r₁ r₂ r₃) : False := by
  have hd : Dist q r₁ r₂ r₃ := ⟨c.h1q.symm, c.h2q.symm, c.h3q.symm, c.h12, c.h13, c.h23⟩
  obtain ⟨hm0, hm1, hm2, hm3⟩ := least_le hS hd
  simp only [leafOK] at h
  rcases hB : accum (step nd w w.D4) box with _ | B
  · rw [hB] at h; simp at h
  rw [hB] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, l0, l1, l2, l3⟩, hX, hfin⟩ := h
  obtain ⟨d0, n0, α0, α1, hα⟩ := weight_ok hS.1 hm0 a0
  obtain ⟨d1, n1, β0, β1, hβ⟩ := weight_ok hS.2.1 hm1 a1
  obtain ⟨d2, n2, γ0, γ1, hγ⟩ := weight_ok hS.2.2.1 hm2 a2
  obtain ⟨d3, n3, δ0, δ1, hδ⟩ := weight_ok hS.2.2.2.1 hm3 a3
  have hD4 : 0 < w.D4 := by unfold Wts.D4; positivity
  obtain ⟨hBpos, hBval, hacc⟩ := accum_spec _ (step_pos hD4) box B hB
  obtain ⟨hTpos, hTval⟩ := val_tail w n0 n1 n2 n3
  set g : ℕ × ℕ × ℕ × ℕ → ℚ := fun v => val ((step nd w w.D4 v).getD (0, 1)) with hg_def
  have hgs : gsum g 5 = val B := by
    rw [gsum_box g, hBval]
    intro v e1 e2 e3 e4
    simp [g, step, e1, e2, e3, e4, val]
  have hg : ∀ s ∈ ord4 N q r₁ r₂ r₃, 300 ≤ s →
      (vec4 q r₁ r₂ r₃ s).1 < 5 → (vec4 q r₁ r₂ r₃ s).2.1 < 5 →
      (vec4 q r₁ r₂ r₃ s).2.2.1 < 5 → (vec4 q r₁ r₂ r₃ s).2.2.2 < 5 →
      fv s - 1 ≤ g (vec4 q r₁ r₂ r₃ s) := by
    intro s hs h300 b1 b2 b3 b4
    obtain ⟨x, hx⟩ := hacc _ (mem_box b1 b2 b3 b4)
    simp only [g, hx, Option.getD_some]
    obtain ⟨hsh, hev⟩ := c.shape hs
    unfold step at hx
    split_ifs at hx with hE hXe
    · exact absurd ⟨Nat.even_iff.mpr hE.1, Nat.even_iff.mpr hE.2.1, Nat.even_iff.mpr hE.2.2.1,
        Nat.even_iff.mpr hE.2.2.2⟩ hev
    · simp only [Bool.and_eq_true] at hXe
      obtain ⟨⟨⟨e0, e1⟩, e2⟩, e3⟩ := hXe
      have hn : nd.s0.pinv ^ (vec4 q r₁ r₂ r₃ s).1 * nd.s1.pinv ^ (vec4 q r₁ r₂ r₃ s).2.1 *
          nd.s2.pinv ^ (vec4 q r₁ r₂ r₃ s).2.2.1 * nd.s3.pinv ^ (vec4 q r₁ r₂ r₃ s).2.2.2 =
          1 + s + s ^ 2 := by
        rw [hsh, ← exOK_pow e0 hS.1, ← exOK_pow e1 hS.2.1, ← exOK_pow e2 hS.2.2.1,
          ← exOK_pow e3 hS.2.2.2.1]
      rw [sqStep_spec hx hn h300]
      unfold val
      simp only
      rw [fv_sub_one (by omega)]
      push_cast
      ring_nf
      exact le_rfl
    · simp only [Option.some.injEq] at hx
      subst hx
      rw [val_cap w _ (by omega) (by omega) (by omega) (by omega) d0 d1 d2 d3]
      exact c.fv_sub_le_min hs (by norm_num) h300 α0 β0 γ0 δ0 hα hβ hγ hδ
  have hX1 : val (padd B (tailP w)) < 1 := by
    unfold val
    have : (0 : ℚ) < (padd B (tailP w)).2 := by exact_mod_cast padd_pos hBpos hTpos
    rw [div_lt_one this]
    exact_mod_cast hX
  have hXle : gsum g 5 + kk 300 * tl4 ((w.w0.1 : ℚ) / w.w0.2) ((w.w1.1 : ℚ) / w.w1.2)
      ((w.w2.1 : ℚ) / w.w2.2) ((w.w3.1 : ℚ) / w.w3.2) 5 ≤ val (padd B (tailP w)) := by
    rw [val_padd hBpos hTpos, hgs, hTval]
  exact c.close 300 5 (by norm_num) α0 α1 β0 β1 γ0 γ1 δ0 δ1 hα hβ hγ hδ
    (rho_le l0 hm0) (rho_le l1 hm1) (rho_le l2 hm2) (rho_le l3 hm3)
    (smallList nd (leastVals cl nd)).toFinset
    (fun x hx => le_trans (by norm_num) (smallList_ge x (List.mem_toFinset.mp hx)))
    (fun s hs h300 => List.mem_toFinset.mpr (mem_smallList c hS hs h300))
    g (fun v => val_nonneg _) hg _ hXle hX1
    (final_bound l0 l1 l2 l3 smallList_ge hX hfin)

/-! ## Soundness of a tree -/

private theorem bump_sat {s : Slot} {x p : ℕ} (hs : s.Sat x) (hp : p < x) : (s.bump p).Sat x := by
  cases s with
  | pin a => exact hs
  | free k lb ex => exact ⟨hs.1, max_le hs.2.1 hp, hs.2.2⟩

private theorem addEx_sat {s : Slot} {x p : ℕ} (hs : s.Sat x) (hp : x ≠ p) :
    (s.addEx p).Sat x := by
  cases s with
  | pin a => exact hs
  | free k lb ex => exact ⟨hs.1, hs.2.1, by simp [hs.2.2, hp]⟩

private theorem pin_sat {cl : ClassTriple} {nd : Node} {a0 a1 a2 a3 p i : ℕ}
    (hS : Sat cl nd a0 a1 a2 a3) (hi : i < 4)
    (hp : (i = 0 ∧ a0 = p) ∨ (i = 1 ∧ a1 = p) ∨ (i = 2 ∧ a2 = p) ∨ (i = 3 ∧ a3 = p)) :
    Sat cl (pinChild cl nd p i) a0 a1 a2 a3 := by
  obtain ⟨h0, h1, h2, h3, o12, o23, o13⟩ := hS
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, h1, h2, h3, o12, o23, o13⟩
  · refine ⟨h0, rfl, ?_, ?_, o12, o23, o13⟩
    · simp only [pinChild]; split_ifs with h
      · exact bump_sat h2 (o12 h)
      · exact h2
    · simp only [pinChild]; split_ifs with h
      · exact bump_sat h3 (o13 h)
      · exact h3
  · refine ⟨h0, h1, rfl, ?_, o12, o23, o13⟩
    simp only [pinChild]; split_ifs with h
    · exact bump_sat h3 (o23 h)
    · exact h3
  · exact ⟨h0, h1, h2, rfl, o12, o23, o13⟩

private theorem rest_sat {cl : ClassTriple} {nd : Node} {a0 a1 a2 a3 p i : ℕ}
    (hS : Sat cl nd a0 a1 a2 a3) (hi : i < 4)
    (hp : ¬ ((i = 0 ∧ a0 = p) ∨ (i = 1 ∧ a1 = p) ∨ (i = 2 ∧ a2 = p) ∨ (i = 3 ∧ a3 = p))) :
    Sat cl (restChild nd p i) a0 a1 a2 a3 := by
  obtain ⟨h0, h1, h2, h3, o12, o23, o13⟩ := hS
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact ⟨addEx_sat h0 (by tauto), h1, h2, h3, o12, o23, o13⟩
  · exact ⟨h0, addEx_sat h1 (by tauto), h2, h3, o12, o23, o13⟩
  · exact ⟨h0, h1, addEx_sat h2 (by tauto), h3, o12, o23, o13⟩
  · exact ⟨h0, h1, h2, addEx_sat h3 (by tauto), o12, o23, o13⟩

/-- Soundness of the tree check: no core configuration satisfies the constraints of the root
of a tree that passes `treeOK`. -/
theorem treeOK_sound {cl : ClassTriple} {N q r₁ r₂ r₃ : ℕ} (c : Ctx4 N q r₁ r₂ r₃) :
    ∀ (t : Tree) (nd : Node), treeOK cl nd t = true → Sat cl nd q r₁ r₂ r₃ → False
  | .leaf w, nd, h, hS => leafOK_sound h c hS
  | .split i p t₁ t₂, nd, h, hS => by
    simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, -⟩, h₁⟩, h₂⟩ := h
    by_cases hp : (i = 0 ∧ q = p) ∨ (i = 1 ∧ r₁ = p) ∨ (i = 2 ∧ r₂ = p) ∨ (i = 3 ∧ r₃ = p)
    · exact treeOK_sound c t₁ _ h₁ (pin_sat hS hi hp)
    · exact treeOK_sound c t₂ _ h₂ (rest_sat hS hi hp)

/-- A leaf check gives the tree check of that leaf; with `treeOK_split` this lets a data module
check the leaves of a large tree in separate declarations. -/
theorem treeOK_leaf {cl : ClassTriple} {nd : Node} {w : Wts} (h : leafOK cl nd w = true) :
    treeOK cl nd (.leaf w) = true := h

/-- Assembling the tree check of a split from the checks of its two children. -/
theorem treeOK_split {cl : ClassTriple} {nd : Node} {i p : ℕ} {t₁ t₂ : Tree} (hi : i < 4)
    (hf : (nd.get i).isFree = true) (h₁ : treeOK cl (pinChild cl nd p i) t₁ = true)
    (h₂ : treeOK cl (restChild nd p i) t₂ = true) : treeOK cl nd (.split i p t₁ t₂) = true := by
  simp [treeOK, hi, hf, h₁, h₂]

/-! ## Coverage -/

/-- The class of a prime `r ≥ 5` prime to 3. -/
def clsOf (r : ℕ) : Cls :=
  if r = 5 then .c5 else if r = 7 then .c7 else if r = 13 then .c13 else if r = 19 then .c19
  else if r = 31 then .c31 else if r = 37 then .c37 else if r = 43 then .c43
  else if r % 3 = 2 then .n2 else .big

/-- The position of a class in class order. -/
def Cls.rank : Cls → ℕ
  | .c5 => 0
  | .c7 => 1
  | .c13 => 2
  | .c19 => 3
  | .c31 => 4
  | .c37 => 5
  | .c43 => 6
  | .n2 => 7
  | .big => 8

/-- All classes, in class order. -/
def allCls : List Cls := [.c5, .c7, .c13, .c19, .c31, .c37, .c43, .n2, .big]

/-- A class triple that is sorted in class order and repeats no fixed class. -/
def tripleOK (t : ClassTriple) : Bool :=
  decide (t.1.rank ≤ t.2.1.rank) && decide (t.2.1.rank ≤ t.2.2.rank) &&
    (!decide (t.1 = t.2.1) || t.1.sortable) && (!decide (t.2.1 = t.2.2) || t.2.1.sortable)

/-- The sorted class triples with no repeated fixed class. -/
def triples : List ClassTriple :=
  (allCls.flatMap fun a => allCls.flatMap fun b => allCls.map fun c => (a, b, c)).filter tripleOK

/-- There are 102 sorted class triples. -/
theorem triples_length : triples.length = 102 := by decide +kernel

/-- The check of a list of trees: every sorted class triple has an entry whose tree passes
`treeOK` from the root constraints of the triple. -/
def allOK (trees : List (ClassTriple × Tree)) : Bool :=
  triples.all fun t => trees.any fun e => decide (e.1 = t) && treeOK t (rootNode t) e.2

/-- A way to establish `allOK` from separate checks of the trees. -/
theorem allOK_of {trees : List (ClassTriple × Tree)}
    (h : ∀ t ∈ triples, ∃ tr, (t, tr) ∈ trees ∧ treeOK t (rootNode t) tr = true) :
    allOK trees = true := by
  simp only [allOK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  intro t ht
  obtain ⟨tr, hm, hok⟩ := h t ht
  exact ⟨(t, tr), hm, rfl, hok⟩

private theorem rank_inj {a b : Cls} (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> simp_all [Cls.rank]

private theorem mem_allCls (a : Cls) : a ∈ allCls := by
  cases a <;> simp [allCls]

private theorem clsOf_fixed {r : ℕ} (h : (clsOf r).sortable = false) : (clsOf r).root = .pin r := by
  unfold clsOf at *
  split_ifs at * <;> simp_all [Cls.sortable, Cls.root]

private theorem root_sat {r : ℕ} (hp : r.Prime) (h5 : 5 ≤ r) (h3 : r % 3 ≠ 0) :
    (clsOf r).root.Sat r := by
  unfold clsOf
  split_ifs with a0 a1 a2 a3 a4 a5 a6 a7 <;> simp only [Cls.root, Slot.Sat, Kind.test,
    decide_eq_true_eq, List.not_mem_nil, not_false_eq_true, and_true]
  all_goals first | omega | skip
  · refine ⟨a7, ?_⟩
    by_contra hc
    interval_cases r <;> first | omega | (exfalso; norm_num at hp)
  · refine ⟨by omega, ?_⟩
    by_contra hc
    interval_cases r <;> first | omega | (exfalso; norm_num at hp)

/-- The order used to relabel `r₁, r₂, r₃`: by class, then by value. -/
private def ord (a b : ℕ) : Prop :=
  (clsOf a).rank < (clsOf b).rank ∨ ((clsOf a).rank = (clsOf b).rank ∧ a < b)

private theorem ord_total {a b : ℕ} (h : a ≠ b) : ord a b ∨ ord b a := by
  unfold ord; omega

private theorem Ctx4.sort {N q r₁ r₂ r₃ : ℕ} (c : Ctx4 N q r₁ r₂ r₃) :
    ∃ a b d, Ctx4 N q a b d ∧ ord a b ∧ ord b d := by
  rcases ord_total c.h12 with h12 | h21 <;> rcases ord_total c.h23 with h23 | h32
  · exact ⟨r₁, r₂, r₃, c, h12, h23⟩
  · rcases ord_total c.h13 with h13 | h31
    · exact ⟨r₁, r₃, r₂, c.swap23, h13, h32⟩
    · exact ⟨r₃, r₁, r₂, c.swap23.swap12, h31, h12⟩
  · rcases ord_total c.h13 with h13 | h31
    · exact ⟨r₂, r₁, r₃, c.swap12, h21, h13⟩
    · exact ⟨r₂, r₃, r₁, c.swap12.swap23, h23, h31⟩
  · exact ⟨r₃, r₂, r₁, c.swap12.swap23.swap12, h32, h21⟩

private theorem same_lt {a b : ℕ} (hab : ord a b) (h : same (clsOf a) (clsOf b) = true) : a < b := by
  simp only [same, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold ord at hab
  rw [h.2] at hab
  omega

/-- Coverage: every core configuration, after relabeling `r₁, r₂, r₃`, satisfies the root
constraints of a sorted class triple. -/
theorem Ctx4.cover {N q r₁ r₂ r₃ : ℕ} (c : Ctx4 N q r₁ r₂ r₃) :
    ∃ a b d, Ctx4 N q a b d ∧ (clsOf a, clsOf b, clsOf d) ∈ triples ∧
      Sat (clsOf a, clsOf b, clsOf d) (rootNode (clsOf a, clsOf b, clsOf d)) q a b d := by
  obtain ⟨a, b, d, c', hab, hbd⟩ := c.sort
  obtain ⟨⟨pa, a5, a3⟩, ⟨pb, b5, b3⟩, ⟨pd, d5, d3⟩⟩ := c'.r_prime
  have hq := c'.q_mod
  have hq2 := c'.hq.two_le
  refine ⟨a, b, d, c', ?_, ?_⟩
  · simp only [triples, List.mem_filter, List.mem_flatMap, List.mem_map]
    refine ⟨⟨clsOf a, mem_allCls _, clsOf b, mem_allCls _, clsOf d, mem_allCls _, rfl⟩, ?_⟩
    have fx : ∀ {x y : ℕ}, x ≠ y → clsOf x = clsOf y → (clsOf x).sortable = true := by
      intro x y hxy he
      by_contra hs
      simp only [Bool.not_eq_true] at hs
      have e1 := clsOf_fixed hs
      have e2 := clsOf_fixed (he ▸ hs)
      rw [he, e2] at e1
      exact hxy (Slot.pin.inj e1).symm
    simp only [tripleOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    unfold ord at hab hbd
    refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, ?_⟩
    · by_cases he : clsOf a = clsOf b
      · exact Or.inr (fx c'.h12 he)
      · exact Or.inl he
    · by_cases he : clsOf b = clsOf d
      · exact Or.inr (fx c'.h23 he)
      · exact Or.inl he
  · refine ⟨⟨by simp [Kind.test, hq], by omega, by simp⟩, root_sat pa a5 a3, root_sat pb b5 b3,
      root_sat pd d5 d3, same_lt hab, same_lt hbd, fun h => ?_⟩
    have h' := h
    simp only [same, Bool.and_eq_true, decide_eq_true_eq] at h'
    unfold ord at hab hbd
    have e := congrArg Cls.rank h'.2
    have : (clsOf a).rank = (clsOf b).rank := by omega
    have : (clsOf b).rank = (clsOf d).rank := by omega
    omega

/-- The statement with three exceptional primes, **conditional on the check**
`allOK trees = true`. This theorem proves nothing by itself: the three exception statement is
proved only once a data module supplies `trees` and establishes the check. If `N` is an odd
perfect number, `q` its special prime, and every prime factor `p` of `N` other than
`q, r₁, r₂, r₃` has an exponent `e` with `3 ∣ e + 1`, then `3 ∣ N`. -/
theorem three_dvd_of_three_exceptions_of_check (trees : List (ClassTriple × Tree))
    (hcheck : allOK trees = true) {N q r₁ r₂ r₃ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hmod : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ → 3 ∣ N.factorization p + 1) :
    3 ∣ N := by
  by_contra h3
  obtain ⟨r₁', r₂', r₃', c₀⟩ := ctx4_of_not_three_dvd h hq hodd hmod h3
  obtain ⟨a, b, d, c, ht, hS⟩ := c₀.cover
  simp only [allOK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  obtain ⟨e, -, -, hok⟩ := hcheck _ ht
  exact treeOK_sound c _ _ hok hS

end ThreeFreeThree

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.val_nonneg
#print axioms OddPerfect.ThreeFreeThree.leafOK_sound
#print axioms OddPerfect.ThreeFreeThree.treeOK_sound
#print axioms OddPerfect.ThreeFreeThree.treeOK_leaf
#print axioms OddPerfect.ThreeFreeThree.treeOK_split
#print axioms OddPerfect.ThreeFreeThree.triples_length
#print axioms OddPerfect.ThreeFreeThree.allOK_of
#print axioms OddPerfect.ThreeFreeThree.Ctx4.cover
#print axioms OddPerfect.ThreeFreeThree.three_dvd_of_three_exceptions_of_check
