import OddPerfect.RadicalBound
import OddPerfect.Certificate

/-!
# A decision procedure for a fixed prime support

For `N = ∏_{p ∈ S} p ^ e_p` put `y_p = p ^ (e_p + 1)`. By `abundancy_eq_prod_mul_prod`,
`σ(N) = 2N` if and only if `∏_{p ∈ S} (1 - 1/y_p) = 2 ∏_{p ∈ S} (p - 1)/p`. The search keeps a
target `a/b` (natural numbers, cross multiplied) equal to the product of `1 - 1/y` over the
`m` primes not yet assigned. If `m = 0` it accepts iff `a = b`. Otherwise, with `d = b - a`:

* every unassigned `y` satisfies `b ≤ d y`, since the product is at most each factor;
* the least unassigned `y` satisfies `d y ≤ m b`, since `1 - ∏ (1 - 1/y) ≤ ∑ 1/y`.

The search branches on the least unassigned `y`: a prime `p` and an exponent `e ≥ 1` with
`lo ≤ y`, `b ≤ d y ≤ m b`, where `lo` is the previously assigned `y` (all remaining values
are at least the least one). The exponent rule is a parameter `ok`. Each branch replaces
`a/b` by `a y / (b (y - 1))`. No divisor sum is factored; everything is exact arithmetic.

Main results:

* `sols_sound`, `sols_complete`: the engine `sols` lists exactly the admissible exponent
  assignments solving the target equation, each once up to order.
* `exists_mem_perfectSols`, `perfect_of_mem_perfectSols`: the bridge to perfect numbers with
  a given support, for any rule.
* `no_oddPerfect_of_search`, `exists_oddPerfect_of_search`: `search S` decides whether some
  odd perfect number has prime support exactly `S` (a list of odd primes).
* Instances: positive controls `{2, 3}`, `{2, 7}`, `{2, 31}` (6, 28, 496) with all exponents
  allowed, the three supports of size three left by the abundancy bound, and the four
  tables of supports of size four used in `OmegaFive`, all closed by `decide +kernel`.

Limitation: the engine treats one support at a time. For a fixed size `k` there are
infinitely many supports, so the engine alone does not give `ω(N) ≥ k + 1`; a separate
argument must first reduce to finitely many supports (as `OmegaFive` does for `k = 4`).
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open Cert (isPrimeB)

namespace FixedSupport

/-! ## The engine -/

/-- Candidate exponents `e ≥ 1` of `p` at a node with `m` unassigned primes, target `a/b`
and lower bound `lo`: those with `ok p e`, `lo ≤ y`, `b ≤ (b - a) y ≤ m b`, `y = p^(e+1)`. -/
def fsCands (ok : ℕ → ℕ → Bool) (p m a b lo : ℕ) : List ℕ :=
  (List.range (Nat.log2 (m * b / (b - a)) + 1)).filter fun e =>
    1 ≤ e && ok p e && lo ≤ p ^ (e + 1) && b ≤ (b - a) * p ^ (e + 1) &&
      (b - a) * p ^ (e + 1) ≤ m * b

/-- All exponent assignments, as lists of pairs `(p, e)` in increasing order of
`p ^ (e + 1)`, solving the target `a/b` over the primes of `l`. The first argument is fuel;
`l.length` suffices. -/
def sols (ok : ℕ → ℕ → Bool) : ℕ → List ℕ → ℕ → ℕ → ℕ → List (List (ℕ × ℕ))
  | _, [], a, b, _ => if a = b then [[]] else []
  | 0, _ :: _, _, _, _ => []
  | n + 1, l@(_ :: _), a, b, lo =>
    l.flatMap fun p => (fsCands ok p l.length a b lo).flatMap fun e =>
      (sols ok n (l.erase p) (a * p ^ (e + 1)) (b * (p ^ (e + 1) - 1)) (p ^ (e + 1))).map
        ((p, e) :: ·)

/-- The engine started at the target `2 ∏ (p - 1) / ∏ p` of a perfect number. -/
def perfectSols (ok : ℕ → ℕ → Bool) (l : List ℕ) : List (List (ℕ × ℕ)) :=
  sols ok l.length l (2 * (l.map (· - 1)).prod) l.prod 0

/-- Euler's rule with special prime `q`: exponent `≡ 1 (mod 4)` at `q`, even elsewhere. -/
def okEuler (q p e : ℕ) : Bool := if p = q then e % 4 == 1 else e % 2 == 0

/-- For a list `S` of odd primes, `search S = true` iff some odd perfect number has prime
support `S` (see `no_oddPerfect_of_search` and `exists_oddPerfect_of_search`). -/
def search (S : List ℕ) : Bool :=
  S.dedup.any fun q => q % 4 == 1 && !(perfectSols (okEuler q) S.dedup).isEmpty

/-! ## Products over the unassigned primes -/

section Products

variable (Y : ℕ → ℕ)

/-- Splitting off one factor of a list product. -/
theorem prod_map_eq_mul_erase {g : ℕ → ℕ} {l : List ℕ} {p : ℕ} (hp : p ∈ l) :
    (l.map g).prod = g p * ((l.erase p).map g).prod := by
  rw [((List.perm_cons_erase hp).map g).prod_eq, List.map_cons, List.prod_cons]

private theorem prod_sub_le (l : List ℕ) :
    (l.map fun p => Y p - 1).prod ≤ (l.map Y).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_le_mul (Nat.sub_le _ _) ih

private theorem prod_pos' {l : List ℕ} (h : ∀ p ∈ l, 1 ≤ Y p) : 0 < (l.map Y).prod :=
  List.prod_pos fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact h p hp

/-- The product of `1 - 1/y` is at most each factor, cross multiplied. -/
private theorem factor_bound {l : List ℕ} {p : ℕ} (hp : p ∈ l) :
    (l.map fun p => Y p - 1).prod * Y p ≤ (l.map Y).prod * (Y p - 1) := by
  rw [prod_map_eq_mul_erase hp, prod_map_eq_mul_erase (g := Y) hp]
  have := prod_sub_le Y (l.erase p)
  calc (Y p - 1) * ((l.erase p).map fun p => Y p - 1).prod * Y p
      = ((Y p - 1) * Y p) * ((l.erase p).map fun p => Y p - 1).prod := by ring
    _ ≤ ((Y p - 1) * Y p) * ((l.erase p).map Y).prod := Nat.mul_le_mul_left _ this
    _ = Y p * ((l.erase p).map Y).prod * (Y p - 1) := by ring

/-- `1 - ∏ (1 - 1/y) ≤ m / t` when every `y ≥ t`, cross multiplied. -/
private theorem sum_bound {l : List ℕ} {t : ℕ} (h1 : ∀ p ∈ l, 1 ≤ Y p)
    (ht : ∀ p ∈ l, t ≤ Y p) :
    (l.map Y).prod * t ≤ (l.map fun p => Y p - 1).prod * t + l.length * (l.map Y).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    have ih := ih (fun p hp => h1 p (List.mem_cons_of_mem _ hp))
      (fun p hp => ht p (List.mem_cons_of_mem _ hp))
    obtain ⟨z, hz⟩ : ∃ z, Y x = z + 1 := ⟨Y x - 1, by have := h1 x (by simp); omega⟩
    have htx : t ≤ z + 1 := hz ▸ ht x (by simp)
    rw [hz, Nat.add_sub_cancel]
    have hQP := prod_sub_le Y xs
    have k1 := Nat.mul_le_mul_left (z + 1) ih
    have k2 := Nat.mul_le_mul hQP htx
    nlinarith

end Products

/-! ## Soundness and completeness of the engine -/

/-- Unfolding `sols` at a nonempty list. -/
private theorem sols_cons (ok : ℕ → ℕ → Bool) (n x : ℕ) (xs : List ℕ) (a b lo : ℕ) :
    sols ok (n + 1) (x :: xs) a b lo = (x :: xs).flatMap fun p =>
      (fsCands ok p (x :: xs).length a b lo).flatMap fun e =>
        (sols ok n ((x :: xs).erase p) (a * p ^ (e + 1)) (b * (p ^ (e + 1) - 1))
          (p ^ (e + 1))).map ((p, e) :: ·) := by
  rfl

/-- Soundness: every output is an admissible assignment solving the target. -/
theorem sols_sound (ok : ℕ → ℕ → Bool) :
    ∀ (n : ℕ) (l : List ℕ) (a b lo : ℕ) (sl : List (ℕ × ℕ)), l.Nodup →
      sl ∈ sols ok n l a b lo → ∃ f : ℕ → ℕ, sl.Perm (l.map fun p => (p, f p)) ∧
        (∀ p ∈ l, 1 ≤ f p ∧ ok p (f p) = true) ∧
        a * (l.map fun p => p ^ (f p + 1)).prod = b * (l.map fun p => p ^ (f p + 1) - 1).prod := by
  intro n
  induction n with
  | zero =>
    intro l a b lo sl _ hsl
    cases l with
    | nil =>
      by_cases hab : a = b
      · simp [sols, hab] at hsl
        exact ⟨fun _ => 0, by simp [hsl], by simp, by simp [hab]⟩
      · simp [sols, hab] at hsl
    | cons x xs => simp [sols] at hsl
  | succ n ih =>
    intro l a b lo sl hnd hsl
    cases l with
    | nil =>
      by_cases hab : a = b
      · simp [sols, hab] at hsl
        exact ⟨fun _ => 0, by simp [hsl], by simp, by simp [hab]⟩
      · simp [sols, hab] at hsl
    | cons x xs =>
      rw [sols_cons] at hsl
      set l := x :: xs with hl
      obtain ⟨p, hp, hsl⟩ := List.mem_flatMap.mp hsl
      obtain ⟨e, he, hsl⟩ := List.mem_flatMap.mp hsl
      obtain ⟨sl', hsl', rfl⟩ := List.mem_map.mp hsl
      obtain ⟨f', hperm, hadm, hinv⟩ := ih _ _ _ _ sl' (hnd.erase p) hsl'
      have he' := (List.mem_filter.mp he).2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at he'
      have hne : ∀ q ∈ l.erase p, q ≠ p := fun q hq => ((hnd.mem_erase_iff).mp hq).1
      set f := Function.update f' p e with hf
      have hfp : f p = e := by simp [hf]
      have hfq : ∀ q ∈ l.erase p, f q = f' q := fun q hq => by
        simp [hf, Function.update_of_ne (hne q hq)]
      refine ⟨f, ?_, ?_, ?_⟩
      · have h1 : (l.map fun q => (q, f q)).Perm ((p, f p) :: (l.erase p).map fun q => (q, f q)) :=
          (List.perm_cons_erase hp).map (fun q => (q, f q))
        have h2 : ((l.erase p).map fun q => (q, f q)) = (l.erase p).map fun q => (q, f' q) :=
          List.map_congr_left fun q hq => by rw [hfq q hq]
        rw [h2, hfp] at h1
        exact (hperm.cons _).trans h1.symm
      · intro q hq
        by_cases hqp : q = p
        · rw [hqp, hfp]; exact ⟨he'.1.1.1.1, he'.1.1.1.2⟩
        · rw [hfq q ((hnd.mem_erase_iff).mpr ⟨hqp, hq⟩)]
          exact hadm q ((hnd.mem_erase_iff).mpr ⟨hqp, hq⟩)
      · have e1 : (l.map fun q => q ^ (f q + 1)).prod =
            p ^ (f p + 1) * ((l.erase p).map fun q => q ^ (f q + 1)).prod :=
          prod_map_eq_mul_erase hp
        have e2 : (l.map fun q => q ^ (f q + 1) - 1).prod =
            (p ^ (f p + 1) - 1) * ((l.erase p).map fun q => q ^ (f q + 1) - 1).prod :=
          prod_map_eq_mul_erase hp
        have m1 : ((l.erase p).map fun q => q ^ (f q + 1)) =
            (l.erase p).map fun q => q ^ (f' q + 1) :=
          List.map_congr_left fun q hq => by rw [hfq q hq]
        have m2 : ((l.erase p).map fun q => q ^ (f q + 1) - 1) =
            (l.erase p).map fun q => q ^ (f' q + 1) - 1 :=
          List.map_congr_left fun q hq => by rw [hfq q hq]
        rw [e1, e2, m1, m2, hfp]
        calc a * (p ^ (e + 1) * ((l.erase p).map fun q => q ^ (f' q + 1)).prod)
            = a * p ^ (e + 1) * ((l.erase p).map fun q => q ^ (f' q + 1)).prod := by ring
          _ = b * (p ^ (e + 1) - 1) * ((l.erase p).map fun q => q ^ (f' q + 1) - 1).prod := hinv
          _ = _ := by ring

/-- Completeness: every admissible assignment solving the target (with all values at least
`lo`) is output, up to order. -/
theorem sols_complete (ok : ℕ → ℕ → Bool) :
    ∀ (n : ℕ) (l : List ℕ) (a b lo : ℕ) (f : ℕ → ℕ), l.Nodup → l.length ≤ n → 0 < b →
      (∀ p ∈ l, 2 ≤ p ∧ 1 ≤ f p ∧ ok p (f p) = true ∧ lo ≤ p ^ (f p + 1)) →
      a * (l.map fun p => p ^ (f p + 1)).prod = b * (l.map fun p => p ^ (f p + 1) - 1).prod →
      ∃ sl ∈ sols ok n l a b lo, sl.Perm (l.map fun p => (p, f p)) := by
  intro n
  induction n with
  | zero =>
    intro l a b lo f _ hlen _ _ hinv
    cases l with
    | nil =>
      simp only [List.map_nil, List.prod_nil, mul_one] at hinv
      exact ⟨[], by simp [sols, hinv], by simp⟩
    | cons x xs => simp at hlen
  | succ n ih =>
    intro l a b lo f hnd hlen hb hadm hinv
    cases l with
    | nil =>
      simp only [List.map_nil, List.prod_nil, mul_one] at hinv
      exact ⟨[], by simp [sols, hinv], by simp⟩
    | cons x xs =>
      rw [sols_cons]
      set l := x :: xs with hl
      set Y : ℕ → ℕ := fun p => p ^ (f p + 1) with hY
      have hY1 : ∀ p ∈ l, 1 ≤ Y p := fun p hp =>
        Nat.one_le_pow _ _ (by have := (hadm p hp).1; omega)
      -- the least value of `y`
      obtain ⟨p, hp, hmin⟩ := l.toFinset.exists_min_image Y ⟨x, by simp [hl]⟩
      have hp : p ∈ l := List.mem_toFinset.mp hp
      have hmin : ∀ q ∈ l, Y p ≤ Y q := fun q hq => hmin q (List.mem_toFinset.mpr hq)
      have hP := prod_pos' Y hY1
      set P := (l.map Y).prod
      set Q := (l.map fun p => Y p - 1).prod
      have hinv' : a * P = b * Q := hinv
      have hQP : Q ≤ P := prod_sub_le Y l
      have e1 : P = Y p * ((l.erase p).map Y).prod := prod_map_eq_mul_erase hp
      have e2 : Q = (Y p - 1) * ((l.erase p).map fun q => Y q - 1).prod :=
        prod_map_eq_mul_erase hp
      have hab : a ≤ b := by
        have : a * P ≤ b * P := calc
          a * P = b * Q := hinv'
          _ ≤ b * P := Nat.mul_le_mul_left b hQP
        exact Nat.le_of_mul_le_mul_right this hP
      obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
      have hd : a + c - a = c := by omega
      -- the two bounds at the least value
      have hlow : a + c ≤ c * Y p := by
        have k : Q * Y p ≤ P * (Y p - 1) := factor_bound Y hp
        have k2 : a * Y p * P ≤ (a + c) * (Y p - 1) * P := by
          calc a * Y p * P = (a * P) * Y p := by ring
            _ = (a + c) * (Q * Y p) := by rw [hinv']; ring
            _ ≤ (a + c) * (P * (Y p - 1)) := Nat.mul_le_mul_left _ k
            _ = _ := by ring
        have k3 := Nat.le_of_mul_le_mul_right k2 hP
        obtain ⟨z, hz⟩ : ∃ z, Y p = z + 1 := ⟨Y p - 1, by have := hY1 p hp; omega⟩
        rw [hz, Nat.add_sub_cancel] at k3
        rw [hz]
        nlinarith
      have hup : c * Y p ≤ l.length * (a + c) := by
        have k : P * Y p ≤ Q * Y p + l.length * P := sum_bound Y hY1 hmin
        have k2 : c * Y p * P ≤ l.length * (a + c) * P := by
          have k1 := Nat.mul_le_mul_left (a + c) k
          have h3 : a * P * Y p = (a + c) * Q * Y p := by rw [hinv']
          nlinarith
        exact Nat.le_of_mul_le_mul_right k2 hP
      have hc : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · subst h0; simp at hlow; omega
        · exact h0
      -- the exponent of `p` is a candidate
      have hmemc : f p ∈ fsCands ok p l.length a (a + c) lo := by
        obtain ⟨hp2, he1, hok, hlo⟩ := hadm p hp
        simp only [fsCands, hd, List.mem_filter, List.mem_range, Bool.and_eq_true,
          decide_eq_true_eq]
        refine ⟨?_, ⟨⟨⟨⟨he1, hok⟩, hlo⟩, hlow⟩, hup⟩⟩
        have hB : Y p ≤ l.length * (a + c) / c := (Nat.le_div_iff_mul_le hc).mpr (by
          rw [Nat.mul_comm]; exact hup)
        have h2 : 2 ^ f p ≤ l.length * (a + c) / c :=
          calc 2 ^ f p ≤ 2 ^ (f p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ ≤ p ^ (f p + 1) := Nat.pow_le_pow_left hp2 _
            _ ≤ _ := hB
        have := (Nat.le_log2 (by have := Nat.one_le_two_pow (n := f p); omega)).mpr h2
        omega
      -- recurse on the remaining primes
      have hY4 : 0 < (a + c) * (Y p - 1) := by
        have : 2 ≤ Y p := by
          have := (hadm p hp).1
          calc 2 ≤ p := this
            _ = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ (f p + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        exact Nat.mul_pos (by omega) (by omega)
      have hinv2 : a * Y p * ((l.erase p).map Y).prod =
          (a + c) * (Y p - 1) * ((l.erase p).map fun q => Y q - 1).prod := by
        calc a * Y p * ((l.erase p).map Y).prod = a * P := by rw [e1]; ring
          _ = (a + c) * Q := hinv'
          _ = _ := by rw [e2]; ring
      have hlen' : (l.erase p).length ≤ n := by
        rw [List.length_erase_of_mem hp]; omega
      obtain ⟨sl', hsl', hperm⟩ := ih (l.erase p) (a * Y p) ((a + c) * (Y p - 1)) (Y p) f
        (hnd.erase p) hlen' hY4 (fun q hq => by
          have hq' := List.mem_of_mem_erase hq
          exact ⟨(hadm q hq').1, (hadm q hq').2.1, (hadm q hq').2.2.1, hmin q hq'⟩) hinv2
      refine ⟨(p, f p) :: sl', ?_, ?_⟩
      · exact List.mem_flatMap.mpr ⟨p, hp, List.mem_flatMap.mpr ⟨f p, hmemc,
          List.mem_map.mpr ⟨sl', hsl', rfl⟩⟩⟩
      · exact (hperm.cons _).trans ((List.perm_cons_erase hp).map (fun q => (q, f q))).symm

/-! ## The bridge to perfect numbers -/

/-- The product `∏ p/(p-1) * ∏ (1 - 1/p^(g p + 1))` as one fraction of natural numbers. -/
private theorem prod_eq_div (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) (g : ℕ → ℕ) :
    (∏ p ∈ S, (p : ℚ) / (p - 1)) * ∏ p ∈ S, (1 - ((p : ℚ) ^ (g p + 1))⁻¹) =
      ((∏ p ∈ S, p * (p ^ (g p + 1) - 1) : ℕ) : ℚ) /
        ((∏ p ∈ S, (p - 1) * p ^ (g p + 1) : ℕ) : ℚ) := by
  rw [← Finset.prod_mul_distrib, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h2 := hS p hp
  have h1 : 1 ≤ p ^ (g p + 1) := Nat.one_le_pow _ _ (by omega)
  have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast h2
  have hy : (0 : ℚ) < (p : ℚ) ^ (g p + 1) := by positivity
  push_cast [Nat.cast_sub h1, Nat.cast_sub (by omega : 1 ≤ p)]
  have : (p : ℚ) - 1 ≠ 0 := by linarith
  have h0 : (p : ℚ) ≠ 0 := by linarith
  field_simp

/-- The perfect number equation for a support `S`, cross multiplied in natural numbers. -/
private theorem two_eq_iff (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) (g : ℕ → ℕ) :
    (∏ p ∈ S, (p : ℚ) / (p - 1)) * ∏ p ∈ S, (1 - ((p : ℚ) ^ (g p + 1))⁻¹) = 2 ↔
      2 * ((∏ p ∈ S, (p - 1)) * ∏ p ∈ S, p ^ (g p + 1)) =
        (∏ p ∈ S, p) * ∏ p ∈ S, (p ^ (g p + 1) - 1) := by
  rw [prod_eq_div S hS g, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hD : (0 : ℚ) < (((∏ p ∈ S, (p - 1)) * ∏ p ∈ S, p ^ (g p + 1) : ℕ) : ℚ) := by
    have : 0 < (∏ p ∈ S, (p - 1)) * ∏ p ∈ S, p ^ (g p + 1) :=
      Nat.mul_pos (Finset.prod_pos fun p hp => by have := hS p hp; omega)
        (Finset.prod_pos fun p hp => by have := hS p hp; positivity)
    exact_mod_cast this
  rw [div_eq_iff hD.ne']
  constructor
  · intro h; exact_mod_cast h.symm
  · intro h; exact_mod_cast h.symm

/-- Prime factors and exponents of `∏ p ^ g p` over a set of primes with `g ≥ 1`. -/
private theorem factorization_prod_pow (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (k : ℕ → ℕ)
    (q : ℕ) : (∏ p ∈ S, p ^ k p).factorization q = if q ∈ S then k q else 0 := by
  rw [Nat.factorization_prod fun p hp => pow_ne_zero _ (hS p hp).ne_zero,
    Finset.sum_apply']
  have hc : ∑ p ∈ S, (p ^ k p).factorization q = ∑ p ∈ S, Finsupp.single p (k p) q :=
    Finset.sum_congr rfl fun p hp => by rw [(hS p hp).factorization_pow]
  rw [hc]
  split_ifs with hq
  · rw [Finset.sum_eq_single q (fun p _ hpq => by simp [hpq])
      (by simp [hq])]
    simp
  · exact Finset.sum_eq_zero fun p hp => by
      simp [show p ≠ q by rintro rfl; exact hq hp]

/-- `∏_{p ∈ S} p ^ g p` has prime support `S` when every `g p ≥ 1`. -/
private theorem primeFactors_prod_pow (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (g : ℕ → ℕ)
    (hg : ∀ p ∈ S, 1 ≤ g p) : (∏ p ∈ S, p ^ g p).primeFactors = S := by
  ext q
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_prod_pow S hS g]
  split_ifs with hq
  · simp only [hq, iff_true]; have := hg q hq; omega
  · simp [hq]

/-- The engine, started at `perfectSols`, finds the exponents of every perfect number with
support `l` (a duplicate free list) whose exponents obey the rule `ok`. -/
theorem exists_mem_perfectSols {ok : ℕ → ℕ → Bool} {l : List ℕ} (hnd : l.Nodup) {N : ℕ}
    (hN : N.Perfect) (hS : N.primeFactors = l.toFinset)
    (hok : ∀ p ∈ l, ok p (N.factorization p) = true) :
    ∃ sl ∈ perfectSols ok l, sl.Perm (l.map fun p => (p, N.factorization p)) := by
  unfold perfectSols
  have hmem : ∀ p ∈ l, p ∈ N.primeFactors := fun p hp => by
    rw [hS]; exact List.mem_toFinset.mpr hp
  have hpr : ∀ p ∈ l, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hmem p hp)
  have h2 : ∀ p ∈ l.toFinset, 2 ≤ p := fun p hp => (hpr p (List.mem_toFinset.mp hp)).two_le
  have key := two_eq_prod_mul_prod hN
  rw [hS, eq_comm, two_eq_iff _ h2 N.factorization] at key
  simp only [List.prod_toFinset _ hnd] at key
  refine sols_complete ok _ l _ _ 0 N.factorization hnd le_rfl ?_ (fun p hp => ?_) ?_
  · exact List.prod_pos fun p hp => (hpr p hp).pos
  · refine ⟨(hpr p hp).two_le, ?_, hok p hp, Nat.zero_le _⟩
    exact (hpr p hp).factorization_pos_of_dvd hN.2.ne'
      (Nat.dvd_of_mem_primeFactors (hmem p hp))
  · simp only [List.map_id'] at key
    rw [mul_assoc]; exact key

/-- Every output of `perfectSols` on a duplicate free list of primes is a perfect number with
that support. -/
theorem perfect_of_mem_perfectSols {ok : ℕ → ℕ → Bool} {l : List ℕ} (hnd : l.Nodup)
    (hl : ∀ p ∈ l, p.Prime) {sl : List (ℕ × ℕ)} (hsl : sl ∈ perfectSols ok l) :
    ∃ f : ℕ → ℕ, sl.Perm (l.map fun p => (p, f p)) ∧ (∀ p ∈ l, 1 ≤ f p ∧ ok p (f p) = true) ∧
      (∏ p ∈ l.toFinset, p ^ f p).Perfect ∧ (∏ p ∈ l.toFinset, p ^ f p).primeFactors = l.toFinset ∧
      ∀ p ∈ l, (∏ p ∈ l.toFinset, p ^ f p).factorization p = f p := by
  obtain ⟨f, hperm, hadm, hinv⟩ := sols_sound ok _ l _ _ _ sl hnd hsl
  have hS : ∀ p ∈ l.toFinset, p.Prime := fun p hp => hl p (List.mem_toFinset.mp hp)
  have h2 : ∀ p ∈ l.toFinset, 2 ≤ p := fun p hp => (hS p hp).two_le
  have hpf := primeFactors_prod_pow _ hS f fun p hp => (hadm p (List.mem_toFinset.mp hp)).1
  have hfac : ∀ p ∈ l, (∏ p ∈ l.toFinset, p ^ f p).factorization p = f p := fun p hp => by
    rw [factorization_prod_pow _ hS, if_pos (List.mem_toFinset.mpr hp)]
  refine ⟨f, hperm, hadm, ?_, hpf, hfac⟩
  set N := ∏ p ∈ l.toFinset, p ^ f p
  have hN : 0 < N := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  rw [perfect_iff_abundancy_eq_two hN, abundancy_eq_prod_mul_prod hN.ne', hpf]
  have hc : ∏ p ∈ l.toFinset, (1 - ((p : ℚ) ^ (N.factorization p + 1))⁻¹) =
      ∏ p ∈ l.toFinset, (1 - ((p : ℚ) ^ (f p + 1))⁻¹) :=
    Finset.prod_congr rfl fun p hp => by rw [hfac p (List.mem_toFinset.mp hp)]
  rw [hc, two_eq_iff _ h2 f]
  simp only [List.prod_toFinset _ hnd]
  rw [mul_assoc] at hinv
  simpa only [List.map_id'] using hinv

/-! ## Odd perfect numbers -/

/-- The dedup of the support. -/
private theorem toFinset_dedup' (S : List ℕ) : S.dedup.toFinset = S.toFinset := by
  ext; simp

/-- If `search S = false` (for a list `S` of odd primes), no odd perfect number has prime
support exactly `S`. -/
theorem no_oddPerfect_of_search (S : List ℕ) (hrun : search S = false) :
    ∀ N, OddPerfect N → N.primeFactors ≠ S.toFinset := by
  intro N h hS
  rw [← toFinset_dedup'] at hS
  obtain ⟨q, hq, hqN, hq4, hqe, hev⟩ := exists_special_prime h
  have hqS : q ∈ S.dedup := by
    rw [← List.mem_toFinset, ← hS]; exact Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩
  obtain ⟨sl, hsl, -⟩ := exists_mem_perfectSols (ok := okEuler q) (List.nodup_dedup S) h.perfect hS
    (fun p hp => by
      have hpp : p.Prime := by
        apply Nat.prime_of_mem_primeFactors (n := N); rw [hS]; exact List.mem_toFinset.mpr hp
      unfold okEuler
      split_ifs with hpq
      · subst hpq; simpa using hqe
      · simpa [Nat.even_iff] using hev p hpp hpq)
  have : search S = true := by
    unfold search
    refine List.any_eq_true.mpr ⟨q, hqS, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨by simp [hq4], ?_⟩
    cases hc : perfectSols (okEuler q) S.dedup with
    | nil => rw [hc] at hsl; simp at hsl
    | cons _ _ => rfl
  rw [hrun] at this; exact absurd this (by decide)

/-- Conversely, if `search S = true` for a list `S` of odd primes, some odd perfect number has
prime support exactly `S`. Together with `no_oddPerfect_of_search`, `search` decides the
question for each support. -/
theorem exists_oddPerfect_of_search (S : List ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hrun : search S = true) : ∃ N, OddPerfect N ∧ N.primeFactors = S.toFinset := by
  unfold search at hrun
  obtain ⟨q, -, hq⟩ := List.any_eq_true.mp hrun
  obtain ⟨sl, hsl⟩ : ∃ sl, sl ∈ perfectSols (okEuler q) S.dedup := by
    cases hc : perfectSols (okEuler q) S.dedup with
    | nil => rw [hc] at hq; simp at hq
    | cons sl rest => exact ⟨sl, by simp⟩
  have hl : ∀ p ∈ S.dedup, p.Prime := fun p hp => (hS p (List.mem_dedup.mp hp)).1
  obtain ⟨f, -, -, hperf, hpf, -⟩ := perfect_of_mem_perfectSols (List.nodup_dedup S) hl hsl
  refine ⟨_, ⟨?_, hperf⟩, by rw [hpf, toFinset_dedup']⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨p, hp, hdvd⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp h2
  have hp' := hS p (List.mem_dedup.mp (List.mem_toFinset.mp hp))
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp'.1).mp (Nat.prime_two.dvd_of_dvd_pow hdvd)
  exact hp'.2 this.symm


/-! ## Instances -/

/-- Positive control: with all exponents allowed, the only perfect number with support
`{2, 3}` is `6 = 2 * 3`. -/
theorem perfectSols_two_three : perfectSols (fun _ _ => true) [2, 3] = [[(2, 1), (3, 1)]] := by
  decide +kernel

/-- Positive control: the only perfect number with support `{2, 7}` is `28 = 2^2 * 7`. -/
theorem perfectSols_two_seven : perfectSols (fun _ _ => true) [2, 7] = [[(2, 2), (7, 1)]] := by
  decide +kernel

/-- Positive control: the only perfect number with support `{2, 31}` is `496 = 2^4 * 31`. -/
theorem perfectSols_two_thirtyone :
    perfectSols (fun _ _ => true) [2, 31] = [[(2, 4), (31, 1)]] := by
  decide +kernel

/-- The supports of size three left by the abundancy bound carry no odd perfect number. -/
theorem search_three : search [3, 5, 7] = false ∧ search [3, 5, 11] = false ∧
    search [3, 5, 13] = false := by
  decide +kernel

/-- No odd perfect number has support `{3, 5, s}` for `s ∈ {7, 11, 13}`, through the engine. -/
theorem primeFactors_ne_three {N : ℕ} (h : OddPerfect N) :
    N.primeFactors ≠ {3, 5, 7} ∧ N.primeFactors ≠ {3, 5, 11} ∧ N.primeFactors ≠ {3, 5, 13} := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using no_oddPerfect_of_search [3, 5, 7] search_three.1 N h
  · simpa using no_oddPerfect_of_search [3, 5, 11] search_three.2.1 N h
  · simpa using no_oddPerfect_of_search [3, 5, 13] search_three.2.2 N h

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The 70 supports `{3, 5, r, s}` with `17 ≤ r` of `OmegaFive`, through the engine. -/
theorem search_tab5 : ∀ r < 32, 17 ≤ r → isPrimeB r = true → ∀ s < 256, r < s →
    16 * (r - 1) * (s - 1) < 15 * r * s → isPrimeB s = true →
    search [3, 5, r, s] = false := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The 6 supports `{3, 7, r, s}` of `OmegaFive`, through the engine. -/
theorem search_tab7 : ∀ r < 16, 8 ≤ r → isPrimeB r = true → ∀ s < 27, r < s →
    8 * (r - 1) * (s - 1) < 7 * r * s → isPrimeB s = true →
    search [3, 7, r, s] = false := by
  decide +kernel

/-- The 20 supports `{3, 5, 11, s}` with `s ≤ 100` of `OmegaFive`, through the engine. -/
theorem search_tab11 : ∀ s < 101, 11 < s → isPrimeB s = true → search [3, 5, 11, s] = false := by
  decide +kernel

/-- The 8 supports `{3, 5, 13, s}` with `s ≤ 46` of `OmegaFive`, through the engine. -/
theorem search_tab13 : ∀ s < 47, 13 < s → isPrimeB s = true → search [3, 5, 13, s] = false := by
  decide +kernel

end FixedSupport

end OddPerfect

#print axioms OddPerfect.FixedSupport.prod_map_eq_mul_erase
#print axioms OddPerfect.FixedSupport.sols_sound
#print axioms OddPerfect.FixedSupport.sols_complete
#print axioms OddPerfect.FixedSupport.exists_mem_perfectSols
#print axioms OddPerfect.FixedSupport.perfect_of_mem_perfectSols
#print axioms OddPerfect.FixedSupport.no_oddPerfect_of_search
#print axioms OddPerfect.FixedSupport.exists_oddPerfect_of_search
#print axioms OddPerfect.FixedSupport.perfectSols_two_three
#print axioms OddPerfect.FixedSupport.perfectSols_two_seven
#print axioms OddPerfect.FixedSupport.perfectSols_two_thirtyone
#print axioms OddPerfect.FixedSupport.search_three
#print axioms OddPerfect.FixedSupport.primeFactors_ne_three
#print axioms OddPerfect.FixedSupport.search_tab5
#print axioms OddPerfect.FixedSupport.search_tab7
#print axioms OddPerfect.FixedSupport.search_tab11
#print axioms OddPerfect.FixedSupport.search_tab13
