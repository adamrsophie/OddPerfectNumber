import OddPerfect.Pratt
import OddPerfect.Phi3

/-!
# A checker for the forcing step of branch A

Branch A of `two_exceptions_five_three_sq_shape` has special prime 5, `e₃ = e₁₃ = 2`, and the
exceptions 61 and a prime `x ≡ 1 (mod 5)` with `Φ₅(x) ∣ N`. For `x < 116281` the contradiction
comes from a prime `t ∣ Φ₅(x)`, `t ∉ {5, 13, 61, x}`, that is `1 (mod 3)` or has
`t^2 + t + 1` divisible by a prime outside `{13, 61, x}`. This file defines a Boolean walk over
`n ≡ 1 (mod 10)` that certifies such a `t` for every prime `n` in a range (composite `n` carry a
divisor), and proves it sound.
-/

namespace OddPerfect.TwoExceptionThreeA

/-- The value `x^4 + x^3 + x^2 + x + 1`. -/
def phi5 (x : ℕ) : ℕ := x ^ 4 + x ^ 3 + x ^ 2 + x + 1

/-- Divide out the factor `g` from `z`, at most `fuel` times. -/
def stripOne (g : ℕ) : ℕ → ℕ → ℕ
  | 0, z => z
  | fuel + 1, z => if 1 < g && z % g == 0 then stripOne g fuel (z / g) else z

/-- Divide out every factor in the list. -/
def strip : ℕ → List ℕ → ℕ
  | z, [] => z
  | z, g :: l => strip (stripOne g 200 z) l

theorem stripOne_dvd (g : ℕ) : ∀ fuel z, stripOne g fuel z ∣ z
  | 0, z => dvd_refl z
  | fuel + 1, z => by
    unfold stripOne
    split_ifs with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact (stripOne_dvd g fuel (z / g)).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hc.2))
    · exact dvd_refl z

theorem strip_dvd : ∀ (l : List ℕ) (z : ℕ), strip z l ∣ z
  | [], z => dvd_refl z
  | g :: l, z => (strip_dvd l _).trans (stripOne_dvd g 200 z)

/-- Trial division by `d, d + 1, …` while `d * d ≤ w`, with fuel. -/
def noDiv (w : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, d => if w < d * d then true else (w % d != 0 && noDiv w k (d + 1))

theorem noDiv_sound (w : ℕ) : ∀ k d, noDiv w k d = true →
    ∀ m, d ≤ m → m * m ≤ w → w % m ≠ 0
  | 0, d, h => by simp [noDiv] at h
  | k + 1, d, h => by
    intro m hdm hmm
    unfold noDiv at h
    split_ifs at h with hlt
    · exact absurd (lt_of_lt_of_le hlt (le_trans (Nat.mul_le_mul hdm hdm) hmm)) (lt_irrefl w)
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.eq_or_lt_of_le hdm with rfl | hlt'
      · exact h.1
      · exact noDiv_sound w k (d + 1) h.2 m hlt' hmm

/-- Primality by trial division up to the square root. -/
def sqrtPrime (w : ℕ) : Bool := 2 ≤ w && noDiv w w 2

theorem sqrtPrime_sound {w : ℕ} (h : sqrtPrime w = true) : w.Prime := by
  simp only [sqrtPrime, Bool.and_eq_true, decide_eq_true_eq] at h
  refine Nat.prime_def_le_sqrt.mpr ⟨h.1, fun m hm hle hd => ?_⟩
  exact noDiv_sound w w 2 h.2 m hm (Nat.le_sqrt.mp hle) (Nat.mod_eq_zero_of_dvd hd)

/-- The cofactor of `t^2 + t + 1` after removing `13`, `61` and `n`. -/
def cof (n t : ℕ) : ℕ := strip (phi3 t) [13, 61, n]

/-- One entry of the walk: `n` is composite with divisor `w`, or `n = 61`, or `w` is a
witness prime for `n`. -/
def okEntry (P : List ℕ) (n w : ℕ) : Bool :=
  (1 < w && w < n && n % w == 0) || n == 61 ||
  (phi5 n % w == 0 && w != 5 && w != 61 && w != n && w != 13 &&
    (w % 3 == 1 || (cof n w != 1 && cof n w % 13 != 0 && cof n w % 61 != 0 &&
      cof n w % n != 0)) &&
    (P.contains w || sqrtPrime w))

/-- The walk over `n, n + 10, …`, ending exactly at `hi`. -/
def cover (P : List ℕ) : ℕ → List (ℕ × ℕ) → ℕ → Bool
  | n, [], hi => n == hi
  | n, (m, w) :: L, hi => m == n && okEntry P m w && cover P (n + 10) L hi

/-- What a witness gives. -/
def Good (x : ℕ) : Prop :=
  ∃ t, t.Prime ∧ t ∣ phi5 x ∧ t ≠ 5 ∧ t ≠ 61 ∧ t ≠ x ∧ t ≠ 13 ∧
    (t % 3 = 1 ∨ ∃ u, u.Prime ∧ u ∣ phi3 t ∧ u ≠ 13 ∧ u ≠ 61 ∧ u ≠ x)

theorem okEntry_sound {P : List ℕ} (hP : ∀ p ∈ P, p.Prime) {n w : ℕ}
    (h : okEntry P n w = true) (hn : n.Prime) (h61 : n ≠ 61) : Good n := by
  simp only [okEntry, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  rcases h with (⟨⟨h1, h2⟩, h3⟩ | h61') | ⟨⟨⟨⟨⟨⟨⟨hd, h5⟩, h6⟩, hn'⟩, h13⟩, hcase⟩, hpr⟩⟩
  · exfalso
    have := (Nat.prime_def_lt.mp hn).2 w h2 (Nat.dvd_of_mod_eq_zero h3)
    omega
  · exact absurd h61' h61
  · have hw : w.Prime := by
      rcases hpr with hc | hs
      · exact hP w (List.contains_iff_mem.mp hc)
      · exact sqrtPrime_sound hs
    refine ⟨w, hw, Nat.dvd_of_mod_eq_zero hd, h5, h6, hn', h13, ?_⟩
    rcases hcase with h1 | ⟨⟨⟨hc1, hc13⟩, hc61⟩, hcn⟩
    · exact Or.inl h1
    · right
      have hdvd : cof n w ∣ phi3 w := strip_dvd _ _
      refine ⟨(cof n w).minFac, Nat.minFac_prime hc1, (Nat.minFac_dvd _).trans hdvd, ?_, ?_, ?_⟩
      · intro he
        have hm := Nat.minFac_dvd (cof n w)
        rw [he] at hm
        exact hc13 (Nat.mod_eq_zero_of_dvd hm)
      · intro he
        have hm := Nat.minFac_dvd (cof n w)
        rw [he] at hm
        exact hc61 (Nat.mod_eq_zero_of_dvd hm)
      · intro he
        have hm := Nat.minFac_dvd (cof n w)
        rw [he] at hm
        exact hcn (Nat.mod_eq_zero_of_dvd hm)

theorem cover_sound {P : List ℕ} (hP : ∀ p ∈ P, p.Prime) {hi : ℕ} :
    ∀ (L : List (ℕ × ℕ)) (n : ℕ), cover P n L hi = true →
      ∀ x, n ≤ x → x < hi → x % 10 = n % 10 → x.Prime → x ≠ 61 → Good x
  | [], n, h => by
    intro x h1 h2
    simp only [cover, beq_iff_eq] at h
    omega
  | (m, w) :: L, n, h => by
    intro x h1 h2 h3 hx h61
    simp only [cover, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hok⟩, hrest⟩ := h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact okEntry_sound hP hok hx h61
    · exact cover_sound hP L (m + 10) hrest x (by omega) h2 (by omega) hx h61

end OddPerfect.TwoExceptionThreeA

#print axioms OddPerfect.TwoExceptionThreeA.stripOne_dvd
#print axioms OddPerfect.TwoExceptionThreeA.strip_dvd
#print axioms OddPerfect.TwoExceptionThreeA.noDiv_sound
#print axioms OddPerfect.TwoExceptionThreeA.sqrtPrime_sound
#print axioms OddPerfect.TwoExceptionThreeA.okEntry_sound
#print axioms OddPerfect.TwoExceptionThreeA.cover_sound
