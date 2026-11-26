import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The divisor sum of an even power of an odd prime is a square only for `3 ^ 4`

For an odd prime `p` and an even exponent `e = 2 k > 0`, the number
`σ(p ^ e) = 1 + p + ⋯ + p ^ e` is a perfect square only for `p = 3`, `e = 4`
(`σ(3 ^ 4) = 121 = 11 ^ 2`). This is the case of odd `n = e + 1` and prime `x` of the equation
`(x ^ n - 1) / (x - 1) = y ^ 2`, which is solved for all integers `x` in classical work (see Nagell
and Ljunggren).

The proof here uses only the Pell equation for `d = p (p - 1)`.

* From `σ(p ^ (2k)) = y ^ 2` we get `p U ^ 2 - (p - 1) V ^ 2 = 1` with `U = p ^ k`, `V = y`.
  In `ℤ√d` the element `β = p U + V √d` satisfies `β ^ 2 = p γ` with
  `γ = (2 p U ^ 2 - 1) + 2 U V √d`
  a solution of `x ^ 2 - d y ^ 2 = 1`. The fundamental solution is `ε = (2 p - 1) + 2 √d`
  (a solution with `y = ± 1` would make `p ^ 2 - p + 1` a square), so `γ = ε ^ n`. An even `n`
  would make `p ^ (2 k + 1)` a square. For odd `n = 2 t + 1` we get
  `(p + √d) ^ (2 t + 1) = p ^ t β`, since `(p + √d) ^ 2 = p ε`.
* Expanding `(p + √d) ^ m` with `m = 2 t + 1` by the binomial theorem, the real part is
  `p ^ (t + 1) U`. The term of index `2 t` equals `m p ^ (t + 1) (p - 1) ^ t`; for `p ≥ 5` every
  other
  term is divisible by `p ^ (t + 2 + v)` with `v = v_p(m)`, because
  `(2 s + 1) C(m, 2 s + 1) = m C(m - 1, 2 s)` and `v_p(2 s + 1) < s`. Hence `p ^ (v + 1) ∤ U`, so
  `p ^ k ∣ m`, while the same term gives `U ≥ m (p - 1) ^ t`. This is impossible for `k ≥ 1`.
* For `p = 3` the same expansion with `v = 0` gives `3 ∣ m`. Writing `m = 3 (2 t' + 1)` and
  `(3 + √6) ^ (2 t' + 1) = 3 ^ t' (3 A + B √6)`, cubing gives `3 ^ (k - 1) = A (4 A ^ 2 - 1)`, which
  forces `A = 1`, `t' = 0`, `m = 3` and `k = 2`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace SquareRow

/-- The real part of a finite sum in `ℤ√d`. -/
private theorem re_sum {d : ℤ} (s : Finset ℕ) (f : ℕ → ℤ√d) :
    (∑ j ∈ s, f j).re = ∑ j ∈ s, (f j).re := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Zsqrtd.re_add, ih]

private theorem re_sqrtd_pow_even (d : ℤ) (t : ℕ) :
    ((Zsqrtd.sqrtd : ℤ√d) ^ (2 * t)).re = d ^ t := by
  rw [pow_mul, sq, Zsqrtd.dmuld, ← Int.cast_pow, Zsqrtd.re_intCast]

private theorem re_sqrtd_pow_odd (d : ℤ) (t : ℕ) :
    ((Zsqrtd.sqrtd : ℤ√d) ^ (2 * t + 1)).re = 0 := by
  rw [pow_succ, pow_mul, sq, Zsqrtd.dmuld, ← Int.cast_pow, Zsqrtd.re_smul, Zsqrtd.re_sqrtd,
    mul_zero]

/-- Binomial expansion of the real part of `(P + √d) ^ m`. -/
private theorem re_pow_formula (P : ℤ) (m : ℕ) :
    ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ m).re = ∑ j ∈ Finset.range (m + 1),
      ((Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j).re * P ^ (m - j) * (m.choose j : ℤ) := by
  have h : (⟨P, 1⟩ : ℤ√(P * (P - 1))) = Zsqrtd.sqrtd + (P : ℤ√(P * (P - 1))) := by
    ext <;> simp
  rw [h, add_pow, re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j * (P : ℤ√(P * (P - 1))) ^ (m - j) *
      ((m.choose j : ℕ) : ℤ√(P * (P - 1))) =
      (((P ^ (m - j) * (m.choose j : ℤ)) : ℤ) : ℤ√(P * (P - 1))) * Zsqrtd.sqrtd ^ j := by
    push_cast; ring
  rw [e, Zsqrtd.re_smul]
  ring

/-- Powers of `P + √d`: `(P + √d) ^ (2 n + 1) = P ^ n (P A + B √d)` with
`P A ^ 2 - (P - 1) B ^ 2 = 1`. -/
private theorem rep (P : ℤ) (hP : 3 ≤ P) (n : ℕ) :
    ∃ A B : ℤ, (⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ (2 * n + 1) =
        ((P ^ n : ℤ) : ℤ√(P * (P - 1))) * ⟨P * A, B⟩ ∧
      P * A ^ 2 - (P - 1) * B ^ 2 = 1 ∧ 1 ≤ A ∧ 1 ≤ B ∧ (1 ≤ n → 2 ≤ A) := by
  induction n with
  | zero => exact ⟨1, 1, by ext <;> simp, by ring, le_rfl, le_rfl, by omega⟩
  | succ n ih =>
    obtain ⟨A, B, h, hn, hA, hB, -⟩ := ih
    refine ⟨(2 * P - 1) * A + 2 * (P - 1) * B, 2 * P * A + (2 * P - 1) * B, ?_,
      by linear_combination hn, by nlinarith, by nlinarith, fun _ => by nlinarith⟩
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, pow_add, h]
    ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul, pow_succ] <;> ring

/-- The Pell step: a solution `(U, V)` of `P U ^ 2 - (P - 1) V ^ 2 = 1` with `U, V ≥ 0` either makes
`P U ^ 2` a square or satisfies `(P + √d) ^ (2 t + 1) = P ^ t (P U + V √d)`. -/
private theorem stepA (P : ℤ) (hP : 3 ≤ P) (U V : ℤ) (hU : 1 ≤ U) (hV : 0 ≤ V)
    (h : P * U ^ 2 - (P - 1) * V ^ 2 = 1) :
    (∃ x : ℤ, P * U ^ 2 = x ^ 2) ∨
      ∃ t : ℕ, (⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ (2 * t + 1) =
        ((P ^ t : ℤ) : ℤ√(P * (P - 1))) * ⟨P * U, V⟩ := by
  let ε : Pell.Solution₁ (P * (P - 1)) := Pell.Solution₁.mk (2 * P - 1) 2 (by ring)
  let γ : Pell.Solution₁ (P * (P - 1)) := Pell.Solution₁.mk (2 * P * U ^ 2 - 1) (2 * U * V)
    (by linear_combination (4 * P * U ^ 2) * h)
  have hfund : Pell.IsFundamental ε := by
    refine ⟨by simp only [ε, Pell.Solution₁.x_mk]; omega, by simp [ε], fun {b} hb => ?_⟩
    have hy := Pell.Solution₁.y_ne_zero_of_one_lt_x hb
    have hprop := b.prop
    simp only [ε, Pell.Solution₁.x_mk]
    by_cases hy1 : b.y = 1 ∨ b.y = -1
    · exfalso
      have hy2 : b.y ^ 2 = 1 := by rcases hy1 with h1 | h1 <;> rw [h1] <;> norm_num
      rw [hy2] at hprop
      rcases le_or_gt b.x (P - 1) with h1 | h1
      · nlinarith
      · have h2 : P ≤ b.x := by omega
        nlinarith
    · have hy4 : 4 ≤ b.y ^ 2 := by
        rcases (show 2 ≤ b.y ∨ b.y ≤ -2 by omega) with h1 | h1 <;> nlinarith
      by_contra hlt
      push Not at hlt
      have h1 : P * (P - 1) * 4 ≤ P * (P - 1) * b.y ^ 2 :=
        mul_le_mul_of_nonneg_left hy4 (by nlinarith)
      nlinarith [mul_self_lt_mul_self (by omega : 0 ≤ b.x) hlt]
  have hγx : 0 < γ.x := by simp only [γ, Pell.Solution₁.x_mk]; nlinarith
  have hγy : 0 ≤ γ.y := by simp only [γ, Pell.Solution₁.y_mk]; positivity
  obtain ⟨n, hn⟩ := hfund.eq_pow_of_nonneg hγx hγy
  have hcoe : ∀ k : ℕ, ((ε ^ k : Pell.Solution₁ (P * (P - 1))) : ℤ√(P * (P - 1))) =
      (ε : ℤ√(P * (P - 1))) ^ k := fun k => SubmonoidClass.coe_pow ε k
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' n
  · left
    refine ⟨(ε ^ t).x, ?_⟩
    have hx := congrArg Pell.Solution₁.x hn
    rw [show 2 * t = t + t by ring, pow_add, Pell.Solution₁.x_mul] at hx
    simp only [γ, Pell.Solution₁.x_mk] at hx
    have hp := (ε ^ t).prop
    have : 2 * (P * U ^ 2) = 2 * (ε ^ t).x ^ 2 := by linear_combination hx - hp
    linarith
  · right
    refine ⟨t, ?_⟩
    obtain ⟨A, B, hrep, hn', hA, hB, -⟩ := rep P hP t
    have hb2 : (⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ 2 = (P : ℤ√(P * (P - 1))) * (ε : ℤ√(P * (P - 1))) := by
      ext <;> simp [ε, Pell.Solution₁.coe_mk, pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
    have hγ : (γ : ℤ√(P * (P - 1))) = (ε : ℤ√(P * (P - 1))) ^ (2 * t + 1) := by
      rw [← hcoe, ← hn]
    have key : ((P ^ (2 * t) : ℤ) : ℤ√(P * (P - 1))) * (⟨P * A, B⟩ ^ 2) =
        ((P ^ (2 * t + 1) : ℤ) : ℤ√(P * (P - 1))) * (γ : ℤ√(P * (P - 1))) := by
      calc ((P ^ (2 * t) : ℤ) : ℤ√(P * (P - 1))) * (⟨P * A, B⟩ ^ 2)
          = (((P ^ t : ℤ) : ℤ√(P * (P - 1))) * ⟨P * A, B⟩) ^ 2 := by push_cast; ring
        _ = ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ 2) ^ (2 * t + 1) := by rw [← hrep]; ring
        _ = _ := by rw [hb2, mul_pow, hγ]; push_cast; ring
    have hre := congrArg Zsqrtd.re key
    have him := congrArg Zsqrtd.im key
    rw [Zsqrtd.re_smul, Zsqrtd.re_smul, pow_two, Zsqrtd.re_mul] at hre
    rw [Zsqrtd.im_smul, Zsqrtd.im_smul, pow_two, Zsqrtd.im_mul] at him
    have hγre : (γ : ℤ√(P * (P - 1))).re = 2 * P * U ^ 2 - 1 := Pell.Solution₁.x_mk _ _ _
    have hγim : (γ : ℤ√(P * (P - 1))).im = 2 * U * V := Pell.Solution₁.y_mk _ _ _
    rw [hγre] at hre
    rw [hγim] at him
    dsimp only at hre him
    have hPt : P ^ (2 * t) ≠ 0 := pow_ne_zero _ (by omega)
    have hre' : P * A * (P * A) + P * (P - 1) * B * B = P * (2 * P * U ^ 2 - 1) := by
      apply mul_left_cancel₀ hPt
      rw [pow_succ] at hre
      linear_combination hre
    have him' : A * B = U * V := by
      apply mul_left_cancel₀ (mul_ne_zero hPt (by omega : (2 * P : ℤ) ≠ 0))
      rw [pow_succ] at him
      linear_combination him
    have hAU2 : (A - U) * (A + U) = 0 := by
      have : P ^ 2 * (2 * ((A - U) * (A + U))) = 0 := by linear_combination hre' + P * hn'
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (pow_ne_zero _ (by omega))
      · linarith
    have hAU : A = U := by
      rcases mul_eq_zero.mp hAU2 with h0 | h0
      · linarith
      · linarith
    subst hAU
    have hBV : B = V := mul_left_cancel₀ (by omega : A ≠ 0) him'
    subst hBV
    exact hrep

private theorem two_mul_add_one_lt_five_pow {s : ℕ} (hs : 1 ≤ s) : 2 * s + 1 < 5 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- For `p ≥ 5` and `p ^ v ∣ m = 2 i + 1`, every term `C(m, 2 t) p ^ (i - t)` with `t < i` is
divisible by `p ^ (v + 1)`. -/
private theorem choose_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {i v t : ℕ} (hv : p ^ v ∣ 2 * i + 1)
    (ht : t < i) : p ^ (v + 1) ∣ (2 * i + 1).choose (2 * t) * p ^ (i - t) := by
  obtain ⟨s, rfl⟩ : ∃ s, i = t + 1 + s := ⟨i - t - 1, by omega⟩
  have hsym : (2 * (t + 1 + s) + 1).choose (2 * t) = (2 * (t + 1 + s) + 1).choose (2 * s + 3) := by
    rw [← Nat.choose_symm (by omega : 2 * t ≤ 2 * (t + 1 + s) + 1)]
    congr 1
    omega
  rw [hsym, show t + 1 + s - t = s + 1 by omega]
  set c := (2 * (t + 1 + s) + 1).choose (2 * s + 3) with hc
  have hc0 : c ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hid : (2 * (t + 1 + s) + 1) * (2 * (t + 1 + s)).choose (2 * s + 2) = c * (2 * s + 3) := by
    rw [hc, Nat.add_one_mul_choose_eq]
  have hdv : p ^ v ∣ c * (2 * s + 3) := hid ▸ Dvd.dvd.mul_right hv _
  rw [hp.pow_dvd_iff_le_factorization (mul_ne_zero hc0 (by omega)),
    Nat.factorization_mul hc0 (by omega)] at hdv
  simp only [Finsupp.add_apply] at hdv
  have hw : (2 * s + 3).factorization p < s + 1 := by
    by_contra hge
    push Not at hge
    have h1 : p ^ (s + 1) ≤ 2 * s + 3 :=
      (Nat.pow_dvd_pow p hge).trans (Nat.ordProj_dvd _ p) |> Nat.le_of_dvd (by omega)
    have h2 : 5 ^ (s + 1) ≤ p ^ (s + 1) := Nat.pow_le_pow_left hp5 _
    have h3 := two_mul_add_one_lt_five_pow (by omega : 1 ≤ s + 1)
    omega
  rw [hp.pow_dvd_iff_le_factorization (mul_ne_zero hc0 (pow_ne_zero _ hp.ne_zero)),
    Nat.factorization_mul hc0 (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self]
  simp only [smul_eq_mul, mul_one]
  omega

/-- The valuation step: if all lower terms are divisible enough and `p ^ (v + 1) ∤ m`, then
`p ^ (v + 1) ∤ U`, where `p ^ (i + 1) U` is the real part of `(p + √d) ^ m`, `m = 2 i + 1`. -/
private theorem not_dvd_U {P : ℤ} (hP0 : P ≠ 0) (i v : ℕ) (U : ℤ)
    (hU : ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ (2 * i + 1)).re = P ^ (i + 1) * U)
    (hH : ∀ t < i, P ^ (v + 1) ∣ ((2 * i + 1).choose (2 * t) : ℤ) * P ^ (i - t))
    (hm : ¬ P ^ (v + 1) ∣ ((2 * i + 1 : ℕ) : ℤ)) : ¬ P ^ (v + 1) ∣ U := by
  intro hdiv
  rw [re_pow_formula] at hU
  set T : ℕ → ℤ := fun j => ((Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j).re * P ^ (2 * i + 1 - j) *
    ((2 * i + 1).choose j : ℤ) with hT
  have hsplit := Finset.add_sum_erase (Finset.range (2 * i + 1 + 1)) T
    (Finset.mem_range.mpr (by omega : 2 * i < 2 * i + 1 + 1))
  have hrest : P ^ (i + 1) * P ^ (v + 1) ∣
      ∑ j ∈ (Finset.range (2 * i + 1 + 1)).erase (2 * i), T j := by
    refine Finset.dvd_sum fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_erase.mp hj
    have hj2 := Finset.mem_range.mp hj2
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
    · have ht : t < i := by omega
      obtain ⟨c, hc⟩ := hH t ht
      obtain ⟨s, rfl⟩ : ∃ s, i = t + 1 + s := ⟨i - t - 1, by omega⟩
      rw [show t + 1 + s - t = s + 1 by omega] at hc
      simp only [hT, re_sqrtd_pow_even]
      rw [show 2 * (t + 1 + s) + 1 - 2 * t = 2 * s + 3 by omega]
      refine ⟨(P - 1) ^ t * c, ?_⟩
      calc (P * (P - 1)) ^ t * P ^ (2 * s + 3) * ((2 * (t + 1 + s) + 1).choose (2 * t) : ℤ)
          = (P - 1) ^ t * P ^ (t + 1 + s + 1) *
              (((2 * (t + 1 + s) + 1).choose (2 * t) : ℤ) * P ^ (s + 1)) := by
            rw [mul_pow]; ring
        _ = _ := by rw [hc]; ring
    · simp [hT, re_sqrtd_pow_odd]
  have hlead : T (2 * i) = P ^ (i + 1) * ((P - 1) ^ i * ((2 * i + 1 : ℕ) : ℤ)) := by
    simp only [hT, re_sqrtd_pow_even]
    rw [show 2 * i + 1 - 2 * i = 1 by omega, Nat.choose_succ_self_right, mul_pow]
    push_cast
    ring
  have htot : P ^ (i + 1) * P ^ (v + 1) ∣ T (2 * i) := by
    have h1 : P ^ (i + 1) * P ^ (v + 1) ∣ P ^ (i + 1) * U := mul_dvd_mul_left _ hdiv
    rw [← hU, ← hsplit] at h1
    exact (dvd_add_left hrest).mp h1
  rw [hlead] at htot
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hP0)).mp htot
  have hcop : IsCoprime (P ^ (v + 1)) ((P - 1) ^ i) :=
    IsCoprime.pow ⟨1, -1, by ring⟩
  exact hm (hcop.dvd_of_dvd_mul_left h2)

/-- The lower bound `U ≥ m (P - 1) ^ i` from the term of index `2 i`. -/
private theorem lower (P : ℤ) (hP : 3 ≤ P) (i : ℕ) (U : ℤ)
    (hU : ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ (2 * i + 1)).re = P ^ (i + 1) * U) :
    ((2 * i + 1 : ℕ) : ℤ) * (P - 1) ^ i ≤ U := by
  rw [re_pow_formula] at hU
  have hnn : ∀ j ∈ Finset.range (2 * i + 1 + 1),
      0 ≤ ((Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j).re * P ^ (2 * i + 1 - j) *
        ((2 * i + 1).choose j : ℤ) := by
    intro j _
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [re_sqrtd_pow_even]
      have : 0 ≤ P * (P - 1) := by nlinarith
      positivity
    · rw [re_sqrtd_pow_odd]; simp
  have h1 := Finset.single_le_sum hnn (Finset.mem_range.mpr (by omega : 2 * i < 2 * i + 1 + 1))
  rw [hU, re_sqrtd_pow_even, show 2 * i + 1 - 2 * i = 1 by omega,
    Nat.choose_succ_self_right, mul_pow] at h1
  have hpos : 0 < P ^ (i + 1) := by positivity
  have : P ^ (i + 1) * (((2 * i + 1 : ℕ) : ℤ) * (P - 1) ^ i) ≤ P ^ (i + 1) * U := by
    push_cast at h1 ⊢
    linear_combination h1
  exact le_of_mul_le_mul_left this hpos

private theorem three_dvd_of_dvd_three_pow {z : ℤ} {n : ℕ} (hz : 2 ≤ z) (h : z ∣ 3 ^ n) :
    3 ∣ z := by
  lift z to ℕ using (by omega)
  have h' : z ∣ 3 ^ n := by exact_mod_cast h
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h'
  have : j ≠ 0 := by rintro rfl; norm_num at hz
  exact_mod_cast dvd_pow_self 3 this

private theorem isSquare_of_even_factorization {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨n.factorization.prod fun p e => p ^ (e / 2), ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [← Finsupp.prod_mul]
  refine Finsupp.prod_congr fun p _ => ?_
  rw [← pow_add, ← two_mul, Nat.mul_div_cancel' (h p).two_dvd]

end SquareRow

open SquareRow in
/-- **Square rows.** For an odd prime `p` and an even exponent `e > 0`, the divisor sum
`σ(p ^ e) = 1 + p + ⋯ + p ^ e` is a perfect square exactly when `p = 3` and `e = 4`
(`σ(3 ^ 4) = 121 = 11 ^ 2`). This is a special case of classical results on
`(x ^ n - 1) / (x - 1) = y ^ 2` (see Nagell and Ljunggren); the proof here goes through the
Pell equation `x ^ 2 - p (p - 1) y ^ 2 = 1` and a `p`-adic valuation count. -/
theorem isSquare_sigma_prime_pow_iff {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : Even e)
    (he0 : e ≠ 0) : IsSquare (σ 1 (p ^ e)) ↔ p = 3 ∧ e = 4 := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := he
    have hk : 1 ≤ k := by omega
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    obtain ⟨P, hPdef⟩ : ∃ P : ℤ, P = p := ⟨_, rfl⟩
    have hP3 : (3 : ℤ) ≤ P := by rw [hPdef]; exact_mod_cast hp3
    have hgeom : (P - 1) * (y : ℤ) ^ 2 = P ^ (2 * k + 1) - 1 := by
      have h1 : ((σ 1 (p ^ (k + k)) : ℕ) : ℤ) = ∑ i ∈ Finset.range (k + k + 1), P ^ i := by
        rw [sigma_one_apply_prime_pow hp, hPdef]; push_cast; rfl
      have h2 := geom_sum_mul P (k + k + 1)
      rw [← h1, hy] at h2
      push_cast at h2
      rw [show 2 * k + 1 = k + k + 1 by ring]
      linear_combination h2
    have hpell : P * (P ^ k) ^ 2 - (P - 1) * (y : ℤ) ^ 2 = 1 := by
      rw [hgeom]; ring
    have hPk : P ≤ P ^ k := by
      calc P = P ^ 1 := (pow_one P).symm
        _ ≤ P ^ k := pow_le_pow_right₀ (by omega) hk
    rcases stepA P hP3 (P ^ k) y (by omega) (by positivity) hpell with ⟨x, hx⟩ | ⟨t, ht⟩
    · exfalso
      have hx' : p ^ (2 * k + 1) = x.natAbs ^ 2 := by
        have : ((p ^ (2 * k + 1) : ℕ) : ℤ) = ((x.natAbs ^ 2 : ℕ) : ℤ) := by
          rw [Nat.cast_pow, Nat.cast_pow, Int.natAbs_pow_two, ← hPdef, ← hx]
          ring
        exact_mod_cast this
      have := congrArg (fun n => n.factorization p) hx'
      simp [Nat.factorization_pow, hp.factorization_self] at this
      omega
    · have hre : ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ (2 * t + 1)).re = P ^ (t + 1) * P ^ k := by
        rw [ht, Zsqrtd.re_smul]; dsimp only; ring
      have hlow := lower P hP3 t (P ^ k) hre
      rcases (show p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h3 | h4 | h5
      · -- p = 3
        subst h3
        have hP : P = 3 := by rw [hPdef]; norm_num
        subst hP
        have h3m : 3 ∣ 2 * t + 1 := by
          by_contra hc
          refine not_dvd_U (by norm_num) t 0 (3 ^ k) hre (fun s hs => ?_) ?_ ?_
          · rw [zero_add, pow_one]
            exact Dvd.dvd.mul_left (dvd_pow_self (3 : ℤ) (by omega : t - s ≠ 0)) _
          · intro hd
            rw [zero_add, pow_one] at hd
            exact hc (by exact_mod_cast hd)
          · rw [zero_add, pow_one]
            exact dvd_pow_self (3 : ℤ) (by omega : k ≠ 0)
        obtain ⟨t', rfl⟩ : ∃ t', t = 3 * t' + 1 := ⟨t / 3, by omega⟩
        obtain ⟨A, B, hrep, hn', hA, -, hA2⟩ := rep 3 hP3 t'
        have hcube : (⟨3, 1⟩ : ℤ√(3 * (3 - 1))) ^ (2 * (3 * t' + 1) + 1) =
            ((⟨3, 1⟩ : ℤ√(3 * (3 - 1))) ^ (2 * t' + 1)) ^ 3 := by
          rw [← pow_mul]; congr 1; ring
        rw [hcube, hrep, mul_pow, ← Int.cast_pow, Zsqrtd.re_smul,
          show ((⟨3 * A, B⟩ : ℤ√(3 * (3 - 1))) ^ 3) =
            ⟨3 * A, B⟩ * ⟨3 * A, B⟩ * ⟨3 * A, B⟩ by ring] at hre
        simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] at hre
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hk' : A * (4 * A ^ 2 - 1) = 3 ^ k' := by
          have h27 : (3 : ℤ) ^ (3 * t') * 27 ≠ 0 := by positivity
          apply mul_left_cancel₀ h27
          linear_combination hre + (3 : ℤ) ^ (3 * t') * 27 * A * hn'
        have hA1 : A = 1 := by
          by_contra hne
          have hA2' : 2 ≤ A := by omega
          have h1 : 3 ∣ A := three_dvd_of_dvd_three_pow hA2' (Dvd.intro _ hk')
          have h2 : 3 ∣ 4 * A ^ 2 - 1 :=
            three_dvd_of_dvd_three_pow (by nlinarith) (Dvd.intro_left _ hk')
          have h3 := dvd_sub (dvd_mul_of_dvd_left h1 (4 * A)) h2
          rw [show A * (4 * A) - (4 * A ^ 2 - 1) = 1 by ring] at h3
          norm_num at h3
        subst hA1
        have ht' : t' = 0 := by
          by_contra hne
          have := hA2 (by omega)
          omega
        subst ht'
        have hk1 : k' = 1 := by
          have h3 : (3 : ℤ) ^ k' = 3 ^ 1 := by rw [← hk']; norm_num
          have h3' : (3 : ℕ) ^ k' = 3 ^ 1 := by exact_mod_cast h3
          exact Nat.pow_right_injective (by norm_num) h3'
        subst hk1
        exact ⟨rfl, rfl⟩
      · subst h4; exact absurd hp (by decide)
      · exfalso
        set v := (2 * t + 1).factorization p
        have hv : p ^ v ∣ 2 * t + 1 := Nat.ordProj_dvd _ p
        have hnv : ¬ p ^ (v + 1) ∣ 2 * t + 1 := Nat.pow_succ_factorization_not_dvd (by omega) hp
        have hH : ∀ s < t, P ^ (v + 1) ∣ ((2 * t + 1).choose (2 * s) : ℤ) * P ^ (t - s) :=
          fun s hs => by rw [hPdef]; exact_mod_cast choose_dvd hp h5 hv hs
        have hnd := not_dvd_U (by omega) t v (P ^ k) hre hH
          (fun hd => hnv (by rw [hPdef] at hd; exact_mod_cast hd))
        have hkv : k ≤ v := by
          by_contra hlt
          exact hnd (pow_dvd_pow _ (by omega))
        have hpk : p ^ k ≤ 2 * t + 1 :=
          Nat.le_of_dvd (by omega) ((Nat.pow_dvd_pow p hkv).trans hv)
        have hpk' : P ^ k ≤ ((2 * t + 1 : ℕ) : ℤ) := by rw [hPdef]; exact_mod_cast hpk
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0
          norm_num at hpk'
          linarith
        · have hP1 : 2 ≤ (P - 1) ^ t := by
            calc (2 : ℤ) ≤ (P - 1) ^ 1 := by simp; omega
              _ ≤ (P - 1) ^ t := pow_le_pow_right₀ (by omega) h0
          have hm0 : (0 : ℤ) < ((2 * t + 1 : ℕ) : ℤ) := by positivity
          nlinarith
  · rintro ⟨rfl, rfl⟩
    refine ⟨11, ?_⟩
    rw [sigma_one_apply_prime_pow Nat.prime_three]
    decide

open SquareRow in
/-- **An odd valuation in a non-square row.** For an odd prime `p` and an even exponent `e > 0` with
`(p, e) ≠ (3, 4)`, some prime `r` divides `σ(p ^ e)` to an odd power. -/
theorem exists_prime_odd_factorization_sigma {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : Even e)
    (he0 : e ≠ 0) (h34 : ¬ (p = 3 ∧ e = 4)) :
    ∃ r, r.Prime ∧ Odd ((σ 1 (p ^ e)).factorization r) := by
  by_contra hno
  push Not at hno
  apply h34
  rw [← isSquare_sigma_prime_pow_iff hp hp2 he he0]
  refine isSquare_of_even_factorization (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne' fun r => ?_
  by_cases hr : r.Prime
  · exact hno r hr
  · rw [Nat.factorization_eq_zero_of_not_prime _ hr]
    exact ⟨0, rfl⟩

end OddPerfect

#print axioms OddPerfect.isSquare_sigma_prime_pow_iff
#print axioms OddPerfect.exists_prime_odd_factorization_sigma
