import Mathlib.NumberTheory.Pell
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Geometric sums with a prime power base are not squares

Let `q ≥ 5` be a prime and `u = q ^ h` with `h ≥ 1`. For odd `n ≥ 3` we show:

* `geom_sum_prime_pow_ne_sq`: for odd `h`, the sum `1 + u + ⋯ + u ^ (n - 1)` is not a square;
* `alternating_sum_prime_pow_ne_sq`: for `u ≡ 1 (mod 4)`, the quotient `(u ^ n + 1) / (u + 1)`
  is not a square, that is `u ^ n + 1 ≠ (u + 1) y ^ 2`.

Both are special cases of Ljunggren's theorem on `(x ^ n - 1) / (x - 1) = y ^ 2` (with `x = u`
and `x = -u`); nothing new is claimed. That the classical statement covers a negative base was
not page checked. The proof follows `OddPerfect.SquareRow`, which treats a
prime base, and replaces the valuation at the base by the valuation at `q`.

* Positive sum: with `P = u`, `U = u ^ k` (`n = 2 k + 1`) and `V = y` we get
  `P U ^ 2 - (P - 1) V ^ 2 = 1`. The Pell step either makes `u ^ n` a square (impossible, as
  `h n` is odd) or gives `(P + √d) ^ (2 t + 1) = P ^ t (P U + V √d)` with `d = P (P - 1)`.
  In the real part, every term except `m (P - 1) ^ t` (`m = 2 t + 1`) is divisible by
  `q ^ (v_q(m) + 1)`, so the power `U` of `q` divides `m`, against `U ≥ m (P - 1) ^ t`.
* Alternating sum: with `P = u + 1`, `U = y` and `V = u ^ k` the same Pell equation holds. The
  first branch makes `u + 1 ≡ 2 (mod 4)` a square. In the second branch the imaginary part
  gives `V = ∑ C(m, 2 s + 1) P ^ (t - s) u ^ s`; the term `s = 0` is `m P ^ t` with `q ∤ P`,
  and every other term is divisible by `q ^ (v_q(m) + 1)`. So `V ∣ m`, against `V ≥ m P ^ t`.
-/

namespace OddPerfect

namespace SignedRepunit

/-- The real part of a finite sum in `ℤ√d`. -/
private theorem sr_re_sum {d : ℤ} (s : Finset ℕ) (f : ℕ → ℤ√d) :
    (∑ j ∈ s, f j).re = ∑ j ∈ s, (f j).re := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Zsqrtd.re_add, ih]

/-- The imaginary part of a finite sum in `ℤ√d`. -/
private theorem sr_im_sum {d : ℤ} (s : Finset ℕ) (f : ℕ → ℤ√d) :
    (∑ j ∈ s, f j).im = ∑ j ∈ s, (f j).im := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Zsqrtd.im_add, ih]

private theorem sr_re_sqrtd_pow_even (d : ℤ) (t : ℕ) :
    ((Zsqrtd.sqrtd : ℤ√d) ^ (2 * t)).re = d ^ t := by
  rw [pow_mul, sq, Zsqrtd.dmuld, ← Int.cast_pow, Zsqrtd.re_intCast]

private theorem sr_re_sqrtd_pow_odd (d : ℤ) (t : ℕ) :
    ((Zsqrtd.sqrtd : ℤ√d) ^ (2 * t + 1)).re = 0 := by
  rw [pow_succ, pow_mul, sq, Zsqrtd.dmuld, ← Int.cast_pow, Zsqrtd.re_smul, Zsqrtd.re_sqrtd,
    mul_zero]

private theorem sr_im_sqrtd_pow_even (d : ℤ) (t : ℕ) :
    ((Zsqrtd.sqrtd : ℤ√d) ^ (2 * t)).im = 0 := by
  rw [pow_mul, sq, Zsqrtd.dmuld, ← Int.cast_pow, Zsqrtd.im_intCast]

private theorem sr_im_sqrtd_pow_odd (d : ℤ) (t : ℕ) :
    ((Zsqrtd.sqrtd : ℤ√d) ^ (2 * t + 1)).im = d ^ t := by
  rw [pow_succ, pow_mul, sq, Zsqrtd.dmuld, ← Int.cast_pow, Zsqrtd.im_smul, Zsqrtd.im_sqrtd,
    mul_one]

/-- Binomial expansion of the real part of `(P + √d) ^ m`. -/
private theorem sr_re_pow_formula (P : ℤ) (m : ℕ) :
    ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ m).re = ∑ j ∈ Finset.range (m + 1),
      ((Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j).re * P ^ (m - j) * (m.choose j : ℤ) := by
  have h : (⟨P, 1⟩ : ℤ√(P * (P - 1))) = Zsqrtd.sqrtd + (P : ℤ√(P * (P - 1))) := by
    ext <;> simp
  rw [h, add_pow, sr_re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j * (P : ℤ√(P * (P - 1))) ^ (m - j) *
      ((m.choose j : ℕ) : ℤ√(P * (P - 1))) =
      (((P ^ (m - j) * (m.choose j : ℤ)) : ℤ) : ℤ√(P * (P - 1))) * Zsqrtd.sqrtd ^ j := by
    push_cast; ring
  rw [e, Zsqrtd.re_smul]
  ring

/-- Binomial expansion of the imaginary part of `(P + √d) ^ m`. -/
private theorem sr_im_pow_formula (P : ℤ) (m : ℕ) :
    ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ m).im = ∑ j ∈ Finset.range (m + 1),
      ((Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j).im * P ^ (m - j) * (m.choose j : ℤ) := by
  have h : (⟨P, 1⟩ : ℤ√(P * (P - 1))) = Zsqrtd.sqrtd + (P : ℤ√(P * (P - 1))) := by
    ext <;> simp
  rw [h, add_pow, sr_im_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j * (P : ℤ√(P * (P - 1))) ^ (m - j) *
      ((m.choose j : ℕ) : ℤ√(P * (P - 1))) =
      (((P ^ (m - j) * (m.choose j : ℤ)) : ℤ) : ℤ√(P * (P - 1))) * Zsqrtd.sqrtd ^ j := by
    push_cast; ring
  rw [e, Zsqrtd.im_smul]
  ring

/-- Powers of `P + √d`: `(P + √d) ^ (2 n + 1) = P ^ n (P A + B √d)` with
`P A ^ 2 - (P - 1) B ^ 2 = 1`. -/
private theorem sr_rep (P : ℤ) (hP : 3 ≤ P) (n : ℕ) :
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

/-- The Pell step: a solution `(U, V)` of `P U ^ 2 - (P - 1) V ^ 2 = 1` with `U, V ≥ 0` either
makes `P U ^ 2` a square or satisfies `(P + √d) ^ (2 t + 1) = P ^ t (P U + V √d)`. -/
private theorem sr_stepA (P : ℤ) (hP : 3 ≤ P) (U V : ℤ) (hU : 1 ≤ U) (hV : 0 ≤ V)
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
    obtain ⟨A, B, hrep, hn', hA, hB, -⟩ := sr_rep P hP t
    have hb2 : (⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ 2 =
        (P : ℤ√(P * (P - 1))) * (ε : ℤ√(P * (P - 1))) := by
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

private theorem sr_two_mul_add_one_lt_five_pow {s : ℕ} (hs : 1 ≤ s) : 2 * s + 1 < 5 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- For `q ≥ 5` prime and `q ^ v ∣ m = 2 i + 1`, every term `C(m, 2 t) q ^ (i - t)` with `t < i`
is divisible by `q ^ (v + 1)`. -/
private theorem sr_choose_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {i v t : ℕ}
    (hv : p ^ v ∣ 2 * i + 1) (ht : t < i) :
    p ^ (v + 1) ∣ (2 * i + 1).choose (2 * t) * p ^ (i - t) := by
  obtain ⟨s, rfl⟩ : ∃ s, i = t + 1 + s := ⟨i - t - 1, by omega⟩
  have hsym : (2 * (t + 1 + s) + 1).choose (2 * t) =
      (2 * (t + 1 + s) + 1).choose (2 * s + 3) := by
    rw [← Nat.choose_symm (by omega : 2 * t ≤ 2 * (t + 1 + s) + 1)]
    congr 1
    omega
  rw [hsym, show t + 1 + s - t = s + 1 by omega]
  set c := (2 * (t + 1 + s) + 1).choose (2 * s + 3) with hc
  have hc0 : c ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hid : (2 * (t + 1 + s) + 1) * (2 * (t + 1 + s)).choose (2 * s + 2) =
      c * (2 * s + 3) := by
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
    have h3 := sr_two_mul_add_one_lt_five_pow (by omega : 1 ≤ s + 1)
    omega
  rw [hp.pow_dvd_iff_le_factorization (mul_ne_zero hc0 (pow_ne_zero _ hp.ne_zero)),
    Nat.factorization_mul hc0 (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self]
  simp only [smul_eq_mul, mul_one]
  omega

/-- The odd index form: for `1 ≤ s ≤ i`, `q ^ (v + 1)` divides `C(2 i + 1, 2 s + 1) q ^ s`. -/
private theorem sr_choose_dvd_odd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {i v s : ℕ}
    (hv : p ^ v ∣ 2 * i + 1) (hs1 : 1 ≤ s) (hs : s ≤ i) :
    p ^ (v + 1) ∣ (2 * i + 1).choose (2 * s + 1) * p ^ s := by
  have h := sr_choose_dvd hp hp5 hv (t := i - s) (by omega)
  have hsym : (2 * i + 1).choose (2 * (i - s)) = (2 * i + 1).choose (2 * s + 1) := by
    rw [← Nat.choose_symm (by omega : 2 * (i - s) ≤ 2 * i + 1)]
    congr 1
    omega
  rwa [hsym, show i - (i - s) = s by omega] at h

/-- The valuation step for the real part, with a general modulus `D` coprime to `P - 1`. -/
private theorem sr_re_not_dvd {P D : ℤ} (hP0 : P ≠ 0) (i : ℕ) (U : ℤ)
    (hU : ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ (2 * i + 1)).re = P ^ (i + 1) * U)
    (hH : ∀ t < i, D ∣ ((2 * i + 1).choose (2 * t) : ℤ) * P ^ (i - t))
    (hcop : IsCoprime D (P - 1)) (hm : ¬ D ∣ ((2 * i + 1 : ℕ) : ℤ)) : ¬ D ∣ U := by
  intro hdiv
  rw [sr_re_pow_formula] at hU
  set T : ℕ → ℤ := fun j => ((Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j).re * P ^ (2 * i + 1 - j) *
    ((2 * i + 1).choose j : ℤ) with hT
  have hsplit := Finset.add_sum_erase (Finset.range (2 * i + 1 + 1)) T
    (Finset.mem_range.mpr (by omega : 2 * i < 2 * i + 1 + 1))
  have hrest : P ^ (i + 1) * D ∣
      ∑ j ∈ (Finset.range (2 * i + 1 + 1)).erase (2 * i), T j := by
    refine Finset.dvd_sum fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_erase.mp hj
    have hj2 := Finset.mem_range.mp hj2
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
    · have ht : t < i := by omega
      obtain ⟨c, hc⟩ := hH t ht
      obtain ⟨s, rfl⟩ : ∃ s, i = t + 1 + s := ⟨i - t - 1, by omega⟩
      rw [show t + 1 + s - t = s + 1 by omega] at hc
      simp only [hT, sr_re_sqrtd_pow_even]
      rw [show 2 * (t + 1 + s) + 1 - 2 * t = 2 * s + 3 by omega]
      refine ⟨(P - 1) ^ t * c, ?_⟩
      calc (P * (P - 1)) ^ t * P ^ (2 * s + 3) * ((2 * (t + 1 + s) + 1).choose (2 * t) : ℤ)
          = (P - 1) ^ t * P ^ (t + 1 + s + 1) *
              (((2 * (t + 1 + s) + 1).choose (2 * t) : ℤ) * P ^ (s + 1)) := by
            rw [mul_pow]; ring
        _ = _ := by rw [hc]; ring
    · simp [hT, sr_re_sqrtd_pow_odd]
  have hlead : T (2 * i) = P ^ (i + 1) * ((P - 1) ^ i * ((2 * i + 1 : ℕ) : ℤ)) := by
    simp only [hT, sr_re_sqrtd_pow_even]
    rw [show 2 * i + 1 - 2 * i = 1 by omega, Nat.choose_succ_self_right, mul_pow]
    push_cast
    ring
  have htot : P ^ (i + 1) * D ∣ T (2 * i) := by
    have h1 : P ^ (i + 1) * D ∣ P ^ (i + 1) * U := mul_dvd_mul_left _ hdiv
    rw [← hU, ← hsplit] at h1
    exact (dvd_add_left hrest).mp h1
  rw [hlead] at htot
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hP0)).mp htot
  exact hm ((hcop.pow_right (n := i)).dvd_of_dvd_mul_left h2)

/-- The lower bound `U ≥ m (P - 1) ^ i` from the term of index `2 i` of the real part. -/
private theorem sr_re_lower (P : ℤ) (hP : 3 ≤ P) (i : ℕ) (U : ℤ)
    (hU : ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ (2 * i + 1)).re = P ^ (i + 1) * U) :
    ((2 * i + 1 : ℕ) : ℤ) * (P - 1) ^ i ≤ U := by
  rw [sr_re_pow_formula] at hU
  have hnn : ∀ j ∈ Finset.range (2 * i + 1 + 1),
      0 ≤ ((Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j).re * P ^ (2 * i + 1 - j) *
        ((2 * i + 1).choose j : ℤ) := by
    intro j _
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [sr_re_sqrtd_pow_even]
      have : 0 ≤ P * (P - 1) := by nlinarith
      positivity
    · rw [sr_re_sqrtd_pow_odd]; simp
  have h1 := Finset.single_le_sum hnn (Finset.mem_range.mpr (by omega : 2 * i < 2 * i + 1 + 1))
  rw [hU, sr_re_sqrtd_pow_even, show 2 * i + 1 - 2 * i = 1 by omega,
    Nat.choose_succ_self_right, mul_pow] at h1
  have hpos : 0 < P ^ (i + 1) := by positivity
  have : P ^ (i + 1) * (((2 * i + 1 : ℕ) : ℤ) * (P - 1) ^ i) ≤ P ^ (i + 1) * U := by
    push_cast at h1 ⊢
    linear_combination h1
  exact le_of_mul_le_mul_left this hpos

/-- The valuation step for the imaginary part, with a general modulus `D` coprime to `P`: if
`P ^ i V` is the imaginary part of `(P + √d) ^ (2 i + 1)`, every term of index `2 s + 1` with
`s ≥ 1` is divisible enough and `D ∤ 2 i + 1`, then `D ∤ V`. -/
private theorem sr_im_not_dvd {P D : ℤ} (hP0 : P ≠ 0) (i : ℕ) (V : ℤ)
    (hV : ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ (2 * i + 1)).im = P ^ i * V)
    (hH : ∀ s, 1 ≤ s → s ≤ i → D ∣ ((2 * i + 1).choose (2 * s + 1) : ℤ) * (P - 1) ^ s)
    (hcop : IsCoprime D P) (hm : ¬ D ∣ ((2 * i + 1 : ℕ) : ℤ)) : ¬ D ∣ V := by
  intro hdiv
  rw [sr_im_pow_formula] at hV
  set T : ℕ → ℤ := fun j => ((Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j).im * P ^ (2 * i + 1 - j) *
    ((2 * i + 1).choose j : ℤ) with hT
  have hsplit := Finset.add_sum_erase (Finset.range (2 * i + 1 + 1)) T
    (Finset.mem_range.mpr (by omega : 1 < 2 * i + 1 + 1))
  have hrest : P ^ i * D ∣ ∑ j ∈ (Finset.range (2 * i + 1 + 1)).erase 1, T j := by
    refine Finset.dvd_sum fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_erase.mp hj
    have hj2 := Finset.mem_range.mp hj2
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' j
    · simp [hT, sr_im_sqrtd_pow_even]
    · have hs1 : 1 ≤ s := by omega
      obtain ⟨c, hc⟩ := hH s hs1 (by omega)
      obtain ⟨r, rfl⟩ : ∃ r, i = s + r := ⟨i - s, by omega⟩
      simp only [hT, sr_im_sqrtd_pow_odd]
      rw [show 2 * (s + r) + 1 - (2 * s + 1) = 2 * r by omega]
      refine ⟨P ^ r * c, ?_⟩
      calc (P * (P - 1)) ^ s * P ^ (2 * r) * ((2 * (s + r) + 1).choose (2 * s + 1) : ℤ)
          = P ^ (s + r) *
              (P ^ r * (((2 * (s + r) + 1).choose (2 * s + 1) : ℤ) * (P - 1) ^ s)) := by
            rw [mul_pow]; ring
        _ = _ := by rw [hc]; ring
  have hlead : T 1 = P ^ i * (P ^ i * ((2 * i + 1 : ℕ) : ℤ)) := by
    simp only [hT, pow_one, Zsqrtd.im_sqrtd, Nat.choose_one_right]
    rw [show 2 * i + 1 - 1 = i + i by omega, pow_add]
    push_cast
    ring
  have htot : P ^ i * D ∣ T 1 := by
    have h1 : P ^ i * D ∣ P ^ i * V := mul_dvd_mul_left _ hdiv
    rw [← hV, ← hsplit] at h1
    exact (dvd_add_left hrest).mp h1
  rw [hlead] at htot
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hP0)).mp htot
  exact hm ((hcop.pow_right (n := i)).dvd_of_dvd_mul_left h2)

/-- The lower bound `V ≥ P ^ i m` from the term of index `1` of the imaginary part. -/
private theorem sr_im_lower (P : ℤ) (hP : 3 ≤ P) (i : ℕ) (V : ℤ)
    (hV : ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ (2 * i + 1)).im = P ^ i * V) :
    P ^ i * ((2 * i + 1 : ℕ) : ℤ) ≤ V := by
  rw [sr_im_pow_formula] at hV
  have hnn : ∀ j ∈ Finset.range (2 * i + 1 + 1),
      0 ≤ ((Zsqrtd.sqrtd : ℤ√(P * (P - 1))) ^ j).im * P ^ (2 * i + 1 - j) *
        ((2 * i + 1).choose j : ℤ) := by
    intro j _
    obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [sr_im_sqrtd_pow_even]; simp
    · rw [sr_im_sqrtd_pow_odd]
      have : 0 ≤ P * (P - 1) := by nlinarith
      positivity
  have h1 := Finset.single_le_sum hnn (Finset.mem_range.mpr (by omega : 1 < 2 * i + 1 + 1))
  rw [hV, pow_one, Zsqrtd.im_sqrtd, Nat.choose_one_right,
    show 2 * i + 1 - 1 = i + i by omega, pow_add] at h1
  have hpos : 0 < P ^ i := by positivity
  have : P ^ i * (P ^ i * ((2 * i + 1 : ℕ) : ℤ)) ≤ P ^ i * V := by
    push_cast at h1 ⊢
    linear_combination h1
  exact le_of_mul_le_mul_left this hpos

end SignedRepunit

open SignedRepunit in
/-- **Prime power repunits are not squares.** For a prime `q ≥ 5`, an odd `h` and an odd
`n ≥ 3`, the sum `1 + q ^ h + ⋯ + (q ^ h) ^ (n - 1)` is not a perfect square. This is a special
case of Ljunggren's theorem on `(x ^ n - 1) / (x - 1) = y ^ 2`; nothing new is claimed. The proof
goes through the Pell equation `x ^ 2 - u (u - 1) y ^ 2 = 1` with `u = q ^ h` and a `q`-adic
valuation count. -/
theorem geom_sum_prime_pow_ne_sq {q h n y : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hh : Odd h)
    (hn : Odd n) (hn3 : 3 ≤ n) : ∑ i ∈ Finset.range n, (q ^ h) ^ i ≠ y ^ 2 := by
  intro hy
  obtain ⟨k, rfl⟩ := hn
  have hk : 1 ≤ k := by omega
  have hh1 : 1 ≤ h := hh.pos
  obtain ⟨P, hPdef⟩ : ∃ P : ℤ, P = (q : ℤ) ^ h := ⟨_, rfl⟩
  have hu5 : 5 ≤ q ^ h := le_trans hq5 (Nat.le_self_pow (by omega) q)
  have hP5 : (5 : ℤ) ≤ P := by rw [hPdef]; exact_mod_cast hu5
  have hgeom : (P - 1) * (y : ℤ) ^ 2 = P ^ (2 * k + 1) - 1 := by
    have h1 : ((∑ i ∈ Finset.range (2 * k + 1), (q ^ h) ^ i : ℕ) : ℤ) =
        ∑ i ∈ Finset.range (2 * k + 1), P ^ i := by
      rw [hPdef]; push_cast; rfl
    have h2 := geom_sum_mul P (2 * k + 1)
    rw [← h1, hy] at h2
    push_cast at h2
    linear_combination h2
  have hpell : P * (P ^ k) ^ 2 - (P - 1) * (y : ℤ) ^ 2 = 1 := by
    rw [hgeom]; ring
  have hPk : P ≤ P ^ k := by
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ k := pow_le_pow_right₀ (by omega) hk
  rcases sr_stepA P (by omega) (P ^ k) y (by omega) (by positivity) hpell with
    ⟨x, hx⟩ | ⟨t, ht⟩
  · have hx' : q ^ (h * (2 * k + 1)) = x.natAbs ^ 2 := by
      have : ((q ^ (h * (2 * k + 1)) : ℕ) : ℤ) = ((x.natAbs ^ 2 : ℕ) : ℤ) := by
        rw [Nat.cast_pow, Nat.cast_pow, Int.natAbs_pow_two, ← hx, hPdef, pow_mul]
        ring
      exact_mod_cast this
    have hfac := congrArg (fun n => n.factorization q) hx'
    simp [Nat.factorization_pow, hq.factorization_self] at hfac
    have hodd : Odd (h * (2 * k + 1)) := hh.mul (odd_two_mul_add_one k)
    obtain ⟨r, hr⟩ := hodd
    omega
  · have hre : ((⟨P, 1⟩ : ℤ√(P * (P - 1))) ^ (2 * t + 1)).re = P ^ (t + 1) * P ^ k := by
      rw [ht, Zsqrtd.re_smul]; dsimp only; ring
    have hlow := sr_re_lower P (by omega) t (P ^ k) hre
    set v := (2 * t + 1).factorization q
    have hv : q ^ v ∣ 2 * t + 1 := Nat.ordProj_dvd _ q
    have hnv : ¬ q ^ (v + 1) ∣ 2 * t + 1 := Nat.pow_succ_factorization_not_dvd (by omega) hq
    have hH : ∀ s < t,
        ((q : ℤ) ^ (v + 1)) ∣ ((2 * t + 1).choose (2 * s) : ℤ) * P ^ (t - s) := by
      intro s hs
      have h1 := sr_choose_dvd hq hq5 hv hs
      have h2 : q ^ (t - s) ∣ (q ^ h) ^ (t - s) := by
        rw [← pow_mul]; exact Nat.pow_dvd_pow q (by nlinarith)
      have h3 := h1.trans (Nat.mul_dvd_mul_left _ h2)
      rw [hPdef]; exact_mod_cast h3
    have hcop : IsCoprime ((q : ℤ) ^ (v + 1)) (P - 1) := by
      apply IsCoprime.pow_left
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      exact ⟨(q : ℤ) ^ h', -1, by rw [hPdef]; ring⟩
    have hnd := sr_re_not_dvd (by omega) t (P ^ k) hre hH hcop
      (fun hd => hnv (by exact_mod_cast hd))
    have hkv : h * k ≤ v := by
      by_contra hlt
      apply hnd
      rw [hPdef, ← pow_mul]
      exact pow_dvd_pow _ (by omega)
    have hqk : q ^ (h * k) ≤ 2 * t + 1 :=
      Nat.le_of_dvd (by omega) ((Nat.pow_dvd_pow q hkv).trans hv)
    have hqk' : P ^ k ≤ ((2 * t + 1 : ℕ) : ℤ) := by
      rw [hPdef, ← pow_mul]; exact_mod_cast hqk
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0
      norm_num at hqk'
      linarith
    · have hP1 : 2 ≤ (P - 1) ^ t := by
        calc (2 : ℤ) ≤ (P - 1) ^ 1 := by simp; omega
          _ ≤ (P - 1) ^ t := pow_le_pow_right₀ (by omega) h0
      have hm0 : (0 : ℤ) < ((2 * t + 1 : ℕ) : ℤ) := by positivity
      nlinarith

open SignedRepunit in
/-- **Alternating prime power sums are not squares.** For a prime `q ≥ 5`, an exponent `h ≥ 1`
with `q ^ h ≡ 1 (mod 4)` and an odd `n ≥ 3`, the number `((q ^ h) ^ n + 1) / (q ^ h + 1)` is not
a perfect square: `(q ^ h) ^ n + 1 ≠ (q ^ h + 1) y ^ 2`. This is reported to be the case
`x = -q ^ h` of Ljunggren's theorem on `(x ^ n - 1) / (x - 1) = y ^ 2` (the statement for a
negative base was not page checked); nothing new is claimed. The proof goes
through the Pell equation `x ^ 2 - (u + 1) u y ^ 2 = 1` with `u = q ^ h` and a `q`-adic valuation
count. -/
theorem alternating_sum_prime_pow_ne_sq {q h n y : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hh : h ≠ 0) (hu : q ^ h % 4 = 1) (hn : Odd n) (hn3 : 3 ≤ n) :
    (q ^ h) ^ n + 1 ≠ (q ^ h + 1) * y ^ 2 := by
  intro hy
  obtain ⟨k, rfl⟩ := hn
  have hk : 1 ≤ k := by omega
  have hh1 : 1 ≤ h := by omega
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hy1 : 1 ≤ (y : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hy0
  obtain ⟨u, hudef⟩ : ∃ u : ℤ, u = (q : ℤ) ^ h := ⟨_, rfl⟩
  have hu5 : 5 ≤ q ^ h := le_trans hq5 (Nat.le_self_pow hh q)
  have hu5' : (5 : ℤ) ≤ u := by rw [hudef]; exact_mod_cast hu5
  have hyZ : u ^ (2 * k + 1) + 1 = (u + 1) * (y : ℤ) ^ 2 := by
    rw [hudef]; exact_mod_cast hy
  have hpell : (u + 1) * (y : ℤ) ^ 2 - (u + 1 - 1) * (u ^ k) ^ 2 = 1 := by
    linear_combination -hyZ
  rcases sr_stepA (u + 1) (by omega) (y : ℤ) (u ^ k) hy1 (by positivity) hpell with
    ⟨x, hx⟩ | ⟨t, ht⟩
  · have hdvd : (y : ℤ) ^ 2 ∣ x ^ 2 := ⟨u + 1, by rw [← hx]; ring⟩
    obtain ⟨z, hz⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp hdvd
    have hz2 : u + 1 = z ^ 2 := by
      have hy2 : (y : ℤ) ^ 2 ≠ 0 := by positivity
      apply mul_left_cancel₀ hy2
      rw [hz] at hx
      linear_combination hx
    have hu4 : u % 4 = 1 := by rw [hudef]; exact_mod_cast hu
    obtain ⟨w, rfl | rfl⟩ := Int.even_or_odd' z
    · have h4 : u + 1 = 4 * w ^ 2 := by rw [hz2]; ring
      omega
    · have h4 : u + 1 = 4 * (w ^ 2 + w) + 1 := by rw [hz2]; ring
      omega
  · have him : ((⟨u + 1, 1⟩ : ℤ√((u + 1) * (u + 1 - 1))) ^ (2 * t + 1)).im =
        (u + 1) ^ t * u ^ k := by
      rw [ht, Zsqrtd.im_smul]
    have hlow := sr_im_lower (u + 1) (by omega) t (u ^ k) him
    set v := (2 * t + 1).factorization q
    have hv : q ^ v ∣ 2 * t + 1 := Nat.ordProj_dvd _ q
    have hnv : ¬ q ^ (v + 1) ∣ 2 * t + 1 := Nat.pow_succ_factorization_not_dvd (by omega) hq
    have hH : ∀ s, 1 ≤ s → s ≤ t → ((q : ℤ) ^ (v + 1)) ∣
        ((2 * t + 1).choose (2 * s + 1) : ℤ) * (u + 1 - 1) ^ s := by
      intro s hs1 hs
      have h1 := sr_choose_dvd_odd hq hq5 hv hs1 hs
      have h2 : q ^ s ∣ (q ^ h) ^ s := by
        rw [← pow_mul]; exact Nat.pow_dvd_pow q (by nlinarith)
      have h3 := h1.trans (Nat.mul_dvd_mul_left _ h2)
      rw [add_sub_cancel_right, hudef]; exact_mod_cast h3
    have hcop : IsCoprime ((q : ℤ) ^ (v + 1)) (u + 1) := by
      apply IsCoprime.pow_left
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      exact ⟨-(q : ℤ) ^ h', 1, by rw [hudef]; ring⟩
    have hnd := sr_im_not_dvd (by omega) t (u ^ k) him hH hcop
      (fun hd => hnv (by exact_mod_cast hd))
    have hkv : h * k ≤ v := by
      by_contra hlt
      apply hnd
      rw [hudef, ← pow_mul]
      exact pow_dvd_pow _ (by omega)
    have hqk : q ^ (h * k) ≤ 2 * t + 1 :=
      Nat.le_of_dvd (by omega) ((Nat.pow_dvd_pow q hkv).trans hv)
    have hqk' : u ^ k ≤ ((2 * t + 1 : ℕ) : ℤ) := by
      rw [hudef, ← pow_mul]; exact_mod_cast hqk
    have huk : u ≤ u ^ k := by
      calc u = u ^ 1 := (pow_one u).symm
        _ ≤ u ^ k := pow_le_pow_right₀ (by omega) hk
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0
      norm_num at hqk'
      linarith
    · have hP1 : 2 ≤ (u + 1) ^ t := by
        calc (2 : ℤ) ≤ (u + 1) ^ 1 := by simp; omega
          _ ≤ (u + 1) ^ t := pow_le_pow_right₀ (by omega) h0
      have hm0 : (0 : ℤ) < ((2 * t + 1 : ℕ) : ℤ) := by positivity
      nlinarith

end OddPerfect

#print axioms OddPerfect.geom_sum_prime_pow_ne_sq
#print axioms OddPerfect.alternating_sum_prime_pow_ne_sq
