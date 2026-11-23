import OddPerfect.EisensteinInt

/-!
# Escape rows read off powers of a normalized Eisenstein prime

For a prime `q ≡ 1 (mod 4)` we find `ρ ≡ 1 (mod 4)` in the Eisenstein integers such that every
odd `p` with `p ^ 2 + p + 1 = q ^ j` or `= 3 * q ^ j` (`j ≥ 1`) satisfies
`p - ω = ω ^ 2 * λ ^ ε * τ ^ j` with `τ ∈ {ρ, star ρ}`; reading off the `ω` coordinate gives a
linear condition on `τ ^ j`.
-/

namespace OddPerfect

open QuadraticAlgebra Eis

namespace EisRows

private lemma star_dvd_star {a b : Eis} (h : a ∣ b) : star a ∣ star b := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨star c, by rw [star_mul, mul_comm]⟩

private lemma nrm_row (p : ℕ) : nrm ⟨(p : ℤ), -1⟩ = ((p ^ 2 + p + 1 : ℕ) : ℤ) := by
  rw [nrm_mk]; push_cast; ring

/-- No element of norm `q ≠ 3` divides both `p - ω` and its conjugate. -/
private lemma not_both {σ : Eis} {q : ℕ} (hσ : nrm σ = q) (hq : q.Prime) (hq3 : q ≠ 3) (p : ℤ)
    (h1 : σ ∣ ⟨p, -1⟩) (h2 : star σ ∣ ⟨p, -1⟩) : False := by
  have h3 : σ ∣ star (⟨p, -1⟩ : Eis) := by
    have := star_dvd_star h2
    rwa [star_star] at this
  have h4 : σ ∣ (⟨-1, -2⟩ : Eis) := by
    have := dvd_sub h1 h3
    have e : (⟨p, -1⟩ : Eis) - star ⟨p, -1⟩ = ⟨-1, -2⟩ := by ext <;> simp
    rwa [e] at this
  obtain ⟨c, hc⟩ := h4
  have h5 : nrm σ * nrm c = 3 := by rw [← nrm_mul, ← hc, nrm_mk]; norm_num
  have h6 : (q : ℤ) ∣ 3 := ⟨nrm c, by rw [← h5, hσ]⟩
  have h7 : q ∣ 3 := by exact_mod_cast h6
  exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h7)

/-- Peeling off powers of `σ`: if `star σ` does not divide `α`, then `σ ^ j` divides `α`. -/
private lemma descent {σ : Eis} {q : ℕ} (hq : q.Prime) (hσ : nrm σ = q) (hp : Prime σ)
    {α : Eis} (hno : ¬ star σ ∣ α) (c : ℤ) (j : ℕ) (hα : nrm α = c * (q : ℤ) ^ j) :
    ∀ k ≤ j, ∃ θ, α = σ ^ k * θ ∧ nrm θ * (q : ℤ) ^ k = c * (q : ℤ) ^ j := by
  intro k
  induction k with
  | zero => intro _; exact ⟨α, by simp, by simpa using hα⟩
  | succ k ih =>
    intro hk
    obtain ⟨θ, hθ, hn⟩ := ih (by omega)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hq0 : (q : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne_zero)
    have hθn : nrm θ = (q : ℤ) * (c * (q : ℤ) ^ m) := by
      apply mul_right_cancel₀ hq0
      rw [hn]; ring
    have hdq : σ ∣ θ * star θ := by
      rw [mul_star_eq, hθn, Int.cast_mul]
      exact Dvd.dvd.mul_right ⟨star σ, by rw [mul_star_eq, hσ]⟩ _
    rcases hp.dvd_or_dvd hdq with ⟨θ', hθ'⟩ | h
    · refine ⟨θ', by rw [hθ, hθ']; ring, ?_⟩
      have e : nrm θ = (q : ℤ) * nrm θ' := by rw [hθ', nrm_mul, hσ]
      rw [← hn, e]; ring
    · exfalso
      apply hno
      have := star_dvd_star h
      rw [star_star] at this
      exact this.trans ⟨σ ^ k, by rw [hθ, mul_comm]⟩

/-- Reading off the coordinates in `p - ω = ⟨X, Y⟩ * θ` for `θ` of norm `1` or `3`. -/
private lemma read_off (p X Y : ℤ) (hp : Odd p) (hX : 4 ∣ X - 1) (hY : 4 ∣ Y) (θ : Eis)
    (h : (⟨p, -1⟩ : Eis) = ⟨X, Y⟩ * θ) :
    (nrm θ = 1 → X = 1) ∧ (nrm θ = 3 → X - 2 * Y = 1) := by
  obtain ⟨k, rfl⟩ := hp
  constructor
  · intro hθ
    rcases eq_of_nrm_eq_one hθ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [QuadraticAlgebra.ext_iff, re_mul, im_mul] at h <;> omega
  · intro hθ
    rcases eq_of_nrm_eq_three hθ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [QuadraticAlgebra.ext_iff, re_mul, im_mul] at h <;> omega

private lemma norm4_mul {z w : Eis} (hz : 4 ∣ z.re - 1 ∧ 4 ∣ z.im)
    (hw : 4 ∣ w.re - 1 ∧ 4 ∣ w.im) : 4 ∣ (z * w).re - 1 ∧ 4 ∣ (z * w).im := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hw
  have e1 : z.re = 4 * a + 1 := by omega
  have e3 : w.re = 4 * c + 1 := by omega
  rw [re_mul, im_mul, e1, e3, hb, hd]
  exact ⟨⟨4 * a * c + a + c - 4 * b * d, by ring⟩,
    ⟨4 * a * d + d + 4 * b * c + b - 4 * b * d, by ring⟩⟩

private lemma norm4_pow {z : Eis} (hz : 4 ∣ z.re - 1 ∧ 4 ∣ z.im) (n : ℕ) :
    4 ∣ (z ^ n).re - 1 ∧ 4 ∣ (z ^ n).im := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact norm4_mul ih hz

private lemma norm4_star {z : Eis} (hz : 4 ∣ z.re - 1 ∧ 4 ∣ z.im) :
    4 ∣ (star z).re - 1 ∧ 4 ∣ (star z).im := by
  obtain ⟨h1, h2⟩ := hz
  exact ⟨by rw [re_star]; omega, by rw [im_star]; omega⟩

private lemma pick (q X Y : ℤ) (hX : X % 2 = 1) (hY : Y % 2 = 0) (h : X ^ 2 - X * Y + Y ^ 2 = q)
    (hq : q % 4 = 1) : ∃ X' Y' : ℤ, X' ^ 2 - X' * Y' + Y' ^ 2 = q ∧ 4 ∣ X' - 1 ∧ 4 ∣ Y' := by
  obtain ⟨x, rfl⟩ : ∃ x, X = 2 * x + 1 := ⟨X / 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, Y = 2 * y := ⟨Y / 2, by omega⟩
  have h' := h
  have e : (2 * x + 1) ^ 2 - (2 * x + 1) * (2 * y) + (2 * y) ^ 2 =
      4 * (x ^ 2 + x - x * y + y ^ 2) + 1 - 2 * y := by ring
  rw [e] at h'
  generalize x ^ 2 + x - x * y + y ^ 2 = t at h'
  have hy : 4 ∣ 2 * y := by omega
  rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hx | hx
  · exact ⟨2 * x + 1, 2 * y, h, by omega, hy⟩
  · exact ⟨-(2 * x + 1), -(2 * y), by rw [← h]; ring, by omega, by omega⟩

/-- A representation of `q ≡ 1 (mod 4)` by the norm form can be normalized. -/
private lemma normalize (q A B : ℤ) (h : A ^ 2 - A * B + B ^ 2 = q) (hq : q % 4 = 1) :
    ∃ X Y : ℤ, X ^ 2 - X * Y + Y ^ 2 = q ∧ 4 ∣ X - 1 ∧ 4 ∣ Y := by
  rcases Int.emod_two_eq_zero_or_one A with hA | hA <;>
    rcases Int.emod_two_eq_zero_or_one B with hB | hB
  · exfalso
    obtain ⟨a, rfl⟩ : ∃ a, A = 2 * a := ⟨A / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, B = 2 * b := ⟨B / 2, by omega⟩
    have e : (2 * a) ^ 2 - (2 * a) * (2 * b) + (2 * b) ^ 2 = 4 * (a ^ 2 - a * b + b ^ 2) := by
      ring
    rw [e] at h
    generalize a ^ 2 - a * b + b ^ 2 = t at h
    omega
  · exact pick q (B - A) (-A) (by omega) (by omega) (by rw [← h]; ring) hq
  · exact pick q A B hA hB h hq
  · exact pick q (-B) (A - B) (by omega) (by omega) (by rw [← h]; ring) hq

/-- If `q` divides the norm of `p - ω`, then `q` is a norm. -/
private lemma exists_nrm_eq {q : ℕ} (hq : q.Prime) (p0 : ℤ) (hd : (q : ℤ) ∣ nrm ⟨p0, -1⟩) :
    ∃ π : Eis, nrm π = q := by
  have hnp : ¬ Prime ((q : ℤ) : Eis) := by
    intro hP
    have h1 : ((q : ℤ) : Eis) ∣ (⟨p0, -1⟩ : Eis) * star ⟨p0, -1⟩ := by
      rw [mul_star_eq]
      obtain ⟨c, hc⟩ := hd
      exact ⟨(c : Eis), by rw [hc, Int.cast_mul]⟩
    rcases hP.dvd_or_dvd h1 with h | h
    · rw [intCast_dvd_iff] at h
      have h2 : (q : ℤ) ∣ -1 := h.2
      have h3 : (q : ℤ) ∣ 1 := dvd_neg.1 h2
      have h4 : q ∣ 1 := by exact_mod_cast h3
      exact hq.ne_one (Nat.dvd_one.1 h4)
    · rw [intCast_dvd_iff] at h
      have h2 : (q : ℤ) ∣ -(-1) := h.2
      rw [neg_neg] at h2
      have h4 : q ∣ 1 := by exact_mod_cast h2
      exact hq.ne_one (Nat.dvd_one.1 h4)
  have hnu : ¬ IsUnit ((q : ℤ) : Eis) := by
    rw [isUnit_iff_nrm_eq_one, nrm_intCast]
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
    intro h; nlinarith
  have hirr : ¬ Irreducible ((q : ℤ) : Eis) := fun h => hnp h.prime
  rw [irreducible_iff] at hirr
  push Not at hirr
  obtain ⟨a, b, hab, ha, hb⟩ := hirr hnu
  rw [isUnit_iff_nrm_eq_one] at ha hb
  have hm : (nrm a).natAbs * (nrm b).natAbs = q ^ 2 := by
    rw [← Int.natAbs_mul, ← nrm_mul, ← hab, nrm_intCast]; simp
  have hna := Int.natAbs_of_nonneg (nrm_nonneg a)
  have hnb := Int.natAbs_of_nonneg (nrm_nonneg b)
  have ha' : (nrm a).natAbs ≠ 1 := fun h1 => ha (by omega)
  have hb' : (nrm b).natAbs ≠ 1 := fun h1 => hb (by omega)
  obtain ⟨h1, -⟩ := (Nat.Prime.mul_eq_prime_sq_iff hq ha' hb').1 hm
  exact ⟨a, by omega⟩

/-- Core factorization: `p - ω = τ ^ j * θ` with `τ ∈ {ρ, star ρ}` and `nrm θ = c`. -/
private lemma core {ρ : Eis} {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) (hρ : nrm ρ = q)
    (p : ℤ) (j : ℕ) (hj : 1 ≤ j) (c : ℤ) (h : nrm ⟨p, -1⟩ = c * (q : ℤ) ^ j) :
    ∃ θ, nrm θ = c ∧
      ((⟨p, -1⟩ : Eis) = ρ ^ j * θ ∨ (⟨p, -1⟩ : Eis) = (star ρ) ^ j * θ) := by
  have hsρ : nrm (star ρ) = q := by rw [nrm_star, hρ]
  have hpr : ∀ σ : Eis, nrm σ = q → Prime σ :=
    fun σ hσ => prime_of_nrm_prime (by rw [hσ]; simpa using hq)
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hdiv : ρ ∣ (⟨p, -1⟩ : Eis) * star ⟨p, -1⟩ := by
    rw [mul_star_eq, h]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact ⟨star ρ * ((c * (q : ℤ) ^ m : ℤ) : Eis), by
      rw [← mul_assoc, mul_star_eq, hρ]; push_cast; ring⟩
  rcases (hpr ρ hρ).dvd_or_dvd hdiv with h1 | h1
  · have hno : ¬ star ρ ∣ ⟨p, -1⟩ := fun h2 => not_both hρ hq hq3 p h1 h2
    obtain ⟨θ, hθ, hn⟩ := descent hq hρ (hpr ρ hρ) hno c j h j le_rfl
    exact ⟨θ, mul_right_cancel₀ (pow_ne_zero j hq0) hn, Or.inl hθ⟩
  · have h1' : star ρ ∣ ⟨p, -1⟩ := by
      have := star_dvd_star h1
      rwa [star_star] at this
    have hno : ¬ star (star ρ) ∣ ⟨p, -1⟩ := by
      rw [star_star]; exact fun h2 => not_both hρ hq hq3 p h2 h1'
    obtain ⟨θ, hθ, hn⟩ := descent hq hsρ (hpr _ hsρ) hno c j h j le_rfl
    exact ⟨θ, mul_right_cancel₀ (pow_ne_zero j hq0) hn, Or.inr hθ⟩

end EisRows

open EisRows in
/-- For a prime `q ≡ 1 (mod 4)` there is an Eisenstein integer `ρ ≡ 1 (mod 4)`, `ρ ≠ 1`, such that
every odd `p` with `p ^ 2 + p + 1 = q ^ j` or `= 3 * q ^ j`, `j ≥ 1`, is read off a power of `ρ` or
of its conjugate. -/
theorem exists_normalized_root {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) :
    ∃ ρ : Eis, ρ ≠ 1 ∧ (4 : ℤ) ∣ ρ.re - 1 ∧ (4 : ℤ) ∣ ρ.im ∧
      ∀ p j : ℕ, Odd p → 1 ≤ j →
        (p ^ 2 + p + 1 = q ^ j → (ρ ^ j).re = 1 ∨ ((star ρ) ^ j).re = 1) ∧
        (p ^ 2 + p + 1 = 3 * q ^ j →
          (ρ ^ j).re - 2 * (ρ ^ j).im = 1 ∨ ((star ρ) ^ j).re - 2 * ((star ρ) ^ j).im = 1) := by
  have hq3 : q ≠ 3 := by omega
  by_cases hex : ∃ p j : ℕ, 1 ≤ j ∧ (p ^ 2 + p + 1 = q ^ j ∨ p ^ 2 + p + 1 = 3 * q ^ j)
  · obtain ⟨p0, j0, hj0, h0⟩ := hex
    have hd : (q : ℤ) ∣ nrm ⟨(p0 : ℤ), -1⟩ := by
      have hnat : q ∣ p0 ^ 2 + p0 + 1 := by
        have hqj : q ∣ q ^ j0 := dvd_pow_self q (by omega)
        rcases h0 with h0 | h0 <;> rw [h0]
        · exact hqj
        · exact hqj.mul_left 3
      rw [nrm_row]; exact_mod_cast hnat
    obtain ⟨π, hπ⟩ := exists_nrm_eq hq p0 hd
    obtain ⟨X, Y, hXY, hX, hY⟩ := normalize (q : ℤ) π.re π.im (by rw [← hπ]; rfl) (by omega)
    have hρ : nrm (⟨X, Y⟩ : Eis) = q := hXY
    have hn4 : 4 ∣ (⟨X, Y⟩ : Eis).re - 1 ∧ 4 ∣ (⟨X, Y⟩ : Eis).im := ⟨hX, hY⟩
    refine ⟨⟨X, Y⟩, ?_, hX, hY, ?_⟩
    · intro h1
      have := congrArg nrm h1
      rw [hρ, nrm_one] at this
      have := hq.one_lt
      omega
    · intro p j hp hj
      have hp' : Odd (p : ℤ) := by
        obtain ⟨k, hk⟩ := hp
        exact ⟨k, by rw [hk]; push_cast; ring⟩
      have hA := norm4_pow hn4 j
      have hB := norm4_pow (norm4_star hn4) j
      constructor
      · intro he
        obtain ⟨θ, hθ, hor⟩ := core hq hq3 hρ p j hj 1 (by rw [nrm_row, he]; push_cast; ring)
        rcases hor with hα | hα
        · left
          exact (read_off p _ _ hp' hA.1 hA.2 θ (by rw [mk_eta]; exact hα)).1 hθ
        · right
          exact (read_off p _ _ hp' hB.1 hB.2 θ (by rw [mk_eta]; exact hα)).1 hθ
      · intro he
        obtain ⟨θ, hθ, hor⟩ := core hq hq3 hρ p j hj 3 (by rw [nrm_row, he]; push_cast; ring)
        rcases hor with hα | hα
        · left
          exact (read_off p _ _ hp' hA.1 hA.2 θ (by rw [mk_eta]; exact hα)).2 hθ
        · right
          exact (read_off p _ _ hp' hB.1 hB.2 θ (by rw [mk_eta]; exact hα)).2 hθ
  · refine ⟨⟨5, 0⟩, ?_, ?_, ?_, ?_⟩
    · intro h
      have := congrArg QuadraticAlgebra.re h
      rw [QuadraticAlgebra.re_one] at this
      norm_num at this
    · show (4 : ℤ) ∣ 5 - 1
      norm_num
    · show (4 : ℤ) ∣ 0
      exact dvd_zero 4
    · intro p j _ hj
      exact ⟨fun h => absurd ⟨p, j, hj, Or.inl h⟩ hex, fun h => absurd ⟨p, j, hj, Or.inr h⟩ hex⟩

open EisRows in
/-- The root of `exists_normalized_root` when at least one row exists: it has norm `q`. -/
theorem exists_normalized_root_of_row {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    (hex : ∃ p j : ℕ, 1 ≤ j ∧ (p ^ 2 + p + 1 = q ^ j ∨ p ^ 2 + p + 1 = 3 * q ^ j)) :
    ∃ ρ : Eis, nrm ρ = q ∧ ρ ≠ 1 ∧ (4 : ℤ) ∣ ρ.re - 1 ∧ (4 : ℤ) ∣ ρ.im ∧
      ∀ p j : ℕ, Odd p → 1 ≤ j →
        (p ^ 2 + p + 1 = q ^ j → (ρ ^ j).re = 1 ∨ ((star ρ) ^ j).re = 1) ∧
        (p ^ 2 + p + 1 = 3 * q ^ j →
          (ρ ^ j).re - 2 * (ρ ^ j).im = 1 ∨ ((star ρ) ^ j).re - 2 * ((star ρ) ^ j).im = 1) := by
  have hq3 : q ≠ 3 := by omega
  obtain ⟨p0, j0, hj0, h0⟩ := hex
  have hd : (q : ℤ) ∣ nrm ⟨(p0 : ℤ), -1⟩ := by
    have hnat : q ∣ p0 ^ 2 + p0 + 1 := by
      have hqj : q ∣ q ^ j0 := dvd_pow_self q (by omega)
      rcases h0 with h0 | h0 <;> rw [h0]
      · exact hqj
      · exact hqj.mul_left 3
    rw [nrm_row]; exact_mod_cast hnat
  obtain ⟨π, hπ⟩ := exists_nrm_eq hq p0 hd
  obtain ⟨X, Y, hXY, hX, hY⟩ := normalize (q : ℤ) π.re π.im (by rw [← hπ]; rfl) (by omega)
  have hρ : nrm (⟨X, Y⟩ : Eis) = q := hXY
  have hn4 : 4 ∣ (⟨X, Y⟩ : Eis).re - 1 ∧ 4 ∣ (⟨X, Y⟩ : Eis).im := ⟨hX, hY⟩
  refine ⟨⟨X, Y⟩, hρ, ?_, hX, hY, ?_⟩
  · intro h1
    have := congrArg nrm h1
    rw [hρ, nrm_one] at this
    have := hq.one_lt
    omega
  · intro p j hp hj
    have hp' : Odd (p : ℤ) := by
      obtain ⟨k, hk⟩ := hp
      exact ⟨k, by rw [hk]; push_cast; ring⟩
    have hA := norm4_pow hn4 j
    have hB := norm4_pow (norm4_star hn4) j
    constructor
    · intro he
      obtain ⟨θ, hθ, hor⟩ := core hq hq3 hρ p j hj 1 (by rw [nrm_row, he]; push_cast; ring)
      rcases hor with hα | hα
      · left
        exact (read_off p _ _ hp' hA.1 hA.2 θ (by rw [mk_eta]; exact hα)).1 hθ
      · right
        exact (read_off p _ _ hp' hB.1 hB.2 θ (by rw [mk_eta]; exact hα)).1 hθ
    · intro he
      obtain ⟨θ, hθ, hor⟩ := core hq hq3 hρ p j hj 3 (by rw [nrm_row, he]; push_cast; ring)
      rcases hor with hα | hα
      · left
        exact (read_off p _ _ hp' hA.1 hA.2 θ (by rw [mk_eta]; exact hα)).2 hθ
      · right
        exact (read_off p _ _ hp' hB.1 hB.2 θ (by rw [mk_eta]; exact hα)).2 hθ

end OddPerfect

#print axioms OddPerfect.exists_normalized_root
#print axioms OddPerfect.exists_normalized_root_of_row
