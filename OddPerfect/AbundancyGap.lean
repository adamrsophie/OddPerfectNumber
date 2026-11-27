import OddPerfect.Abundancy

/-!
# A gap below 2 for abundancy products of few prime powers with large exponents

For a finite set `C` of odd primes with at most `K` elements, write
`V = ∏ c ∈ C, σ(c ^ e_c) / c ^ e_c`. The theorem `exists_abundancy_gap` gives, for every `K`,
a bound `B` and a rational `ε > 0` such that `V ≤ 2` forces `V < 2 - ε` whenever every exponent
`e_c` with `c ≠ q` is at least `B`, and the exceptional prime `q` (if it lies in `C`) satisfies
`q % 4 = 1` and `e_q % 4 = 1`.

This is the abundancy input of the restricted family in which one odd prime divides every
ordinary index `e_p + 1`: there every ordinary exponent is at least that prime minus one. The
module itself mentions no odd perfect number.

Argument. Write `H(c) = c / (c - 1)` and `h(c, e) = σ(c ^ e) / c ^ e`. A state is a finite set
`F` of odd primes together with an optional exact entry `(q, a)`, `q ∈ F`, `q % 4 = 1`,
`a % 4 = 1` (the absent entry is encoded as `q = a = 0`). Its ideal value is
`I = (∏ c ∈ F, c ≠ q, H(c)) * h(q, a)`. A parity argument shows `I ≠ 2`. By induction on the
number `k` of primes outside `F`, every state has a bound `B` and an `ε > 0` that work for all
`C ⊇ F` with at most `k` new primes: when `I > 2` a large `B` pushes the value above 2; when
`I < 2` either the least new prime is large (and the product stays below `(I + 2) / 2`) or it is
one of finitely many small primes, which are added to the state.

The bound `B` and the gap `ε` are not explicit: the proof gives no value.

Restricted result (one odd prime divides every ordinary index); no published source was
checked; novelty not verified. The common index family is not excluded by this module, and the
odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace AbundancyGap

/-- `hv c n = σ(c ^ n) / c ^ n` as a rational. -/
def hv (c n : ℕ) : ℚ := (σ 1 (c ^ n) : ℚ) / ((c : ℚ) ^ n)

/-- `Hv c = c / (c - 1)` as a rational. -/
def Hv (c : ℕ) : ℚ := (c : ℚ) / ((c : ℚ) - 1)

/-- The ideal value of a state: `H` over `F` without `q`, times the exact factor `hv q a`. -/
def ideal (F : Finset ℕ) (q a : ℕ) : ℚ := (∏ c ∈ F.erase q, Hv c) * hv q a

/-- A valid state: odd primes, an exact entry `(q, a)` when `a ≠ 0`, and `q = 0` otherwise. -/
def Valid (F : Finset ℕ) (q a : ℕ) : Prop :=
  (∀ c ∈ F, c.Prime ∧ c ≠ 2) ∧ (a ≠ 0 → q ∈ F ∧ q % 4 = 1 ∧ a % 4 = 1) ∧ (a = 0 → q = 0)

/-- The exponent hypotheses on an extension `C` of a state, with exceptional prime `q'`. -/
def Hyp (B : ℕ) (F : Finset ℕ) (q a : ℕ) (C : Finset ℕ) (e : ℕ → ℕ) (q' : ℕ) : Prop :=
  (∀ c ∈ C, c ≠ q → (c ∈ F ∨ c ≠ q') → B ≤ e c) ∧ (a ≠ 0 → q' = q ∧ e q = a) ∧
    (a = 0 → q' ∈ C → q' ∉ F → q' % 4 = 1 ∧ e q' % 4 = 1)

/-- The gap property of a state for extensions by at most `k` primes. -/
def Good (k : ℕ) (F : Finset ℕ) (q a B : ℕ) (ε : ℚ) : Prop :=
  ∀ (C : Finset ℕ) (e : ℕ → ℕ) (q' : ℕ), F ⊆ C → (C \ F).card ≤ k →
    (∀ c ∈ C, c.Prime ∧ c ≠ 2) → Hyp B F q a C e q' →
    ∏ c ∈ C, hv c (e c) ≤ 2 → ∏ c ∈ C, hv c (e c) < 2 - ε

theorem hv_eq_abundancy (c n : ℕ) : hv c n = abundancy (c ^ n) := by
  rw [hv, abundancy, Nat.cast_pow]

theorem hv_zero (c : ℕ) : hv c 0 = 1 := by
  rw [hv, pow_zero, pow_zero, isMultiplicative_sigma.map_one, Nat.cast_one, div_one]

theorem hv_nonneg (c n : ℕ) : 0 ≤ hv c n := by
  unfold hv; positivity

theorem one_le_hv {c : ℕ} (hc : c.Prime) (n : ℕ) : 1 ≤ hv c n := by
  have h := abundancy_prime_pow_mono hc (Nat.zero_le n)
  rw [← hv_eq_abundancy, ← hv_eq_abundancy, hv_zero] at h
  exact h

theorem hv_lt_Hv {c : ℕ} (hc : c.Prime) (n : ℕ) : hv c n < Hv c := by
  rw [hv_eq_abundancy, Hv]
  exact abundancy_prime_pow_lt hc n

theorem one_le_Hv {c : ℕ} (hc : 2 ≤ c) : 1 ≤ Hv c := by
  have h : (2 : ℚ) ≤ c := by exact_mod_cast hc
  rw [Hv, le_div_iff₀ (by linarith)]
  linarith

theorem Hv_le_two {c : ℕ} (hc : 2 ≤ c) : Hv c ≤ 2 := by
  have h : (2 : ℚ) ≤ c := by exact_mod_cast hc
  rw [Hv, div_le_iff₀ (by linarith)]
  linarith

theorem Hv_anti {c d : ℕ} (hc : 2 ≤ c) (hcd : c ≤ d) : Hv d ≤ Hv c := by
  have h : (2 : ℚ) ≤ c := by exact_mod_cast hc
  have h' : (c : ℚ) ≤ d := by exact_mod_cast hcd
  rw [Hv, Hv, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem Hv_mul {c : ℕ} (hc : 2 ≤ c) : Hv c * (1 - (c : ℚ)⁻¹) = 1 := by
  have h : (2 : ℚ) ≤ c := by exact_mod_cast hc
  have h0 : (c : ℚ) ≠ 0 := by positivity
  have h1 : (c : ℚ) - 1 ≠ 0 := by
    intro h1
    linarith
  rw [Hv]
  field_simp

/-- The lower bound `H(c) (1 - 3 ^ (-(B + 1))) ≤ h(c, n)` for an odd prime `c` and `B ≤ n`. -/
theorem Hv_mul_le_hv {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) {B n : ℕ} (hBn : B ≤ n) :
    Hv c * (1 - ((3 : ℚ) ^ (B + 1))⁻¹) ≤ hv c n := by
  have h3 : 3 ≤ c := by
    have := hc.two_le
    omega
  have h3q : (3 : ℚ) ≤ c := by exact_mod_cast h3
  have hg := geom_sum_mul_neg ((c : ℚ)⁻¹) (n + 1)
  have hHm := Hv_mul (c := c) (by omega)
  have key : hv c n = Hv c * (1 - ((c : ℚ)⁻¹) ^ (n + 1)) := by
    rw [hv_eq_abundancy, abundancy_prime_pow hc]
    linear_combination (Hv c) * hg -
      (∑ i ∈ Finset.range (n + 1), ((c : ℚ)⁻¹) ^ i) * hHm
  rw [key]
  have hH : 0 ≤ Hv c := le_trans zero_le_one (one_le_Hv (by omega))
  apply mul_le_mul_of_nonneg_left _ hH
  have : ((c : ℚ)⁻¹) ^ (n + 1) ≤ ((3 : ℚ) ^ (B + 1))⁻¹ := by
    rw [inv_pow]
    apply inv_anti₀ (by positivity)
    calc (3 : ℚ) ^ (B + 1) ≤ 3 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ (c : ℚ) ^ (n + 1) := pow_le_pow_left₀ (by norm_num) h3q _
  linarith

/-- A large `B` makes `I (1 - 3 ^ (-(B + 1))) ^ n` exceed 2 when `I > 2`. -/
theorem exists_B_big (I : ℚ) (hI : 2 < I) (n : ℕ) :
    ∃ B : ℕ, 2 < I * (1 - ((3 : ℚ) ^ (B + 1))⁻¹) ^ n := by
  obtain ⟨N, hN⟩ := exists_nat_gt (I * n / (I - 2))
  refine ⟨N, ?_⟩
  have h3 : (N : ℚ) + 1 ≤ (3 : ℚ) ^ (N + 1) := by
    have := one_add_mul_le_pow (a := (2 : ℚ)) (by norm_num) (N + 1)
    push_cast at this
    norm_num at this
    linarith
  have hpos : (0 : ℚ) < (3 : ℚ) ^ (N + 1) := by positivity
  have hτ1 : ((3 : ℚ) ^ (N + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hb := one_add_mul_le_pow (a := -((3 : ℚ) ^ (N + 1))⁻¹) (by linarith) n
  have e1 : (1 : ℚ) + -((3 : ℚ) ^ (N + 1))⁻¹ = 1 - ((3 : ℚ) ^ (N + 1))⁻¹ := by ring
  rw [e1] at hb
  have hkey : I * n * ((3 : ℚ) ^ (N + 1))⁻¹ < I - 2 := by
    rw [div_lt_iff₀ (by linarith)] at hN
    rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℚ) ≤ I - 2)
    nlinarith
  have := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℚ) ≤ I)
  nlinarith

/-- `H(c) ^ m (1 - m / c) ≤ 1`. -/
theorem Hv_pow_mul_le (c m : ℕ) (hc : 2 ≤ c) : Hv c ^ m * (1 - (m : ℚ) / c) ≤ 1 := by
  have hc' : (2 : ℚ) ≤ c := by exact_mod_cast hc
  have hinv : (c : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hb := one_add_mul_le_pow (a := -(c : ℚ)⁻¹) (by linarith) m
  have e1 : (1 : ℚ) + -(c : ℚ)⁻¹ = 1 - (c : ℚ)⁻¹ := by ring
  have e2 : (m : ℚ) * -(c : ℚ)⁻¹ = -((m : ℚ) / c) := by ring
  rw [e1, e2] at hb
  have hpow : Hv c ^ m * (1 - (c : ℚ)⁻¹) ^ m = 1 := by
    rw [← mul_pow, Hv_mul hc, one_pow]
  have hH : 0 ≤ Hv c ^ m := pow_nonneg (le_trans zero_le_one (one_le_Hv hc)) m
  calc Hv c ^ m * (1 - (m : ℚ) / c) ≤ Hv c ^ m * (1 - (c : ℚ)⁻¹) ^ m :=
        mul_le_mul_of_nonneg_left (by linarith) hH
    _ = 1 := hpow

/-- A large least new prime keeps the product below `(I + 2) / 2`. -/
theorem small_tail (I : ℚ) (hI0 : 0 ≤ I) (m c : ℕ) (hc : 2 ≤ c)
    (hcI : (I + 2) * m < (2 - I) * c) : I * Hv c ^ m < (I + 2) / 2 := by
  have hc' : (0 : ℚ) < c := by
    have : (2 : ℚ) ≤ c := by exact_mod_cast hc
    linarith
  have h1 := Hv_pow_mul_le c m hc
  have hu : (I + 2) * ((m : ℚ) / c) < 2 - I := by
    rw [← mul_div_assoc, div_lt_iff₀ hc']
    linarith
  have hX : 0 < Hv c ^ m := pow_pos (lt_of_lt_of_le zero_lt_one (one_le_Hv hc)) m
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℚ) ≤ I + 2),
    mul_lt_mul_of_pos_right hu hX]

theorem sigma_mod_four {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) (a : ℕ) :
    σ 1 (q ^ a) % 4 = (a + 1) % 4 := by
  rw [sigma_one_apply_prime_pow hq, Finset.sum_nat_mod]
  have h : ∀ i ∈ Finset.range (a + 1), q ^ i % 4 = 1 := by
    intro i _
    rw [Nat.pow_mod, hq4]
    simp
  rw [Finset.sum_congr rfl h]
  simp

theorem prod_mod_two (G : Finset ℕ) (h : ∀ c ∈ G, c % 2 = 1) : (∏ c ∈ G, c) % 2 = 1 := by
  rw [Finset.prod_nat_mod, Finset.prod_congr rfl h]
  simp

/-- Parity: the ideal value of a valid state is never 2. -/
theorem ideal_ne_two {F : Finset ℕ} {q a : ℕ} (hval : Valid F q a) : ideal F q a ≠ 2 := by
  obtain ⟨hF, hsome, hnone⟩ := hval
  intro h2
  unfold ideal at h2
  have hGp : ∀ c ∈ F.erase q, c.Prime ∧ c ≠ 2 :=
    fun c hc => hF c (Finset.mem_of_mem_erase hc)
  have hG3 : ∀ c ∈ F.erase q, 3 ≤ c := by
    intro c hc
    have := (hGp c hc).1.two_le
    have := (hGp c hc).2
    omega
  have hGodd : ∀ c ∈ F.erase q, c % 2 = 1 :=
    fun c hc => Nat.odd_iff.mp ((hGp c hc).1.odd_of_ne_two (hGp c hc).2)
  have hprod : ∏ c ∈ F.erase q, Hv c =
      ((∏ c ∈ F.erase q, c : ℕ) : ℚ) / ((∏ c ∈ F.erase q, (c - 1) : ℕ) : ℚ) := by
    rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun c hc => ?_
    have := hG3 c hc
    rw [Hv, Nat.cast_sub (by omega), Nat.cast_one]
  have hQ0 : ((∏ c ∈ F.erase q, (c - 1) : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.prod_ne_zero_iff]
    intro c hc
    have := hG3 c hc
    omega
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have hq0 := hnone ha
    subst ha
    subst hq0
    rw [hv_zero, mul_one, hprod, div_eq_iff hQ0] at h2
    have hnat : (∏ c ∈ F.erase 0, c) = 2 * (∏ c ∈ F.erase 0, (c - 1)) := by
      exact_mod_cast h2
    have hodd := prod_mod_two _ hGodd
    omega
  obtain ⟨hqF, hq4, ha4⟩ := hsome (by omega)
  have hq := (hF q hqF).1
  rcases (F.erase q).eq_empty_or_nonempty with hGe | ⟨d, hd⟩
  · rw [hGe, Finset.prod_empty, one_mul] at h2
    have := hv_lt_Hv hq a
    have := Hv_le_two hq.two_le
    linarith
  have hqa : ((q : ℚ) ^ a) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne_zero)
  rw [hv, hprod, div_mul_div_comm, div_eq_iff (mul_ne_zero hQ0 hqa)] at h2
  have hnat : (∏ c ∈ F.erase q, c) * σ 1 (q ^ a) =
      2 * ((∏ c ∈ F.erase q, (c - 1)) * q ^ a) := by
    exact_mod_cast h2
  have hS : σ 1 (q ^ a) % 4 = 2 := by
    rw [sigma_mod_four hq hq4 a]
    omega
  have hP := prod_mod_two _ hGodd
  have hQ2 : 2 ∣ ∏ c ∈ F.erase q, (c - 1) := by
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun c => c - 1) hd)
    have := hGodd d hd
    have := hG3 d hd
    omega
  obtain ⟨w, hw⟩ := hQ2
  rw [hw, show 2 * (2 * w * q ^ a) = 4 * (w * q ^ a) by ring] at hnat
  have hL : ((∏ c ∈ F.erase q, c) * σ 1 (q ^ a)) % 4 = 2 := by
    rw [Nat.mul_mod, hS]
    have : (∏ c ∈ F.erase q, c) % 4 = 1 ∨ (∏ c ∈ F.erase q, c) % 4 = 3 := by omega
    rcases this with h | h <;> rw [h]
  rw [hnat] at hL
  omega

theorem ideal_nonneg {F : Finset ℕ} {q a : ℕ} (hval : Valid F q a) : 0 ≤ ideal F q a := by
  unfold ideal
  refine mul_nonneg (Finset.prod_nonneg fun c hc => ?_) (hv_nonneg _ _)
  exact le_trans zero_le_one (one_le_Hv (hval.1 c (Finset.mem_of_mem_erase hc)).1.two_le)

/-- Two sided bounds for the product over the known primes of a state. -/
theorem known_bounds {B : ℕ} {F : Finset ℕ} {q a : ℕ} {C : Finset ℕ} {e : ℕ → ℕ} {q' : ℕ}
    (hval : Valid F q a) (hFC : F ⊆ C) (hyp : Hyp B F q a C e q') :
    ideal F q a * (1 - ((3 : ℚ) ^ (B + 1))⁻¹) ^ F.card ≤ ∏ c ∈ F, hv c (e c) ∧
      ∏ c ∈ F, hv c (e c) ≤ ideal F q a := by
  obtain ⟨hF, hsome, hnone⟩ := hval
  obtain ⟨hB, hq', -⟩ := hyp
  have hτ0 : 0 ≤ ((3 : ℚ) ^ (B + 1))⁻¹ := by positivity
  have hτ1 : ((3 : ℚ) ^ (B + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hsplit : ∏ c ∈ F, hv c (e c) = (∏ c ∈ F.erase q, hv c (e c)) * hv q a := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · have hq0 := hnone ha
      subst ha
      subst hq0
      have h0 : (0 : ℕ) ∉ F := fun h => Nat.not_prime_zero (hF 0 h).1
      rw [Finset.erase_eq_of_notMem h0, hv_zero, mul_one]
    · obtain ⟨hqF, -, -⟩ := hsome (by omega)
      rw [← Finset.mul_prod_erase F _ hqF, (hq' (by omega)).2, mul_comm]
  have hGp : ∀ c ∈ F.erase q, c.Prime ∧ c ≠ 2 :=
    fun c hc => hF c (Finset.mem_of_mem_erase hc)
  have hG : ∀ c ∈ F.erase q, B ≤ e c := fun c hc =>
    hB c (hFC (Finset.mem_of_mem_erase hc)) (Finset.ne_of_mem_erase hc)
      (Or.inl (Finset.mem_of_mem_erase hc))
  have hHn : ∀ c ∈ F.erase q, 0 ≤ Hv c :=
    fun c hc => le_trans zero_le_one (one_le_Hv (hGp c hc).1.two_le)
  have hup : ∏ c ∈ F.erase q, hv c (e c) ≤ ∏ c ∈ F.erase q, Hv c :=
    Finset.prod_le_prod₀ (fun c _ => hv_nonneg _ _) (fun c hc => (hv_lt_Hv (hGp c hc).1 _).le)
  have hlow : ∏ c ∈ F.erase q, (Hv c * (1 - ((3 : ℚ) ^ (B + 1))⁻¹)) ≤
      ∏ c ∈ F.erase q, hv c (e c) :=
    Finset.prod_le_prod₀ (fun c hc => mul_nonneg (hHn c hc) (by linarith))
      (fun c hc => Hv_mul_le_hv (hGp c hc).1 (hGp c hc).2 (hG c hc))
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hlow
  have hcard : (1 - ((3 : ℚ) ^ (B + 1))⁻¹) ^ F.card ≤
      (1 - ((3 : ℚ) ^ (B + 1))⁻¹) ^ (F.erase q).card :=
    pow_le_pow_of_le_one (by linarith) (by linarith) Finset.card_erase_le
  have hhq : 0 ≤ hv q a := hv_nonneg _ _
  have hPH : 0 ≤ ∏ c ∈ F.erase q, Hv c := Finset.prod_nonneg hHn
  rw [hsplit]
  unfold ideal
  constructor
  · calc (∏ c ∈ F.erase q, Hv c) * hv q a * (1 - ((3 : ℚ) ^ (B + 1))⁻¹) ^ F.card
          ≤ (∏ c ∈ F.erase q, Hv c) * hv q a *
            (1 - ((3 : ℚ) ^ (B + 1))⁻¹) ^ (F.erase q).card :=
          mul_le_mul_of_nonneg_left hcard (mul_nonneg hPH hhq)
      _ = ((∏ c ∈ F.erase q, Hv c) * (1 - ((3 : ℚ) ^ (B + 1))⁻¹) ^ (F.erase q).card) *
            hv q a := by ring
      _ ≤ (∏ c ∈ F.erase q, hv c (e c)) * hv q a := mul_le_mul_of_nonneg_right hlow hhq
  · exact mul_le_mul_of_nonneg_right hup hhq

theorem one_le_rest {C F : Finset ℕ} {e : ℕ → ℕ} (hC : ∀ d ∈ C, d.Prime ∧ d ≠ 2) :
    1 ≤ ∏ d ∈ C \ F, hv d (e d) := by
  calc (1 : ℚ) = ∏ d ∈ C \ F, (1 : ℚ) := by rw [Finset.prod_const_one]
    _ ≤ ∏ d ∈ C \ F, hv d (e d) :=
      Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
        (fun d hd => one_le_hv (hC d (Finset.mem_sdiff.mp hd).1).1 _)

theorem rest_le {C F : Finset ℕ} {e : ℕ → ℕ} {c m : ℕ} (hC : ∀ d ∈ C, d.Prime ∧ d ≠ 2)
    (hc : 2 ≤ c) (hmin : ∀ d ∈ C \ F, c ≤ d) (hcard : (C \ F).card ≤ m) :
    ∏ d ∈ C \ F, hv d (e d) ≤ Hv c ^ m := by
  calc ∏ d ∈ C \ F, hv d (e d) ≤ ∏ d ∈ C \ F, Hv c :=
        Finset.prod_le_prod₀ (fun _ _ => hv_nonneg _ _)
          (fun d hd => (hv_lt_Hv (hC d (Finset.mem_sdiff.mp hd).1).1 _).le.trans
            (Hv_anti hc (hmin d hd)))
    _ = Hv c ^ (C \ F).card := Finset.prod_const _
    _ ≤ Hv c ^ m := pow_le_pow_right₀ (one_le_Hv hc) hcard

theorem le_ideal_of_empty {B : ℕ} {F : Finset ℕ} {q a : ℕ} {C : Finset ℕ} {e : ℕ → ℕ}
    {q' : ℕ} (hval : Valid F q a) (hFC : F ⊆ C) (hyp : Hyp B F q a C e q')
    (hemp : C \ F = ∅) : ∏ c ∈ C, hv c (e c) ≤ ideal F q a := by
  rw [← Finset.prod_sdiff hFC, hemp, Finset.prod_empty, one_mul]
  exact (known_bounds hval hFC hyp).2

/-- A finite family of positive rationals has a common positive lower bound. -/
theorem exists_eps_le {ι : Type*} (S : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ S, 0 < f i)
    (ε0 : ℚ) (h0 : 0 < ε0) : ∃ ε : ℚ, 0 < ε ∧ ε ≤ ε0 ∧ ∀ i ∈ S, ε ≤ f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨ε0, h0, le_rfl, by simp⟩
  | @insert j S hj ih =>
    obtain ⟨ε, hε, hε0, hS⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min ε (f j), lt_min hε (hf j (Finset.mem_insert_self j S)),
      (min_le_left _ _).trans hε0, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hS i hi)

theorem good_of_two_lt {k : ℕ} {F : Finset ℕ} {q a : ℕ} (hval : Valid F q a)
    (hI : 2 < ideal F q a) : ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ Good k F q a B ε := by
  obtain ⟨B, hB⟩ := exists_B_big _ hI F.card
  refine ⟨B, 1, one_pos, ?_⟩
  intro C e q' hFC _ hC hyp hV
  exfalso
  have hlow := (known_bounds hval hFC hyp).1
  have hr1 := one_le_rest (F := F) (e := e) hC
  rw [← Finset.prod_sdiff hFC] at hV
  have hVF : 0 ≤ ∏ c ∈ F, hv c (e c) := by linarith
  have := mul_le_mul_of_nonneg_right hr1 hVF
  linarith

theorem good_zero {F : Finset ℕ} {q a : ℕ} (hval : Valid F q a) :
    ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ Good 0 F q a B ε := by
  rcases lt_or_gt_of_ne (ideal_ne_two hval) with hI | hI
  · refine ⟨0, (2 - ideal F q a) / 2, by linarith, ?_⟩
    intro C e q' hFC hcard hC hyp _
    have := le_ideal_of_empty hval hFC hyp (Finset.card_eq_zero.mp (by omega))
    linarith
  · exact good_of_two_lt hval hI

theorem good_succ {k : ℕ}
    (ih : ∀ (F : Finset ℕ) (q a : ℕ), Valid F q a → ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ Good k F q a B ε)
    {F : Finset ℕ} {q a : ℕ} (hval : Valid F q a) :
    ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ Good (k + 1) F q a B ε := by
  rcases lt_or_gt_of_ne (ideal_ne_two hval) with hI | hI
  swap
  · exact good_of_two_lt hval hI
  have hI0 := ideal_nonneg hval
  obtain ⟨N, hN⟩ := exists_nat_gt ((ideal F q a + 2) * ((k : ℚ) + 1) / (2 - ideal F q a))
  set P := (Finset.range (max N 3)).filter (fun c => c.Prime ∧ c ≠ 2) with hPdef
  have hval1 : ∀ c ∈ P, Valid (insert c F) q a := by
    intro c hc
    have hc' := (Finset.mem_filter.mp hc).2
    refine ⟨fun d hd => ?_, fun ha => ?_, hval.2.2⟩
    · rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hc'
      · exact hval.1 d hd
    · obtain ⟨h1, h2, h3⟩ := hval.2.1 ha
      exact ⟨Finset.mem_insert_of_mem h1, h2, h3⟩
  have hfam1 : ∀ c ∈ P, ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ Good k (insert c F) q a B ε :=
    fun c hc => ih _ _ _ (hval1 c hc)
  choose! B1 ε1 hε1 hG1 using hfam1
  set P2 := (P ×ˢ Finset.range (P.sup B1)).filter (fun p => p.1 % 4 = 1 ∧ p.2 % 4 = 1)
    with hP2def
  have hval2 : ∀ p ∈ P2, Valid (insert p.1 F) p.1 p.2 := by
    intro p hp
    obtain ⟨hpP, h4⟩ := Finset.mem_filter.mp hp
    have hp1 := (Finset.mem_filter.mp (Finset.mem_product.mp hpP).1).2
    refine ⟨fun d hd => ?_, fun _ => ⟨Finset.mem_insert_self _ _, h4⟩, fun h0 => ?_⟩
    · rcases Finset.mem_insert.mp hd with rfl | hd
      · exact hp1
      · exact hval.1 d hd
    · have := h4.2
      omega
  have hfam2 : ∀ p ∈ P2, ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ Good k (insert p.1 F) p.1 p.2 B ε :=
    fun p hp => ih _ _ _ (hval2 p hp)
  choose! B2 ε2 hε2 hG2 using hfam2
  obtain ⟨εa, hεa, hεa0, hεa1⟩ := exists_eps_le P ε1 hε1 ((2 - ideal F q a) / 2) (by linarith)
  obtain ⟨ε, hε, hεεa, hεb⟩ := exists_eps_le P2 ε2 hε2 εa hεa
  refine ⟨max (P.sup B1) (P2.sup B2), ε, hε, ?_⟩
  intro C e q' hFC hcard hC hyp hV
  obtain ⟨hB, hq', hmod⟩ := hyp
  by_cases hemp : C \ F = ∅
  · have := le_ideal_of_empty hval hFC ⟨hB, hq', hmod⟩ hemp
    linarith
  obtain ⟨c, hcmem, hmin⟩ :=
    (C \ F).exists_min_image id (Finset.nonempty_iff_ne_empty.mpr hemp)
  simp only [id] at hmin
  have hcC : c ∈ C := (Finset.mem_sdiff.mp hcmem).1
  have hcF : c ∉ F := (Finset.mem_sdiff.mp hcmem).2
  have hcp := hC c hcC
  have hc3 : 3 ≤ c := by
    have := hcp.1.two_le
    have := hcp.2
    omega
  by_cases hcbig : max N 3 ≤ c
  · obtain ⟨-, hup⟩ := known_bounds hval hFC ⟨hB, hq', hmod⟩
    have hr := rest_le (F := F) (e := e) hC (by omega) hmin hcard
    have hNc : (N : ℚ) ≤ c := by exact_mod_cast (le_max_left N 3).trans hcbig
    have hcI : (ideal F q a + 2) * (((k + 1 : ℕ) : ℚ)) < (2 - ideal F q a) * c := by
      rw [div_lt_iff₀ (by linarith)] at hN
      have := mul_le_mul_of_nonneg_left hNc (by linarith : (0 : ℚ) ≤ 2 - ideal F q a)
      push_cast
      nlinarith
    have ht := small_tail (ideal F q a) hI0 (k + 1) c (by omega) hcI
    rw [← Finset.prod_sdiff hFC]
    have hVF0 : 0 ≤ ∏ d ∈ F, hv d (e d) := Finset.prod_nonneg fun _ _ => hv_nonneg _ _
    have hHp : 0 ≤ Hv c ^ (k + 1) :=
      pow_nonneg (le_trans zero_le_one (one_le_Hv (by omega))) _
    have := mul_le_mul hr hup hVF0 hHp
    linarith
  have hcP : c ∈ P :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcp⟩
  have hcard' : (C \ insert c F).card ≤ k := by
    rw [Finset.sdiff_insert, Finset.card_erase_of_mem hcmem]
    omega
  have hsub : insert c F ⊆ C := Finset.insert_subset hcC hFC
  have hB1c : B1 c ≤ max (P.sup B1) (P2.sup B2) :=
    (Finset.le_sup (f := B1) hcP).trans (le_max_left _ _)
  by_cases hsp : a = 0 ∧ c = q' ∧ e c < B1 c
  · obtain ⟨ha, hcq, hec⟩ := hsp
    have hq0 := hval.2.2 ha
    have hm := hmod ha (hcq ▸ hcC) (hcq ▸ hcF)
    rw [← hcq] at hm
    have hp2 : (c, e c) ∈ P2 := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hcP, Finset.mem_range.mpr ?_⟩, hm⟩
      exact lt_of_lt_of_le hec (Finset.le_sup (f := B1) hcP)
    have hB2c : B2 (c, e c) ≤ max (P.sup B1) (P2.sup B2) :=
      (Finset.le_sup (f := B2) hp2).trans (le_max_right _ _)
    have hgood := hG2 (c, e c) hp2 C e q' hsub hcard' hC ?_ hV
    · have := hεb _ hp2
      linarith
    refine ⟨?_, fun _ => ⟨hcq.symm, rfl⟩, fun h0 => ?_⟩
    · intro d hd hdc hdor
      refine hB2c.trans (hB d hd (by rw [hq0]; exact (hC d hd).1.ne_zero) ?_)
      rcases hdor with hdF | hdq
      · rcases Finset.mem_insert.mp hdF with h | h
        · exact absurd h hdc
        · exact Or.inl h
      · exact Or.inr hdq
    · have := hm.2
      simp only at h0
      omega
  · have hgood := hG1 c hcP C e q' hsub hcard' hC ?_ hV
    · have := hεa1 c hcP
      linarith
    refine ⟨?_, hq', ?_⟩
    · intro d hd hdq hdor
      by_cases hdo : d ∈ F ∨ d ≠ q'
      · exact hB1c.trans (hB d hd hdq hdo)
      push Not at hdo
      obtain ⟨hdF, hdq'⟩ := hdo
      have hdc : d = c := by
        rcases hdor with h | h
        · rcases Finset.mem_insert.mp h with h | h
          · exact h
          · exact absurd h hdF
        · exact absurd hdq' h
      rw [hdc]
      by_cases ha : a = 0
      · exact not_lt.mp fun h => hsp ⟨ha, hdc.symm.trans hdq', h⟩
      · exact absurd (hdq'.trans (hq' ha).1) hdq
    · intro ha hq'C hq'F
      exact hmod ha hq'C fun h => hq'F (Finset.mem_insert_of_mem h)

theorem claim (k : ℕ) : ∀ (F : Finset ℕ) (q a : ℕ), Valid F q a →
    ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧ Good k F q a B ε := by
  induction k with
  | zero => exact fun F q a h => good_zero h
  | succ k ih => exact fun F q a h => good_succ ih h

end AbundancyGap

/-- A gap below 2: for at most `K` odd primes, with every exponent except that of `q` at least
`B`, and `q % 4 = 1`, `e q % 4 = 1` when `q ∈ C`, a product `∏ σ(c ^ e_c) / c ^ e_c` that is at
most 2 is below `2 - ε`. Restricted result (one odd prime divides every ordinary index); the
bound is not explicit (the proof gives no value); no published source was checked; novelty not
verified; the common index family is not excluded; the odd perfect number conjecture remains
open. -/
theorem exists_abundancy_gap (K : ℕ) :
    ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧
      ∀ (C : Finset ℕ) (e : ℕ → ℕ) (q : ℕ), C.card ≤ K → (∀ c ∈ C, c.Prime ∧ c ≠ 2) →
        (∀ c ∈ C, c ≠ q → B ≤ e c) → (q ∈ C → q % 4 = 1 ∧ e q % 4 = 1) →
        ∏ c ∈ C, ((σ 1 (c ^ e c) : ℚ) / ((c : ℚ) ^ e c)) ≤ 2 →
        ∏ c ∈ C, ((σ 1 (c ^ e c) : ℚ) / ((c : ℚ) ^ e c)) < 2 - ε := by
  obtain ⟨B, ε, hε, hG⟩ :=
    AbundancyGap.claim K ∅ 0 0 ⟨by simp, fun h => absurd rfl h, fun _ => rfl⟩
  refine ⟨B, ε, hε, ?_⟩
  intro C e q hcard hC hB hq hV
  refine hG C e q (Finset.empty_subset _) (by simpa using hcard) hC ⟨?_, ?_, ?_⟩ hV
  · intro c hc _ hor
    rcases hor with h | h
    · simp at h
    · exact hB c hc h
  · intro h
    exact absurd rfl h
  · intro _ hqC _
    exact hq hqC

end OddPerfect

#print axioms OddPerfect.exists_abundancy_gap
