import OddPerfect.ExceptSmallBound

/-!
# Tools for the bound `max 331 (2 * h ^ 2)` on a small exceptional prime

Analytic tools used in `OddPerfect.ExceptSmallTwo`:

* `exceptSmallTwo_weight_mul`: a completely multiplicative weight splits off a prime factor;
* `exceptSmallTwo_tail`: the part of a finite Euler product made of numbers with at least `k`
  prime factors (counted with multiplicity), `k ≤ 3`, is at most the matching tail
  `exceptSmallTwoTau z n k` of the series of `(1 - z) ^ (-n)`, where `n` is the number of primes
  and `z` bounds every weight;
* `exceptSmallTwo_ap`: the sum of `1 / (s - 1)` over distinct integers `s ≡ 5 (mod 6)` with
  `s ≥ d + 1` is at most `log (1 + 6 k / (d - 6)) / 6`, where `k` is their number;
* `exceptSmallTwo_exp_le` and `exceptSmallTwo_glue`: rational upper bounds for `exp`;
* `exceptSmallTwoCheck_all`: a finite rational check for `h ≤ 80`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

namespace OddPerfect

/-- A completely multiplicative weight splits off one prime factor. -/
theorem exceptSmallTwo_weight_mul (D : Finset ℕ) (w : ℕ → ℝ) {a m : ℕ} (ha : a.Prime)
    (haD : a ∈ D) (hm : m ≠ 0) :
    ∏ t ∈ D, w t ^ (a * m).factorization t = w a * ∏ t ∈ D, w t ^ m.factorization t := by
  rw [Nat.factorization_mul ha.ne_zero hm, ha.factorization]
  simp only [Finsupp.coe_add, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single a (fun t _ hta => by simp [Ne.symm hta])
    (fun h => absurd haD h)]
  simp

/-- The tails of the series `(1 - z) ^ (-n) = ∑_k C(n + k - 1, k) z ^ k`: the sum of the terms
of degree at least `k`, for `k ≤ 3` (the value for `k ≥ 3` is the tail from degree `3`). -/
noncomputable def exceptSmallTwoTau (z : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => ((1 - z) ^ n)⁻¹
  | 1 => ((1 - z) ^ n)⁻¹ - 1
  | 2 => ((1 - z) ^ n)⁻¹ - 1 - n * z
  | _ => ((1 - z) ^ n)⁻¹ - 1 - n * z - n * (n + 1) / 2 * z ^ 2

/-- The recursion of the tails in the number of variables. -/
theorem exceptSmallTwoTau_succ {z : ℝ} (hz : z < 1) (n k : ℕ) (hk : k ≤ 2) :
    exceptSmallTwoTau z (n + 1) (k + 1) =
      exceptSmallTwoTau z n (k + 1) + z * exceptSmallTwoTau z (n + 1) k := by
  have h1 : (1 - z) ≠ 0 := by linarith
  have hp : (1 - z) ^ n ≠ 0 := pow_ne_zero _ h1
  interval_cases k <;> simp only [exceptSmallTwoTau] <;> push_cast <;> rw [pow_succ] <;>
    field_simp <;> ring

/-- A finite Euler product with weights `0 ≤ w t ≤ z < 1` is at most `(1 - z) ^ (-n)`, where `n`
is the number of factors. -/
theorem exceptSmallTwo_prod_le {z : ℝ} (hz1 : z < 1) (w : ℕ → ℝ) (H : Finset ℕ)
    (hH : ∀ t ∈ H, 0 ≤ w t ∧ w t ≤ z) : ∏ t ∈ H, (1 - w t)⁻¹ ≤ ((1 - z) ^ H.card)⁻¹ := by
  rw [← Finset.prod_const, ← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod
  · intro t ht
    exact (inv_pos.mpr (by linarith [(hH t ht).2])).le
  · intro t ht
    have h1 := (hH t ht).2
    exact inv_anti₀ (by linarith) (by linarith)

/-- The tail bound for a finite Euler product. Let `H` be a finite set of primes with weights
`0 ≤ w t ≤ z < 1`, and let `T` be a finite set of positive integers whose prime factors lie in
`H` and which have at least `k ≤ 3` prime factors counted with multiplicity. Then the sum over `T`
of the completely multiplicative weights is at most `exceptSmallTwoTau z H.card k`. -/
theorem exceptSmallTwo_tail {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (w : ℕ → ℝ) :
    ∀ (H : Finset ℕ), (∀ t ∈ H, t.Prime ∧ 0 ≤ w t ∧ w t ≤ z) → ∀ k, k ≤ 3 →
      ∀ T : Finset ℕ, (∀ n ∈ T, n ≠ 0 ∧ n.primeFactors ⊆ H ∧ k ≤ Ω n) →
        ∑ n ∈ T, ∏ t ∈ H, w t ^ n.factorization t ≤ exceptSmallTwoTau z H.card k := by
  classical
  -- degree zero: the full Euler product
  have zero : ∀ (H : Finset ℕ), (∀ t ∈ H, t.Prime ∧ 0 ≤ w t ∧ w t ≤ z) →
      ∀ T : Finset ℕ, (∀ n ∈ T, n ≠ 0 ∧ n.primeFactors ⊆ H) →
        ∑ n ∈ T, ∏ t ∈ H, w t ^ n.factorization t ≤ exceptSmallTwoTau z H.card 0 := by
    intro H hH T hT
    have := exceptSmall_euler H w (fun t ht => (hH t ht).2.1)
      (fun t ht => lt_of_le_of_lt (hH t ht).2.2 hz1) T hT
    refine this.trans ?_
    simp only [exceptSmallTwoTau]
    exact exceptSmallTwo_prod_le hz1 w H fun t ht => (hH t ht).2
  intro H
  induction H using Finset.induction_on with
  | empty =>
    intro _ k hk T hT
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact zero ∅ (by simp) T (fun n hn => ⟨(hT n hn).1, (hT n hn).2.1⟩)
    · have hT0 : T = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro n hn
        obtain ⟨hn0, hsub, hk'⟩ := hT n hn
        have : n.primeFactors = ∅ := Finset.subset_empty.mp hsub
        rcases Nat.primeFactors_eq_empty.mp this with h0 | h1
        · exact hn0 h0
        · subst h1
          simp at hk'
          omega
      rw [hT0, Finset.sum_empty]
      interval_cases k <;> simp [exceptSmallTwoTau]
  | @insert a H haH ih =>
    intro hH
    have hHH : ∀ t ∈ H, t.Prime ∧ 0 ≤ w t ∧ w t ≤ z :=
      fun t ht => hH t (Finset.mem_insert_of_mem ht)
    obtain ⟨hap, hwa0, hwaz⟩ := hH a (Finset.mem_insert_self _ _)
    have ih' := ih hHH
    rw [Finset.card_insert_of_notMem haH]
    intro k
    induction k with
    | zero =>
      intro _ T hT
      have := zero (insert a H) hH T (fun n hn => ⟨(hT n hn).1, (hT n hn).2.1⟩)
      rwa [Finset.card_insert_of_notMem haH] at this
    | succ k ihk =>
      intro hk T hT
      rw [exceptSmallTwoTau_succ hz1 _ _ (by omega)]
      rw [← Finset.sum_filter_add_sum_filter_not T (fun n => a ∣ n), add_comm]
      apply add_le_add
      · -- the numbers not divisible by `a`
        have hle := ih' (k + 1) hk (T.filter fun n => ¬ a ∣ n) (by
          intro n hn
          rw [Finset.mem_filter] at hn
          obtain ⟨hn0, hsub, hk'⟩ := hT n hn.1
          refine ⟨hn0, ?_, hk'⟩
          intro p hp
          rcases Finset.mem_insert.mp (hsub hp) with rfl | hp'
          · exact absurd (Nat.dvd_of_mem_primeFactors hp) hn.2
          · exact hp')
        refine le_of_eq_of_le ?_ hle
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.mem_filter] at hn
        rw [Finset.prod_insert haH, Nat.factorization_eq_zero_of_not_dvd hn.2, pow_zero,
          one_mul]
      · -- the numbers divisible by `a`
        set T2 := T.filter fun n => a ∣ n with hT2
        have hmem : ∀ n ∈ T2, n ∈ T ∧ a ∣ n := fun n hn => Finset.mem_filter.mp hn
        have hinj : Set.InjOn (fun n => n / a) T2 := by
          intro n hn m hm hnm
          exact Nat.div_left_inj (hmem n hn).2 (hmem m hm).2 |>.mp hnm
        have hsum : ∑ n ∈ T2, ∏ t ∈ insert a H, w t ^ n.factorization t =
            w a * ∑ m ∈ T2.image (fun n => n / a), ∏ t ∈ insert a H, w t ^ m.factorization t := by
          rw [Finset.sum_image hinj, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n hn => ?_
          obtain ⟨hnT, han⟩ := hmem n hn
          have hn0 := (hT n hnT).1
          have hm0 : n / a ≠ 0 := by
            intro h0
            rcases Nat.div_eq_zero_iff.mp h0 with h | h
            · exact hap.ne_zero h
            · exact hn0 (Nat.eq_zero_of_dvd_of_lt han h)
          conv_lhs => rw [← Nat.mul_div_cancel' han]
          exact exceptSmallTwo_weight_mul _ w hap (Finset.mem_insert_self _ _) hm0
        have hbound := ihk (by omega) (T2.image fun n => n / a) (by
          intro m hm
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
          obtain ⟨hnT, han⟩ := hmem n hn
          obtain ⟨hn0, hsub, hk'⟩ := hT n hnT
          have hm0 : n / a ≠ 0 := by
            intro h0
            rcases Nat.div_eq_zero_iff.mp h0 with h | h
            · exact hap.ne_zero h
            · exact hn0 (Nat.eq_zero_of_dvd_of_lt han h)
          refine ⟨hm0, (Nat.primeFactors_mono (Nat.div_dvd_of_dvd han) hn0).trans hsub, ?_⟩
          have hΩ : Ω n = Ω a + Ω (n / a) := by
            rw [← cardFactors_mul hap.ne_zero hm0, Nat.mul_div_cancel' han]
          rw [cardFactors_apply_prime hap] at hΩ
          omega)
        have hS0 : 0 ≤ ∑ m ∈ T2.image (fun n => n / a), ∏ t ∈ insert a H,
            w t ^ m.factorization t :=
          Finset.sum_nonneg fun m _ => Finset.prod_nonneg fun t ht =>
            pow_nonneg (hH t ht).2.1 _
        rw [hsum]
        calc w a * ∑ m ∈ T2.image (fun n => n / a), ∏ t ∈ insert a H, w t ^ m.factorization t
            ≤ z * ∑ m ∈ T2.image (fun n => n / a), ∏ t ∈ insert a H,
                w t ^ m.factorization t := mul_le_mul_of_nonneg_right hwaz hS0
          _ ≤ z * exceptSmallTwoTau z (H.card + 1) k := by
              exact mul_le_mul_of_nonneg_left hbound hz0

/-- Distinct integers `≡ 5 (mod 6)` that are at least `d + 1` are spread out: the largest one is
at least `d + 1 + 6 (k - 1)`, where `k` is their number. -/
theorem exceptSmallTwo_spread (d : ℕ) (A : Finset ℕ) (hA : ∀ s ∈ A, d + 1 ≤ s ∧ s % 6 = 5)
    (x : ℕ) (hx : x ∈ A) (hmax : ∀ y ∈ A, y ≤ x) : d + 1 + 6 * (A.card - 1) ≤ x := by
  have hc : A.card ≤ (Finset.Icc ((d + 1) / 6) (x / 6)).card := by
    apply Finset.card_le_card_of_injOn (fun y => y / 6)
    · intro y hy
      have := hA y hy
      have := hmax y hy
      simp only [Finset.coe_Icc, Set.mem_Icc]
      constructor
      · omega
      · exact Nat.div_le_div_right (hmax y hy)
    · intro y hy y' hy' hyy
      have := hA y hy
      have := hA y' hy'
      simp only at hyy
      omega
  rw [Nat.card_Icc] at hc
  have := hA x hx
  omega

/-- The sum of `1 / (s - 1)` over distinct integers `s ≡ 5 (mod 6)` with `s ≥ d + 1` is at most
`log (1 + 6 k / (d - 6)) / 6`, where `k` is their number. -/
theorem exceptSmallTwo_ap (d : ℕ) (hd : 7 ≤ d) (A : Finset ℕ)
    (hA : ∀ s ∈ A, d + 1 ≤ s ∧ s % 6 = 5) :
    ∑ s ∈ A, ((s : ℝ) - 1)⁻¹ ≤ Real.log (1 + 6 * A.card / ((d : ℝ) - 6)) / 6 := by
  classical
  have hd' : (7 : ℝ) ≤ d := by exact_mod_cast hd
  induction A using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hA' : ∀ x ∈ s, d + 1 ≤ x ∧ x % 6 = 5 := fun x hx => hA x (Finset.mem_insert_of_mem hx)
    have hsp := exceptSmallTwo_spread d (insert a s) hA a (Finset.mem_insert_self _ _)
      (fun y hy => by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact le_rfl
        · exact (hlt y hy).le)
    rw [Finset.card_insert_of_notMem has] at hsp
    simp only [Nat.add_sub_cancel] at hsp
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has]
    have ih' := ih hA'
    set k := s.card
    have hak : (d : ℝ) + 6 * k + 1 ≤ a := by exact_mod_cast (by omega : d + 6 * k + 1 ≤ a)
    set u : ℝ := (d : ℝ) - 6 with hu
    have hu0 : 0 < u := by linarith
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hX : 0 < 1 + 6 * (k : ℝ) / u := by positivity
    have hX' : 0 < 1 + 6 * ((k + 1 : ℕ) : ℝ) / u := by positivity
    have hlog : 6 / ((d : ℝ) + 6 * k) ≤
        Real.log (1 + 6 * ((k + 1 : ℕ) : ℝ) / u) - Real.log (1 + 6 * (k : ℝ) / u) := by
      rw [← Real.log_div hX'.ne' hX.ne']
      have hpos : 0 < (1 + 6 * ((k + 1 : ℕ) : ℝ) / u) / (1 + 6 * (k : ℝ) / u) :=
        div_pos hX' hX
      have := Real.one_sub_inv_le_log_of_pos hpos
      refine le_trans (le_of_eq ?_) this
      push_cast
      field_simp
      rw [hu]
      ring
    have hterm : ((a : ℝ) - 1)⁻¹ ≤ 6 / ((d : ℝ) + 6 * k) / 6 := by
      rw [show 6 / ((d : ℝ) + 6 * k) / 6 = ((d : ℝ) + 6 * k)⁻¹ by field_simp]
      exact inv_anti₀ (by linarith) (by linarith)
    linarith

/-- `exp x ≤ (1 - x / n) ^ (-n)` for `x < n`. -/
theorem exceptSmallTwo_exp_le (x : ℝ) (n : ℕ) (hn : 0 < n) (hx : x < n) :
    Real.exp x ≤ ((1 - x / n) ^ n)⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 0 < 1 - x / n := by
    rw [sub_pos, div_lt_one hn']
    exact hx
  have h2 : 1 - x / n ≤ Real.exp (-(x / n)) := by
    have := Real.add_one_le_exp (-(x / n))
    linarith
  have h3 : Real.exp (x / n) ≤ (1 - x / n)⁻¹ := by
    rw [Real.exp_neg] at h2
    rw [le_inv_comm₀ (Real.exp_pos _) h1]
    exact h2
  calc Real.exp x = Real.exp (x / n) ^ n := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
    _ ≤ ((1 - x / n)⁻¹) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le h3 n
    _ = ((1 - x / n) ^ n)⁻¹ := inv_pow _ _

/-- The final step: if `X * (5 / 2) < 64 * (1 - 6 R / 16) ^ 16` then
`log X / 6 + log (5 / 2) / 6 + R ≤ log 2`. -/
theorem exceptSmallTwo_glue (X R : ℝ) (hX : 0 < X) (h6 : 6 * R < 16)
    (hc : X * (5 / 2) < 64 * (1 - 6 * R / 16) ^ 16) :
    Real.log X / 6 + Real.log (5 / 2) / 6 + R ≤ Real.log 2 := by
  have he := exceptSmallTwo_exp_le (6 * R) 16 (by norm_num) (by exact_mod_cast h6)
  push_cast at he
  have hp : 0 < (1 - 6 * R / 16) ^ 16 := by
    have : 0 < 1 - 6 * R / 16 := by linarith
    positivity
  have hprod : X * (5 / 2) * Real.exp (6 * R) ≤ 64 := by
    calc X * (5 / 2) * Real.exp (6 * R) ≤ X * (5 / 2) * ((1 - 6 * R / 16) ^ 16)⁻¹ :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ 64 := by
          rw [← div_eq_mul_inv, div_le_iff₀ hp]
          linarith
  have hlog := Real.log_le_log (by positivity) hprod
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hX.ne' (by norm_num),
    Real.log_exp] at hlog
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  linarith

/-- The parameter `M = max 331 (2 h ^ 2)`. -/
def exceptSmallTwoM (h : ℕ) : ℕ := max 331 (2 * h ^ 2)

/-- A lower bound for the square root of `M + 1`. -/
def exceptSmallTwoR (h : ℕ) : ℕ := max 18 (1414 * h / 1000)

/-- A lower bound, minus one, for the exact square primes `s` with `s ^ 2 + s + 1 > M`. -/
def exceptSmallTwoD (h : ℕ) : ℕ := max 40 (1414 * h / 1000 - 1)

/-- The rational remainder term of the estimate for `h` exceptional primes. -/
def exceptSmallTwoRest (h : ℕ) : ℚ :=
  1 / 672 + h / exceptSmallTwoM h + 41 / 40 *
    ((exceptSmallTwoR h / (exceptSmallTwoR h - 1 : ℚ)) ^ h / 24 +
      ((exceptSmallTwoR h / (exceptSmallTwoR h - 1 : ℚ)) ^ h - 1 - h / exceptSmallTwoR h -
        h * (h + 1) / 2 / (exceptSmallTwoR h : ℚ) ^ 2))

/-- The logarithmic term of the estimate for `h` exceptional primes. -/
def exceptSmallTwoX (h : ℕ) : ℚ := 1 + 6 * h / ((exceptSmallTwoD h : ℚ) - 6)

/-- The finite check for one value of `h`. -/
def exceptSmallTwoCheck (h : ℕ) : Bool :=
  decide (exceptSmallTwoR h ^ 2 ≤ exceptSmallTwoM h + 1) &&
  (decide (exceptSmallTwoD h = 40) ||
    decide (exceptSmallTwoD h ^ 2 + exceptSmallTwoD h + 1 ≤ exceptSmallTwoM h)) &&
  decide (6 * exceptSmallTwoRest h < 16) &&
  decide (exceptSmallTwoX h * (5 / 2) < 64 * (1 - 6 * exceptSmallTwoRest h / 16) ^ 16)

/-- The finite check holds for every `h ≤ 80`. -/
theorem exceptSmallTwoCheck_all : ∀ h < 81, exceptSmallTwoCheck h = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
/-- The numerical part of the estimate, for every `h`: parameters `z` and `d` that bound the
weights of the primes above `M` and the exact square primes `s` with `s ^ 2 + s + 1 > M`, and
for which the total of the estimate is at most `log 2`. -/
theorem exceptSmallTwo_numeric (h : ℕ) :
    ∃ z : ℝ, ∃ d : ℕ, 0 ≤ z ∧ z < 1 ∧
      (∀ t, exceptSmallTwoM h < t → ((Nat.sqrt t : ℕ) : ℝ)⁻¹ ≤ z) ∧ 7 ≤ d ∧
      (∀ s, 41 ≤ s → exceptSmallTwoM h < phi3 s → d + 1 ≤ s) ∧
      Real.log (1 + 6 * h / ((d : ℝ) - 6)) / 6 + Real.log (5 / 2) / 6 +
        (1 / 672 + h / (exceptSmallTwoM h : ℝ) + 41 / 40 *
          (((1 - z) ^ h)⁻¹ / 24 + exceptSmallTwoTau z h 3)) ≤ Real.log 2 := by
  have hM1 : 331 ≤ exceptSmallTwoM h := le_max_left _ _
  have hM2 : 2 * h ^ 2 ≤ exceptSmallTwoM h := le_max_right _ _
  rcases Nat.lt_or_ge h 81 with hlt | hge
  · -- the finite range
    have hc := exceptSmallTwoCheck_all h hlt
    simp only [exceptSmallTwoCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hr, hd⟩, h6⟩, hfin⟩ := hc
    set r := exceptSmallTwoR h with hr_def
    have hr18 : 18 ≤ r := le_max_left _ _
    have hr' : (18 : ℝ) ≤ r := by exact_mod_cast hr18
    have hd40 : 40 ≤ exceptSmallTwoD h := le_max_left _ _
    refine ⟨(r : ℝ)⁻¹, exceptSmallTwoD h, by positivity, ?_, ?_, by omega, ?_, ?_⟩
    · rw [inv_lt_one₀ (by linarith)]
      linarith
    · intro t ht
      have hle : r ≤ Nat.sqrt t := Nat.le_sqrt.mpr (by nlinarith)
      have : (r : ℝ) ≤ (Nat.sqrt t : ℝ) := by exact_mod_cast hle
      exact inv_anti₀ (by linarith) this
    · intro s hs hsM
      rcases hd with hd | hd
      · omega
      · have : phi3 (exceptSmallTwoD h) < phi3 s := lt_of_le_of_lt (by unfold phi3; omega) hsM
        have := phi3_strictMono.lt_iff_lt.mp this
        omega
    · have hfinR := (Rat.cast_lt (K := ℝ)).mpr hfin
      have h6R := (Rat.cast_lt (K := ℝ)).mpr h6
      push_cast [exceptSmallTwoX, exceptSmallTwoRest] at hfinR h6R
      have hX : (0 : ℝ) < 1 + 6 * h / ((exceptSmallTwoD h : ℝ) - 6) := by
        have : (40 : ℝ) ≤ exceptSmallTwoD h := by exact_mod_cast hd40
        have : (0 : ℝ) ≤ 6 * h / ((exceptSmallTwoD h : ℝ) - 6) :=
          div_nonneg (by positivity) (by linarith)
        linarith
      have hglue := exceptSmallTwo_glue _ _ hX h6R hfinR
      refine le_of_eq_of_le ?_ hglue
      have hP : ((1 - (r : ℝ)⁻¹) ^ h)⁻¹ = ((r : ℝ) / ((r : ℝ) - 1)) ^ h := by
        rw [← inv_pow]
        congr 1
        field_simp
      simp only [exceptSmallTwoTau]
      rw [hP]
      ring
  · -- the general range
    have hh0 : (81 : ℝ) ≤ h := by exact_mod_cast hge
    have hhpos : (0 : ℝ) < h := by linarith
    set z : ℝ := 5 / (7 * h) with hz
    have hz0 : 0 ≤ z := by positivity
    have hzs : z ≤ 5 / 567 := by
      rw [hz, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hz1 : z < 1 := by linarith
    refine ⟨z, 7 * h / 5 - 1, hz0, hz1, ?_, by omega, ?_, ?_⟩
    · intro t ht
      set m := (7 * h + 4) / 5 with hm
      have hm5 : 7 * h ≤ 5 * m := by omega
      have hm5' : 5 * m ≤ 7 * h + 4 := by omega
      have hmm : m * m ≤ t := by nlinarith
      have hle : m ≤ Nat.sqrt t := Nat.le_sqrt.mpr hmm
      have hmR : (7 : ℝ) * h ≤ 5 * (Nat.sqrt t : ℝ) := by exact_mod_cast (by omega :
        7 * h ≤ 5 * Nat.sqrt t)
      have hpos : (0 : ℝ) < Nat.sqrt t := by linarith
      rw [hz, inv_eq_one_div, div_le_div_iff₀ hpos (by positivity)]
      linarith
    · intro s hs hsM
      by_contra hlt
      have h5 : 5 * (s + 1) ≤ 7 * h := by omega
      have : 25 * phi3 s ≤ 50 * h ^ 2 := by
        unfold phi3
        nlinarith
      omega
    · -- the logarithmic term
      have hd : (7 * h / 5 - 1 : ℕ) + 1 = 7 * h / 5 := by omega
      have hd5 : (7 : ℝ) * h ≤ 5 * (((7 * h / 5 - 1 : ℕ) : ℝ) + 1) + 4 := by
        have : 7 * h ≤ 5 * ((7 * h / 5 - 1) + 1) + 4 := by omega
        exact_mod_cast this
      set d : ℝ := ((7 * h / 5 - 1 : ℕ) : ℝ) with hdR
      have hd6 : 0 < d - 6 := by linarith
      have hX : 1 + 6 * h / (d - 6) ≤ 57 / 10 := by
        rw [← sub_nonneg, show (57 : ℝ) / 10 - (1 + 6 * h / (d - 6)) =
          ((47 / 10) * (d - 6) - 6 * h) / (d - 6) by field_simp; ring]
        apply div_nonneg _ hd6.le
        linarith
      have hX0 : 0 < 1 + 6 * h / (d - 6) := by positivity
      have hlog1 := Real.log_le_log hX0 hX
      -- the Euler product part
      have hP : ((1 - z) ^ h)⁻¹ ≤ 208 / 100 := by
        have h1z : 0 < 1 - z := by linarith
        have hstep : (1 - z)⁻¹ ≤ Real.exp (z / (1 - z)) := by
          have := Real.add_one_le_exp (z / (1 - z))
          rw [show z / (1 - z) + 1 = (1 - z)⁻¹ by field_simp; ring] at this
          exact this
        have hhz : (h : ℝ) * z = 5 / 7 := by
          rw [hz]
          field_simp
        calc ((1 - z) ^ h)⁻¹ = ((1 - z)⁻¹) ^ h := (inv_pow _ _).symm
          _ ≤ Real.exp (z / (1 - z)) ^ h := pow_le_pow_left₀ (by positivity) hstep h
          _ = Real.exp (h * (z / (1 - z))) := by rw [← Real.exp_nat_mul]
          _ ≤ Real.exp (2835 / 3934) := by
              apply Real.exp_le_exp.mpr
              rw [show (h : ℝ) * (z / (1 - z)) = (5 / 7) / (1 - z) by
                rw [← hhz]
                ring]
              rw [div_le_div_iff₀ h1z (by norm_num)]
              linarith
          _ ≤ ((1 - 2835 / 3934 / 32) ^ 32)⁻¹ := by
              have := exceptSmallTwo_exp_le (2835 / 3934) 32 (by norm_num) (by norm_num)
              push_cast at this
              exact this
          _ ≤ 208 / 100 := by norm_num
      have hT : exceptSmallTwoTau z h 3 ≤ ((1 - z) ^ h)⁻¹ - 1 - 5 / 7 - 25 / 98 := by
        simp only [exceptSmallTwoTau]
        have hhz : (h : ℝ) * z = 5 / 7 := by
          rw [hz]
          field_simp
        have hq : (25 : ℝ) / 98 ≤ h * (h + 1) / 2 * z ^ 2 := by
          rw [show (h : ℝ) * (h + 1) / 2 * z ^ 2 = (h * z) ^ 2 / 2 + (h * z) * z / 2 by ring,
            hhz]
          nlinarith
        linarith
      have hHM : (h : ℝ) / (exceptSmallTwoM h : ℝ) ≤ 1 / 162 := by
        have : (2 : ℝ) * h ^ 2 ≤ exceptSmallTwoM h := by exact_mod_cast hM2
        rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
        nlinarith
      have hglue := exceptSmallTwo_glue (57 / 10)
        (1 / 672 + 1 / 162 + 41 / 40 * (208 / 100 / 24 + (208 / 100 - 1 - 5 / 7 - 25 / 98)))
        (by norm_num) (by norm_num) (by norm_num)
      have hPpos : 0 ≤ ((1 - z) ^ h)⁻¹ := by
        have : 0 < 1 - z := by linarith
        positivity
      linarith

end OddPerfect

#print axioms OddPerfect.exceptSmallTwo_weight_mul
#print axioms OddPerfect.exceptSmallTwoTau_succ
#print axioms OddPerfect.exceptSmallTwo_tail
#print axioms OddPerfect.exceptSmallTwo_spread
#print axioms OddPerfect.exceptSmallTwo_ap
#print axioms OddPerfect.exceptSmallTwo_exp_le
#print axioms OddPerfect.exceptSmallTwo_glue
#print axioms OddPerfect.exceptSmallTwoCheck_all
#print axioms OddPerfect.exceptSmallTwo_prod_le
#print axioms OddPerfect.exceptSmallTwo_numeric
