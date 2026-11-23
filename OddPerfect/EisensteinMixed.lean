import OddPerfect.ZeroDefect

/-!
# At most one escape row unless the special prime is 13 modulo 24

For a prime `q ≡ 1 (mod 4)` the library shows that each of the shapes `phi3 p = q ^ n` and
`phi3 p = 3 * q ^ m` has at most one odd solution `p` (`phi3_eq_mul_prime_pow_unique`). Here we
show that both shapes occur together only if `q ≡ 5 (mod 8)`. A prime dividing `phi3 p` other than
`3` is `1` modulo `3`, so with two escape rows the special prime is `13` modulo `24`.

Local step (`eisenstein_two_forms_norm_mod_eight`): write `z = 1 + 2 ^ h w` with `h ≥ 2` and `w`
not divisible by `2`. If `L (z ^ n) = 1` for `L (a + b ω) = a + ℓ b` and `n ≥ 1`, then
`2 ^ (h - 1)` divides `L w` (binomial expansion). With `ℓ = 0` and `ℓ = -2` this forces `h = 2`,
`w.re` even and `w.im` odd, hence `norm z ≡ 5 (mod 8)`.

Both shapes are settled in the literature by classical theorems that this library does not
prove; this is an elementary route for one residue class. Novelty is not verified.

With the positive support defect of `ZeroDefect` this gives `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 5`
for every special prime that is not `13` modulo `24`. The total excess is not bounded here.
-/

open ArithmeticFunction Finset QuadraticAlgebra
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Sharp step one on integers: if `∑ C(n, r) 2 ^ ((h + 1) r) t r = 1` with `t 0 = 1`, `n ≥ 1`,
then `2 ^ h` divides `t 1`. -/
private theorem step_one_sharp (h : ℕ) (t : ℕ → ℤ) (ht0 : t 0 = 1) {n : ℕ} (hn : 1 ≤ n)
    (hsum : ∑ r ∈ range (n + 2), (n.choose r : ℤ) * 2 ^ ((h + 1) * r) * t r = 1) :
    (2 : ℤ) ^ h ∣ t 1 := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, f = fun r => (n.choose r : ℤ) * 2 ^ ((h + 1) * r) * t r :=
    ⟨_, rfl⟩
  have hs : ∑ r ∈ range (n + 2), f r = 1 := by rw [hf]; exact hsum
  rw [sum_range_succ', sum_range_succ'] at hs
  have e0 : f 0 = 1 := by rw [hf]; simp [ht0]
  have e1 : f (0 + 1) = n * 2 ^ (h + 1) * t 1 := by rw [hf]; simp
  rw [e0, e1] at hs
  obtain ⟨e, k, hk, hnk⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have htail : ∀ i ∈ range n, (2 : ℤ) ^ (e + (2 * h + 1)) ∣ f (i + 1 + 1) := by
    intro i _
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hN : 2 ^ e ∣ (i + 2) * (n' + 1).choose (i + 2) := by
      have := Nat.add_one_mul_choose_eq n' (i + 1)
      refine (show 2 ^ e ∣ n' + 1 from ⟨k, hnk⟩).trans ?_
      rw [mul_comm]
      exact ⟨n'.choose (i + 1), this.symm⟩
    have hZ : (2 : ℤ) ^ e ∣ ((i + 2 : ℕ) : ℤ) * ((n' + 1).choose (i + 2) : ℤ) := by
      have := Int.natCast_dvd_natCast.2 hN
      push_cast at this ⊢
      exact this
    have hb := two_pow_dvd_of_mul_odd_part (F := i + 2) (K := 2 * h + 1)
      (e := (h + 1) * (i + 2)) (by omega)
      (fun j hj => by
        have h1 : j < 2 ^ j := Nat.lt_two_pow_self
        have h2 := Nat.le_of_dvd (by omega) hj
        nlinarith) hZ
    rw [hf]
    simp only
    rw [show i + 1 + 1 = i + 2 by ring]
    rw [show ((n' + 1).choose (i + 2) : ℤ) * 2 ^ ((h + 1) * (i + 2)) * t (i + 2)
      = 2 ^ ((h + 1) * (i + 2)) * ((n' + 1).choose (i + 2) : ℤ) * t (i + 2) by ring]
    exact dvd_mul_of_dvd_left hb _
  have hd : (2 : ℤ) ^ (e + (2 * h + 1)) ∣ n * 2 ^ (h + 1) * t 1 := by
    have h1 : (n : ℤ) * 2 ^ (h + 1) * t 1 = -(∑ i ∈ range n, f (i + 1 + 1)) := by linarith
    rw [h1]
    exact (dvd_neg).2 (dvd_sum htail)
  have h2 : (n : ℤ) * 2 ^ (h + 1) * t 1 = 2 ^ (e + h + 1) * (k * t 1) := by
    rw [hnk]; push_cast; ring
  rw [h2, show e + (2 * h + 1) = (e + h + 1) + h by ring, pow_add] at hd
  have h3 : (2 : ℤ) ^ h ∣ k * t 1 := (mul_dvd_mul_iff_left (by positivity)).1 hd
  have hcop : IsCoprime ((2 : ℤ) ^ h) (k : ℤ) := by
    have : Nat.Coprime (2 ^ h) k := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hk)
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  exact hcop.dvd_of_dvd_mul_left h3

/-- Sharp step one: if `L ((1 + 2 ^ (h + 1) w) ^ n) = 1` with `n ≥ 1`, then `2 ^ h ∣ L w`. -/
private theorem step_one_sharp_eis (ℓ : ℤ) (h : ℕ) (w : Eis) {n : ℕ} (hn : 1 ≤ n)
    (h1 : eisLin ℓ ((1 + (((2 : ℤ) ^ (h + 1) : ℤ) : Eis) * w) ^ n) = 1) :
    (2 : ℤ) ^ h ∣ eisLin ℓ w := by
  rw [eisLin_pow_expand_range ℓ (h + 1) w (N := n + 2) (by omega)] at h1
  have := step_one_sharp h (fun r => eisLin ℓ (w ^ r)) (by simp [eisLin_one]) hn h1
  simpa using this

/-- Local: for `z ≡ 1 (mod 4)`, `z ≠ 1`, both linear forms `L_0 (a + b ω) = a` and
`L_(-2) (a + b ω) = a - 2 b` cannot hit `1` on powers of `z` unless `norm z ≡ 5 (mod 8)`. -/
theorem eisenstein_two_forms_norm_mod_eight {z : Eis} (hz : z ≠ 1) (hre : (4 : ℤ) ∣ z.re - 1)
    (him : (4 : ℤ) ∣ z.im) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (h1 : (z ^ n).re = 1)
    (h2 : (z ^ m).re - 2 * (z ^ m).im = 1) : Eis.nrm z % 8 = 5 := by
  obtain ⟨h, hh, w, rfl, hw⟩ := eisenstein_decomp hz hre him
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
  have L1 : eisLin 0 ((1 + (((2 : ℤ) ^ (g + 1) : ℤ) : Eis) * w) ^ n) = 1 := by
    rw [eisLin_apply]; linarith
  have L2 : eisLin (-2) ((1 + (((2 : ℤ) ^ (g + 1) : ℤ) : Eis) * w) ^ m) = 1 := by
    rw [eisLin_apply]; linarith
  have A := step_one_sharp_eis 0 g w hn L1
  have B := step_one_sharp_eis (-2) g w hm L2
  rw [eisLin_apply] at A B
  have hre' : (1 + (((2 : ℤ) ^ (g + 1) : ℤ) : Eis) * w).re = 1 + 2 ^ (g + 1) * w.re := by
    simp only [re_add, re_one, re_mul, re_intCast, im_intCast, Int.cast_id]; ring
  have him' : (1 + (((2 : ℤ) ^ (g + 1) : ℤ) : Eis) * w).im = 2 ^ (g + 1) * w.im := by
    simp only [im_add, im_one, im_mul, re_intCast, im_intCast, Int.cast_id]; ring
  rcases (show g = 1 ∨ 2 ≤ g by omega) with rfl | hg
  · have hu : (2 : ℤ) ∣ w.re := by simpa using A
    have hv : ¬ (2 : ℤ) ∣ w.im := fun hv => hw ⟨hu, hv⟩
    obtain ⟨c, hc⟩ : ∃ c, w.im = 2 * c + 1 := ⟨w.im / 2, by omega⟩
    rw [Eis.nrm, hre', him', hc]
    have e : (1 + 2 ^ (1 + 1) * w.re) ^ 2 - (1 + 2 ^ (1 + 1) * w.re) * (2 ^ (1 + 1) * (2 * c + 1))
        + (2 ^ (1 + 1) * (2 * c + 1)) ^ 2 =
        8 * (w.re + 2 * w.re ^ 2 - 2 * w.re * (2 * c + 1) + 2 * (2 * c + 1) ^ 2 - c - 1) + 5 := by
      ring
    rw [e]
    omega
  · exfalso
    have h4 : (4 : ℤ) ∣ 2 ^ g := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 hg
    have A4 := h4.trans A
    have B4 := h4.trans B
    exact hw ⟨by omega, by omega⟩

/-- The control: `z = 1 + 4 ω` has norm `13`, `L_0 (z) = 1` and `L_(-2) (z ^ 2) = 1`, so the
congruence `5 (mod 8)` cannot be dropped; `22 ^ 2 + 22 + 1 = 3 * 13 ^ 2` is the matching base. -/
example : Eis.nrm ⟨1, 4⟩ = 13 ∧ ((⟨1, 4⟩ : Eis) ^ 1).re = 1 ∧
    ((⟨1, 4⟩ : Eis) ^ 2).re - 2 * ((⟨1, 4⟩ : Eis) ^ 2).im = 1 ∧ phi3 22 = 3 * 13 ^ 2 := by
  refine ⟨by simp [Eis.nrm], by simp, ?_, by simp [phi3]⟩
  simp [pow_two]

/-- For a prime `q ≡ 1 (mod 4)`, if `phi3 p = q ^ n` and `phi3 p' = 3 * q ^ m` with odd `p`,
`p'` and `n, m ≥ 1`, then `q ≡ 5 (mod 8)`. Elementary;
classical theorems, not proved in this library, say more. -/
theorem phi3_both_shapes_mod_eight {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) {p p' n m : ℕ}
    (hp : Odd p) (hp' : Odd p') (hn : 1 ≤ n) (hm : 1 ≤ m) (h1 : phi3 p = q ^ n)
    (h2 : phi3 p' = 3 * q ^ m) : q % 8 = 5 := by
  obtain ⟨ρ, hρq, hρ1, hre, him, hrow⟩ :=
    exists_normalized_root_of_row hq hq4 ⟨p, n, hn, Or.inl (by rw [← h1]; rfl)⟩
  have hs1 : star ρ ≠ 1 := fun e => hρ1 (by simpa using congrArg star e)
  have hsre : (4 : ℤ) ∣ (star ρ).re - 1 := by
    obtain ⟨a, ha⟩ := hre
    obtain ⟨b, hb⟩ := him
    exact ⟨a - b, by rw [QuadraticAlgebra.re_star]; linear_combination ha - hb⟩
  have hsim : (4 : ℤ) ∣ (star ρ).im := by
    obtain ⟨b, hb⟩ := him
    exact ⟨-b, by rw [QuadraticAlgebra.im_star, hb]; ring⟩
  have key : ∀ z : Eis, Eis.nrm z = q → z ≠ 1 → (4 : ℤ) ∣ z.re - 1 → (4 : ℤ) ∣ z.im →
      (z ^ n).re = 1 → (z ^ m).re - 2 * (z ^ m).im = 1 → q % 8 = 5 := by
    intro z hzq hz1 hzr hzi ha hb
    have := eisenstein_two_forms_norm_mod_eight hz1 hzr hzi hn hm ha hb
    rw [hzq] at this
    omega
  rcases (hrow p n hp hn).1 (by rw [← h1]; rfl) with a | a <;>
    rcases (hrow p' m hp' hm).2 (by rw [← h2]; rfl) with b | b
  · exact key ρ hρq hρ1 hre him a b
  · exfalso
    refine eisenstein_pow_linear_star_ne_one hρ1 hre him (ℓ := 0) (ℓ' := -2) ⟨0, by norm_num⟩
      ⟨-1, by norm_num⟩ hn hm (by linarith) (by linarith)
  · exfalso
    refine eisenstein_pow_linear_star_ne_one hs1 hsre hsim (ℓ := 0) (ℓ' := -2) ⟨0, by norm_num⟩
      ⟨-1, by norm_num⟩ hn hm (by linarith) (by rw [star_star]; linarith)
  · exact key (star ρ) (by rw [Eis.nrm_star, hρq]) hs1 hsre hsim a b

/-- For a prime `q ≡ 1 (mod 8)`, the two shapes do not both have an odd solution. Elementary;
classical theorems, not proved in this library, say more. -/
theorem not_phi3_both_shapes_of_mod_eight {q : ℕ} (hq : q.Prime) (hq8 : q % 8 = 1) {p p' n m : ℕ}
    (hp : Odd p) (hp' : Odd p') (hn : 1 ≤ n) (hm : 1 ≤ m) (h1 : phi3 p = q ^ n)
    (h2 : phi3 p' = 3 * q ^ m) : False := by
  have := phi3_both_shapes_mod_eight hq (by omega) hp hp' hn hm h1 h2
  omega

/-- At most one escape row unless the special prime is `13` modulo `24`. No classical input. -/
theorem card_escapeRows_le_one {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hq24 : q % 24 ≠ 13) : (escapeRows N q).card ≤ 1 := by
  have hq4 : q % 4 = 1 := (special_mod_four h hq hodd).1
  have hq3 : q ≠ 3 := by omega
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨hao, j, hj, hsa | hsa⟩ := phi3_escapeRow h ha <;>
    obtain ⟨hbo, k, hk, hsb | hsb⟩ := phi3_escapeRow h hb
  · exact phi3_eq_mul_prime_pow_unique hq hq4 (Or.inl rfl) hao hbo hj hk
      (by rw [hsa, one_mul]) (by rw [hsb, one_mul])
  · have h8 := phi3_both_shapes_mod_eight hq hq4 hao hbo hj hk hsa hsb
    have h31 := prime_dvd_phi3_mod_three hq hq3 (x := a)
      (by rw [hsa]; exact dvd_pow_self q (by omega))
    omega
  · have h8 := phi3_both_shapes_mod_eight hq hq4 hbo hao hk hj hsb hsa
    have h31 := prime_dvd_phi3_mod_three hq hq3 (x := b)
      (by rw [hsb]; exact dvd_pow_self q (by omega))
    omega
  · exact phi3_eq_mul_prime_pow_unique hq hq4 (Or.inr rfl) hao hbo hj hk hsa hsb

/-- At most one escape row when the special prime is `1` modulo `8`. No classical input. -/
theorem card_escapeRows_le_one_of_mod_eight {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hq8 : q % 8 = 1) : (escapeRows N q).card ≤ 1 :=
  card_escapeRows_le_one h hq hodd (by omega)

/-- Unless the special prime `q` is `13` modulo `24`, `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 5`,
where `T` is the total excess. No classical input: the defect identity, the positive defect for
`q ≡ 1 (mod 3)` and at most one escape row. Whether this bound is new has not been verified. The
total excess is not bounded. -/
theorem card_primeFactors_add_two_mul_le_five_excess_add_five_of_mod_ne {N q : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hq24 : q % 24 ≠ 13) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5 := by
  have hq4 := (special_mod_four h hq hodd).1
  have hq0 : q % 3 ≠ 0 := fun h0 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp (Nat.dvd_of_mod_eq_zero h0)
    omega
  rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with hq3 | hq3
  · have hI := card_primeFactors_add_two_mul_add_defect_eq h hq hodd
    have hZ := one_le_supportDefect h hq hodd hq3
    have hH := card_escapeRows_le_one h hq hodd hq24
    omega
  · exact card_primeFactors_add_two_mul_le_five_excess_add_five h hq hodd hq3

/-- For a special prime `q ≡ 1 (mod 8)`, `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 5`, where `T` is the
total excess. No classical input. -/
theorem card_primeFactors_add_two_mul_le_five_excess_add_five_of_mod_eight {N q : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hq8 : q % 8 = 1) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5 :=
  card_primeFactors_add_two_mul_le_five_excess_add_five_of_mod_ne h hq hodd (by omega)

end OddPerfect

#print axioms OddPerfect.eisenstein_two_forms_norm_mod_eight
#print axioms OddPerfect.phi3_both_shapes_mod_eight
#print axioms OddPerfect.not_phi3_both_shapes_of_mod_eight
#print axioms OddPerfect.card_escapeRows_le_one
#print axioms OddPerfect.card_escapeRows_le_one_of_mod_eight
#print axioms OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_five_of_mod_ne
#print axioms OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_five_of_mod_eight
