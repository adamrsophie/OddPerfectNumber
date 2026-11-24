import OddPerfect.EisensteinMixed

/-!
# At most one escape row, with no classical hypothesis

Let `q` be a prime with `q ≡ 1 (mod 4)`. We work in the Eisenstein integers
`Eis = QuadraticAlgebra ℤ (-1) (-1)`, elements `a + b ω` with `ω ^ 2 = -1 - ω`, and call `z`
normalized when `4 ∣ z.re - 1` and `4 ∣ z.im`.

* Theorem 1 (`not_phi3_eq_special_pow_of_dvd`): if `phi3 x = q ^ j` with `x` odd, then `j` has
  no factor `n ≥ 2` with `3 ∤ n`. The row gives a normalized `z ≠ 1` with `(z ^ j).re = 1`; put
  `β = z ^ (j / n)` and multiply `β` by `ω ^ 2` or by `ω`. The imaginary part of an element
  divides the imaginary part of each of its powers (`eis_im_dvd_im_pow`), which forces
  `β.re = 1` or `(star β).re = 1`; both contradict the 2-adic uniqueness lemmas of
  `EisensteinLocal`. With the cube lemma for prime `x` this gives `j = 1` for odd prime `x`
  (`phi3_eq_special_pow_exponent`).
* Lemma B (`eis_one_add_mul_omega_pow_eq_one`): if `c ≠ 0`, `4 ∣ c`, `m ≥ 1` and
  `L ((1 + c ω) ^ m) = 1` for `L (a + b ω) = a - 2 b`, then `c = 4` or `c = -4`. The binomial
  expansion gives `2 m = ∑_{i ≥ 2} C(m, i) c ^ (i - 1) L (ω ^ i)`, and a comparison of
  valuations rules out an odd prime factor of `c` and the case `8 ∣ c`.
* Theorem 2 (`not_phi3_eq_special_and_three_mul_pow`): `phi3 x = q` and `phi3 x' = 3 * q ^ m`
  with odd `x`, `x'` and `m ≥ 1` do not both hold. By Lemma B the root is `1 + 4 ω` or
  `1 - 4 ω`; the second has norm `21`, the first forces `q = 13`, `m = 2` and `x' = 22`.
* Theorem 3 (`card_escapeRows_le_one_all`): an odd perfect number has at most one escape row for
  its special prime.

Hence `ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 5`, `ω(N) ≤ 5 * T + 5` and `N < 2 ^ 4 ^ (5 * T + 5)`
for every odd perfect number `N` with special prime `q` and total excess `T`. No classical
hypothesis is used. The total excess `T` is not bounded here, the odd perfect number conjecture
is open and nothing here decides it. Novelty was not verified: published bounds of Ochem and Rao
are stronger for small special exponent.
-/

open ArithmeticFunction Finset QuadraticAlgebra
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ### Normalized elements and Lemma A -/

private theorem nz_mul {x y : Eis} (hx : (4 : ℤ) ∣ x.re - 1 ∧ (4 : ℤ) ∣ x.im)
    (hy : (4 : ℤ) ∣ y.re - 1 ∧ (4 : ℤ) ∣ y.im) :
    (4 : ℤ) ∣ (x * y).re - 1 ∧ (4 : ℤ) ∣ (x * y).im := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hy
  have e1 : x.re = 4 * a + 1 := by linarith
  have e2 : y.re = 4 * c + 1 := by linarith
  rw [re_mul, im_mul, e1, e2, hb, hd]
  exact ⟨⟨a + c + 4 * a * c - 4 * b * d, by ring⟩,
    ⟨d + 4 * a * d + b + 4 * b * c - 4 * b * d, by ring⟩⟩

private theorem nz_pow {x : Eis} (hx : (4 : ℤ) ∣ x.re - 1 ∧ (4 : ℤ) ∣ x.im) (n : ℕ) :
    (4 : ℤ) ∣ (x ^ n).re - 1 ∧ (4 : ℤ) ∣ (x ^ n).im := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact nz_mul ih hx

/-- Lemma A: the imaginary part of `α` divides the imaginary part of every power of `α`. -/
theorem eis_im_dvd_im_pow (α : Eis) (n : ℕ) : α.im ∣ (α ^ n).im := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨(α ^ n).re + k * α.re - k * α.im, ?_⟩
    rw [pow_succ, im_mul, hk]; ring

/-- If `α ^ n = ω ^ 2 * u` with `u.re = 1`, then `α.im = ±1`. -/
private theorem im_unit_of_pow {α u : Eis} {n : ℕ} (hα : α ^ n = ⟨-1, -1⟩ * u)
    (hu : u.re = 1) : α.im = 1 ∨ α.im = -1 := by
  have hd := eis_im_dvd_im_pow α n
  have e : (α ^ n).im = -1 := by
    rw [hα]; simp only [im_mul, hu]; ring
  rw [e] at hd
  exact Int.isUnit_iff.mp (isUnit_of_dvd_one (dvd_neg.mp hd))

/-! ### Theorem 1 -/

/-- The core of Theorem 1, for one normalized element. -/
private theorem pow_factor_false {z : Eis} (hz : z ≠ 1) (hre : (4 : ℤ) ∣ z.re - 1)
    (him : (4 : ℤ) ∣ z.im) {n j' : ℕ} (hj' : 1 ≤ j') (hn : 2 ≤ n) (hn3 : ¬ 3 ∣ n)
    (h1 : (z ^ (n * j')).re = 1) : False := by
  have hβn : (z ^ j') ^ n = z ^ (n * j') := by rw [← pow_mul, mul_comm]
  obtain ⟨hbr, hbi⟩ := nz_pow ⟨hre, him⟩ j'
  have hω3 : (⟨0, 1⟩ : Eis) ^ 3 = 1 := by ext <;> simp [pow_succ]
  have hω2 : (⟨0, 1⟩ : Eis) ^ 2 = ⟨-1, -1⟩ := by ext <;> simp [pow_succ]
  have hjn : 1 ≤ n * j' := by nlinarith
  rcases (show n % 3 = 1 ∨ n % 3 = 2 by omega) with h3 | h3
  · have hpow : (⟨-1, -1⟩ : Eis) ^ n = ⟨-1, -1⟩ := by
      rw [← hω2, ← pow_mul, show 2 * n = 3 * (2 * (n / 3)) + 2 by omega, pow_add, pow_mul, hω3,
        one_pow, one_mul]
    have hd := im_unit_of_pow (α := (⟨-1, -1⟩ : Eis) * z ^ j') (u := z ^ (n * j'))
      (by rw [mul_pow, hpow, hβn]) h1
    have e : ((⟨-1, -1⟩ : Eis) * z ^ j').im = -(z ^ j').re := by simp only [im_mul]; ring
    rw [e] at hd
    have hb1 : (z ^ j').re = 1 := by omega
    have := eisenstein_pow_linear_eq_one_unique hz hre him 0 hj' hjn
      (by rw [zero_mul, add_zero]; exact hb1) (by rw [zero_mul, add_zero]; exact h1)
    nlinarith
  · have hpow : (⟨0, 1⟩ : Eis) ^ n = ⟨-1, -1⟩ := by
      rw [← hω2, show n = 3 * (n / 3) + 2 by omega, pow_add, pow_mul, hω3, one_pow, one_mul]
    have hd := im_unit_of_pow (α := (⟨0, 1⟩ : Eis) * z ^ j') (u := z ^ (n * j'))
      (by rw [mul_pow, hpow, hβn]) h1
    have e : ((⟨0, 1⟩ : Eis) * z ^ j').im = (z ^ j').re - (z ^ j').im := by
      simp only [im_mul]; ring
    rw [e] at hd
    have hs : ((star z) ^ j').re + 0 * ((star z) ^ j').im = 1 := by
      rw [← star_pow, re_star]; omega
    exact eisenstein_pow_linear_star_ne_one hz hre him (ℓ := 0) (ℓ' := 0) ⟨0, by norm_num⟩
      ⟨0, by norm_num⟩ hjn hj' (by rw [zero_mul, add_zero]; exact h1) hs

/-- Theorem 1. Let `q` be a prime with `q % 4 = 1` and `x` odd with `phi3 x = q ^ j`, `j ≥ 1`.
Then `j` has no factor `n ≥ 2` with `3 ∤ n`. Elementary; no classical hypothesis. -/
theorem not_phi3_eq_special_pow_of_dvd {q x j n j' : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    (hx : Odd x) (hj : 1 ≤ j) (h : phi3 x = q ^ j) (hjn : j = n * j') (hn : 2 ≤ n)
    (hn3 : ¬ 3 ∣ n) : False := by
  subst hjn
  have hj' : 1 ≤ j' := by
    rcases Nat.eq_zero_or_pos j' with h0 | h0
    · rw [h0, mul_zero] at hj; omega
    · exact h0
  obtain ⟨ρ, -, hρ1, hre, him, hrow⟩ :=
    exists_normalized_root_of_row hq hq4 ⟨x, n * j', hj, Or.inl (by rw [← h]; rfl)⟩
  have hs1 : star ρ ≠ 1 := fun e => hρ1 (by simpa using congrArg star e)
  have hsre : (4 : ℤ) ∣ (star ρ).re - 1 := by
    obtain ⟨a, ha⟩ := hre
    obtain ⟨b, hb⟩ := him
    exact ⟨a - b, by rw [QuadraticAlgebra.re_star]; linear_combination ha - hb⟩
  have hsim : (4 : ℤ) ∣ (star ρ).im := by
    obtain ⟨b, hb⟩ := him
    exact ⟨-b, by rw [QuadraticAlgebra.im_star, hb]; ring⟩
  rcases (hrow x (n * j') hx hj).1 (by rw [← h]; rfl) with a | a
  · exact pow_factor_false hρ1 hre him hj' hn hn3 a
  · exact pow_factor_false hs1 hsre hsim hj' hn hn3 a

/-- For an odd prime `x` and a prime `q` with `q % 4 = 1`, `phi3 x = q ^ j` with `j ≥ 1` forces
`j = 1`. This is Nagell's classical theorem restricted to primes `q ≡ 1 (mod 4)`, proved here
elementarily; the classical theorem (not proved in this library) covers every prime `q`. Some
hypothesis on `x` is needed: `phi3 18 = 7 ^ 3`. -/
theorem phi3_eq_special_pow_exponent {q x j : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    (hx : x.Prime) (hx2 : Odd x) (hj : 1 ≤ j) (h : phi3 x = q ^ j) : j = 1 := by
  by_contra hj1
  obtain ⟨ℓ, hℓ, j', hj'⟩ := Nat.exists_prime_and_dvd hj1
  by_cases h3 : ℓ = 3
  · subst h3
    exact phi3_ne_cube_of_prime hx (q ^ j') (by rw [h, hj', pow_mul'])
  · have hn3 : ¬ 3 ∣ ℓ := fun hd => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 hd).symm
    exact not_phi3_eq_special_pow_of_dvd hq hq4 hx2 hj h hj' hℓ.two_le hn3

/-! ### Lemma B -/

/-- Cancel the part of `F` prime to `p`: if every power `p ^ k` dividing `F` satisfies
`k + K ≤ e`, and `p ^ v ∣ F * X`, then `p ^ (v + K) ∣ p ^ e * X`. -/
private theorem pow_dvd_of_mul_prime {p : ℕ} (hp : p.Prime) {F : ℕ} (hF : F ≠ 0) {K e v : ℕ}
    (hk : ∀ k, p ^ k ∣ F → k + K ≤ e) {X : ℤ} (hX : (p : ℤ) ^ v ∣ (F : ℤ) * X) :
    (p : ℤ) ^ (v + K) ∣ (p : ℤ) ^ e * X := by
  obtain ⟨s, t, ht, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hF p hp.ne_one
  have hs := hk s (dvd_mul_right _ _)
  have hcop : IsCoprime ((p : ℤ) ^ v) (t : ℤ) := by
    have : Nat.Coprime (p ^ v) t :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 ht)
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  have h1 : (p : ℤ) ^ v ∣ (p : ℤ) ^ s * X := by
    refine hcop.dvd_of_dvd_mul_left ?_
    have : ((p ^ s * t : ℕ) : ℤ) * X = (t : ℤ) * ((p : ℤ) ^ s * X) := by push_cast; ring
    rwa [this] at hX
  have h2 : (p : ℤ) ^ (v + K) ∣ (p : ℤ) ^ (s + K) * X := by
    have : (p : ℤ) ^ (s + K) * X = (p : ℤ) ^ K * ((p : ℤ) ^ s * X) := by rw [pow_add]; ring
    rw [this, pow_add, mul_comm ((p : ℤ) ^ v)]
    exact mul_dvd_mul_left _ h1
  exact h2.trans (mul_dvd_mul_right (pow_dvd_pow _ (by omega)) X)

/-- The valuation step of Lemma B on integers. -/
private theorem sum_aux {p : ℕ} (hp : p.Prime) {c : ℤ} (hc : c ≠ 0) {d K : ℕ}
    (hd : (p : ℤ) ^ d ∣ c) (hK : ∀ i e : ℕ, p ^ e ∣ i + 2 → e + K ≤ d * (i + 1))
    (t : ℕ → ℤ) (ht0 : t 0 = 1) (ht1 : t 1 = -2) {m : ℕ} (hm : 1 ≤ m)
    (hsum : ∑ i ∈ range (m + 1), (m.choose i : ℤ) * c ^ i * t i = 1)
    {a r : ℕ} (hmr : m = p ^ a * r) : (p : ℤ) ^ K ∣ 2 * r := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, f = fun i => ((m' + 1).choose i : ℤ) * c ^ i * t i :=
    ⟨_, rfl⟩
  have hs : ∑ i ∈ range (m' + 1 + 1), f i = 1 := by rw [hf]; exact hsum
  rw [sum_range_succ', sum_range_succ'] at hs
  have e0 : f 0 = 1 := by rw [hf]; simp [ht0]
  have e1 : f (0 + 1) = ((m' + 1 : ℕ) : ℤ) * c * (-2) := by
    rw [hf]; simp only [zero_add, Nat.choose_one_right, pow_one, ht1]
  rw [e0, e1] at hs
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have htail : ∀ i ∈ range m', (p : ℤ) ^ (a + K) * c ∣ f (i + 1 + 1) := by
    intro i _
    have hN : p ^ a ∣ (i + 2) * (m' + 1).choose (i + 2) := by
      have := Nat.add_one_mul_choose_eq m' (i + 1)
      refine (show p ^ a ∣ m' + 1 from ⟨r, hmr⟩).trans ?_
      rw [mul_comm]
      exact ⟨m'.choose (i + 1), this.symm⟩
    have hZ : (p : ℤ) ^ a ∣ ((i + 2 : ℕ) : ℤ) * ((m' + 1).choose (i + 2) : ℤ) := by
      have := Int.natCast_dvd_natCast.2 hN
      push_cast at this ⊢
      exact this
    have hb := pow_dvd_of_mul_prime hp (F := i + 2) (by omega) (hK i) hZ
    have hc' : (p : ℤ) ^ (d * (i + 1)) ∣ c ^ (i + 1) := by
      rw [pow_mul]; exact pow_dvd_pow_of_dvd hd _
    have h2 : (p : ℤ) ^ (a + K) ∣ ((m' + 1).choose (i + 2) : ℤ) * c ^ (i + 1) := by
      refine hb.trans ?_
      rw [mul_comm ((p : ℤ) ^ (d * (i + 1)))]
      exact mul_dvd_mul_left _ hc'
    rw [hf]
    simp only
    rw [show i + 1 + 1 = i + 2 by ring]
    rw [show ((m' + 1).choose (i + 2) : ℤ) * c ^ (i + 2) * t (i + 2) =
      (((m' + 1).choose (i + 2) : ℤ) * c ^ (i + 1)) * (c * t (i + 2)) by ring]
    exact mul_dvd_mul h2 (dvd_mul_right c _)
  have hd2 : (p : ℤ) ^ (a + K) * c ∣ (p : ℤ) ^ a * (2 * r) * c := by
    have h1 : (p : ℤ) ^ a * (2 * r) * c = ∑ i ∈ range m', f (i + 1 + 1) := by
      have h3 : ((m' + 1 : ℕ) : ℤ) = (p : ℤ) ^ a * r := by rw [hmr]; push_cast; ring
      rw [h3] at hs; linarith
    rw [h1]; exact dvd_sum htail
  rw [pow_add] at hd2
  have h4 := (mul_dvd_mul_iff_right hc).1 hd2
  exact (mul_dvd_mul_iff_left (pow_ne_zero a hp0)).1 h4

/-- Binomial expansion of `L ((1 + c w) ^ n)` for an integer `c`. -/
private theorem eisLin_pow_expand_int (ℓ c : ℤ) (w : Eis) (n : ℕ) :
    eisLin ℓ ((1 + (c : Eis) * w) ^ n) =
      ∑ r ∈ range (n + 1), (n.choose r : ℤ) * c ^ r * eisLin ℓ (w ^ r) := by
  rw [add_comm, add_pow, map_sum]
  refine sum_congr rfl fun r _ => ?_
  have : ((c : Eis) * w) ^ r * 1 ^ (n - r) * (n.choose r : Eis)
      = ((((n.choose r : ℤ) * c ^ r : ℤ)) : Eis) * w ^ r := by
    rw [one_pow, mul_one, mul_pow, ← Int.cast_pow]
    push_cast; ring
  rw [this, eisLin_intCast_mul]

/-- Lemma B: if `c ≠ 0`, `4 ∣ c`, `m ≥ 1` and `z = 1 + c ω` has
`(z ^ m).re - 2 * (z ^ m).im = 1`, then `c = 4` or `c = -4`. -/
theorem eis_one_add_mul_omega_pow_eq_one {c : ℤ} (hc : c ≠ 0) (hc4 : (4 : ℤ) ∣ c) {m : ℕ}
    (hm : 1 ≤ m) (h : ((⟨1, c⟩ : Eis) ^ m).re - 2 * ((⟨1, c⟩ : Eis) ^ m).im = 1) :
    c = 4 ∨ c = -4 := by
  have hz : (⟨1, c⟩ : Eis) = 1 + (c : Eis) * ⟨0, 1⟩ := by ext <;> simp
  have hsum : ∑ i ∈ range (m + 1), (m.choose i : ℤ) * c ^ i *
      eisLin (-2) ((⟨0, 1⟩ : Eis) ^ i) = 1 := by
    rw [← eisLin_pow_expand_int (-2) c ⟨0, 1⟩ m, ← hz, eisLin_apply]; linarith
  have ht0 : eisLin (-2) ((⟨0, 1⟩ : Eis) ^ 0) = 1 := by rw [pow_zero, eisLin_one]
  have ht1 : eisLin (-2) ((⟨0, 1⟩ : Eis) ^ 1) = -2 := by simp [eisLin_apply]
  have run : ∀ p d K : ℕ, p.Prime → (p : ℤ) ^ d ∣ c →
      (∀ i e : ℕ, p ^ e ∣ i + 2 → e + K ≤ d * (i + 1)) → ∃ r, ¬ p ∣ r ∧ (p : ℤ) ^ K ∣ 2 * r := by
    intro p d K hp hd hK
    obtain ⟨a, r, hr, hmr⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (show m ≠ 0 by omega) p hp.ne_one
    exact ⟨r, hr, sum_aux hp hc hd hK (fun i => eisLin (-2) ((⟨0, 1⟩ : Eis) ^ i)) ht0 ht1 hm
      hsum hmr⟩
  obtain ⟨k, rfl⟩ := hc4
  by_cases h2 : (2 : ℤ) ∣ k
  · exfalso
    obtain ⟨r, hr, hdv⟩ := run 2 3 2 Nat.prime_two
      (by obtain ⟨l, rfl⟩ := h2; exact ⟨l, by push_cast; ring⟩)
      (fun i e he => by
        have h1 : e < 2 ^ e := Nat.lt_two_pow_self
        have hle := Nat.le_of_dvd (by omega) he
        omega)
    have e4 : ((2 : ℕ) : ℤ) ^ 2 = 4 := by norm_num
    rw [e4] at hdv
    omega
  · by_cases hk1 : k.natAbs = 1
    · have := Int.natAbs_eq k
      rw [hk1] at this
      omega
    · exfalso
      obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
      have hpz : (p : ℤ) ∣ k := Int.ofNat_dvd_left.2 hpk
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact h2 (by exact_mod_cast hpz)
      obtain ⟨r, hr, hdv⟩ := run p 1 1 hp (by rw [pow_one]; exact dvd_mul_of_dvd_right hpz 4)
        (fun i e he => by
          have h3 : 3 ≤ p := by have := hp.two_le; omega
          by_contra hcon
          have hle := Nat.le_of_dvd (by omega) he
          have h1 : e < 2 ^ e := Nat.lt_two_pow_self
          have h4 : 2 ^ e < p ^ e := Nat.pow_lt_pow_left (by omega) (by omega)
          omega)
      rw [pow_one] at hdv
      have hdv' : p ∣ 2 * r := by exact_mod_cast hdv
      rcases (Nat.Prime.dvd_mul hp).1 hdv' with h5 | h5
      · have := Nat.le_of_dvd (by norm_num) h5
        have := hp.two_le
        omega
      · exact hr h5

/-! ### Theorem 2 and Theorem 3 -/

/-- Theorem 2. For a prime `q` with `q % 4 = 1`, odd `x`, `x'` and `m ≥ 1`, the equations
`phi3 x = q` and `phi3 x' = 3 * q ^ m` do not both hold. Elementary; no classical hypothesis. -/
theorem not_phi3_eq_special_and_three_mul_pow {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    {x x' m : ℕ} (hx : Odd x) (hx' : Odd x') (hm : 1 ≤ m) (h1 : phi3 x = q)
    (h2 : phi3 x' = 3 * q ^ m) : False := by
  have h1' : phi3 x = q ^ 1 := by rw [pow_one]; exact h1
  obtain ⟨ρ, hρq, hρ1, hre, him, hrow⟩ :=
    exists_normalized_root_of_row hq hq4 ⟨x, 1, le_rfl, Or.inl (by rw [← h1']; rfl)⟩
  have hs1 : star ρ ≠ 1 := fun e => hρ1 (by simpa using congrArg star e)
  have hsre : (4 : ℤ) ∣ (star ρ).re - 1 := by
    obtain ⟨a, ha⟩ := hre
    obtain ⟨b, hb⟩ := him
    exact ⟨a - b, by rw [QuadraticAlgebra.re_star]; linear_combination ha - hb⟩
  have hsim : (4 : ℤ) ∣ (star ρ).im := by
    obtain ⟨b, hb⟩ := him
    exact ⟨-b, by rw [QuadraticAlgebra.im_star, hb]; ring⟩
  have key : ∀ z : Eis, Eis.nrm z = q → z ≠ 1 → (4 : ℤ) ∣ z.re - 1 → (4 : ℤ) ∣ z.im →
      (z ^ 1).re = 1 → (z ^ m).re - 2 * (z ^ m).im = 1 → False := by
    rintro ⟨a, c⟩ hzq hz1 hzr hzi ha hb
    have ha1 : a = 1 := by simpa using ha
    subst ha1
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hz1 (by ext <;> simp)
    rcases eis_one_add_mul_omega_pow_eq_one hc0 hzi hm hb with rfl | rfl
    · have hq13 : q = 13 := by
        rw [Eis.nrm_mk] at hzq
        norm_num at hzq
        omega
      have hm2 := eisenstein_pow_linear_eq_one_unique hz1 hzr hzi (-2) hm (m := 2)
        (by norm_num) (by linarith) (by norm_num [pow_two])
      subst hq13
      subst hm2
      obtain ⟨k, rfl⟩ := hx'
      unfold phi3 at h2
      have hk : k ≤ 10 := by nlinarith
      interval_cases k <;> norm_num at h2
    · rw [Eis.nrm_mk] at hzq
      have hq21 : q = 21 := by
        norm_num at hzq
        omega
      subst hq21
      norm_num at hq
  rcases (hrow x 1 hx le_rfl).1 (by rw [← h1']; rfl) with a | a <;>
    rcases (hrow x' m hx' hm).2 (by rw [← h2]; rfl) with b | b
  · exact key ρ hρq hρ1 hre him a b
  · exact eisenstein_pow_linear_star_ne_one hρ1 hre him (ℓ := 0) (ℓ' := -2) ⟨0, by norm_num⟩
      ⟨-1, by norm_num⟩ le_rfl hm (by linarith) (by linarith)
  · exact eisenstein_pow_linear_star_ne_one hs1 hsre hsim (ℓ := 0) (ℓ' := -2) ⟨0, by norm_num⟩
      ⟨-1, by norm_num⟩ le_rfl hm (by linarith) (by rw [star_star]; linarith)
  · exact key (star ρ) (by rw [Eis.nrm_star, hρq]) hs1 hsre hsim a b

/-- Theorem 3. For every odd perfect number `N` and its special prime `q` there is at most one
escape row. No classical hypothesis is used. -/
theorem card_escapeRows_le_one_all {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : (escapeRows N q).card ≤ 1 := by
  have hq4 : q % 4 = 1 := (special_mod_four h hq hodd).1
  have hprime : ∀ {p : ℕ}, p ∈ escapeRows N q → p.Prime := by
    intro p hp
    obtain ⟨hpS, -⟩ := mem_escapeRows.mp hp
    simp only [squarePrimes, Finset.mem_filter] at hpS
    exact Nat.prime_of_mem_primeFactors hpS.1
  rw [Finset.card_le_one]
  intro a ha b hb
  obtain ⟨hao, j, hj, hsa | hsa⟩ := phi3_escapeRow h ha <;>
    obtain ⟨hbo, k, hk, hsb | hsb⟩ := phi3_escapeRow h hb
  · exact phi3_eq_mul_prime_pow_unique hq hq4 (Or.inl rfl) hao hbo hj hk
      (by rw [hsa, one_mul]) (by rw [hsb, one_mul])
  · have hj1 := phi3_eq_special_pow_exponent hq hq4 (hprime ha) hao hj hsa
    subst hj1
    exact (not_phi3_eq_special_and_three_mul_pow hq hq4 hao hbo hk
      (by rw [hsa, pow_one]) hsb).elim
  · have hk1 := phi3_eq_special_pow_exponent hq hq4 (hprime hb) hbo hk hsb
    subst hk1
    exact (not_phi3_eq_special_and_three_mul_pow hq hq4 hbo hao hj
      (by rw [hsb, pow_one]) hsa).elim
  · exact phi3_eq_mul_prime_pow_unique hq hq4 (Or.inr rfl) hao hbo hj hk hsa hsb

/-! ### Corollaries -/

/-- For every odd perfect number `N` and its special prime `q`,
`ω(N) + 2 * v_3(σ(q ^ a)) ≤ 5 * T + 5`, where `T` is the total excess. No classical hypothesis is
used. The total excess is not bounded here; the odd perfect number conjecture is open and this
does not decide it. Novelty was not verified: published bounds of Ochem and Rao are stronger for
small special exponent. -/
theorem card_primeFactors_add_two_mul_le_five_excess_add_five_all {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    N.primeFactors.card + 2 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5 := by
  have hq4 := (special_mod_four h hq hodd).1
  have hq0 : q % 3 ≠ 0 := fun h0 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp (Nat.dvd_of_mod_eq_zero h0)
    omega
  rcases (show q % 3 = 1 ∨ q % 3 = 2 by omega) with hq3 | hq3
  · have hI := card_primeFactors_add_two_mul_add_defect_eq h hq hodd
    have hZ := one_le_supportDefect h hq hodd hq3
    have hH := card_escapeRows_le_one_all h hq hodd
    omega
  · exact card_primeFactors_add_two_mul_le_five_excess_add_five h hq hodd hq3

/-- For every odd perfect number `N` and its special prime `q`, `ω(N) ≤ 5 * T + 5`, where `T` is
the total excess. No classical hypothesis is used. The total excess is not bounded here; the odd
perfect number conjecture is open and this does not decide it. Novelty was not verified. -/
theorem card_primeFactors_le_five_excess_add_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N.primeFactors.card ≤
      5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5 := by
  have := card_primeFactors_add_two_mul_le_five_excess_add_five_all h hq hodd
  omega

/-- For every odd perfect number `N` and its special prime `q`, `N < 2 ^ 4 ^ (5 * T + 5)`, where
`T` is the total excess. No classical hypothesis is used. The total excess is not bounded here;
the odd perfect number conjecture is open and this does not decide it. Novelty was not
verified. -/
theorem lt_two_pow_four_pow_excess_add_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N < 2 ^ 4 ^ (5 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 5) :=
  (lt_two_pow_four_pow h).trans_le (Nat.pow_le_pow_right two_pos
    (Nat.pow_le_pow_right (by norm_num) (card_primeFactors_le_five_excess_add_five h hq hodd)))

end OddPerfect

#print axioms OddPerfect.eis_im_dvd_im_pow
#print axioms OddPerfect.not_phi3_eq_special_pow_of_dvd
#print axioms OddPerfect.phi3_eq_special_pow_exponent
#print axioms OddPerfect.eis_one_add_mul_omega_pow_eq_one
#print axioms OddPerfect.not_phi3_eq_special_and_three_mul_pow
#print axioms OddPerfect.card_escapeRows_le_one_all
#print axioms OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_five_all
#print axioms OddPerfect.card_primeFactors_le_five_excess_add_five
#print axioms OddPerfect.lt_two_pow_four_pow_excess_add_five
