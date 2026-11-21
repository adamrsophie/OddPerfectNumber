import OddPerfect.RadicalBound
import OddPerfect.ExponentCap

/-!
# Small prime factors of an odd perfect number

Let `N` be an odd perfect number with `k = ω(N)` distinct prime factors.

* A general bound for the smallest prime factor `p` outside a set `S` of `i` prime factors in
  terms of the exact component abundancy `H_S = ∏_{q ∈ S} σ(q^{e_q})/q^{e_q}`: from
  `2 = H_S * H_T` with `T` the remaining prime factors and the telescoped bound
  `H_T < 1 + (k - i)/(p - 1)` one gets `2 (p - 1) < H_S (p - 1 + k - i)`
  (`two_mul_sub_one_lt`). With the odd step telescoping, `4 (p - 2) < H_S² (p - 2 + 2 (k - i))`
  (`four_mul_sub_two_lt`). Cap versions with `H_S ≤ a/b` are stated in `ℕ`; integrality
  (`H_S = σ(D)/D`) gives `p ≤ σ(D) (k - i)`. Corollaries: improved bounds for the second, third
  and fourth smallest prime factors, and bounds for the fifth and sixth in terms of the fourth
  and fifth.
* An exchange lemma: a set of `k` integers `≥ 2` that dominate `T` outside `T` has
  `∏ s/(s-1)` at most `∏_{t ∈ T} t/(t-1)` when `|S| ≤ |T|`. With `T` the primes in an interval,
  computed by the kernel, this gives the least `ω(N)` for each lower bound on the smallest prime
  factor: `7, 15, 27, 41, 62, 85, 115` for `5, 7, 11, 13, 17, 19, 23`.
* When `3 ∤ N`: `ω(N) ≥ 8`, by excluding the four supports with seven prime factors whose
  `∏ p/(p-1)` exceeds two, using the exponent restrictions coming from `3 ∤ N`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N : ℕ}

/-! ## Helpers -/

private theorem abund_one_le {p : ℕ} (hp : p.Prime) (e : ℕ) : 1 ≤ abundancy (p ^ e) := by
  have := abundancy_le_of_dvd (pow_ne_zero e hp.ne_zero) (one_dvd (p ^ e))
  simpa [abundancy] using this

private theorem abund_pos {p : ℕ} (hp : p.Prime) (e : ℕ) : 0 < abundancy (p ^ e) :=
  zero_lt_one.trans_le (abund_one_le hp e)

private theorem g_one_le {x : ℕ} (hx : 2 ≤ x) : (1 : ℚ) ≤ (x : ℚ) / (x - 1) := by
  have hx' : (2 : ℚ) ≤ x := by exact_mod_cast hx
  rw [le_div_iff₀ (by linarith)]; linarith

private theorem g_anti {m x : ℕ} (hm : 2 ≤ m) (hx : m ≤ x) :
    (x : ℚ) / (x - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hx' : (m : ℚ) ≤ x := by exact_mod_cast hx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private theorem odd_mem {p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) : Odd p :=
  (Nat.prime_of_mem_primeFactors hp).odd_of_ne_two fun h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)

private theorem three_le_mem {p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) : 3 ≤ p := by
  have := (Nat.prime_of_mem_primeFactors hp).two_le
  obtain ⟨j, rfl⟩ := odd_mem h hp; omega

/-! ## The general bound -/

/-- For a perfect `N` and a set `S` of prime factors, the component abundancies over `S` and
over the remaining prime factors multiply to two. -/
theorem prod_mul_prod_sdiff_eq_two (hN : N.Perfect) {S : Finset ℕ} (hS : S ⊆ N.primeFactors) :
    (∏ q ∈ S, abundancy (q ^ N.factorization q)) *
      ∏ q ∈ N.primeFactors \ S, abundancy (q ^ N.factorization q) = 2 := by
  rw [mul_comm, Finset.prod_sdiff hS, ← abundancy_eq_prod_primeFactors hN.2.ne',
    (perfect_iff_abundancy_eq_two hN.2).mp hN]

/-- The components outside a proper subset contribute more than one. -/
private theorem one_lt_prod_sdiff (hN : N.Perfect) {S : Finset ℕ} {p : ℕ}
    (hp : p ∈ N.primeFactors) (hpS : p ∉ S) :
    1 < ∏ q ∈ N.primeFactors \ S, abundancy (q ^ N.factorization q) := by
  have h := Finset.prod_lt_prod_of_nonempty (s := N.primeFactors \ S) (f := fun _ => (1 : ℚ))
    (g := fun q => abundancy (q ^ N.factorization q)) (fun _ _ => zero_lt_one)
    (fun q hq => by
      have hqN := (Finset.mem_sdiff.mp hq).1
      have hq' := Nat.prime_of_mem_primeFactors hqN
      have h1 := one_add_inv_le_abundancy_prime_pow hq'
        (hq'.factorization_pos_of_dvd hN.2.ne' (Nat.dvd_of_mem_primeFactors hqN))
      have : (0 : ℚ) < (q : ℚ)⁻¹ := by have := hq'.pos; positivity
      linarith)
    ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpS⟩⟩
  simpa using h

/-- For a perfect `N` and a set `S` of prime factors missing at least one prime factor, the
component abundancy `H_S = ∏_{q ∈ S} σ(q^{e_q})/q^{e_q}` is below two. -/
theorem prod_abundancy_lt_two (hN : N.Perfect) {S : Finset ℕ} (hS : S ⊆ N.primeFactors) {p : ℕ}
    (hp : p ∈ N.primeFactors) (hpS : p ∉ S) :
    ∏ q ∈ S, abundancy (q ^ N.factorization q) < 2 := by
  have h1 := one_lt_prod_sdiff hN hp hpS
  have h2 := prod_mul_prod_sdiff_eq_two hN hS
  have h0 : 0 < ∏ q ∈ S, abundancy (q ^ N.factorization q) :=
    Finset.prod_pos fun q hq => abund_pos (Nat.prime_of_mem_primeFactors (hS hq)) _
  nlinarith

/-- Conversely, if `H_S < 2` for a set `S` of prime factors of a perfect `N`, then some prime
factor lies outside `S`, and there is a least one. -/
theorem exists_min_not_mem_of_prod_lt_two (hN : N.Perfect) {S : Finset ℕ}
    (hlt : ∏ q ∈ S, abundancy (q ^ N.factorization q) < 2) :
    ∃ p ∈ N.primeFactors, p ∉ S ∧ ∀ r ∈ N.primeFactors, r ∉ S → p ≤ r := by
  have hne : (N.primeFactors \ S).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hsub : N.primeFactors ⊆ S := Finset.sdiff_eq_empty_iff_subset.mp he
    have := prod_mul_prod_sdiff_eq_two hN (S := N.primeFactors) subset_rfl
    rw [Finset.sdiff_self, Finset.prod_empty, mul_one] at this
    have hle : ∏ q ∈ N.primeFactors, abundancy (q ^ N.factorization q) ≤
        ∏ q ∈ S, abundancy (q ^ N.factorization q) := by
      apply Finset.prod_le_prod_of_subset_of_one_le hsub
      · intro q hq; exact (abund_pos (Nat.prime_of_mem_primeFactors hq) _).le
      · intro q hq hqN
        by_cases hq' : q.Prime
        · exact abund_one_le hq' _
        · rw [Nat.factorization_eq_zero_of_not_prime N hq']; simp [abundancy]
    linarith
  set p := (N.primeFactors \ S).min' hne
  have hp := Finset.min'_mem _ hne
  refine ⟨p, (Finset.mem_sdiff.mp hp).1, (Finset.mem_sdiff.mp hp).2, fun r hr hrS => ?_⟩
  exact Finset.min'_le _ _ (Finset.mem_sdiff.mpr ⟨hr, hrS⟩)

/-- **General bound.** Let `N` be perfect, `S` a set of prime factors, and `p` the least prime
factor outside `S`. With `H_S = ∏_{q ∈ S} σ(q^{e_q})/q^{e_q}` and `k = ω(N)`,
`2 (p - 1) < H_S (p - 1 + (k - |S|))`, that is `p - 1 < H_S/(2 - H_S) * (k - |S|)`. -/
theorem two_mul_sub_one_lt (hN : N.Perfect) {S : Finset ℕ} (hS : S ⊆ N.primeFactors) {p : ℕ}
    (hp : p ∈ N.primeFactors) (hpS : p ∉ S) (hmin : ∀ r ∈ N.primeFactors, r ∉ S → p ≤ r) :
    2 * ((p : ℚ) - 1) < (∏ q ∈ S, abundancy (q ^ N.factorization q)) *
      ((p : ℚ) - 1 + ((N.primeFactors.card - S.card : ℕ) : ℚ)) := by
  set H := ∏ q ∈ S, abundancy (q ^ N.factorization q)
  set T := N.primeFactors \ S
  set m := N.primeFactors.card - S.card
  have hpT : p ∈ T := Finset.mem_sdiff.mpr ⟨hp, hpS⟩
  have hTpf : ∀ r ∈ T, r ∈ N.primeFactors := fun r hr => (Finset.mem_sdiff.mp hr).1
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  have hcard : T.card = m := Finset.card_sdiff_of_subset hS
  have hsplit := prod_mul_prod_sdiff_eq_two hN hS
  have hG : ∏ q ∈ T, abundancy (q ^ N.factorization q) < ∏ q ∈ T, (q : ℚ) / (q - 1) :=
    Finset.prod_lt_prod_of_nonempty
      (fun q hq => abund_pos (Nat.prime_of_mem_primeFactors (hTpf q hq)) _)
      (fun q hq => abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors (hTpf q hq)) _)
      ⟨p, hpT⟩
  have hTel := prod_div_sub_one_le T hp2
    (fun r hr => hmin r (hTpf r hr) (Finset.mem_sdiff.mp hr).2)
  rw [hcard] at hTel
  have hH : 0 < H := Finset.prod_pos fun q hq => abund_pos (Nat.prime_of_mem_primeFactors (hS hq)) _
  have hp1 : (0 : ℚ) < p - 1 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp2
    linarith
  have h2 : 2 < H * (1 + (m : ℚ) / (p - 1)) := by
    calc (2 : ℚ) = H * ∏ q ∈ T, abundancy (q ^ N.factorization q) := hsplit.symm
      _ < H * ∏ q ∈ T, (q : ℚ) / (q - 1) := mul_lt_mul_of_pos_left hG hH
      _ ≤ _ := mul_le_mul_of_nonneg_left hTel hH.le
  have e : H * (1 + (m : ℚ) / (p - 1)) * (p - 1) = H * (p - 1 + m) := by
    field_simp
  have := mul_lt_mul_of_pos_right h2 hp1
  rw [e] at this
  linarith

/-- **General bound, odd step.** For an odd perfect `N`, a set `S` of prime factors and the
least prime factor `p` outside `S`: `4 (p - 2) < H_S² (p - 2 + 2 (k - |S|))`, from the
telescoped product over `p, p + 2, p + 4, …`. -/
theorem four_mul_sub_two_lt (h : OddPerfect N) {S : Finset ℕ} (hS : S ⊆ N.primeFactors) {p : ℕ}
    (hp : p ∈ N.primeFactors) (hpS : p ∉ S) (hmin : ∀ r ∈ N.primeFactors, r ∉ S → p ≤ r) :
    4 * ((p : ℚ) - 2) < (∏ q ∈ S, abundancy (q ^ N.factorization q)) ^ 2 *
      ((p : ℚ) - 2 + 2 * ((N.primeFactors.card - S.card : ℕ) : ℚ)) := by
  set H := ∏ q ∈ S, abundancy (q ^ N.factorization q)
  set T := N.primeFactors \ S
  set m := N.primeFactors.card - S.card
  have hpT : p ∈ T := Finset.mem_sdiff.mpr ⟨hp, hpS⟩
  have hTpf : ∀ r ∈ T, r ∈ N.primeFactors := fun r hr => (Finset.mem_sdiff.mp hr).1
  have hp3 := three_le_mem h hp
  have hcard : T.card = m := Finset.card_sdiff_of_subset hS
  have hsplit := prod_mul_prod_sdiff_eq_two h.perfect hS
  have hG : ∏ q ∈ T, abundancy (q ^ N.factorization q) < ∏ q ∈ T, (q : ℚ) / (q - 1) :=
    Finset.prod_lt_prod_of_nonempty
      (fun q hq => abund_pos (Nat.prime_of_mem_primeFactors (hTpf q hq)) _)
      (fun q hq => abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors (hTpf q hq)) _)
      ⟨p, hpT⟩
  have hTel := sq_prod_div_sub_one_le T hp3
    (fun r hr => ⟨hmin r (hTpf r hr) (Finset.mem_sdiff.mp hr).2, odd_mem h (hTpf r hr)⟩)
  rw [hcard] at hTel
  have hH : 0 < H := Finset.prod_pos fun q hq => abund_pos (Nat.prime_of_mem_primeFactors (hS hq)) _
  have hp1 : (0 : ℚ) < p - 2 := by
    have : (3 : ℚ) ≤ p := by exact_mod_cast hp3
    linarith
  have hG0 : 0 ≤ ∏ q ∈ T, abundancy (q ^ N.factorization q) :=
    Finset.prod_nonneg fun q hq => (abund_pos (Nat.prime_of_mem_primeFactors (hTpf q hq)) _).le
  have h2 : 2 < H * ∏ q ∈ T, (q : ℚ) / (q - 1) := by
    calc (2 : ℚ) = H * ∏ q ∈ T, abundancy (q ^ N.factorization q) := hsplit.symm
      _ < _ := mul_lt_mul_of_pos_left hG hH
  have h4 : 4 < H ^ 2 * (1 + 2 * (m : ℚ) / (p - 2)) := by
    have hP0 : 0 ≤ H * ∏ q ∈ T, (q : ℚ) / (q - 1) := by linarith
    calc (4 : ℚ) < (H * ∏ q ∈ T, (q : ℚ) / (q - 1)) ^ 2 := by nlinarith
      _ = H ^ 2 * (∏ q ∈ T, (q : ℚ) / (q - 1)) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hTel (by positivity)
  have e : H ^ 2 * (1 + 2 * (m : ℚ) / (p - 2)) * (p - 2) = H ^ 2 * (p - 2 + 2 * m) := by
    field_simp
  have := mul_lt_mul_of_pos_right h4 hp1
  rw [e] at this
  linarith

/-- **Cap form in `ℕ`.** If `H_S ≤ a/b` with `b > 0`, then `2 b (p - 1) < a (p - 1 + (k - |S|))`.
For `a < 2 b` this says `p - 1 < a (k - |S|)/(2 b - a)`. -/
theorem two_mul_mul_sub_one_lt_of_le (hN : N.Perfect) {S : Finset ℕ} (hS : S ⊆ N.primeFactors)
    {p : ℕ} (hp : p ∈ N.primeFactors) (hpS : p ∉ S)
    (hmin : ∀ r ∈ N.primeFactors, r ∉ S → p ≤ r) {a b : ℕ} (hb : 0 < b)
    (hH : ∏ q ∈ S, abundancy (q ^ N.factorization q) ≤ (a : ℚ) / b) :
    2 * b * (p - 1) < a * (p - 1 + (N.primeFactors.card - S.card)) := by
  have key := two_mul_sub_one_lt hN hS hp hpS hmin
  set m := N.primeFactors.card - S.card
  have hp1 := (Nat.prime_of_mem_primeFactors hp).one_le
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hx : (0 : ℚ) ≤ (p : ℚ) - 1 + m := by
    have : (1 : ℚ) ≤ p := by exact_mod_cast hp1
    have : (0 : ℚ) ≤ m := by positivity
    linarith
  have h1 : 2 * ((p : ℚ) - 1) < (a : ℚ) / b * ((p : ℚ) - 1 + m) :=
    key.trans_le (mul_le_mul_of_nonneg_right hH hx)
  have h2 : 2 * (b : ℚ) * ((p : ℚ) - 1) < a * ((p : ℚ) - 1 + m) := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hb'] at h1
    linarith
  have : ((2 * b * (p - 1) : ℕ) : ℚ) < ((a * (p - 1 + m) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub hp1]
    linarith
  exact_mod_cast this

/-- **Cap form, odd step, in `ℕ`.** For an odd perfect `N`, if `H_S ≤ a/b` with `b > 0`, then
`4 b² (p - 2) < a² (p - 2 + 2 (k - |S|))`. -/
theorem four_mul_sq_mul_sub_two_lt_of_le (h : OddPerfect N) {S : Finset ℕ}
    (hS : S ⊆ N.primeFactors) {p : ℕ} (hp : p ∈ N.primeFactors) (hpS : p ∉ S)
    (hmin : ∀ r ∈ N.primeFactors, r ∉ S → p ≤ r) {a b : ℕ} (hb : 0 < b)
    (hH : ∏ q ∈ S, abundancy (q ^ N.factorization q) ≤ (a : ℚ) / b) :
    4 * b ^ 2 * (p - 2) < a ^ 2 * (p - 2 + 2 * (N.primeFactors.card - S.card)) := by
  have key := four_mul_sub_two_lt h hS hp hpS hmin
  set m := N.primeFactors.card - S.card
  have hp3 := three_le_mem h hp
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hH0 : 0 ≤ ∏ q ∈ S, abundancy (q ^ N.factorization q) :=
    Finset.prod_nonneg fun q hq => (abund_pos (Nat.prime_of_mem_primeFactors (hS hq)) _).le
  have hx : (0 : ℚ) ≤ (p : ℚ) - 2 + 2 * m := by
    have : (3 : ℚ) ≤ p := by exact_mod_cast hp3
    have : (0 : ℚ) ≤ m := by positivity
    linarith
  have hsq : (∏ q ∈ S, abundancy (q ^ N.factorization q)) ^ 2 ≤ ((a : ℚ) / b) ^ 2 :=
    pow_le_pow_left₀ hH0 hH 2
  have h1 : 4 * ((p : ℚ) - 2) < ((a : ℚ) / b) ^ 2 * ((p : ℚ) - 2 + 2 * m) :=
    key.trans_le (mul_le_mul_of_nonneg_right hsq hx)
  have h2 : 4 * (b : ℚ) ^ 2 * ((p : ℚ) - 2) < (a : ℚ) ^ 2 * ((p : ℚ) - 2 + 2 * m) := by
    rw [div_pow, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)] at h1
    linarith
  have : ((4 * b ^ 2 * (p - 2) : ℕ) : ℚ) < ((a ^ 2 * (p - 2 + 2 * m) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub (show 2 ≤ p by omega)]
    linarith
  exact_mod_cast this

/-- **Integrality form.** For a perfect `N`, a set `S` of prime factors and the least prime
factor `p` outside `S`: `p ≤ (∏_{q ∈ S} σ(q^{e_q})) (k - |S|)`. Here `H_S = σ(D)/D` with
`D = ∏_{q ∈ S} q^{e_q}`, and `H_S < 2` forces `2 D - σ(D) ≥ 1`. -/
theorem le_prod_sigma_mul (hN : N.Perfect) {S : Finset ℕ} (hS : S ⊆ N.primeFactors) {p : ℕ}
    (hp : p ∈ N.primeFactors) (hpS : p ∉ S) (hmin : ∀ r ∈ N.primeFactors, r ∉ S → p ≤ r) :
    p ≤ (∏ q ∈ S, σ 1 (q ^ N.factorization q)) * (N.primeFactors.card - S.card) := by
  set A := ∏ q ∈ S, σ 1 (q ^ N.factorization q)
  set D := ∏ q ∈ S, q ^ N.factorization q
  have hD : 0 < D := Finset.prod_pos fun q hq =>
    pow_pos (Nat.prime_of_mem_primeFactors (hS hq)).pos _
  have hHe : ∏ q ∈ S, abundancy (q ^ N.factorization q) = (A : ℚ) / D := by
    simp only [abundancy, A, D, Nat.cast_prod, Finset.prod_div_distrib]
  have hcap := two_mul_mul_sub_one_lt_of_le hN hS hp hpS hmin hD hHe.le
  have hlt := prod_abundancy_lt_two hN hS hp hpS
  rw [hHe, div_lt_iff₀ (by exact_mod_cast hD)] at hlt
  have hA : A + 1 ≤ 2 * D := by
    have : A < 2 * D := by exact_mod_cast (by linarith : (A : ℚ) < 2 * D)
    omega
  have h1 := Nat.mul_le_mul_right (p - 1) hA
  have hp1 := (Nat.prime_of_mem_primeFactors hp).one_le
  have : p - 1 < A * (N.primeFactors.card - S.card) := by nlinarith
  omega

/-! ## Corollaries for the second to sixth smallest prime factors -/

private theorem mem_pair {r a b : ℕ} : r ∉ ({a, b} : Finset ℕ) ↔ r ≠ a ∧ r ≠ b := by simp

/-- Second smallest prime factor, odd step form: if `q < p` are prime factors of an odd perfect
`N` and every prime factor other than `q` is at least `p`, then `7 (p - 2) < 18 (ω(N) - 1)`.
This improves `second_prime_le` (`p ≤ 3 ω - 3`) and implies it. -/
theorem seven_mul_second_prime_lt {p q : ℕ} (h : OddPerfect N) (hq : q ∈ N.primeFactors)
    (hp : p ∈ N.primeFactors) (hqp : q < p) (hmin : ∀ r ∈ N.primeFactors, r ≠ q → p ≤ r) :
    7 * (p - 2) < 18 * (N.primeFactors.card - 1) := by
  have hq3 := three_le_mem h hq
  have hH : ∏ x ∈ ({q} : Finset ℕ), abundancy (x ^ N.factorization x) ≤ ((3 : ℕ) : ℚ) / (2 : ℕ) := by
    rw [Finset.prod_singleton]
    have := (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors hq) (N.factorization q)).le.trans
      (g_anti (m := 3) (by norm_num) hq3)
    norm_num at this ⊢; exact this
  have key := four_mul_sq_mul_sub_two_lt_of_le h (S := {q}) (by simpa using hq) hp
    (by simp; omega) (fun r hr hrS => hmin r hr (by simpa using hrS)) (by norm_num) hH
  rw [Finset.card_singleton] at key
  have hp3 := three_le_mem h hp
  omega

/-- Third smallest prime factor, odd step form: if `q₁ < q₂ < p` are prime factors of an odd
perfect `N` and every prime factor other than `q₁, q₂` is at least `p`, then
`31 (p - 2) < 450 (ω(N) - 2)` (compare `third_prime_le`: `p ≤ 15 ω - 30`). -/
theorem thirtyOne_mul_third_prime_lt {p q₁ q₂ : ℕ} (h : OddPerfect N) (hq₁ : q₁ ∈ N.primeFactors)
    (hq₂ : q₂ ∈ N.primeFactors) (hp : p ∈ N.primeFactors) (h12 : q₁ < q₂) (h2p : q₂ < p)
    (hmin : ∀ r ∈ N.primeFactors, r ≠ q₁ → r ≠ q₂ → p ≤ r) :
    31 * (p - 2) < 450 * (N.primeFactors.card - 2) := by
  have hq₁3 := three_le_mem h hq₁
  have hq₂5 : 5 ≤ q₂ := by obtain ⟨j, rfl⟩ := odd_mem h hq₂; omega
  have hH : ∏ x ∈ ({q₁, q₂} : Finset ℕ), abundancy (x ^ N.factorization x) ≤
      ((15 : ℕ) : ℚ) / (8 : ℕ) := by
    rw [Finset.prod_pair h12.ne]
    have a := (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors hq₁)
      (N.factorization q₁)).le.trans (g_anti (m := 3) (by norm_num) hq₁3)
    have b := (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors hq₂)
      (N.factorization q₂)).le.trans (g_anti (m := 5) (by norm_num) hq₂5)
    have b0 := abund_pos (Nat.prime_of_mem_primeFactors hq₂) (N.factorization q₂)
    norm_num at a b ⊢
    nlinarith
  have hsub : ({q₁, q₂} : Finset ℕ) ⊆ N.primeFactors := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have key := four_mul_sq_mul_sub_two_lt_of_le h hsub hp (by simp; omega)
    (fun r hr hrS => by rw [mem_pair] at hrS; exact hmin r hr hrS.1 hrS.2) (by norm_num) hH
  rw [Finset.card_pair h12.ne] at key
  have hp3 := three_le_mem h hp
  omega

private theorem prod_triple {q₁ q₂ q₃ : ℕ} (f : ℕ → ℚ) (h12 : q₁ < q₂) (h23 : q₂ < q₃) :
    ∏ x ∈ ({q₁, q₂, q₃} : Finset ℕ), f x = f q₁ * f q₂ * f q₃ := by
  rw [Finset.prod_insert (by simp; omega), Finset.prod_pair h23.ne, mul_assoc]

private theorem sub_triple {q₁ q₂ q₃ : ℕ} (hq₁ : q₁ ∈ N.primeFactors) (hq₂ : q₂ ∈ N.primeFactors)
    (hq₃ : q₃ ∈ N.primeFactors) : ({q₁, q₂, q₃} : Finset ℕ) ⊆ N.primeFactors := by
  intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

/-- Fourth smallest prime factor, odd step form: if `q₁ < q₂ < q₃ < p` are prime factors of an
odd perfect `N` and every prime factor other than `q₁, q₂, q₃` is at least `p`, then
`511 (p - 2) < 130050 (ω(N) - 3)`, from the cap `255/128` (compare `fourth_prime_le`:
`p ≤ 255 ω - 765`; the new bound is better for `ω ≥ 6`). -/
theorem fiveHundredEleven_mul_fourth_prime_lt {p q₁ q₂ q₃ : ℕ} (h : OddPerfect N)
    (hq₁ : q₁ ∈ N.primeFactors) (hq₂ : q₂ ∈ N.primeFactors) (hq₃ : q₃ ∈ N.primeFactors)
    (hp : p ∈ N.primeFactors) (h12 : q₁ < q₂) (h23 : q₂ < q₃) (h3p : q₃ < p)
    (hmin : ∀ r ∈ N.primeFactors, r ≠ q₁ → r ≠ q₂ → r ≠ q₃ → p ≤ r) :
    511 * (p - 2) < 130050 * (N.primeFactors.card - 3) := by
  have hH : ∏ x ∈ ({q₁, q₂, q₃} : Finset ℕ), abundancy (x ^ N.factorization x) ≤
      ((255 : ℕ) : ℚ) / (128 : ℕ) := by
    rw [prod_triple _ h12 h23]
    have := abundancy_three_components_lt h hq₁ hq₂ hq₃ h12 h23
    norm_num; exact this.le
  have key := four_mul_sq_mul_sub_two_lt_of_le h (sub_triple hq₁ hq₂ hq₃) hp
    (by simp; omega) (fun r hr hrS => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrS
      exact hmin r hr hrS.1 hrS.2.1 hrS.2.2) (by norm_num) hH
  rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair h23.ne] at key
  have hp3 := three_le_mem h hp
  omega

/-- Fifth smallest prime factor: if `q₁ < q₂ < q₃ < q₄ < p` are prime factors of an odd perfect
`N` and every prime factor other than the `qᵢ` is at least `p`, then
`256 (q₄ - 1)(p - 1) < 255 q₄ (p - 1 + ω(N) - 4)`, from `H < (255/128) q₄/(q₄ - 1)`.
For `q₄ ≥ 257` this reads `(p - 1)(q₄ - 256) < 255 q₄ (ω(N) - 4)`. -/
theorem fifth_prime_bound {p q₁ q₂ q₃ q₄ : ℕ} (h : OddPerfect N)
    (hq₁ : q₁ ∈ N.primeFactors) (hq₂ : q₂ ∈ N.primeFactors) (hq₃ : q₃ ∈ N.primeFactors)
    (hq₄ : q₄ ∈ N.primeFactors) (hp : p ∈ N.primeFactors)
    (h12 : q₁ < q₂) (h23 : q₂ < q₃) (h34 : q₃ < q₄) (h4p : q₄ < p)
    (hmin : ∀ r ∈ N.primeFactors, r ≠ q₁ → r ≠ q₂ → r ≠ q₃ → r ≠ q₄ → p ≤ r) :
    2 * (128 * (q₄ - 1)) * (p - 1) < 255 * q₄ * (p - 1 + (N.primeFactors.card - 4)) := by
  have hq₄p := Nat.prime_of_mem_primeFactors hq₄
  have hq₄2 := hq₄p.two_le
  have hS : ({q₁, q₂, q₃, q₄} : Finset ℕ) ⊆ N.primeFactors := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hH : ∏ x ∈ ({q₁, q₂, q₃, q₄} : Finset ℕ), abundancy (x ^ N.factorization x) ≤
      ((255 * q₄ : ℕ) : ℚ) / ((128 * (q₄ - 1) : ℕ) : ℚ) := by
    rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_pair h34.ne]
    have A := abundancy_three_components_lt h hq₁ hq₂ hq₃ h12 h23
    have B := (abundancy_prime_pow_lt hq₄p (N.factorization q₄)).le
    have B0 := abund_pos hq₄p (N.factorization q₄)
    have A0 := mul_pos (mul_pos (abund_pos (Nat.prime_of_mem_primeFactors hq₁) (N.factorization q₁))
      (abund_pos (Nat.prime_of_mem_primeFactors hq₂) (N.factorization q₂)))
      (abund_pos (Nat.prime_of_mem_primeFactors hq₃) (N.factorization q₃))
    have e : ((255 * q₄ : ℕ) : ℚ) / ((128 * (q₄ - 1) : ℕ) : ℚ) =
        255 / 128 * ((q₄ : ℚ) / (q₄ - 1)) := by
      push_cast [Nat.cast_sub (show 1 ≤ q₄ by omega)]
      have : (q₄ : ℚ) - 1 ≠ 0 := by
        have : (2 : ℚ) ≤ q₄ := by exact_mod_cast hq₄2
        linarith
      field_simp
    rw [e, ← mul_assoc, ← mul_assoc]
    calc _ ≤ (255 / 128 : ℚ) * abundancy (q₄ ^ N.factorization q₄) :=
          mul_le_mul_of_nonneg_right A.le B0.le
      _ ≤ _ := mul_le_mul_of_nonneg_left B (by norm_num)
  have key := two_mul_mul_sub_one_lt_of_le h.perfect hS hp (by simp; omega)
    (fun r hr hrS => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrS
      exact hmin r hr hrS.1 hrS.2.1 hrS.2.2.1 hrS.2.2.2) (by omega) hH
  rwa [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega),
    Finset.card_pair h34.ne] at key

/-- Sixth smallest prime factor: if `q₁ < q₂ < q₃ < q₄ < q₅ < p` are prime factors of an odd
perfect `N` and every prime factor other than the `qᵢ` is at least `p`, then
`256 (q₄ - 1)(q₅ - 1)(p - 1) < 255 q₄ q₅ (p - 1 + ω(N) - 5)`, from
`H < (255/128) (q₄/(q₄ - 1)) (q₅/(q₅ - 1))`. -/
theorem sixth_prime_bound {p q₁ q₂ q₃ q₄ q₅ : ℕ} (h : OddPerfect N)
    (hq₁ : q₁ ∈ N.primeFactors) (hq₂ : q₂ ∈ N.primeFactors) (hq₃ : q₃ ∈ N.primeFactors)
    (hq₄ : q₄ ∈ N.primeFactors) (hq₅ : q₅ ∈ N.primeFactors) (hp : p ∈ N.primeFactors)
    (h12 : q₁ < q₂) (h23 : q₂ < q₃) (h34 : q₃ < q₄) (h45 : q₄ < q₅) (h5p : q₅ < p)
    (hmin : ∀ r ∈ N.primeFactors, r ≠ q₁ → r ≠ q₂ → r ≠ q₃ → r ≠ q₄ → r ≠ q₅ → p ≤ r) :
    2 * (128 * (q₄ - 1) * (q₅ - 1)) * (p - 1) <
      255 * q₄ * q₅ * (p - 1 + (N.primeFactors.card - 5)) := by
  have hq₄p := Nat.prime_of_mem_primeFactors hq₄
  have hq₅p := Nat.prime_of_mem_primeFactors hq₅
  have hq₄2 := hq₄p.two_le
  have hq₅2 := hq₅p.two_le
  have hS : ({q₁, q₂, q₃, q₄, q₅} : Finset ℕ) ⊆ N.primeFactors := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hH : ∏ x ∈ ({q₁, q₂, q₃, q₄, q₅} : Finset ℕ), abundancy (x ^ N.factorization x) ≤
      ((255 * q₄ * q₅ : ℕ) : ℚ) / ((128 * (q₄ - 1) * (q₅ - 1) : ℕ) : ℚ) := by
    rw [Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_insert (by simp; omega), Finset.prod_pair h45.ne]
    have A := abundancy_three_components_lt h hq₁ hq₂ hq₃ h12 h23
    have B := (abundancy_prime_pow_lt hq₄p (N.factorization q₄)).le
    have C := (abundancy_prime_pow_lt hq₅p (N.factorization q₅)).le
    have B0 := abund_pos hq₄p (N.factorization q₄)
    have C0 := abund_pos hq₅p (N.factorization q₅)
    have hq4' : (2 : ℚ) ≤ q₄ := by exact_mod_cast hq₄2
    have hq5' : (2 : ℚ) ≤ q₅ := by exact_mod_cast hq₅2
    have e : ((255 * q₄ * q₅ : ℕ) : ℚ) / ((128 * (q₄ - 1) * (q₅ - 1) : ℕ) : ℚ) =
        255 / 128 * ((q₄ : ℚ) / (q₄ - 1)) * ((q₅ : ℚ) / (q₅ - 1)) := by
      push_cast [Nat.cast_sub (show 1 ≤ q₄ by omega), Nat.cast_sub (show 1 ≤ q₅ by omega)]
      have : (q₄ : ℚ) - 1 ≠ 0 := by linarith
      have : (q₅ : ℚ) - 1 ≠ 0 := by linarith
      field_simp
    rw [e, ← mul_assoc, ← mul_assoc, ← mul_assoc]
    have hf4 : (0 : ℚ) ≤ (q₄ : ℚ) / (q₄ - 1) := div_nonneg (by linarith) (by linarith)
    calc _ ≤ (255 / 128 : ℚ) * abundancy (q₄ ^ N.factorization q₄) *
          abundancy (q₅ ^ N.factorization q₅) := by gcongr
      _ ≤ (255 / 128 : ℚ) * ((q₄ : ℚ) / (q₄ - 1)) * abundancy (q₅ ^ N.factorization q₅) := by
          gcongr
      _ ≤ _ := by gcongr
  have key := two_mul_mul_sub_one_lt_of_le h.perfect hS hp (by simp; omega)
    (fun r hr hrS => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrS
      exact hmin r hr hrS.1 hrS.2.1 hrS.2.2.1 hrS.2.2.2.1 hrS.2.2.2.2)
    (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)) hH
  rwa [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega),
    Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair h45.ne] at key

/-! ## The exchange lemma -/

/-- **Exchange lemma.** Let `S, T` be finite sets of integers `≥ 2` with `|S| ≤ |T|`, such that
every element of `S` outside `T` is at least every element of `T`. Then
`∏_{s ∈ S} s/(s-1) ≤ ∏_{t ∈ T} t/(t-1)`. For primes: a set of `k` primes all `≥ m` has product of
`p/(p-1)` at most that of the first `k` primes `≥ m`. -/
theorem prod_div_sub_one_le_of_exchange {S T : Finset ℕ} (hS : ∀ s ∈ S, 2 ≤ s)
    (hT : ∀ t ∈ T, 2 ≤ t) (hST : ∀ s ∈ S, s ∉ T → ∀ t ∈ T, t ≤ s) (hcard : S.card ≤ T.card) :
    ∏ s ∈ S, (s : ℚ) / (s - 1) ≤ ∏ t ∈ T, (t : ℚ) / (t - 1) := by
  classical
  set f : ℕ → ℚ := fun x => (x : ℚ) / (x - 1) with hf
  have hsz : (S \ T).card ≤ (T \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S T
    have h2 := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm] at h2
    omega
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hsz
  have hfS : ∀ s ∈ S, 0 ≤ f s := fun s hs => zero_le_one.trans (g_one_le (hS s hs))
  have hRT : ∀ r ∈ R, r ∈ T := fun r hr => (Finset.mem_sdiff.mp (hRsub hr)).1
  have key : ∏ s ∈ S \ T, f s ≤ ∏ r ∈ R, f r := by
    rcases (S \ T).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.card_empty] at hRcard
      rw [he, Finset.card_eq_zero.mp hRcard]
    · set c := (S \ T).min' hne
      have hc := Finset.min'_mem _ hne
      have hc2 : 2 ≤ c := hS c (Finset.mem_sdiff.mp hc).1
      have step1 : ∏ s ∈ S \ T, f s ≤ f c ^ (S \ T).card := by
        rw [← Finset.prod_const]
        apply Finset.prod_le_prod (fun s hs => hfS s (Finset.mem_sdiff.mp hs).1)
        intro s hs
        exact g_anti hc2 (Finset.min'_le _ _ hs)
      have step2 : f c ^ R.card ≤ ∏ r ∈ R, f r := by
        rw [← Finset.prod_const]
        apply Finset.prod_le_prod (fun _ _ => zero_le_one.trans (g_one_le hc2))
        intro r hr
        exact g_anti (hT r (hRT r hr))
          (hST c (Finset.mem_sdiff.mp hc).1 (Finset.mem_sdiff.mp hc).2 r (hRT r hr))
      rw [hRcard] at step2
      exact step1.trans step2
  have hdisj : Disjoint (S ∩ T) R := by
    rw [Finset.disjoint_left]
    intro x hx hxR
    exact (Finset.mem_sdiff.mp (hRsub hxR)).2 (Finset.mem_inter.mp hx).1
  have step3 : ∏ x ∈ (S ∩ T) ∪ R, f x ≤ ∏ t ∈ T, f t := by
    apply Finset.prod_le_prod_of_subset_of_one_le
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact (Finset.mem_inter.mp h).2
      · exact hRT x h
    · intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact hfS x (Finset.mem_inter.mp h).1
      · exact zero_le_one.trans (g_one_le (hT x (hRT x h)))
    · intro x hx _
      exact g_one_le (hT x hx)
  rw [Finset.prod_union hdisj] at step3
  have hI : 0 ≤ ∏ x ∈ S ∩ T, f x :=
    Finset.prod_nonneg fun x hx => hfS x (Finset.mem_inter.mp hx).1
  rw [← Finset.prod_inter_mul_prod_sdiff S T]
  calc (∏ x ∈ S ∩ T, f x) * ∏ x ∈ S \ T, f x ≤ (∏ x ∈ S ∩ T, f x) * ∏ r ∈ R, f r :=
        mul_le_mul_of_nonneg_left key hI
    _ ≤ _ := step3

/-- For an odd perfect `N` and a finite set `T` of integers `≥ 2` such that every prime factor
of `N` outside `T` is at least every element of `T`: if `ω(N) ≤ |T|`, then
`2 < ∏_{t ∈ T} t/(t-1)`. -/
theorem two_lt_prod_of_card_le (h : OddPerfect N) {T : Finset ℕ} (hT : ∀ t ∈ T, 2 ≤ t)
    (hcover : ∀ p ∈ N.primeFactors, p ∉ T → ∀ t ∈ T, t ≤ p)
    (hk : N.primeFactors.card ≤ T.card) : 2 < ∏ t ∈ T, (t : ℚ) / (t - 1) :=
  (two_lt_prod_primeFactors h).trans_le (prod_div_sub_one_le_of_exchange
    (fun _ hs => (Nat.prime_of_mem_primeFactors hs).two_le) hT hcover hk)

/-! ## Primes in an interval, by kernel computation -/

/-- Trial division primality test (a `Bool`, for kernel computation). -/
def primeB (n : ℕ) : Bool := 2 ≤ n && (List.range' 2 (n - 2)).all fun d => n % d != 0

/-- The primes in `[m, L]`, in increasing order. -/
def primesIn (m L : ℕ) : List ℕ := (List.range' m (L + 1 - m)).filter primeB

theorem primeB_of_prime {n : ℕ} (hn : n.Prime) : primeB n = true := by
  have h2 := hn.two_le
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range'_1,
    bne_iff_ne, ne_eq]
  refine ⟨h2, fun d hd h0 => ?_⟩
  rcases hn.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega

theorem two_le_of_primeB {n : ℕ} (h : primeB n = true) : 2 ≤ n := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem mem_primesIn {m L n : ℕ} : n ∈ primesIn m L ↔ m ≤ n ∧ n ≤ L ∧ primeB n = true := by
  rw [primesIn, List.mem_filter, List.mem_range'_1]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

theorem nodup_primesIn (m L : ℕ) : (primesIn m L).Nodup :=
  List.Nodup.filter _ List.nodup_range'

private theorem list_prod_div (l : List ℕ) (hl : ∀ t ∈ l, 1 ≤ t) :
    (l.map fun t : ℕ => (t : ℚ) / (t - 1)).prod =
      (l.prod : ℚ) / ((l.map (· - 1)).prod : ℕ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    simp only [List.map_cons, List.prod_cons]
    rw [ih (fun t ht => hl t (by simp [ht]))]
    push_cast [Nat.cast_sub ha]
    rw [div_mul_div_comm]

/-- **Least number of prime factors from a lower bound on the smallest one.** If every prime
factor of an odd perfect `N` is at least `m` (that is `m ≤ N.minFac`) and the primes in `[m, L]`
satisfy `∏ t ≤ 2 ∏ (t - 1)`, then `N` has more prime factors than there are primes in
`[m, L]`. -/
theorem length_primesIn_lt_card (h : OddPerfect N) {m L : ℕ} (hm : m ≤ N.minFac)
    (hval : (primesIn m L).prod ≤ 2 * ((primesIn m L).map (· - 1)).prod) :
    (primesIn m L).length < N.primeFactors.card := by
  set T := (primesIn m L).toFinset
  have hTcard : T.card = (primesIn m L).length := List.toFinset_card_of_nodup (nodup_primesIn m L)
  have hT : ∀ t ∈ T, 2 ≤ t := fun t ht =>
    two_le_of_primeB (mem_primesIn.mp (List.mem_toFinset.mp ht)).2.2
  have hcover : ∀ p ∈ N.primeFactors, p ∉ T → ∀ t ∈ T, t ≤ p := by
    intro p hp hpT t ht
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hmp : m ≤ p := hm.trans (Nat.minFac_le_of_dvd hpp.two_le (Nat.dvd_of_mem_primeFactors hp))
    have htL := (mem_primesIn.mp (List.mem_toFinset.mp ht)).2.1
    by_contra hlt
    exact hpT (List.mem_toFinset.mpr (mem_primesIn.mpr ⟨hmp, by omega, primeB_of_prime hpp⟩))
  by_contra hk
  have h2 := two_lt_prod_of_card_le h hT hcover (by omega)
  have hprod : ∏ t ∈ T, (t : ℚ) / (t - 1) =
      ((primesIn m L).map fun t : ℕ => (t : ℚ) / (t - 1)).prod :=
    List.prod_toFinset _ (nodup_primesIn m L)
  have hl : ∀ t ∈ primesIn m L, 2 ≤ t := fun t ht => two_le_of_primeB (mem_primesIn.mp ht).2.2
  rw [hprod, list_prod_div _ (fun t ht => (hl t ht).trans' (by norm_num))] at h2
  have hpos : (0 : ℚ) < (((primesIn m L).map (· - 1)).prod : ℕ) := by
    have : 0 < ((primesIn m L).map (· - 1)).prod := List.prod_pos (by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      have := hl t ht; omega)
    exact_mod_cast this
  rw [lt_div_iff₀ hpos] at h2
  have : ((2 * ((primesIn m L).map (· - 1)).prod : ℕ) : ℚ) < ((primesIn m L).prod : ℚ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]; linarith
  have : 2 * ((primesIn m L).map (· - 1)).prod < (primesIn m L).prod := by exact_mod_cast this
  omega

/-- If every prime factor of an odd perfect number is at least `5` (that is `3 ∤ N`), then
`ω(N) ≥ 7`. This is the value already in `seven_le_card_primeFactors_of_not_three_dvd`; the exact
prime product gives no more. -/
theorem seven_le_card_of_five_le_minFac (h : OddPerfect N) (hm : 5 ≤ N.minFac) :
    7 ≤ N.primeFactors.card := by
  have := length_primesIn_lt_card h (L := 19) hm (by decide +kernel)
  have e : (primesIn 5 19).length = 6 := by decide +kernel
  omega

/-- If every prime factor of an odd perfect number is at least `7`, then `ω(N) ≥ 15` (the value
already in `fifteen_le_card_primeFactors_of_not_three_dvd_of_not_five_dvd`). -/
theorem fifteen_le_card_of_seven_le_minFac (h : OddPerfect N) (hm : 7 ≤ N.minFac) :
    15 ≤ N.primeFactors.card := by
  have := length_primesIn_lt_card h (L := 59) hm (by decide +kernel)
  have e : (primesIn 7 59).length = 14 := by decide +kernel
  omega

/-- If every prime factor of an odd perfect number is at least `11`, then `ω(N) ≥ 27`. -/
theorem twentySeven_le_card_of_eleven_le_minFac (h : OddPerfect N) (hm : 11 ≤ N.minFac) :
    27 ≤ N.primeFactors.card := by
  have := length_primesIn_lt_card h (L := 113) hm (by decide +kernel)
  have e : (primesIn 11 113).length = 26 := by decide +kernel
  omega

/-- If every prime factor of an odd perfect number is at least `13`, then `ω(N) ≥ 41`. -/
theorem fortyOne_le_card_of_thirteen_le_minFac (h : OddPerfect N) (hm : 13 ≤ N.minFac) :
    41 ≤ N.primeFactors.card := by
  have := length_primesIn_lt_card h (L := 197) hm (by decide +kernel)
  have e : (primesIn 13 197).length = 40 := by decide +kernel
  omega

/-- If every prime factor of an odd perfect number is at least `17`, then `ω(N) ≥ 62`. -/
theorem sixtyTwo_le_card_of_seventeen_le_minFac (h : OddPerfect N) (hm : 17 ≤ N.minFac) :
    62 ≤ N.primeFactors.card := by
  have := length_primesIn_lt_card h (L := 331) hm (by decide +kernel)
  have e : (primesIn 17 331).length = 61 := by decide +kernel
  omega

/-- If every prime factor of an odd perfect number is at least `19`, then `ω(N) ≥ 85`. -/
theorem eightyFive_le_card_of_nineteen_le_minFac (h : OddPerfect N) (hm : 19 ≤ N.minFac) :
    85 ≤ N.primeFactors.card := by
  have := length_primesIn_lt_card h (L := 467) hm (by decide +kernel)
  have e : (primesIn 19 467).length = 84 := by decide +kernel
  omega

/-- If every prime factor of an odd perfect number is at least `23`, then `ω(N) ≥ 115`. -/
theorem oneHundredFifteen_le_card_of_twentyThree_le_minFac (h : OddPerfect N)
    (hm : 23 ≤ N.minFac) : 115 ≤ N.primeFactors.card := by
  have := length_primesIn_lt_card h (L := 673) hm (by decide +kernel)
  have e : (primesIn 23 673).length = 114 := by decide +kernel
  omega

/-! ## Three free odd perfect numbers have at least eight prime factors -/

/-- `σ(p^e)/p^e` written as an explicit rational, for evaluation. -/
private def abQ (p e : ℕ) : ℚ := ((∑ i ∈ Finset.range (e + 1), p ^ i : ℕ) : ℚ) / ((p ^ e : ℕ) : ℚ)

private theorem abundancy_eq_abQ {p : ℕ} (hp : p.Prime) (e : ℕ) : abundancy (p ^ e) = abQ p e := by
  rw [abundancy, sigma_one_apply_prime_pow hp, abQ]

/-- Leaf of a branch and bound over exponents. If `N.primeFactors = s`, `g p ≤ e_p` for all
`p ∈ s`, and `e_p = g p` for `p ∈ F`, then `∏ σ(p^{g p})/p^{g p} ≤ 2` (an abundant divisor is
impossible) and `2 ≤ ∏ (exact value on F, p/(p-1) elsewhere)`. -/
private theorem leaf (h : OddPerfect N) {s : Finset ℕ} (hs : N.primeFactors = s) (g : ℕ → ℕ)
    (F : Finset ℕ) (hg : ∀ p ∈ s, g p ≤ N.factorization p ∧ (p ∈ F → N.factorization p = g p)) :
    ∏ p ∈ s, abQ p (g p) ≤ 2 ∧
      2 ≤ ∏ p ∈ s, (if p ∈ F then abQ p (g p) else (p : ℚ) / (p - 1)) := by
  have h2 : ∏ p ∈ s, abundancy (p ^ N.factorization p) = 2 := by
    rw [← hs, ← abundancy_eq_prod_primeFactors h.ne_zero,
      (perfect_iff_abundancy_eq_two h.pos).mp h.perfect]
  have hpr : ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hs ▸ hp)
  constructor
  · rw [← h2]
    apply Finset.prod_le_prod
    · intro p hp
      rw [← abundancy_eq_abQ (hpr p hp)]
      unfold abundancy; positivity
    · intro p hp
      rw [← abundancy_eq_abQ (hpr p hp)]
      exact abundancy_prime_pow_mono (hpr p hp) (hg p hp).1
  · rw [← h2]
    apply Finset.prod_le_prod
    · intro p hp; unfold abundancy; positivity
    · intro p hp
      split_ifs with hF
      · rw [(hg p hp).2 hF, abundancy_eq_abQ (hpr p hp)]
      · exact (abundancy_prime_pow_lt (hpr p hp) _).le

/-- Exponent facts for an ordinary prime factor when `3 ∤ N`. -/
private theorem ord_facts (h : OddPerfect N) (h3 : ¬ 3 ∣ N) {sp : ℕ}
    (hev : ∀ p : ℕ, p.Prime → p ≠ sp → Even (N.factorization p)) {p : ℕ}
    (hp : p ∈ N.primeFactors) (hne : p ≠ sp) :
    2 ≤ N.factorization p ∧ N.factorization p % 2 = 0 ∧
      (p % 3 = 1 → N.factorization p % 3 ≠ 2) := by
  obtain ⟨j, hj⟩ := hev p (Nat.prime_of_mem_primeFactors hp) hne
  have h1 := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd h.ne_zero
    (Nat.dvd_of_mem_primeFactors hp)
  exact ⟨by omega, by omega, fun h1 => factorization_mod_three_ne_two h h3 hp h1⟩

/-- Setup common to the four supports: the special prime `sp` with its facts. -/
private theorem special_setup (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    ∃ sp, sp ∈ N.primeFactors ∧ sp % 12 = 1 ∧ N.factorization sp % 4 = 1 ∧
      (∀ p : ℕ, p.Prime → p ≠ sp → Even (N.factorization p)) ∧
      N.factorization sp % 3 ≠ 2 := by
  obtain ⟨sp, hsp, hspN, -, hspe, hev⟩ := exists_special_prime h
  have hmem : sp ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hsp, hspN, h.ne_zero⟩
  have h12 := special_mod_twelve h h3 hsp (Nat.odd_iff.mpr (by omega))
  exact ⟨sp, hmem, h12, hspe, hev, factorization_mod_three_ne_two h h3 hmem (by omega)⟩

private theorem excl_23_13 (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hpf : N.primeFactors = {23, 5, 7, 11, 13, 17, 19})
    (hev : ∀ p : ℕ, p.Prime → p ≠ 13 → Even (N.factorization p))
    (hs4 : N.factorization 13 % 4 = 1) (_hs3 : N.factorization 13 % 3 ≠ 2) : False := by
  have O := fun p (hp : p ∈ ({23, 5, 7, 11, 13, 17, 19} : Finset ℕ)) (hne : p ≠ 13) =>
    ord_facts h h3 hev (hpf ▸ hp) hne
  obtain ⟨a5, b5, -⟩ := O 5 (by decide) (by decide)
  obtain ⟨a7, b7, c7⟩ := O 7 (by decide) (by decide)
  have c7 := c7 (by norm_num)
  obtain ⟨a11, b11, -⟩ := O 11 (by decide) (by decide)
  obtain ⟨a17, b17, -⟩ := O 17 (by decide) (by decide)
  obtain ⟨a19, b19, c19⟩ := O 19 (by decide) (by decide)
  have c19 := c19 (by norm_num)
  obtain ⟨a23, b23, -⟩ := O 23 (by decide) (by decide)
  have L := leaf h hpf (fun p => if p = 7 ∨ p = 19 then 4 else if p = 13 then 1 else 2) ∅ (by
      intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
  norm_num [abQ, Finset.sum_range_succ] at L

private theorem excl_29_13 (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hpf : N.primeFactors = {29, 5, 7, 11, 13, 17, 19})
    (hev : ∀ p : ℕ, p.Prime → p ≠ 13 → Even (N.factorization p))
    (hs4 : N.factorization 13 % 4 = 1) (hs3 : N.factorization 13 % 3 ≠ 2) : False := by
  have O := fun p (hp : p ∈ ({29, 5, 7, 11, 13, 17, 19} : Finset ℕ)) (hne : p ≠ 13) =>
    ord_facts h h3 hev (hpf ▸ hp) hne
  obtain ⟨a5, b5, -⟩ := O 5 (by decide) (by decide)
  obtain ⟨a7, b7, c7⟩ := O 7 (by decide) (by decide)
  have c7 := c7 (by norm_num)
  obtain ⟨a11, b11, -⟩ := O 11 (by decide) (by decide)
  obtain ⟨a17, b17, -⟩ := O 17 (by decide) (by decide)
  obtain ⟨a19, b19, c19⟩ := O 19 (by decide) (by decide)
  have c19 := c19 (by norm_num)
  obtain ⟨a29, b29, -⟩ := O 29 (by decide) (by decide)
  rcases (by omega : N.factorization 5 = 2 ∨ 4 ≤ N.factorization 5) with e5 | e5
  · rcases (by omega : N.factorization 13 = 1 ∨ 9 ≤ N.factorization 13) with e13 | e13
    · have L := leaf h hpf (fun p => if p = 5 then 2 else if p = 13 then 1 else if p = 7 ∨ p = 19 then 4 else 2) {5, 13} (by
          intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
      norm_num [abQ, Finset.sum_range_succ] at L
    · have L := leaf h hpf (fun p => if p = 5 then 2 else if p = 13 then 9 else if p = 7 ∨ p = 19 then 4 else 2) ∅ (by
          intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
      norm_num [abQ, Finset.sum_range_succ] at L
  · have L := leaf h hpf (fun p => if p = 5 then 4 else if p = 13 then 1 else if p = 7 ∨ p = 19 then 4 else 2) ∅ (by
        intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
    norm_num [abQ, Finset.sum_range_succ] at L

private theorem excl_31_13 (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hpf : N.primeFactors = {31, 5, 7, 11, 13, 17, 19})
    (hev : ∀ p : ℕ, p.Prime → p ≠ 13 → Even (N.factorization p))
    (hs4 : N.factorization 13 % 4 = 1) (hs3 : N.factorization 13 % 3 ≠ 2) : False := by
  have O := fun p (hp : p ∈ ({31, 5, 7, 11, 13, 17, 19} : Finset ℕ)) (hne : p ≠ 13) =>
    ord_facts h h3 hev (hpf ▸ hp) hne
  obtain ⟨a5, b5, -⟩ := O 5 (by decide) (by decide)
  obtain ⟨a7, b7, c7⟩ := O 7 (by decide) (by decide)
  have c7 := c7 (by norm_num)
  obtain ⟨a11, b11, -⟩ := O 11 (by decide) (by decide)
  obtain ⟨a17, b17, -⟩ := O 17 (by decide) (by decide)
  obtain ⟨a19, b19, c19⟩ := O 19 (by decide) (by decide)
  have c19 := c19 (by norm_num)
  obtain ⟨a31, b31, c31⟩ := O 31 (by decide) (by decide)
  have c31 := c31 (by norm_num)
  rcases (by omega : N.factorization 5 = 2 ∨ 4 ≤ N.factorization 5) with e5 | e5
  · have L := leaf h hpf (fun p => if p = 5 then 2 else if p = 11 then 2 else if p = 13 then 1 else if p = 7 ∨ p = 19 ∨ p = 31 then 4 else 2) {5} (by
        intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
    norm_num [abQ, Finset.sum_range_succ] at L
  · rcases (by omega : N.factorization 13 = 1 ∨ 9 ≤ N.factorization 13) with e13 | e13
    · rcases (by omega : N.factorization 11 = 2 ∨ 4 ≤ N.factorization 11) with e11 | e11
      · rcases (by omega : N.factorization 5 = 4 ∨ 6 ≤ N.factorization 5) with e5' | e5'
        · have L := leaf h hpf (fun p => if p = 5 then 4 else if p = 11 then 2 else if p = 13 then 1 else if p = 7 ∨ p = 19 ∨ p = 31 then 4 else 2) {5, 11, 13} (by
              intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
              rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
          norm_num [abQ, Finset.sum_range_succ] at L
        · have L := leaf h hpf (fun p => if p = 5 then 6 else if p = 11 then 2 else if p = 13 then 1 else if p = 7 ∨ p = 19 ∨ p = 31 then 4 else 2) ∅ (by
              intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
              rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
          norm_num [abQ, Finset.sum_range_succ] at L
      · have L := leaf h hpf (fun p => if p = 5 then 4 else if p = 11 then 4 else if p = 13 then 1 else if p = 7 ∨ p = 19 ∨ p = 31 then 4 else 2) ∅ (by
            intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
        norm_num [abQ, Finset.sum_range_succ] at L
    · have L := leaf h hpf (fun p => if p = 5 then 4 else if p = 11 then 2 else if p = 13 then 9 else if p = 7 ∨ p = 19 ∨ p = 31 then 4 else 2) ∅ (by
          intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
      norm_num [abQ, Finset.sum_range_succ] at L

private theorem excl_37_13 (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hpf : N.primeFactors = {37, 5, 7, 11, 13, 17, 19})
    (hev : ∀ p : ℕ, p.Prime → p ≠ 13 → Even (N.factorization p))
    (hs4 : N.factorization 13 % 4 = 1) (hs3 : N.factorization 13 % 3 ≠ 2) : False := by
  have O := fun p (hp : p ∈ ({37, 5, 7, 11, 13, 17, 19} : Finset ℕ)) (hne : p ≠ 13) =>
    ord_facts h h3 hev (hpf ▸ hp) hne
  obtain ⟨a5, b5, -⟩ := O 5 (by decide) (by decide)
  obtain ⟨a7, b7, c7⟩ := O 7 (by decide) (by decide)
  have c7 := c7 (by norm_num)
  obtain ⟨a11, b11, -⟩ := O 11 (by decide) (by decide)
  obtain ⟨a17, b17, -⟩ := O 17 (by decide) (by decide)
  obtain ⟨a19, b19, c19⟩ := O 19 (by decide) (by decide)
  have c19 := c19 (by norm_num)
  obtain ⟨a37, b37, c37⟩ := O 37 (by decide) (by decide)
  have c37 := c37 (by norm_num)
  rcases (by omega : N.factorization 5 = 2 ∨ 4 ≤ N.factorization 5) with e5 | e5
  · have L := leaf h hpf (fun p => if p = 5 then 2 else if p = 13 then 1 else if p = 7 ∨ p = 19 ∨ p = 37 then 4 else 2) {5} (by
        intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
    norm_num [abQ, Finset.sum_range_succ] at L
  · rcases (by omega : N.factorization 13 = 1 ∨ 9 ≤ N.factorization 13) with e13 | e13
    · have L := leaf h hpf (fun p => if p = 5 then 4 else if p = 13 then 1 else if p = 7 ∨ p = 19 ∨ p = 37 then 4 else 2) {13} (by
          intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
      norm_num [abQ, Finset.sum_range_succ] at L
    · have L := leaf h hpf (fun p => if p = 5 then 4 else if p = 13 then 9 else if p = 7 ∨ p = 19 ∨ p = 37 then 4 else 2) ∅ (by
          intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
      norm_num [abQ, Finset.sum_range_succ] at L

private theorem excl_37_37 (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hpf : N.primeFactors = {37, 5, 7, 11, 13, 17, 19})
    (hev : ∀ p : ℕ, p.Prime → p ≠ 37 → Even (N.factorization p))
    (hs4 : N.factorization 37 % 4 = 1) (hs3 : N.factorization 37 % 3 ≠ 2) : False := by
  have O := fun p (hp : p ∈ ({37, 5, 7, 11, 13, 17, 19} : Finset ℕ)) (hne : p ≠ 37) =>
    ord_facts h h3 hev (hpf ▸ hp) hne
  obtain ⟨a5, b5, -⟩ := O 5 (by decide) (by decide)
  obtain ⟨a7, b7, c7⟩ := O 7 (by decide) (by decide)
  have c7 := c7 (by norm_num)
  obtain ⟨a11, b11, -⟩ := O 11 (by decide) (by decide)
  obtain ⟨a13, b13, c13⟩ := O 13 (by decide) (by decide)
  have c13 := c13 (by norm_num)
  obtain ⟨a17, b17, -⟩ := O 17 (by decide) (by decide)
  obtain ⟨a19, b19, c19⟩ := O 19 (by decide) (by decide)
  have c19 := c19 (by norm_num)
  rcases (by omega : N.factorization 5 = 2 ∨ 4 ≤ N.factorization 5) with e5 | e5
  · have L := leaf h hpf (fun p => if p = 5 then 2 else if p = 11 then 2 else if p = 17 then 2 else if p = 37 then 1 else if p = 7 ∨ p = 13 ∨ p = 19 then 4 else 2) {5} (by
        intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
    norm_num [abQ, Finset.sum_range_succ] at L
  · rcases (by omega : N.factorization 11 = 2 ∨ 4 ≤ N.factorization 11) with e11 | e11
    · rcases (by omega : N.factorization 37 = 1 ∨ 9 ≤ N.factorization 37) with e37 | e37
      · rcases (by omega : N.factorization 5 = 4 ∨ 6 ≤ N.factorization 5) with e5' | e5'
        · have L := leaf h hpf (fun p => if p = 5 then 4 else if p = 11 then 2 else if p = 17 then 2 else if p = 37 then 1 else if p = 7 ∨ p = 13 ∨ p = 19 then 4 else 2) {5, 11, 37} (by
              intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
              rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
          norm_num [abQ, Finset.sum_range_succ] at L
        · rcases (by omega : N.factorization 17 = 2 ∨ 4 ≤ N.factorization 17) with e17 | e17
          · have L := leaf h hpf (fun p => if p = 5 then 6 else if p = 11 then 2 else if p = 17 then 2 else if p = 37 then 1 else if p = 7 ∨ p = 13 ∨ p = 19 then 4 else 2) {11, 17, 37} (by
                intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
                rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
            norm_num [abQ, Finset.sum_range_succ] at L
          · have L := leaf h hpf (fun p => if p = 5 then 6 else if p = 11 then 2 else if p = 17 then 4 else if p = 37 then 1 else if p = 7 ∨ p = 13 ∨ p = 19 then 4 else 2) ∅ (by
                intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
                rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
            norm_num [abQ, Finset.sum_range_succ] at L
      · have L := leaf h hpf (fun p => if p = 5 then 4 else if p = 11 then 2 else if p = 17 then 2 else if p = 37 then 9 else if p = 7 ∨ p = 13 ∨ p = 19 then 4 else 2) ∅ (by
            intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
            rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
        norm_num [abQ, Finset.sum_range_succ] at L
    · have L := leaf h hpf (fun p => if p = 5 then 4 else if p = 11 then 4 else if p = 17 then 2 else if p = 37 then 1 else if p = 7 ∨ p = 13 ∨ p = 19 then 4 else 2) ∅ (by
          intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)
      norm_num [abQ, Finset.sum_range_succ] at L

private theorem gt29 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hn : p ∉ ({5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ)) : 29 < p := by
  by_contra hle
  interval_cases p <;> first | (simp at hn; done) | norm_num at hp

/-- If a prime `r` among `5, …, 19` is missing, `∏ p/(p-1)` over at most seven primes `≥ 5`
is at most the product over the first seven such primes other than `r`. -/
private theorem absent (h : OddPerfect N) (hk : N.primeFactors.card ≤ 7)
    (hge : ∀ p ∈ N.primeFactors, 5 ≤ p) {r : ℕ} (hr : r ∉ N.primeFactors) (T : Finset ℕ)
    (hT : ∀ t ∈ T, 2 ≤ t ∧ t ≤ 29)
    (hcov : ∀ x ∈ ({5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ), x ≠ r → x ∈ T)
    (hcard : 7 ≤ T.card) (hval : ∏ t ∈ T, (t : ℚ) / (t - 1) ≤ 2) : False := by
  have := two_lt_prod_of_card_le h (fun t ht => (hT t ht).1) (fun p hp hpT t ht => by
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpr : p ≠ r := fun e => hr (e ▸ hp)
    have hU : p ∉ ({5, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := fun hu => hpT (hcov p hu hpr)
    have := gt29 hpp (hge p hp) hU
    have := (hT t ht).2
    omega) (by omega)
  linarith

/-- If `3 ∤ N` for an odd perfect number `N`, then `N` has at least eight distinct prime
factors. With seven prime factors the support would be `{5, 7, 11, 13, 17, 19, q}` with
`q ∈ {23, 29, 31, 37}` (the only supports with `∏ p/(p-1) > 2`); each is excluded by the
exponent restrictions for `3 ∤ N` (the special prime is `≡ 1 (mod 12)`, primes `≡ 1 (mod 3)`
have exponent `≢ 2 (mod 3)`, all other exponents are even) and a short branch and bound on the
exponents of `5, 11, 13, 17, 37` with abundancy bounds only. -/
theorem eight_le_card_primeFactors_of_not_three_dvd (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    8 ≤ N.primeFactors.card := by
  have hge : ∀ p ∈ N.primeFactors, 5 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    have : p ≠ 2 := fun e => h.not_two_dvd (e ▸ hd)
    have : p ≠ 3 := fun e => h3 (e ▸ hd)
    have : p ≠ 4 := fun e => by subst e; norm_num at hpp
    have := hpp.two_le
    omega
  have h7 := seven_le_card_primeFactors_of_not_three_dvd h h3
  by_contra hlt
  have hk : N.primeFactors.card = 7 := by omega
  have hB : ({5, 7, 11, 13, 17, 19} : Finset ℕ) ⊆ N.primeFactors := by
    intro r hr
    by_contra hrn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absent h hk.le hge hrn {7, 11, 13, 17, 19, 23, 29} (by decide) (by decide)
        (by decide) (by norm_num [Finset.prod_insert])
    · exact absent h hk.le hge hrn {5, 11, 13, 17, 19, 23, 29} (by decide) (by decide)
        (by decide) (by norm_num [Finset.prod_insert])
    · exact absent h hk.le hge hrn {5, 7, 13, 17, 19, 23, 29} (by decide) (by decide)
        (by decide) (by norm_num [Finset.prod_insert])
    · exact absent h hk.le hge hrn {5, 7, 11, 17, 19, 23, 29} (by decide) (by decide)
        (by decide) (by norm_num [Finset.prod_insert])
    · exact absent h hk.le hge hrn {5, 7, 11, 13, 19, 23, 29} (by decide) (by decide)
        (by decide) (by norm_num [Finset.prod_insert])
    · exact absent h hk.le hge hrn {5, 7, 11, 13, 17, 23, 29} (by decide) (by decide)
        (by decide) (by norm_num [Finset.prod_insert])
  have hc : (N.primeFactors \ {5, 7, 11, 13, 17, 19}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hB, hk]; rfl
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hc
  have hqm : q ∈ N.primeFactors \ {5, 7, 11, 13, 17, 19} := hq ▸ Finset.mem_singleton_self q
  have hqpf := (Finset.mem_sdiff.mp hqm).1
  have hqB := (Finset.mem_sdiff.mp hqm).2
  have hpf : N.primeFactors = insert q {5, 7, 11, 13, 17, 19} := by
    ext x
    rw [Finset.mem_insert]
    constructor
    · intro hx
      by_cases hxB : x ∈ ({5, 7, 11, 13, 17, 19} : Finset ℕ)
      · exact Or.inr hxB
      · left
        have : x ∈ N.primeFactors \ {5, 7, 11, 13, 17, 19} := Finset.mem_sdiff.mpr ⟨hx, hxB⟩
        rw [hq] at this; exact Finset.mem_singleton.mp this
    · rintro (rfl | hx)
      · exact hqpf
      · exact hB hx
  have hqp := Nat.prime_of_mem_primeFactors hqpf
  have hq23 : 23 ≤ q := by
    have := hge q hqpf
    by_contra hlt'
    interval_cases q <;> first | (simp at hqB; done) | norm_num at hqp
  have hq39 : q ≤ 39 := by
    by_contra hlt'
    have h2 := two_lt_prod_primeFactors h
    rw [hpf, Finset.prod_insert hqB] at h2
    have hf := g_anti (m := 40) (by norm_num) (show 40 ≤ q by omega)
    have hv : ∏ t ∈ ({5, 7, 11, 13, 17, 19} : Finset ℕ), (t : ℚ) / (t - 1) = 323323 / 165888 := by
      norm_num [Finset.prod_insert]
    rw [hv] at h2
    norm_num at hf
    linarith
  obtain ⟨sp, hsm, h12, hs4, hev, hs3⟩ := special_setup h h3
  rw [hpf] at hsm
  interval_cases q <;> (try norm_num at hqp)
  · obtain rfl : sp = 13 := by simp at hsm; omega
    exact excl_23_13 h h3 hpf hev hs4 hs3
  · obtain rfl : sp = 13 := by simp at hsm; omega
    exact excl_29_13 h h3 hpf hev hs4 hs3
  · obtain rfl : sp = 13 := by simp at hsm; omega
    exact excl_31_13 h h3 hpf hev hs4 hs3
  · rcases (by simp at hsm; omega : sp = 13 ∨ sp = 37) with rfl | rfl
    · exact excl_37_13 h h3 hpf hev hs4 hs3
    · exact excl_37_37 h h3 hpf hev hs4 hs3

end OddPerfect
#print axioms OddPerfect.prod_mul_prod_sdiff_eq_two
#print axioms OddPerfect.prod_abundancy_lt_two
#print axioms OddPerfect.exists_min_not_mem_of_prod_lt_two
#print axioms OddPerfect.two_mul_sub_one_lt
#print axioms OddPerfect.four_mul_sub_two_lt
#print axioms OddPerfect.two_mul_mul_sub_one_lt_of_le
#print axioms OddPerfect.four_mul_sq_mul_sub_two_lt_of_le
#print axioms OddPerfect.le_prod_sigma_mul
#print axioms OddPerfect.seven_mul_second_prime_lt
#print axioms OddPerfect.thirtyOne_mul_third_prime_lt
#print axioms OddPerfect.fiveHundredEleven_mul_fourth_prime_lt
#print axioms OddPerfect.fifth_prime_bound
#print axioms OddPerfect.sixth_prime_bound
#print axioms OddPerfect.prod_div_sub_one_le_of_exchange
#print axioms OddPerfect.two_lt_prod_of_card_le
#print axioms OddPerfect.primeB_of_prime
#print axioms OddPerfect.two_le_of_primeB
#print axioms OddPerfect.mem_primesIn
#print axioms OddPerfect.nodup_primesIn
#print axioms OddPerfect.length_primesIn_lt_card
#print axioms OddPerfect.seven_le_card_of_five_le_minFac
#print axioms OddPerfect.fifteen_le_card_of_seven_le_minFac
#print axioms OddPerfect.twentySeven_le_card_of_eleven_le_minFac
#print axioms OddPerfect.fortyOne_le_card_of_thirteen_le_minFac
#print axioms OddPerfect.sixtyTwo_le_card_of_seventeen_le_minFac
#print axioms OddPerfect.eightyFive_le_card_of_nineteen_le_minFac
#print axioms OddPerfect.oneHundredFifteen_le_card_of_twentyThree_le_minFac
#print axioms OddPerfect.eight_le_card_primeFactors_of_not_three_dvd
