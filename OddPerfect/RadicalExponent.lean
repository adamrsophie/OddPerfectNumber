import OddPerfect.LargePrimes
import OddPerfect.SpecialBelow
import OddPerfect.OmegaFive

/-!
# The radical of an odd perfect number

Write `R = ∏_{p ∣ N} p` for the radical of an odd perfect number `N` with special prime `q`.

* Stage 1, from the landed bounds: `R ^ 2 q ^ k ≤ q ^ 2 N` (`rad_sq_mul_special_le`), so
  `R ^ 2 < N` when `k ≠ 1`. With the Acquaah and Konyagin bound `q ^ 3 < 3 N` this gives
  `R ^ 6 < 3 N ^ 4` (`rad_pow_six_lt`), the exponent `2/3`. If `q < m` in Euler's form
  `N = q ^ k * m ^ 2`, then `R ^ 3 < N ^ 2` (`rad_cube_lt_sq_of_special_lt`), so
  `R ^ 3 < N ^ 2` outside the exceptional shape of `special_lt_or_shape`
  (`rad_cube_lt_sq_or_shape`).
* Stage 2: the theorem of Luca and Pomerance (On the radical of a perfect number, New York
  J. Math. 16 (2010), 23 to 30, Proposition 1), `R < 2 N ^ (17/26)`, stated for odd perfect
  numbers as `R ^ 26 < 2 ^ 26 * N ^ 17` (`rad_pow_twentysix_lt`).

Known mathematics. The proof of Proposition 1 was read in the paper and rewritten in integer
form: the thresholds `q ^ 13 < 2 ^ 26 N ^ 4`, `N ^ 9 ≤ q ^ 26` and `N ≤ 2 ^ 52 K ^ 13` (with
`K` the product of the components of exponent at least four, so `K = k ^ 2` in the paper's
notation) replace the real powers; the middle range uses `R ^ 2 q ^ 2 ≤ q ^ 3 N < 3 N ^ 2`
from the Acquaah and Konyagin bound instead of the paper's case split; and the final
contradiction uses `five_le_card_primeFactors` in place of Sylvester's theorem.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Helpers -/

private lemma prod_pow_factorization_eq {N : ℕ} (hN : N ≠ 0) :
    ∏ t ∈ N.primeFactors, t ^ N.factorization t = N := by
  have := Nat.prod_factorization_pow_eq_self hN
  rwa [Finsupp.prod, Nat.support_factorization] at this

/-- Prime by prime comparison of `R ^ a * ∏ f` with `(∏ g) * N`. -/
private lemma rad_pow_mul_le {N : ℕ} (a : ℕ) (hN : N ≠ 0) (f g : ℕ → ℕ)
    (h : ∀ t ∈ N.primeFactors, t ^ a * f t ≤ g t * t ^ N.factorization t) :
    (∏ t ∈ N.primeFactors, t) ^ a * ∏ t ∈ N.primeFactors, f t ≤
      (∏ t ∈ N.primeFactors, g t) * N := by
  calc (∏ t ∈ N.primeFactors, t) ^ a * ∏ t ∈ N.primeFactors, f t
      = ∏ t ∈ N.primeFactors, (t ^ a * f t) := by
        rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    _ ≤ ∏ t ∈ N.primeFactors, (g t * t ^ N.factorization t) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) h
    _ = (∏ t ∈ N.primeFactors, g t) * N := by
        rw [Finset.prod_mul_distrib, prod_pow_factorization_eq hN]

private lemma sigma_le_sq (n : ℕ) : σ 1 n ≤ n ^ 2 := by
  rw [sigma_one_apply, sq]
  calc ∑ d ∈ n.divisors, d ≤ ∑ _d ∈ n.divisors, n :=
        Finset.sum_le_sum fun d hd => Nat.divisor_le hd
    _ = n.divisors.card * n := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)

private lemma lt_sigma {n : ℕ} (hn : 1 < n) : n < σ 1 n := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have h1 : 1 ∈ n.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr hn
  have := Finset.single_le_sum (f := fun i => i) (fun _ _ => Nat.zero_le _) h1
  omega

private lemma le_prod_of_mem {s : Finset ℕ} {f : ℕ → ℕ} (hf : ∀ i ∈ s, 0 < f i) {a : ℕ}
    (ha : a ∈ s) : f a ≤ ∏ i ∈ s, f i :=
  Nat.le_of_dvd (Finset.prod_pos hf) (Finset.dvd_prod_of_mem f ha)

/-- A sum of naturals equal to two has one term at least two or two distinct nonzero terms. -/
private lemma sum_eq_two_split {F : Finset ℕ} {w : ℕ → ℕ} (h : ∑ t ∈ F, w t = 2) :
    (∃ t ∈ F, 2 ≤ w t) ∨ ∃ t ∈ F, ∃ s ∈ F, t ≠ s ∧ 1 ≤ w t ∧ 1 ≤ w s := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  set S := F.filter (fun t => 1 ≤ w t) with hS
  have hcard : S.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    by_contra hab
    rw [hS, Finset.mem_filter] at ha hb
    have := h2 a ha.1 b hb.1 hab ha.2
    omega
  have heq : ∑ t ∈ S, w t = ∑ t ∈ F, w t :=
    Finset.sum_filter_of_ne fun t _ ht => by omega
  have hle : ∑ t ∈ S, w t ≤ ∑ _t ∈ S, 1 := Finset.sum_le_sum fun t ht => by
    rw [hS, Finset.mem_filter] at ht
    have := h1 t ht.1
    omega
  rw [Finset.sum_const, smul_eq_mul, mul_one] at hle
  omega

/-! ## Stage 1 -/

/-- For the special prime `q` with exponent `k`: `R ^ 2 * q ^ k ≤ q ^ 2 * N`, where `R` is the
radical. -/
theorem rad_sq_mul_special_le {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    (∏ p ∈ N.primeFactors, p) ^ 2 * q ^ N.factorization q ≤ q ^ 2 * N := by
  have hN0 := h.ne_zero
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr hodd.pos.ne'
  have key := rad_pow_mul_le 2 hN0 (fun t => if t = q then q ^ N.factorization q else 1)
    (fun t => if t = q then q ^ 2 else 1) fun t ht => by
      by_cases htq : t = q
      · subst htq; simp
      · simp only [htq, if_false, mul_one, one_mul]
        obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd (Nat.prime_of_mem_primeFactors ht) htq
        have h1 : 1 ≤ N.factorization t :=
          (Nat.prime_of_mem_primeFactors ht).dvd_iff_one_le_factorization hN0 |>.mp
            (Nat.dvd_of_mem_primeFactors ht)
        exact Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors ht).pos (by omega)
  simpa [Finset.prod_ite_eq', hqmem] using key

/-- If the special exponent is not one, then `R ^ 2 < N`. -/
theorem rad_sq_lt_of_exponent_ne_one {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hk : N.factorization q ≠ 1) :
    (∏ p ∈ N.primeFactors, p) ^ 2 < N := by
  have key := rad_sq_mul_special_le h hq hodd
  have hk3 : 3 ≤ N.factorization q := by obtain ⟨j, hj⟩ := hodd; omega
  have hlt : q ^ 2 < q ^ N.factorization q := Nat.pow_lt_pow_right hq.one_lt (by omega)
  have hN := h.pos
  have h1 : q ^ 2 * N < N * q ^ N.factorization q := by
    rw [mul_comm N]; exact Nat.mul_lt_mul_of_pos_right hlt hN
  exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt key h1)

/-- Exponent one: `R ^ 2 ≤ q * N`. -/
private lemma rad_sq_le_of_exponent_one {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) : (∏ p ∈ N.primeFactors, p) ^ 2 ≤ q * N := by
  have key := rad_sq_mul_special_le h hq (by rw [hq1]; exact odd_one)
  rw [hq1, pow_one] at key
  refine Nat.le_of_mul_le_mul_right ?_ hq.pos
  calc (∏ p ∈ N.primeFactors, p) ^ 2 * q ≤ q ^ 2 * N := key
    _ = q * N * q := by ring

/-- Acquaah and Konyagin's exponent `2/3` for the radical: `R ^ 6 < 3 * N ^ 4`. -/
theorem rad_pow_six_lt {N : ℕ} (h : OddPerfect N) :
    (∏ p ∈ N.primeFactors, p) ^ 6 < 3 * N ^ 4 := by
  obtain ⟨q, hq, hqN, -, hk4, -⟩ := exists_special_prime h
  have hodd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
  have hN := h.pos
  set R := ∏ p ∈ N.primeFactors, p
  by_cases hk : N.factorization q = 1
  · have h2 := rad_sq_le_of_exponent_one h hq hk
    have h3 := pow_three_lt_three_mul h hq hqN
    calc R ^ 6 = (R ^ 2) ^ 3 := by ring
      _ ≤ (q * N) ^ 3 := Nat.pow_le_pow_left h2 3
      _ = q ^ 3 * N ^ 3 := by ring
      _ < 3 * N * N ^ 3 := Nat.mul_lt_mul_of_pos_right h3 (by positivity)
      _ = 3 * N ^ 4 := by ring
  · have h2 := rad_sq_lt_of_exponent_ne_one h hq hodd hk
    calc R ^ 6 = (R ^ 2) ^ 3 := by ring
      _ < N ^ 3 := Nat.pow_lt_pow_left h2 (by norm_num)
      _ ≤ N ^ 4 := Nat.pow_le_pow_right hN (by norm_num)
      _ ≤ 3 * N ^ 4 := Nat.le_mul_of_pos_left _ (by norm_num)

/-- If `q < m` in Euler's form `N = q ^ k * m ^ 2`, then `R ^ 3 < N ^ 2`. -/
theorem rad_cube_lt_sq_of_special_lt {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hlt : q < m) :
    (∏ p ∈ N.primeFactors, p) ^ 3 < N ^ 2 := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hfac : N.factorization q = k := by
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
      Finsupp.smul_apply, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  have hkodd : Odd k := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  have hodd : Odd (N.factorization q) := hfac ▸ hkodd
  have hNpos := h.pos
  set R := ∏ p ∈ N.primeFactors, p
  have hsq : (R ^ 3) ^ 2 < (N ^ 2) ^ 2 := by
    by_cases hk : k = 1
    · subst hk
      have h2 := rad_sq_le_of_exponent_one h hq hfac
      have hq3 : q ^ 3 < N := by
        rw [hN, pow_one]
        calc q ^ 3 = q * q ^ 2 := by ring
          _ < q * m ^ 2 := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hlt (by norm_num))
              hq.pos
      calc (R ^ 3) ^ 2 = (R ^ 2) ^ 3 := by ring
        _ ≤ (q * N) ^ 3 := Nat.pow_le_pow_left h2 3
        _ = q ^ 3 * N ^ 3 := by ring
        _ < N * N ^ 3 := Nat.mul_lt_mul_of_pos_right hq3 (by positivity)
        _ = (N ^ 2) ^ 2 := by ring
    · have h2 := rad_sq_lt_of_exponent_ne_one h hq hodd (by rw [hfac]; exact hk)
      calc (R ^ 3) ^ 2 = (R ^ 2) ^ 3 := by ring
        _ < N ^ 3 := Nat.pow_lt_pow_left h2 (by norm_num)
        _ ≤ (N ^ 2) ^ 2 := by
          rw [← pow_mul]; exact Nat.pow_le_pow_right hNpos (by norm_num)
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hsq

/-- `R ^ 3 < N ^ 2` for every odd perfect number `N = q ^ k * m ^ 2` in Euler's form, unless
`N` has the exceptional shape of `special_lt_or_shape`. -/
theorem rad_cube_lt_sq_or_shape {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    (∏ p ∈ N.primeFactors, p) ^ 3 < N ^ 2 ∨
      (k = 1 ∧ ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ 2 * m ^ 2 = p ^ N.factorization p * (q + 1) ∧
        σ 1 (p ^ N.factorization p) = q ∧ σ 1 ((q + 1) / 2) = p ^ N.factorization p) := by
  rcases special_lt_or_shape h hq hN hqm with h1 | h1
  · exact Or.inl (rad_cube_lt_sq_of_special_lt h hq hN hqm h1)
  · exact Or.inr h1

/-! ## Stage 2: Luca and Pomerance -/

/-- A closed set of components: if a nonempty set `Z` of at most four prime factors satisfies
`ℓ * z ≥ 2 N` for each `ℓ ∈ Z`, with `z = ∏_{ℓ ∈ Z} ℓ ^ v_ℓ(N)`, then `N` is not an odd
perfect number. -/
private lemma closed_false {N : ℕ} (h : OddPerfect N) {Z : Finset ℕ} (hZ : Z ⊆ N.primeFactors)
    (hZne : Z.Nonempty) (hcard : Z.card ≤ 4)
    (hbig : ∀ ℓ ∈ Z, 2 * N ≤ ℓ * ∏ t ∈ Z, t ^ N.factorization t) : False := by
  have hN0 := h.ne_zero
  have hNpos := h.pos
  have hpos : ∀ t ∈ N.primeFactors, 0 < t ^ N.factorization t := fun t ht =>
    pow_pos (Nat.prime_of_mem_primeFactors ht).pos _
  set z := ∏ t ∈ Z, t ^ N.factorization t with hz
  set y := ∏ t ∈ N.primeFactors \ Z, t ^ N.factorization t with hy
  have hzy : y * z = N := by
    have := Finset.prod_sdiff (f := fun t => t ^ N.factorization t) hZ
    rwa [prod_pow_factorization_eq hN0] at this
  have hcop : Nat.Coprime z y := by
    refine Nat.Coprime.prod_left fun ℓ hℓ => Nat.Coprime.prod_right fun t ht => ?_
    have htF := (Finset.mem_sdiff.mp ht)
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hZ hℓ))
      (Nat.prime_of_mem_primeFactors htF.1)).mpr (by rintro rfl; exact htF.2 hℓ))
  have hσ : σ 1 z * σ 1 y = 2 * N := by
    rw [← isMultiplicative_sigma.map_mul_of_coprime hcop, mul_comm z y, hzy]
    exact h.sigma_eq
  obtain ⟨ℓ₀, hℓ₀⟩ := hZne
  have hz1 : 1 < z := by
    have h1 := le_prod_of_mem (fun t ht => hpos t (hZ ht)) hℓ₀
    have hp := Nat.prime_of_mem_primeFactors (hZ hℓ₀)
    have he : 1 ≤ N.factorization ℓ₀ :=
      (hp.dvd_iff_one_le_factorization hN0).mp (Nat.dvd_of_mem_primeFactors (hZ hℓ₀))
    have := Nat.le_self_pow (by omega : N.factorization ℓ₀ ≠ 0) ℓ₀
    have := hp.two_le
    omega
  have hzσ := lt_sigma hz1
  have hy0 : 0 < y := Finset.prod_pos fun t ht => hpos t (Finset.mem_sdiff.mp ht).1
  have hσy : 0 < σ 1 y := sigma_pos 1 y hy0.ne'
  have hlt : z * σ 1 y < 2 * N := by
    rw [← hσ]; exact Nat.mul_lt_mul_of_pos_right hzσ hσy
  have hcop2 : Nat.Coprime z (σ 1 y) := by
    refine Nat.Coprime.prod_left fun ℓ hℓ => Nat.Coprime.pow_left _ ?_
    rw [(Nat.prime_of_mem_primeFactors (hZ hℓ)).coprime_iff_not_dvd]
    intro hd
    have h1 := Nat.le_of_dvd hσy hd
    have h2 := hbig ℓ hℓ
    have : ℓ * z ≤ z * σ 1 y := by rw [mul_comm ℓ z]; exact Nat.mul_le_mul_left z h1
    omega
  have hzd : z ∣ σ 1 z := by
    refine hcop2.dvd_of_dvd_mul_right ⟨2 * y, ?_⟩
    rw [hσ, ← hzy]; ring
  obtain ⟨c, hc⟩ := hzd
  have hc2 : 2 ≤ c := by
    by_contra hc2
    have : c ≤ 1 := by omega
    have := Nat.mul_le_mul_left z this
    omega
  have hcy : c * σ 1 y = 2 * y := by
    refine Nat.eq_of_mul_eq_mul_left (show 0 < z by omega) ?_
    calc z * (c * σ 1 y) = σ 1 z * σ 1 y := by rw [hc]; ring
      _ = 2 * N := hσ
      _ = z * (2 * y) := by rw [← hzy]; ring
  have hsy : σ 1 y ≤ y := by
    have := Nat.mul_le_mul_right (σ 1 y) hc2
    omega
  have hy1 : y = 1 := by
    by_contra hy1
    have := lt_sigma (show 1 < y by omega)
    omega
  have hsub : N.primeFactors ⊆ Z := by
    rw [← Finset.sdiff_eq_empty_iff_subset]
    by_contra hne
    obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h1 := le_prod_of_mem (fun t ht => hpos t (Finset.mem_sdiff.mp ht).1) ht
    rw [← hy, hy1] at h1
    have htF := (Finset.mem_sdiff.mp ht).1
    have hp := Nat.prime_of_mem_primeFactors htF
    have he : 1 ≤ N.factorization t :=
      (hp.dvd_iff_one_le_factorization hN0).mp (Nat.dvd_of_mem_primeFactors htF)
    have := Nat.le_self_pow (by omega : N.factorization t ≠ 0) t
    have := hp.two_le
    omega
  have := Finset.card_le_card hsub
  have := five_le_card_primeFactors h
  omega

/-- Final size step with two feeding primes: from `2 ^ 26 N ^ 4 ≤ q ^ 13`, `8 q ≤ 27 ℓ ^ 4`,
`2 q ≤ 3 p ^ 2`, `2 p ≤ 3 t ^ 2`, `2 p ≤ 3 s ^ 2` get `2 N ≤ ℓ (q p ^ 2 t ^ 2 s ^ 2)`. -/
private lemma bound_two {N q p t s ℓ : ℕ} (hN : 2 ^ 26 * N ^ 4 ≤ q ^ 13) (hl : 8 * q ≤ 27 * ℓ ^ 4)
    (hp : 2 * q ≤ 3 * p ^ 2) (ht : 2 * p ≤ 3 * t ^ 2) (hs : 2 * p ≤ 3 * s ^ 2) :
    2 * N ≤ ℓ * (q * p ^ 2 * t ^ 2 * s ^ 2) := by
  have hp8 : 16 * q ^ 4 ≤ 81 * p ^ 8 := by
    have := Nat.pow_le_pow_left hp 4; ring_nf at this ⊢; linarith
  have h4t : 8 * q ≤ 27 * t ^ 4 := by
    have := Nat.pow_le_pow_left ht 2; ring_nf at this ⊢; omega
  have h4s : 8 * q ≤ 27 * s ^ 4 := by
    have := Nat.pow_le_pow_left hs 2; ring_nf at this ⊢; omega
  have ht8 : 64 * q ^ 2 ≤ 729 * t ^ 8 := by
    have := Nat.pow_le_pow_left h4t 2; ring_nf at this ⊢; linarith
  have hs8 : 64 * q ^ 2 ≤ 729 * s ^ 8 := by
    have := Nat.pow_le_pow_left h4s 2; ring_nf at this ⊢; linarith
  have A := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hl hp8) ht8) hs8
  have B := Nat.mul_le_mul_left (q ^ 4) A
  set X := (ℓ * (q * p ^ 2 * t ^ 2 * s ^ 2)) ^ 4 with hX
  have hfin : 2 ^ 41 * (16 * N ^ 4) ≤ 2 ^ 41 * X := by
    calc 2 ^ 41 * (16 * N ^ 4) = 524288 * (2 ^ 26 * N ^ 4) := by ring
      _ ≤ 524288 * q ^ 13 := Nat.mul_le_mul_left _ hN
      _ = q ^ 4 * (8 * q * (16 * q ^ 4) * (64 * q ^ 2) * (64 * q ^ 2)) := by ring
      _ ≤ q ^ 4 * (27 * ℓ ^ 4 * (81 * p ^ 8) * (729 * t ^ 8) * (729 * s ^ 8)) := B
      _ = 1162261467 * X := by rw [hX]; ring
      _ ≤ 2 ^ 41 * X := Nat.mul_le_mul_right _ (by norm_num)
  have h16 : (2 * N) ^ 4 ≤ X := by
    have := Nat.le_of_mul_le_mul_left hfin (by positivity)
    calc (2 * N) ^ 4 = 16 * N ^ 4 := by ring
      _ ≤ X := this
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h16

/-- Final size step with one feeding prime: from `2 ^ 26 N ^ 4 ≤ q ^ 13`, `8 q ≤ 27 ℓ ^ 4`,
`2 q ≤ 3 p ^ 2`, `2 p ^ 2 ≤ 3 t ^ 2` get `2 N ≤ ℓ (q p ^ 2 t ^ 2)`. -/
private lemma bound_one {N q p t ℓ : ℕ} (hN : 2 ^ 26 * N ^ 4 ≤ q ^ 13) (hl : 8 * q ≤ 27 * ℓ ^ 4)
    (hp : 2 * q ≤ 3 * p ^ 2) (ht : 2 * p ^ 2 ≤ 3 * t ^ 2) :
    2 * N ≤ ℓ * (q * p ^ 2 * t ^ 2) := by
  have hp8 : 16 * q ^ 4 ≤ 81 * p ^ 8 := by
    have := Nat.pow_le_pow_left hp 4; ring_nf at this ⊢; linarith
  have hp4 : 4 * q ^ 2 ≤ 9 * p ^ 4 := by
    have := Nat.pow_le_pow_left hp 2; ring_nf at this ⊢; linarith
  have ht4 : 4 * p ^ 4 ≤ 9 * t ^ 4 := by
    have := Nat.pow_le_pow_left ht 2; ring_nf at this ⊢; linarith
  have h16 : 16 * q ^ 2 ≤ 81 * t ^ 4 := by linarith
  have ht8 : 256 * q ^ 4 ≤ 6561 * t ^ 8 := by
    have := Nat.pow_le_pow_left h16 2; ring_nf at this ⊢; linarith
  have A := Nat.mul_le_mul (Nat.mul_le_mul hl hp8) ht8
  have B := Nat.mul_le_mul_left (q ^ 4) A
  set X := (ℓ * (q * p ^ 2 * t ^ 2)) ^ 4 with hX
  have hfin : 2 ^ 37 * (16 * N ^ 4) ≤ 2 ^ 37 * X := by
    calc 2 ^ 37 * (16 * N ^ 4) = 32768 * (2 ^ 26 * N ^ 4) := by ring
      _ ≤ 32768 * q ^ 13 := Nat.mul_le_mul_left _ hN
      _ = q ^ 4 * (8 * q * (16 * q ^ 4) * (256 * q ^ 4)) := by ring
      _ ≤ q ^ 4 * (27 * ℓ ^ 4 * (81 * p ^ 8) * (6561 * t ^ 8)) := B
      _ = 14348907 * X := by rw [hX]; ring
      _ ≤ 2 ^ 37 * X := Nat.mul_le_mul_right _ (by norm_num)
  have h16' : (2 * N) ^ 4 ≤ X := by
    have := Nat.le_of_mul_le_mul_left hfin (by positivity)
    calc (2 * N) ^ 4 = 16 * N ^ 4 := by ring
      _ ≤ X := this
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h16'

/-- The case `k = 1` of the theorem of Luca and Pomerance. -/
private lemma lp_exponent_one {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq1 : N.factorization q = 1) :
    (∏ p ∈ N.primeFactors, p) ^ 26 < 2 ^ 26 * N ^ 17 := by
  have hN0 := h.ne_zero
  have hNpos := h.pos
  have hodd : Odd (N.factorization q) := by rw [hq1]; exact odd_one
  have hqN : q ∣ N := (hq.dvd_iff_one_le_factorization hN0).mpr (by omega)
  have hqmem : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqN, hN0⟩
  have hq4 := (special_mod_four h hq hodd).1
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  set R := ∏ p ∈ N.primeFactors, p with hR
  have hR2 := rad_sq_le_of_exponent_one h hq hq1
  have hq3 := pow_three_lt_three_mul h hq hqN
  -- even exponents
  have hexp : ∀ t ∈ N.primeFactors, t ≠ q → 2 ≤ N.factorization t ∧ Even (N.factorization t) := by
    intro t ht htq
    have hev := even_factorization_of_ne h hq hodd (Nat.prime_of_mem_primeFactors ht) htq
    have h1 : 1 ≤ N.factorization t :=
      (Nat.prime_of_mem_primeFactors ht).dvd_iff_one_le_factorization hN0 |>.mp
        (Nat.dvd_of_mem_primeFactors ht)
    obtain ⟨j, hj⟩ := hev
    exact ⟨by omega, ⟨j, hj⟩⟩
  -- Range 1: `q ^ 13 < 2 ^ 26 N ^ 4`.
  by_cases hA : q ^ 13 < 2 ^ 26 * N ^ 4
  · calc R ^ 26 = (R ^ 2) ^ 13 := by ring
      _ ≤ (q * N) ^ 13 := Nat.pow_le_pow_left hR2 13
      _ = q ^ 13 * N ^ 13 := by ring
      _ < 2 ^ 26 * N ^ 4 * N ^ 13 := Nat.mul_lt_mul_of_pos_right hA (by positivity)
      _ = 2 ^ 26 * N ^ 17 := by ring
  push Not at hA
  -- Range 2: `N ^ 9 ≤ q ^ 26`.
  by_cases hB : N ^ 9 ≤ q ^ 26
  · have h3 : R ^ 2 * q ^ 2 < 3 * N ^ 2 := by
      calc R ^ 2 * q ^ 2 ≤ q * N * q ^ 2 := Nat.mul_le_mul_right _ hR2
        _ = q ^ 3 * N := by ring
        _ < 3 * N * N := Nat.mul_lt_mul_of_pos_right hq3 hNpos
        _ = 3 * N ^ 2 := by ring
    have h13 : R ^ 26 * q ^ 26 < 3 ^ 13 * N ^ 26 := by
      calc R ^ 26 * q ^ 26 = (R ^ 2 * q ^ 2) ^ 13 := by ring
        _ < (3 * N ^ 2) ^ 13 := Nat.pow_lt_pow_left h3 (by norm_num)
        _ = 3 ^ 13 * N ^ 26 := by ring
    have h17 : R ^ 26 * N ^ 9 < 3 ^ 13 * N ^ 17 * N ^ 9 := by
      calc R ^ 26 * N ^ 9 ≤ R ^ 26 * q ^ 26 := Nat.mul_le_mul_left _ hB
        _ < 3 ^ 13 * N ^ 26 := h13
        _ = 3 ^ 13 * N ^ 17 * N ^ 9 := by ring
    have := Nat.lt_of_mul_lt_mul_right h17
    calc R ^ 26 < 3 ^ 13 * N ^ 17 := this
      _ ≤ 2 ^ 26 * N ^ 17 := Nat.mul_le_mul_right _ (by norm_num)
  push Not at hB
  -- The squarefull part `K`.
  set K := ∏ t ∈ N.primeFactors, (if 4 ≤ N.factorization t then t ^ N.factorization t else 1)
    with hK
  have hKpos : 0 < K := Finset.prod_pos fun t ht => by
    split_ifs
    · exact pow_pos (Nat.prime_of_mem_primeFactors ht).pos _
    · exact one_pos
  have hKle : ∀ t ∈ N.primeFactors, 4 ≤ N.factorization t → t ^ N.factorization t ≤ K := by
    intro t ht h4
    have := le_prod_of_mem (s := N.primeFactors)
      (f := fun t => if 4 ≤ N.factorization t then t ^ N.factorization t else 1)
      (fun t ht => by
        split_ifs
        · exact pow_pos (Nat.prime_of_mem_primeFactors ht).pos _
        · exact one_pos) ht
    simpa [h4] using this
  have hRK : R ^ 4 * K ≤ q ^ 2 * N * N := by
    have key := rad_pow_mul_le 4 hN0
      (fun t => if 4 ≤ N.factorization t then t ^ N.factorization t else 1)
      (fun t => (if t = q then q ^ 2 else 1) * t ^ N.factorization t) fun t ht => by
        by_cases htq : t = q
        · rw [htq, hq1]
          rw [if_neg (show ¬ (4 ≤ 1) by norm_num), if_pos (rfl : q = q)]
          apply le_of_eq; ring
        · obtain ⟨h2, hev⟩ := hexp t ht htq
          have htp := (Nat.prime_of_mem_primeFactors ht).pos
          simp only [htq, if_false, one_mul]
          split_ifs with h4
          · rw [← pow_add, ← pow_add]
            exact Nat.pow_le_pow_right htp (by omega)
          · have he : N.factorization t = 2 := by obtain ⟨j, hj⟩ := hev; omega
            rw [he, mul_one, ← pow_add]
    rw [Finset.prod_mul_distrib, prod_pow_factorization_eq hN0] at key
    simpa [Finset.prod_ite_eq', hqmem] using key
  -- Range 3: `N ≤ 2 ^ 52 K ^ 13`.
  by_cases hC : N ≤ 2 ^ 52 * K ^ 13
  · have h1 : R ^ 52 * K ^ 13 < N ^ 35 := by
      calc R ^ 52 * K ^ 13 = (R ^ 4 * K) ^ 13 := by ring
        _ ≤ (q ^ 2 * N * N) ^ 13 := Nat.pow_le_pow_left hRK 13
        _ = q ^ 26 * N ^ 26 := by ring
        _ < N ^ 9 * N ^ 26 := Nat.mul_lt_mul_of_pos_right hB (by positivity)
        _ = N ^ 35 := by ring
    have h2 : R ^ 52 * K ^ 13 < 2 ^ 52 * N ^ 34 * K ^ 13 := by
      calc R ^ 52 * K ^ 13 < N ^ 35 := h1
        _ = N * N ^ 34 := by ring
        _ ≤ 2 ^ 52 * K ^ 13 * N ^ 34 := Nat.mul_le_mul_right _ hC
        _ = 2 ^ 52 * N ^ 34 * K ^ 13 := by ring
    have h3 := Nat.lt_of_mul_lt_mul_right h2
    have h4 : (R ^ 26) ^ 2 < (2 ^ 26 * N ^ 17) ^ 2 := by
      calc (R ^ 26) ^ 2 = R ^ 52 := by ring
        _ < 2 ^ 52 * N ^ 34 := h3
        _ = (2 ^ 26 * N ^ 17) ^ 2 := by ring
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h4
  push Not at hC
  -- `K ^ 2 < q`
  have hKq : K ^ 2 < q := by
    have h1 : (K ^ 2) ^ 13 < q ^ 13 := by
      have hC2 : (2 ^ 52 * K ^ 13) ^ 2 < N ^ 2 := Nat.pow_lt_pow_left hC (by norm_num)
      have hN2 : N ^ 2 ≤ 2 ^ 26 * N ^ 4 := by
        have := Nat.pow_le_pow_right hNpos (show 2 ≤ 4 by norm_num)
        nlinarith
      calc (K ^ 2) ^ 13 = K ^ 26 := by ring
        _ ≤ 2 ^ 104 * K ^ 26 := Nat.le_mul_of_pos_left _ (by positivity)
        _ = (2 ^ 52 * K ^ 13) ^ 2 := by ring
        _ < N ^ 2 := hC2
        _ ≤ 2 ^ 26 * N ^ 4 := hN2
        _ ≤ q ^ 13 := hA
    exact lt_of_pow_lt_pow_left₀ 13 (Nat.zero_le _) h1
  -- The prime `p` whose component carries `q`.
  obtain ⟨p, hpq, hpmem, -, hqd⟩ := exists_sigmaEdge_into h.perfect hqmem (by omega)
  have hp := Nat.prime_of_mem_primeFactors hpmem
  have hpodd : Odd p := h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hpmem)
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h2 | _
    · subst h2; exact absurd hpodd (by decide)
    · have := hp.two_le; obtain ⟨j, hj⟩ := hpodd; omega
  obtain ⟨hep2, hepev⟩ := hexp p hpmem hpq
  have hσpos : ∀ n : ℕ, 0 < n → 0 < σ 1 n := fun n hn => sigma_pos 1 n hn.ne'
  have hep : N.factorization p = 2 := by
    by_contra hne
    have h4 : 4 ≤ N.factorization p := by obtain ⟨j, hj⟩ := hepev; omega
    have h1 := hKle p hpmem h4
    have h2 := sigma_le_sq (p ^ N.factorization p)
    have h3 := Nat.le_of_dvd (hσpos _ (pow_pos hp.pos _)) hqd
    have : (p ^ N.factorization p) ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left h1 2
    omega
  rw [hep, sigma_prime_sq hp] at hqd
  have hpnd : ¬ p ∣ q + 1 := by
    intro hd
    have := (prime_dvd_phi3_dvd_succ hp hq hqd hd).1
    omega
  have h3p : 2 * q < 3 * p ^ 2 := by
    have := Nat.le_of_dvd (by unfold phi3; positivity) hqd
    unfold phi3 at this
    nlinarith
  have hKp : K ^ 2 < p := by
    have hC4 : (2 ^ 52 * K ^ 13) ^ 4 < N ^ 4 := Nat.pow_lt_pow_left hC (by norm_num)
    have h234 : 2 ^ 234 * K ^ 52 < q ^ 13 := by
      calc 2 ^ 234 * K ^ 52 = 2 ^ 26 * (2 ^ 52 * K ^ 13) ^ 4 := by ring
        _ < 2 ^ 26 * N ^ 4 := Nat.mul_lt_mul_of_pos_left hC4 (by positivity)
        _ ≤ q ^ 13 := hA
    have h1 : (3 * K ^ 4) ^ 13 < (2 * q) ^ 13 := by
      calc (3 * K ^ 4) ^ 13 = 3 ^ 13 * K ^ 52 := by ring
        _ ≤ 2 ^ 247 * K ^ 52 := Nat.mul_le_mul_right _ (by norm_num)
        _ = 2 ^ 13 * (2 ^ 234 * K ^ 52) := by ring
        _ < 2 ^ 13 * q ^ 13 := Nat.mul_lt_mul_of_pos_left h234 (by positivity)
        _ = (2 * q) ^ 13 := by ring
    have h2 : 3 * K ^ 4 < 2 * q := lt_of_pow_lt_pow_left₀ 13 (Nat.zero_le _) h1
    have h3 : (K ^ 2) ^ 2 < p ^ 2 := by
      have : 3 * (K ^ 2) ^ 2 < 3 * p ^ 2 := by
        calc 3 * (K ^ 2) ^ 2 = 3 * K ^ 4 := by ring
          _ < 2 * q := h2
          _ < 3 * p ^ 2 := h3p
      omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h3
  -- Weights of the components at `p`.
  set w : ℕ → ℕ := fun t => sigmaWeight N t p with hw
  have hsum : ∑ t ∈ N.primeFactors, w t = 2 := by
    rw [hw]; simp only; rw [sigmaWeight_sum_eq h.perfect hp (by omega), hep]
  have hwq : w q = 0 := by
    simp only [hw, sigmaWeight, hq1]
    refine Nat.factorization_eq_zero_of_not_dvd ?_
    rwa [sigma_one_apply_prime_pow hq, Finset.sum_range_succ, Finset.sum_range_one, pow_zero,
      pow_one, add_comm]
  have hwp : w p = 0 := by
    simp only [hw, sigmaWeight]
    exact Nat.factorization_eq_zero_of_not_dvd
      ((hp.coprime_iff_not_dvd).mp (coprime_sigma_prime_pow hp _).symm)
  have hwbig : ∀ t ∈ N.primeFactors, 4 ≤ N.factorization t → w t = 0 := by
    intro t ht h4
    simp only [hw, sigmaWeight]
    refine Nat.factorization_eq_zero_of_not_dvd fun hd => ?_
    have htp := (Nat.prime_of_mem_primeFactors ht).pos
    have h1 := Nat.le_of_dvd (hσpos _ (pow_pos htp _)) hd
    have h2 := sigma_le_sq (t ^ N.factorization t)
    have h3 : (t ^ N.factorization t) ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left (hKle t ht h4) 2
    omega
  -- A feeding prime.
  have hfeed : ∀ t ∈ N.primeFactors, 1 ≤ w t →
      t ≠ q ∧ t ≠ p ∧ N.factorization t = 2 ∧ 3 ≤ t ∧ p ^ w t ≤ t ^ 2 + t + 1 := by
    intro t ht hwt
    have htq : t ≠ q := by rintro rfl; omega
    have htp : t ≠ p := by rintro rfl; omega
    obtain ⟨h2, hev⟩ := hexp t ht htq
    have he : N.factorization t = 2 := by
      by_contra hne
      have h4 : 4 ≤ N.factorization t := by obtain ⟨j, hj⟩ := hev; omega
      have := hwbig t ht h4
      omega
    have htpr := Nat.prime_of_mem_primeFactors ht
    have htodd : Odd t := h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors ht)
    have ht3 : 3 ≤ t := by
      rcases htpr.eq_two_or_odd' with h2 | _
      · subst h2; exact absurd htodd (by decide)
      · have := htpr.two_le; obtain ⟨j, hj⟩ := htodd; omega
    refine ⟨htq, htp, he, ht3, ?_⟩
    have hd : p ^ w t ∣ σ 1 (t ^ N.factorization t) := Nat.ordProj_dvd _ p
    rw [he, sigma_prime_sq htpr] at hd
    exact Nat.le_of_dvd (by positivity) hd
  have hpq' : p ≠ q := hpq
  have hlq : 8 * q ≤ 27 * q ^ 4 := by
    have : q ≤ q ^ 4 := Nat.le_self_pow (by norm_num) q
    omega
  have hlp : 8 * q ≤ 27 * p ^ 4 := by
    have : p ^ 2 ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos (by norm_num)
    omega
  rcases sum_eq_two_split hsum with ⟨t, ht, hwt⟩ | ⟨t, ht, s, hs, hts, hwt, hws⟩
  · -- one feeding prime with `p ^ 2 ∣ σ(t ^ 2)`
    obtain ⟨htq, htp, het, ht3, hpt⟩ := hfeed t ht (by omega)
    have hpt2 : p ^ 2 ≤ t ^ 2 + t + 1 :=
      le_trans (Nat.pow_le_pow_right hp.pos hwt) hpt
    have h3t : 3 * t ≤ t ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right t ht3
    have h2t : 2 * p ^ 2 ≤ 3 * t ^ 2 := by omega
    have hlt : 8 * q ≤ 27 * t ^ 4 := by
      have h1 : 4 * p ^ 4 ≤ 9 * t ^ 4 := by
        have := Nat.pow_le_pow_left h2t 2; ring_nf at this ⊢; linarith
      have h2 : 4 * q ^ 2 ≤ 9 * p ^ 4 := by
        have := Nat.pow_le_pow_left h3p.le 2; ring_nf at this ⊢; linarith
      have hq2 : 2 * q ≤ q ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right q (by omega)
      omega
    exfalso
    refine closed_false h (Z := {q, p, t}) ?_ ⟨q, by simp⟩ ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · have := Finset.card_insert_le q {p, t}
      have := Finset.card_insert_le p {t}
      simp only [Finset.card_singleton] at *
      omega
    · have hprod : ∏ x ∈ ({q, p, t} : Finset ℕ), x ^ N.factorization x = q * p ^ 2 * t ^ 2 := by
        rw [Finset.prod_insert (by simp [hpq'.symm, htq.symm]),
          Finset.prod_insert (by simp [htp.symm]), Finset.prod_singleton, hq1, hep, het]
        ring
      rw [hprod]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact bound_one hA hlq h3p.le h2t
      · exact bound_one hA hlp h3p.le h2t
      · exact bound_one hA hlt h3p.le h2t
  · -- two feeding primes
    obtain ⟨htq, htp, het, ht3, hpt⟩ := hfeed t ht hwt
    obtain ⟨hsq, hsp, hes, hs3, hps⟩ := hfeed s hs hws
    have hpt1 : p ≤ t ^ 2 + t + 1 := le_trans (Nat.le_self_pow (by omega) p) hpt
    have hps1 : p ≤ s ^ 2 + s + 1 := le_trans (Nat.le_self_pow (by omega) p) hps
    have h3t : 3 * t ≤ t ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right t ht3
    have h3s : 3 * s ≤ s ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right s hs3
    have h2t : 2 * p ≤ 3 * t ^ 2 := by omega
    have h2s : 2 * p ≤ 3 * s ^ 2 := by omega
    have hlt : 8 * q ≤ 27 * t ^ 4 := by
      have := Nat.pow_le_pow_left h2t 2; ring_nf at this ⊢; omega
    have hls : 8 * q ≤ 27 * s ^ 4 := by
      have := Nat.pow_le_pow_left h2s 2; ring_nf at this ⊢; omega
    exfalso
    refine closed_false h (Z := {q, p, t, s}) ?_ ⟨q, by simp⟩ ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · have := Finset.card_insert_le q {p, t, s}
      have := Finset.card_insert_le p {t, s}
      have := Finset.card_insert_le t {s}
      simp only [Finset.card_singleton] at *
      omega
    · have hprod : ∏ x ∈ ({q, p, t, s} : Finset ℕ), x ^ N.factorization x =
          q * p ^ 2 * t ^ 2 * s ^ 2 := by
        rw [Finset.prod_insert (by simp [hpq'.symm, htq.symm, hsq.symm]),
          Finset.prod_insert (by simp [htp.symm, hsp.symm]),
          Finset.prod_insert (by simp [hts]), Finset.prod_singleton, hq1, hep, het, hes]
        ring
      rw [hprod]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact bound_two hA hlq h3p.le h2t h2s
      · exact bound_two hA hlp h3p.le h2t h2s
      · exact bound_two hA hlt h3p.le h2t h2s
      · exact bound_two hA hls h3p.le h2t h2s

/-- Luca and Pomerance (New York J. Math. 16 (2010), Proposition 1), for odd perfect numbers:
the radical `R` satisfies `R < 2 N ^ (17/26)`, stated as `R ^ 26 < 2 ^ 26 * N ^ 17`. -/
theorem rad_pow_twentysix_lt {N : ℕ} (h : OddPerfect N) :
    (∏ p ∈ N.primeFactors, p) ^ 26 < 2 ^ 26 * N ^ 17 := by
  obtain ⟨q, hq, -, -, hk4, -⟩ := exists_special_prime h
  by_cases hk : N.factorization q = 1
  · exact lp_exponent_one h hq hk
  · have hodd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
    have h2 := rad_sq_lt_of_exponent_ne_one h hq hodd hk
    have hN := h.pos
    calc (∏ p ∈ N.primeFactors, p) ^ 26 = ((∏ p ∈ N.primeFactors, p) ^ 2) ^ 13 := by ring
      _ < N ^ 13 := Nat.pow_lt_pow_left h2 (by norm_num)
      _ ≤ N ^ 17 := Nat.pow_le_pow_right hN (by norm_num)
      _ < 2 ^ 26 * N ^ 17 := by
        have : 0 < N ^ 17 := by positivity
        omega

end OddPerfect

#print axioms OddPerfect.rad_sq_mul_special_le
#print axioms OddPerfect.rad_sq_lt_of_exponent_ne_one
#print axioms OddPerfect.rad_pow_six_lt
#print axioms OddPerfect.rad_cube_lt_sq_of_special_lt
#print axioms OddPerfect.rad_cube_lt_sq_or_shape
#print axioms OddPerfect.rad_pow_twentysix_lt
