import OddPerfect.LargestPrimeSafeNone

/-!
# Largest prime factor of the form `4 R + 1` with `R > 3` prime: it is the special prime

Let `N` be an odd perfect number whose largest prime factor is `P = 4 R + 1` with `R > 3`
prime. A *sender* is a prime factor `u ≠ P` with `P ∣ σ(u ^ e_u)`, where `e_u = v_u(N)`.

* `largest_four_sender_row`: a sender `u` with even exponent has `e_u = R - 1`, order `R`
  modulo `P`, and row `1 + u + ⋯ + u ^ (R - 1) = P ^ j` with `j = v_P(σ(u ^ e_u)) ≥ 1`.
* `largest_four_special_not_sender`: a prime factor `q ≠ P` with odd exponent is not a sender.
* `largest_four_sender_unique`: there is at most one sender.
* `largest_four_special`: `P` is the special prime. Its exponent `j = v_P(N)` is odd,
  `j ≡ 1 (mod 4)`, `5 ≤ j < R`, and there is a prime factor `u ≠ P` with `e_u = R - 1` and
  `1 + u + ⋯ + u ^ (R - 1) = P ^ j`.

Proof sketch. As `P = 4 R + 1` is prime and `R > 3`, `R ≡ 1 (mod 3)`, so `3 ∣ 2 R + 1`. Hence
the only prime `r ≤ P` with `2 R ∣ r - 1` is `P`, and no odd prime `u < P` has `u ≡ 1 (mod R)`.
A root `x` of `1 + x + ⋯ + x ^ (R - 1)` modulo a prime `r` is `1` (then `r = R`) or has order
`R` (then `2 R ∣ r - 1`). This makes every row of length `R` that divides `2 N` a power of
`P`. For a sender with odd exponent `a`, the order of `q` modulo `P` forces `a + 1 = 2 R`, so
`σ(q ^ a) = F · (q ^ R + 1)` with `F = 1 + q + ⋯ + q ^ (R - 1)`; `F` is a power of `P`, so
`P ∤ q ^ R + 1`, and `A = (q ^ R + 1) / (q + 1)` is a power of `R`. Lifting the exponent gives
`v_R(A) = 1`, so `A = R`, which is too small. Uniqueness repeats the lifting argument of
`largest_safe_sender_unique`. In the main theorem `v_P(N)` is the row exponent of the only
sender; an even exponent makes `σ(u ^ (R - 1))` a square, so `R = 5` and `P = 21`.

Scope: these are necessary conditions in the restricted case that the largest prime factor
is `4 R + 1` with `R > 3` prime; the later module `LargestPrimeFourNone` excludes this case.
The odd perfect number conjecture remains open. No published source was checked; novelty not
verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N P R : ℕ}

private theorem lpf_odd_of_mem (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) :
    p % 2 = 1 :=
  Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))

/-- If `R > 3` is prime and `4 R + 1` is prime, then `R ≡ 1 (mod 3)`. -/
private theorem lpf_mod_three (hR : R.Prime) (hR3 : 3 < R) (hP : (4 * R + 1).Prime) :
    R % 3 = 1 := by
  have h0 : R % 3 ≠ 0 := by
    intro h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hR).mp (by omega)
    omega
  have h2 : R % 3 ≠ 2 := by
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hP).mp (by omega)
    omega
  omega

/-- A prime `r ≤ 4 R + 1` with `2 R ∣ r - 1` is `4 R + 1`, since `3 ∣ 2 R + 1`. -/
private theorem lpf_eq_of_dvd {r : ℕ} (hr : r.Prime) (hR3 : 3 < R) (hR1 : R % 3 = 1)
    (hd : 2 * R ∣ r - 1) (hle : r ≤ 4 * R + 1) : r = 4 * R + 1 := by
  obtain ⟨k, hk⟩ := hd
  have hr2 := hr.two_le
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (by
    rintro rfl
    simp at hk
    omega)
  have hk3 : k < 3 := by
    by_contra hc
    have := Nat.mul_le_mul_left (2 * R) (show 3 ≤ k by omega)
    omega
  interval_cases k
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp (by omega)
    omega
  · omega

/-- A root `x` of `1 + x + ⋯ + x ^ (R - 1)` modulo a prime `r` (with `R` an odd prime) is
`1`, and then `r = R`, or has order `R`, and then `2 R ∣ r - 1`. -/
private theorem lpf_zmod_row {r : ℕ} (hr : r.Prime) (hR : R.Prime) (hR2 : R ≠ 2)
    {x : ZMod r} (h0 : ∑ i ∈ Finset.range R, x ^ i = 0) :
    (x = 1 ∧ r = R) ∨ 2 * R ∣ r - 1 := by
  have : Fact r.Prime := ⟨hr⟩
  by_cases hx : x = 1
  · left
    refine ⟨hx, ?_⟩
    rw [hx] at h0
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h0
    exact (Nat.prime_dvd_prime_iff_eq hr hR).mp ((ZMod.natCast_eq_zero_iff R r).mp h0)
  right
  have hxR : x ^ R = 1 := by
    have := geom_sum_mul x R
    rw [h0, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hR.ne_zero] at hxR
    exact zero_ne_one hxR
  have hord : orderOf x = R := by
    rcases (Nat.dvd_prime hR).mp (orderOf_dvd_of_pow_eq_one hxR) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx
    · exact h1
  have hdvd := ZMod.orderOf_dvd_card_sub_one hx0
  rw [hord] at hdvd
  have h2 : 2 ∣ r - 1 := by
    rcases hr.eq_two_or_odd with h2 | ho
    · rw [h2] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      have := hR.two_le
      omega
    · omega
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
    ((Nat.coprime_two_left).mpr (hR.odd_of_ne_two hR2)) h2 hdvd

/-- A prime `r ∣ 2 N` that kills a row of length `R` is a prime factor of `N`, so `r ≤ P`. -/
private theorem lpf_le_of_root (h : OddPerfect N) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hR : R.Prime) (hR3 : 3 < R) {r : ℕ} (hr : r.Prime) {x : ZMod r}
    (h0 : ∑ i ∈ Finset.range R, x ^ i = 0) (hr2N : r ∣ 2 * N) : r ≤ P := by
  have hr2 : r ≠ 2 := by
    intro hr2
    rcases lpf_zmod_row hr hR (by omega) h0 with ⟨-, h2⟩ | h2
    · omega
    · rw [hr2] at h2
      have := Nat.le_of_dvd (by norm_num) h2
      omega
  exact hmax r (Nat.mem_primeFactors.mpr ⟨hr, Nat.Coprime.dvd_of_dvd_mul_left
    ((Nat.coprime_primes hr Nat.prime_two).mpr hr2) hr2N, h.ne_zero⟩)

/-- No odd prime `u < 4 R + 1` has `u ≡ 1 (mod R)` (for an odd `R > 3` with `R ≡ 1 (mod 3)`). -/
private theorem lpf_mod_ne_one {u : ℕ} (hu : u.Prime) (hu2 : u % 2 = 1) (hR3 : 3 < R)
    (hR1 : R % 3 = 1) (hRo : R % 2 = 1) (hlt : u < 4 * R + 1) : u % R ≠ 1 := by
  intro hm
  have hk := Nat.div_add_mod u R
  obtain ⟨k, hk'⟩ : ∃ k, k = u / R := ⟨_, rfl⟩
  rw [← hk'] at hk
  have hk4 : k < 4 := by
    by_contra hc
    have := Nat.mul_le_mul_left R (show 4 ≤ k by omega)
    omega
  have hu2' := hu.two_le
  interval_cases k
  · omega
  · omega
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hu).mp (by omega)
    omega
  · omega

/-- A row `1 + x + ⋯ + x ^ (R - 1)` dividing `2 N`, with `x % R ≠ 1`, is a power of
`P = 4 R + 1`. -/
private theorem lpf_row_pow (h : OddPerfect N) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hR : R.Prime) (hR3 : 3 < R) (hR1 : R % 3 = 1) (hPR : P = 4 * R + 1) {x : ℕ}
    (hxR : x % R ≠ 1) (hF : ∑ i ∈ Finset.range R, x ^ i ∣ 2 * N) :
    ∃ k, ∑ i ∈ Finset.range R, x ^ i = P ^ k := by
  have hF0 : ∑ i ∈ Finset.range R, x ^ i ≠ 0 :=
    ne_zero_of_dvd_ne_zero (by have := h.ne_zero; omega) hF
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hF0 fun {r} hr hrF => ?_⟩
  have : Fact r.Prime := ⟨hr⟩
  have h0 : ∑ i ∈ Finset.range R, ((x : ℕ) : ZMod r) ^ i = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ r).mpr hrF
    push_cast at this
    exact this
  have hle := lpf_le_of_root h hmax hR hR3 hr h0 (hrF.trans hF)
  rcases (lpf_zmod_row hr hR (by omega) h0) with ⟨hx1, hrR⟩ | hd
  · exfalso
    apply hxR
    have := (ZMod.natCast_eq_natCast_iff' x 1 r).mp (by rw [Nat.cast_one]; exact hx1)
    rwa [Nat.mod_eq_of_lt hr.one_lt, hrR] at this
  · have := lpf_eq_of_dvd hr hR3 hR1 hd (by omega)
    omega

/-- Growth: `4 n + 1 < 3 ^ (n - 1)` for `n ≥ 5`. -/
private theorem lpf_three_pow {n : ℕ} (hn : 5 ≤ n) : 4 * n + 1 < 3 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    generalize 3 ^ (n - 1) = X at ih ⊢
    omega

/-- A divisor `t ≥ 3` of `4 R` (with `R` prime) that is not divisible by `4` is `R` or
`2 R`. -/
private theorem lpf_dvd_four_mul {t : ℕ} (hR : R.Prime) (ht : t ∣ 4 * R) (ht3 : 3 ≤ t)
    (h4 : ¬ 4 ∣ t) : t = R ∨ t = 2 * R := by
  obtain ⟨d1, d2, h1, h2, rfl⟩ := Nat.dvd_mul.mp ht
  have hd1 : d1 ≤ 4 := Nat.le_of_dvd (by norm_num) h1
  rcases (Nat.dvd_prime hR).mp h2 with h | h <;> rw [h] at ht3 h4 ⊢ <;>
    interval_cases d1 <;> omega

/-- Exact row of a sender with even exponent. Let the largest prime factor of an odd perfect
number `N` be `P = 4 R + 1` with `R > 3` prime, and let `u ≠ P` be a prime factor with even
exponent and `P ∣ σ(u ^ e_u)`. Then `e_u = R - 1`, the order of `u` modulo `P` is `R`, and
`1 + u + ⋯ + u ^ (R - 1) = P ^ j` with `j = v_P(σ(u ^ e_u)) ≥ 1`. A necessary condition in a
restricted case, which `LargestPrimeFourNone` excludes. No published source was checked;
novelty not verified. -/
theorem largest_four_sender_row (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) (hR3 : 3 < R) (hPR : P = 4 * R + 1)
    {u : ℕ} (hu : u ∈ N.primeFactors) (huP : u ≠ P) (hev : Even (N.factorization u))
    (hd : P ∣ σ 1 (u ^ N.factorization u)) :
    N.factorization u = R - 1 ∧ orderOf (u : ZMod P) = R ∧
      ∑ i ∈ Finset.range R, u ^ i = P ^ padicValNat P (σ 1 (u ^ N.factorization u)) ∧
      1 ≤ padicValNat P (σ 1 (u ^ N.factorization u)) := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have : Fact P.Prime := ⟨hPp⟩
  have hup := Nat.prime_of_mem_primeFactors hu
  have hR1 := lpf_mod_three hR hR3 (by rw [← hPR]; exact hPp)
  have hRo := Nat.odd_iff.mp (hR.odd_of_ne_two (by omega))
  obtain ⟨hlt, hu2, ht3, ht4, -⟩ := sender_largest_data h hP hmax hu huP hd
  have he := two_mul_factorization_add_three_le h hu hmax
  set e := N.factorization u with hedef
  set t := orderOf (u : ZMod P) with htdef
  have hte : t ∣ e + 1 := by
    have hdd := (dvd_sigma_prime_pow_iff hup hPp huP).mp hd
    rwa [← htdef, if_neg (by omega)] at hdd
  have hu0 : (u : ZMod P) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hh
    have := Nat.le_of_dvd hup.pos hh
    omega
  have htP : t ∣ 4 * R := by
    have := ZMod.orderOf_dvd_card_sub_one hu0
    rwa [show P - 1 = 4 * R by omega] at this
  have heo : (e + 1) % 2 = 1 := by obtain ⟨m, hm⟩ := hev; omega
  have htR : t = R := by
    rcases lpf_dvd_four_mul hR htP ht3 ht4 with h1 | h1
    · exact h1
    · exfalso
      have h2 : 2 ∣ e + 1 := (Dvd.intro R rfl).trans (h1 ▸ hte)
      omega
  have heR : e + 1 = R := by
    obtain ⟨c, hc⟩ := hte
    rw [htR] at hc
    have hc3 : c < 3 := by
      by_contra hcc
      have := Nat.mul_le_mul_left R (show 3 ≤ c by omega)
      omega
    interval_cases c <;> omega
  have hσ : σ 1 (u ^ e) = ∑ i ∈ Finset.range R, u ^ i := by
    rw [sigma_one_apply_prime_pow hup, heR]
  have hF2N : ∑ i ∈ Finset.range R, u ^ i ∣ 2 * N := by
    rw [← hσ]
    exact OPNStarter.component_sigma_dvd h.perfect hup hedef.symm
  obtain ⟨k, hk⟩ := lpf_row_pow h hmax hR hR3 hR1 hPR
    (lpf_mod_ne_one hup hu2 hR3 hR1 hRo (by omega)) hF2N
  have hj : padicValNat P (σ 1 (u ^ e)) = k := by rw [hσ, hk, padicValNat.prime_pow]
  refine ⟨by omega, htR, by rw [hj]; exact hk, ?_⟩
  rw [hj]
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · rw [hσ, hk, h0, pow_zero] at hd
    have := Nat.le_of_dvd one_pos hd
    omega
  · omega

/-- The special prime does not send into `P = 4 R + 1` (with `R > 3` prime and `P` the largest
prime factor of an odd perfect number `N`): a prime factor `q ≠ P` with odd exponent has
`¬ P ∣ σ(q ^ e_q)`. A necessary condition in a restricted case, which
`LargestPrimeFourNone` excludes. No published source was checked; novelty not verified. -/
theorem largest_four_special_not_sender (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) (hR3 : 3 < R) (hPR : P = 4 * R + 1)
    {q : ℕ} (hq : q ∈ N.primeFactors) (hqP : q ≠ P) (hodd : Odd (N.factorization q)) :
    ¬ P ∣ σ 1 (q ^ N.factorization q) := by
  intro hd
  have hPp := Nat.prime_of_mem_primeFactors hP
  have : Fact P.Prime := ⟨hPp⟩
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hR1 := lpf_mod_three hR hR3 (by rw [← hPR]; exact hPp)
  have hRo' : Odd R := hR.odd_of_ne_two (by omega)
  have hRo := Nat.odd_iff.mp hRo'
  obtain ⟨hlt, hq2, ht3, ht4, -⟩ := sender_largest_data h hP hmax hq hqP hd
  obtain ⟨hq4, ha4⟩ := special_mod_four h hqp hodd
  have he := two_mul_factorization_add_three_le h hq hmax
  set a := N.factorization q with hadef
  set t := orderOf (q : ZMod P) with htdef
  have hta : t ∣ a + 1 := by
    have hdd := (dvd_sigma_prime_pow_iff hqp hPp hqP).mp hd
    rwa [← htdef, if_neg (by omega)] at hdd
  have hq0 : (q : ZMod P) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hh
    have := Nat.le_of_dvd hqp.pos hh
    omega
  have htP : t ∣ 4 * R := by
    have := ZMod.orderOf_dvd_card_sub_one hq0
    rwa [show P - 1 = 4 * R by omega] at this
  have hRt : R ∣ t := by
    rcases lpf_dvd_four_mul hR htP ht3 ht4 with h1 | h1
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
  have h2R : 2 * R ∣ a + 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_two_left).mpr hRo')
      (by omega : 2 ∣ a + 1) (hRt.trans hta)
  have haR : a + 1 = 2 * R := by
    obtain ⟨c, hc⟩ := h2R
    have hc2 : c < 2 := by
      by_contra hcc
      have := Nat.mul_le_mul_left (2 * R) (show 2 ≤ c by omega)
      omega
    interval_cases c <;> omega
  -- `σ(q ^ a) = F · (q ^ R + 1)`
  have hσ : σ 1 (q ^ a) = (∑ i ∈ Finset.range R, q ^ i) * (q ^ R + 1) := by
    rw [sigma_one_apply_prime_pow hqp, haR, two_mul, Finset.sum_range_add]
    simp_rw [pow_add, ← Finset.mul_sum]
    ring
  have h2N : σ 1 (q ^ a) ∣ 2 * N := OPNStarter.component_sigma_dvd h.perfect hqp hadef.symm
  have hF2N : ∑ i ∈ Finset.range R, q ^ i ∣ 2 * N := (Dvd.intro _ hσ.symm).trans h2N
  have hB2N : q ^ R + 1 ∣ 2 * N := (Dvd.intro_left _ hσ.symm).trans h2N
  -- `F` is a power of `P`, and `F > 1`
  obtain ⟨k, hk⟩ := lpf_row_pow h hmax hR hR3 hR1 hPR
    (lpf_mod_ne_one hqp hq2 hR3 hR1 hRo (by omega)) hF2N
  have hFq : 1 + q ≤ ∑ i ∈ Finset.range R, q ^ i := by
    have hsub : ∑ i ∈ Finset.range 2, q ^ i ≤ ∑ i ∈ Finset.range R, q ^ i :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    simpa [Finset.sum_range_succ] using hsub
  have hPF : P ∣ ∑ i ∈ Finset.range R, q ^ i := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [hk, h0, pow_zero] at hFq
      have := hqp.two_le
      omega
    · rw [hk]
      exact dvd_pow_self P h0.ne'
  -- so `P ∣ q ^ R - 1` and `P ∤ q ^ R + 1`
  have hgeo := geom_sum_mul_add (q - 1) R
  rw [Nat.sub_add_cancel hqp.one_lt.le] at hgeo
  have hPB : ¬ P ∣ q ^ R + 1 := by
    intro hB
    rw [← hgeo, add_assoc] at hB
    have h2 := (Nat.dvd_add_right (dvd_mul_of_dvd_left hPF _)).mp hB
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  -- `A = (q ^ R + 1) / (q + 1)` is a power of `R`
  obtain ⟨A, hA⟩ : q + 1 ∣ q ^ R + 1 := by
    simpa using hRo'.nat_add_dvd_pow_add_pow q 1
  have hAZ : (A : ℤ) = ∑ i ∈ Finset.range R, (-(q : ℤ)) ^ i := by
    have hg := geom_sum_mul (-(q : ℤ)) R
    rw [Odd.neg_pow hRo'] at hg
    have hAz : (q : ℤ) ^ R + 1 = ((q : ℤ) + 1) * A := by exact_mod_cast hA
    have hq1 : (q : ℤ) + 1 ≠ 0 := by positivity
    apply mul_left_cancel₀ hq1
    linear_combination hg - hAz
  have hA2N : A ∣ 2 * N := (Dvd.intro_left _ hA.symm).trans hB2N
  have hA0 : A ≠ 0 := ne_zero_of_dvd_ne_zero (by have := h.ne_zero; omega) hA2N
  have hAR : ∀ {r : ℕ}, r.Prime → r ∣ A → r = R ∧ r ∣ q + 1 := by
    intro r hr hrA
    have : Fact r.Prime := ⟨hr⟩
    have h0 : ∑ i ∈ Finset.range R, (-(q : ZMod r)) ^ i = 0 := by
      have h1 := (ZMod.natCast_eq_zero_iff _ r).mpr hrA
      have h2 : ((A : ℤ) : ZMod r) = 0 := by exact_mod_cast h1
      rw [hAZ] at h2
      push_cast at h2
      exact h2
    have hle := lpf_le_of_root h hmax hR hR3 hr h0 (hrA.trans hA2N)
    rcases lpf_zmod_row hr hR (by omega) h0 with ⟨hx1, hrR⟩ | hd'
    · refine ⟨hrR, (ZMod.natCast_eq_zero_iff _ r).mp ?_⟩
      push_cast
      rw [neg_eq_iff_eq_neg.mp hx1]
      ring
    · exfalso
      have := lpf_eq_of_dvd hr hR3 hR1 hd' (by omega)
      apply hPB
      rw [show P = r by omega]
      exact hrA.trans (Dvd.intro_left _ hA.symm)
  obtain ⟨m, hm⟩ : ∃ m, A = R ^ m :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hA0 (fun hr hrA => (hAR hr hrA).1)⟩
  -- size: `A > R`
  have hq5 : 3 ≤ q := by have := hqp.two_le; omega
  have hbig : (q + 1) * R < q ^ R + 1 := by
    have hqR : q ^ R = q * q ^ (R - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hR.one_le]
    have h3 := lpf_three_pow (show 5 ≤ R by omega)
    have hle : 3 ^ (R - 1) ≤ q ^ (R - 1) := Nat.pow_le_pow_left hq5 _
    have hX : q * (4 * R + 2) ≤ q * q ^ (R - 1) := Nat.mul_le_mul_left q (by omega)
    rw [hqR]
    nlinarith
  have hAgt : R < A := by
    have : (q + 1) * R < (q + 1) * A := by rw [← hA]; exact hbig
    exact Nat.lt_of_mul_lt_mul_left this
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    have := hR.two_le
    omega
  have hRq : R ∣ q + 1 := (hAR hR (by rw [hm]; exact dvd_pow_self R hm0)).2
  -- lifting the exponent: `v_R(A) = 1`
  have : Fact R.Prime := ⟨hR⟩
  have hRqn : ¬ R ∣ q := by
    intro hRq'
    have h1 := (Nat.dvd_add_right hRq').mp hRq
    have := Nat.le_of_dvd one_pos h1
    omega
  have hlte := padicValNat.pow_add_pow (p := R) hRo' (x := q) (y := 1) hRq hRqn hRo'
  rw [one_pow, hA, padicValNat.mul (by omega) hA0, padicValNat_self, hm,
    padicValNat.prime_pow] at hlte
  have hm1 : m = 1 := by omega
  rw [hm1, pow_one] at hm
  omega

/-- `u ^ R ≡ 1` modulo the row `1 + u + ⋯ + u ^ (R - 1)`. -/
private theorem lpf_pow_modEq {u R : ℕ} (hu : 1 ≤ u) :
    u ^ R ≡ 1 [MOD ∑ i ∈ Finset.range R, u ^ i] := by
  have hg := geom_sum_mul_add (u - 1) R
  rw [Nat.sub_add_cancel hu] at hg
  rw [← hg, Nat.ModEq, Nat.mul_add_mod_self_left]

/-- Two odd primes `u₁, u₂ < P` of order `R` modulo `P` whose rows are `P ^ j₁` and `P ^ j₂`
with `1 ≤ j₁ ≤ j₂` are equal (a copy of a private lemma of
`OddPerfect/LargestPrimeSafeNone.lean`). -/
private theorem lpf_eq_aux {u₁ u₂ j₁ j₂ : ℕ} (hP : P.Prime) (hR2 : 2 ≤ R) (hPm : ¬ P ∣ 2 * R)
    (hu₁ : u₁.Prime) (hu₂ : u₂.Prime) (h1o : u₁ % 2 = 1) (h2o : u₂ % 2 = 1) (h2lt : u₂ < P)
    (hord1 : orderOf (u₁ : ZMod P) = R) (hord2 : orderOf (u₂ : ZMod P) = R)
    (hF1 : ∑ i ∈ Finset.range R, u₁ ^ i = P ^ j₁) (hF2 : ∑ i ∈ Finset.range R, u₂ ^ i = P ^ j₂)
    (hj1 : 1 ≤ j₁) (hj : j₁ ≤ j₂) : u₁ = u₂ := by
  have : Fact P.Prime := ⟨hP⟩
  set x : ZMod P := (u₁ : ZMod P) with hx
  have hxR : x ^ R = 1 := by rw [← hord1]; exact pow_orderOf_eq_one x
  have hyR : (u₂ : ZMod P) ^ R = 1 := by rw [← hord2]; exact pow_orderOf_eq_one _
  set L := (List.range R).map (fun i => x ^ i) with hL
  have hnd : L.Nodup := by
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
    have ha' : a < orderOf x := by rw [hord1]; exact List.mem_range.mp ha
    have hb' : b < orderOf x := by rw [hord1]; exact List.mem_range.mp hb
    exact pow_injOn_Iio_orderOf ha' hb' hab
  have hmem := mem_of_pow_eq_one_of_nodup (by omega) hnd (by simp [hL])
    (fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
      rw [← pow_mul, mul_comm, pow_mul, hxR, one_pow]) hyR
  obtain ⟨k, hkR, hk⟩ := List.mem_map.mp hmem
  have hkR' := List.mem_range.mp hkR
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    rw [← hk, orderOf_one] at hord2
    omega
  have hM : P ^ j₁ ∣ P ^ j₂ := pow_dvd_pow P hj
  have hX2 : u₂ ^ (2 * R) ≡ 1 [MOD P ^ j₁] := by
    have h1 := (lpf_pow_modEq (R := R) hu₂.one_lt.le).of_dvd (hF2 ▸ hM)
    rw [mul_comm, pow_mul]
    simpa using h1.pow 2
  have hY2 : (u₁ ^ k) ^ (2 * R) ≡ 1 [MOD P ^ j₁] := by
    have h1 := lpf_pow_modEq (R := R) hu₁.one_lt.le
    rw [hF1] at h1
    rw [← pow_mul, show k * (2 * R) = R * (2 * k) by ring, pow_mul]
    simpa using h1.pow (2 * k)
  have hXlt : u₂ < P ^ j₁ := lt_of_lt_of_le h2lt (Nat.le_self_pow (by omega) P)
  have hYlt : u₁ ^ k < P ^ j₁ := by
    rw [← hF1]
    have hsub : ∑ i ∈ Finset.range (k + 1), u₁ ^ i ≤ ∑ i ∈ Finset.range R, u₁ ^ i :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    rw [Finset.sum_range_succ] at hsub
    have hpos : 0 < ∑ i ∈ Finset.range k, u₁ ^ i :=
      Finset.sum_pos (fun i _ => pow_pos hu₁.pos i) ⟨0, Finset.mem_range.mpr (by omega)⟩
    omega
  have hYo : u₁ ^ k % 2 = 1 := by simp [Nat.pow_mod, h1o]
  have hXY : u₂ ^ 2 ≡ (u₁ ^ k) ^ 2 [MOD P] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    rw [← hk]
  have heq := eq_of_sq_modEq_of_pow_two_mul_modEq_one hP hPm hj1 hXlt hYlt h2o hYo hX2 hY2 hXY
  exact (Nat.prime_dvd_prime_iff_eq hu₁ hu₂).mp (heq ▸ dvd_pow_self u₁ hk0)

/-- A sender into `P = 4 R + 1` has even exponent. -/
private theorem lpf_even_of_sender (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) (hR3 : 3 < R) (hPR : P = 4 * R + 1)
    {u : ℕ} (hu : u ∈ N.primeFactors) (huP : u ≠ P) (hd : P ∣ σ 1 (u ^ N.factorization u)) :
    Even (N.factorization u) := by
  rcases Nat.even_or_odd (N.factorization u) with he | ho
  · exact he
  · exact absurd hd (largest_four_special_not_sender h hP hmax hR hR3 hPR hu huP ho)

/-- At most one sender. Let the largest prime factor of an odd perfect number `N` be
`P = 4 R + 1` with `R > 3` prime. If `u` and `v` are prime factors different from `P` with
`P ∣ σ(u ^ e_u)` and `P ∣ σ(v ^ e_v)`, then `u = v`. A necessary condition in a restricted
case, which `LargestPrimeFourNone` excludes. No published source was checked; novelty not
verified. -/
theorem largest_four_sender_unique (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) (hR3 : 3 < R) (hPR : P = 4 * R + 1)
    {u v : ℕ} (hu : u ∈ N.primeFactors) (huP : u ≠ P) (hdu : P ∣ σ 1 (u ^ N.factorization u))
    (hv : v ∈ N.primeFactors) (hvP : v ≠ P) (hdv : P ∣ σ 1 (v ^ N.factorization v)) :
    u = v := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  obtain ⟨-, hou, hFu, hju⟩ := largest_four_sender_row h hP hmax hR hR3 hPR hu huP
    (lpf_even_of_sender h hP hmax hR hR3 hPR hu huP hdu) hdu
  obtain ⟨-, hov, hFv, hjv⟩ := largest_four_sender_row h hP hmax hR hR3 hPR hv hvP
    (lpf_even_of_sender h hP hmax hR hR3 hPR hv hvP hdv) hdv
  obtain ⟨hlu, -⟩ := sender_largest_data h hP hmax hu huP hdu
  obtain ⟨hlv, -⟩ := sender_largest_data h hP hmax hv hvP hdv
  have hPm : ¬ P ∣ 2 * R := by
    intro hd
    have := Nat.le_of_dvd (by have := hR.two_le; omega) hd
    omega
  have hup := Nat.prime_of_mem_primeFactors hu
  have hvp := Nat.prime_of_mem_primeFactors hv
  rcases le_total (padicValNat P (σ 1 (u ^ N.factorization u)))
      (padicValNat P (σ 1 (v ^ N.factorization v))) with hle | hle
  · exact lpf_eq_aux hPp hR.two_le hPm hup hvp (lpf_odd_of_mem h hu) (lpf_odd_of_mem h hv)
      hlv hou hov hFu hFv hju hle
  · exact (lpf_eq_aux hPp hR.two_le hPm hvp hup (lpf_odd_of_mem h hv) (lpf_odd_of_mem h hu)
      hlu hov hou hFv hFu hjv hle).symm

/-- The senders into `P` and the ledger `v_P(N) = Σ_senders v_P(σ(u ^ e_u))` (a copy of a
private lemma of `OddPerfect/LargestPrimeCapacity.lean`). -/
private theorem lpf_sum_senders (h : OddPerfect N) (hP : P ∈ N.primeFactors) :
    N.factorization P = ∑ p ∈ (N.primeFactors.erase P).filter
      (fun p => P ∣ σ 1 (p ^ N.factorization p)), padicValNat P (σ 1 (p ^ N.factorization p)) := by
  have hP2 : P ≠ 2 := by have := lpf_odd_of_mem h hP; omega
  rw [factorization_eq_sum_erase h.perfect (Nat.prime_of_mem_primeFactors hP) hP2,
    Finset.sum_filter_of_ne]
  intro p _ hne
  by_contra hd
  exact hne (padicValNat.eq_zero_of_not_dvd hd)

/-- **Largest prime factor `4 R + 1`: it is the special prime.** Let the largest prime factor
of an odd perfect number `N` be `P = 4 R + 1` with `R > 3` prime. Then `v_P(N)` is odd,
`v_P(N) ≡ 1 (mod 4)`, `5 ≤ v_P(N) < R`, and there is a prime factor `u ≠ P` with
`v_u(N) = R - 1` and `1 + u + ⋯ + u ^ (R - 1) = P ^ v_P(N)`. These are necessary conditions in
a restricted case; the later module `LargestPrimeFourNone` excludes the case `P = 4 R + 1`.
The odd perfect number conjecture remains open. No published source was checked; novelty not
verified. -/
theorem largest_four_special (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) (hR3 : 3 < R) (hPR : P = 4 * R + 1) :
    Odd (N.factorization P) ∧ N.factorization P % 4 = 1 ∧ 5 ≤ N.factorization P ∧
      N.factorization P < R ∧
      ∃ u ∈ N.primeFactors, u ≠ P ∧ N.factorization u = R - 1 ∧
        ∑ i ∈ Finset.range R, u ^ i = P ^ N.factorization P := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hRo := Nat.odd_iff.mp (hR.odd_of_ne_two (by omega))
  set S := (N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p))
    with hSdef
  have hsum := lpf_sum_senders h hP
  rw [← hSdef] at hsum
  have hpos : N.factorization P ≠ 0 := Finsupp.mem_support_iff.mp hP
  obtain ⟨u, huS⟩ : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hS
    rw [hS, Finset.sum_empty] at hsum
    exact hpos hsum
  have huS' := huS
  rw [hSdef, Finset.mem_filter, Finset.mem_erase] at huS'
  obtain ⟨⟨huP, hu⟩, hd⟩ := huS'
  have hS : S = {u} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨huS, fun x hx => ?_⟩
    rw [hSdef, Finset.mem_filter, Finset.mem_erase] at hx
    exact largest_four_sender_unique h hP hmax hR hR3 hPR hx.1.2 hx.1.1 hx.2 hu huP hd
  rw [hS, Finset.sum_singleton] at hsum
  obtain ⟨he, -, hrow, -⟩ := largest_four_sender_row h hP hmax hR hR3 hPR hu huP
    (lpf_even_of_sender h hP hmax hR hR3 hPR hu huP hd) hd
  rw [← hsum] at hrow
  have hup := Nat.prime_of_mem_primeFactors hu
  have hu2 := lpf_odd_of_mem h hu
  have hu3 : 3 ≤ u := by have := hup.two_le; omega
  set j := N.factorization P with hjdef
  -- parity: an even `j` makes the row a square
  have hodd : Odd j := by
    rcases Nat.even_or_odd j with ⟨m, hm⟩ | ho
    · exfalso
      have hsq : IsSquare (σ 1 (u ^ (R - 1))) :=
        ⟨P ^ m, by
          rw [sigma_one_apply_prime_pow hup, Nat.sub_add_cancel hR.one_le, hrow, hm, pow_add]⟩
      have := (isSquare_sigma_prime_pow_iff hup (by omega) ⟨(R - 1) / 2, by omega⟩
        (by omega)).mp hsq
      have hR5 : R = 5 := by omega
      rw [hR5] at hPR
      rw [hPR] at hPp
      norm_num at hPp
    · exact ho
  have hj4 : j % 4 = 1 := (special_mod_four h hPp hodd).2
  -- size: the row exceeds `P`
  have hbigF : 4 * R + 1 < ∑ i ∈ Finset.range R, u ^ i := by
    have h1 : u ^ (R - 1) ≤ ∑ i ∈ Finset.range R, u ^ i :=
      Finset.single_le_sum (f := fun i => u ^ i) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
    have h2 : 3 ^ (R - 1) ≤ u ^ (R - 1) := Nat.pow_le_pow_left hu3 _
    exact lt_of_lt_of_le (lpf_three_pow (show 5 ≤ R by omega)) (h2.trans h1)
  have hj1 : j ≠ 1 := by
    intro hj
    rw [hj, pow_one] at hrow
    omega
  -- `P ^ j = F(u) < u ^ R < P ^ R`
  have hgeo := geom_sum_mul_add (u - 1) R
  rw [Nat.sub_add_cancel hup.one_lt.le] at hgeo
  have hlt1 : ∑ i ∈ Finset.range R, u ^ i < u ^ R := by
    have : ∑ i ∈ Finset.range R, u ^ i ≤ (∑ i ∈ Finset.range R, u ^ i) * (u - 1) :=
      le_mul_of_one_le_right (Nat.zero_le _) (by omega)
    omega
  obtain ⟨hult, -⟩ := sender_largest_data h hP hmax hu huP hd
  have hlt2 : u ^ R < P ^ R := Nat.pow_lt_pow_left hult (by omega)
  have hPj : P ^ j < P ^ R := by rw [← hrow]; exact hlt1.trans hlt2
  have hjR : j < R := by
    by_contra hc
    have := Nat.pow_le_pow_right hPp.pos (show R ≤ j by omega)
    omega
  exact ⟨hodd, hj4, by omega, hjR, u, hu, huP, he, hrow⟩

/-! ## Controls -/

/-- The arithmetic of `R`: for `R = 7`, `P = 29` is prime and `2 R + 1 = 15 = 3 · 5`. -/
example : Nat.Prime 29 ∧ 2 * 7 + 1 = 3 * 5 := by norm_num

end OddPerfect

#print axioms OddPerfect.largest_four_sender_row
#print axioms OddPerfect.largest_four_special_not_sender
#print axioms OddPerfect.largest_four_sender_unique
#print axioms OddPerfect.largest_four_special
