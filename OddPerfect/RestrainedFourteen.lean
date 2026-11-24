import OddPerfect.RestrainedEight
import OddPerfect.DefectRules

/-!
# Restrained odd perfect numbers: the prime row inequality

Setting of `restrained_omega_le`: `N` is an odd perfect number with special prime `q`, `r ≠ q`
is a further prime, and every prime factor other than `q` and `r` has exponent exactly 2. The
landed results give `r = 3`, and every prime factor other than `3` and `q` is at least
`B = 132257` (`restrained_le_of_ne_three`).

Notation (namespace `OddPerfect.RestrainedFourteen`):
* `ordPrimes N q` (the set `R`): the prime factors of `N` other than `3` and `q`;
* `ordOne N q` and `ordTwo N q` (`O1`, `O2`): the members of `R` that are 1, respectively 2,
  modulo 3;
* `rowCount N q s` (`k s`): `∑ t ∈ R, v_t(s ^ 2 + s + 1)`, the number of ordinary primes in the
  row of `s`, with multiplicity;
* `lightRows N q` (`K1`): the members `s` of `R` with `k s ≤ 1`;
* `recipSum X` (`S1 X`): `∑ s ∈ X, 1 / s` in `ℚ`.

Results.
* `restrained_recip_row_ineq`:
  `(183/250) S1 (O1 \ K1) + (132257/132258) S1 (O2 \ K1) ≤ S1 (O1 ∩ K1)`.
* `restrained_recip_total_le`: `S1 R ≤ (433/183) S1 (O1 ∩ K1) + S1 (O2 ∩ K1)`.
* `restrained_recip_two_le`: `S1 (O2 \ K1) ≤ (132258/132257) S1 (O1 ∩ K1)`.
* `restrained_light_row_shape`: a row in `K1` not divisible by `q` is `t` or `3 t` with `t` a
  prime in `O1`.

Proof. Each `t ∈ R` has exponent 2, so the rows of the members of `R` feed `t` at most 2 in
total (`sum_sigmaWeight_le_factorization`). With `ρ s = ∑ t ∈ O1, v_t(s ^ 2 + s + 1) / t` this
gives `∑ s ∈ R, ρ s ≤ 2 S1 O1`. A row with `k s ≥ 2` contains `t₁ t₂` (and also the factor 3
when `s ≡ 1 (mod 3)`), so `3 ^ ε t₁ t₂ < (s + 1) ^ 2`, and comparing squares gives
`ρ s ≥ 1/t₁ + 1/t₂ ≥ 2 β / (s + 1)` with `β = 173205/100000` when `ε = 1` and `β = 1` otherwise.
Since `s ≥ B` this is at least `2 β (B/(B+1)) / s`, and summing over `R \ K1` gives the
inequality.

This inequality does not close the family; it moves the question to the rows with at most one
ordinary prime, whose reciprocal sum is not bounded here.

Status: conditional family result; whether it is in the literature was not verified. The odd
perfect number conjecture is open and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace RestrainedFourteen

open RestrainedSeven

/-- The set `R`: the prime factors of `N` other than `3` and `q`. -/
def ordPrimes (N q : ℕ) : Finset ℕ := N.primeFactors.filter (fun p => p ≠ 3 ∧ p ≠ q)

/-- The set `O1`: the members of `ordPrimes N q` that are 1 modulo 3. -/
def ordOne (N q : ℕ) : Finset ℕ := (ordPrimes N q).filter (fun p => p % 3 = 1)

/-- The set `O2`: the members of `ordPrimes N q` that are 2 modulo 3. -/
def ordTwo (N q : ℕ) : Finset ℕ := (ordPrimes N q).filter (fun p => p % 3 = 2)

/-- The number `k s` of ordinary primes in the row `phi3 s = s ^ 2 + s + 1`, with
multiplicity. -/
def rowCount (N q s : ℕ) : ℕ := ∑ t ∈ ordPrimes N q, (phi3 s).factorization t

/-- The set `K1`: the members `s` of `ordPrimes N q` with `rowCount N q s ≤ 1`. -/
def lightRows (N q : ℕ) : Finset ℕ := (ordPrimes N q).filter (fun s => rowCount N q s ≤ 1)

/-- The reciprocal sum `S1 X = ∑ s ∈ X, 1 / s` in `ℚ`. -/
def recipSum (X : Finset ℕ) : ℚ := ∑ s ∈ X, (1 / s : ℚ)

/-- The weight `ρ s = ∑ t ∈ O1, v_t(phi3 s) / t` of the row of `s`. -/
def rowWeight (N q s : ℕ) : ℚ := ∑ t ∈ ordOne N q, ((phi3 s).factorization t : ℚ) / t

/-- Unpacking membership in `ordPrimes N q`. -/
theorem mem_ord {N q s : ℕ} (F : Fam N q) (hs : s ∈ ordPrimes N q) :
    s.Prime ∧ s ∈ N.primeFactors ∧ s ≠ 3 ∧ s ≠ q ∧ N.factorization s = 2 := by
  obtain ⟨hsN, hs3, hsq⟩ := Finset.mem_filter.mp hs
  exact ⟨Nat.prime_of_mem_primeFactors hsN, hsN, hs3, hsq, F.sq s hsN hsq hs3⟩

/-- A prime other than `3` is 1 or 2 modulo 3. -/
theorem mod_three_of_prime {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : p % 3 = 1 ∨ p % 3 = 2 := by
  have : ¬ 3 ∣ p := fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd).symm
  omega

/-- For `s ∈ R` the sigma weight of `s` at `t` is the exponent of `t` in `phi3 s`. -/
theorem weight_eq {N q s t : ℕ} (F : Fam N q) (hs : s ∈ ordPrimes N q) :
    sigmaWeight N s t = (phi3 s).factorization t := by
  obtain ⟨hsp, -, -, -, h2⟩ := mem_ord F hs
  unfold sigmaWeight
  rw [h2, sigma_prime_sq hsp]

/-- Capacity: the rows of the members of `R` feed `t ∈ R` at most 2 in total. -/
theorem capacity {N q t : ℕ} (F : Fam N q) (ht : t ∈ ordPrimes N q) :
    ∑ s ∈ ordPrimes N q, (phi3 s).factorization t ≤ 2 := by
  obtain ⟨htp, htN, -, -, h2⟩ := mem_ord F ht
  have ht2 : t ≠ 2 := by
    rintro rfl
    exact F.perf.not_two_dvd (Nat.dvd_of_mem_primeFactors htN)
  have hc := sum_sigmaWeight_le_factorization F.perf htp ht2
    (S := ordPrimes N q) (Finset.filter_subset _ _)
  rw [h2] at hc
  calc ∑ s ∈ ordPrimes N q, (phi3 s).factorization t
      = ∑ s ∈ ordPrimes N q, sigmaWeight N s t :=
        Finset.sum_congr rfl (fun s hs => (weight_eq F hs).symm)
    _ ≤ 2 := hc

/-- The weighted sum: `∑ s ∈ R, ρ s ≤ 2 S1 O1`. -/
theorem sum_rowWeight_le {N q : ℕ} (F : Fam N q) :
    ∑ s ∈ ordPrimes N q, rowWeight N q s ≤ 2 * recipSum (ordOne N q) := by
  unfold rowWeight recipSum
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun t ht => ?_
  have htR : t ∈ ordPrimes N q := (Finset.mem_filter.mp ht).1
  have hc : ((∑ s ∈ ordPrimes N q, (phi3 s).factorization t : ℕ) : ℚ) ≤ 2 := by
    exact_mod_cast capacity F htR
  push_cast at hc
  have htpos : (0 : ℚ) < t := by exact_mod_cast (mem_ord F htR).1.pos
  calc ∑ s ∈ ordPrimes N q, ((phi3 s).factorization t : ℚ) / t
      = (∑ s ∈ ordPrimes N q, ((phi3 s).factorization t : ℚ)) * (1 / t) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun s _ => by ring)
    _ ≤ 2 * (1 / t) := mul_le_mul_of_nonneg_right hc (by positivity)

/-- The weight of a row is nonnegative. -/
theorem rowWeight_nonneg (N q s : ℕ) : 0 ≤ rowWeight N q s :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- A row with `k s ≥ 2` has a prime `t ∈ R` of exponent at least 2, or two distinct primes
of `R`. -/
theorem two_receivers {N q s : ℕ} (hk : 2 ≤ rowCount N q s) :
    ∃ t₁ ∈ ordPrimes N q, ∃ t₂ ∈ ordPrimes N q,
      (t₁ = t₂ ∧ 2 ≤ (phi3 s).factorization t₁) ∨
      (t₁ ≠ t₂ ∧ 1 ≤ (phi3 s).factorization t₁ ∧ 1 ≤ (phi3 s).factorization t₂) := by
  unfold rowCount at hk
  by_cases h2 : ∃ t ∈ ordPrimes N q, 2 ≤ (phi3 s).factorization t
  · obtain ⟨t, ht, h⟩ := h2
    exact ⟨t, ht, t, ht, Or.inl ⟨rfl, h⟩⟩
  push Not at h2
  have h1 : ∃ t ∈ ordPrimes N q, 1 ≤ (phi3 s).factorization t := by
    by_contra hc
    push Not at hc
    have : ∑ t ∈ ordPrimes N q, (phi3 s).factorization t = 0 :=
      Finset.sum_eq_zero fun t ht => by have := hc t ht; omega
    omega
  obtain ⟨t₁, ht₁, h₁⟩ := h1
  have hsplit : (phi3 s).factorization t₁ +
      ∑ t ∈ (ordPrimes N q).erase t₁, (phi3 s).factorization t =
      ∑ t ∈ ordPrimes N q, (phi3 s).factorization t := Finset.add_sum_erase _ _ ht₁
  have hle := h2 t₁ ht₁
  have h1' : ∃ t ∈ (ordPrimes N q).erase t₁, 1 ≤ (phi3 s).factorization t := by
    by_contra hc
    push Not at hc
    have : ∑ t ∈ (ordPrimes N q).erase t₁, (phi3 s).factorization t = 0 :=
      Finset.sum_eq_zero fun t ht => by have := hc t ht; omega
    omega
  obtain ⟨t₂, ht₂, h₂⟩ := h1'
  obtain ⟨hne, ht₂R⟩ := Finset.mem_erase.mp ht₂
  exact ⟨t₁, ht₁, t₂, ht₂R, Or.inr ⟨hne.symm, h₁, h₂⟩⟩

/-- A row with `k s ≥ 2` contains `t₁ t₂` with `t₁, t₂ ∈ O1` and `ρ s ≥ 1/t₁ + 1/t₂`. -/
theorem row_pair {N q s : ℕ} (F : Fam N q) (hk : 2 ≤ rowCount N q s) :
    ∃ t₁ ∈ ordOne N q, ∃ t₂ ∈ ordOne N q, t₁ * t₂ ∣ phi3 s ∧
      1 / (t₁ : ℚ) + 1 / t₂ ≤ rowWeight N q s := by
  have hn : phi3 s ≠ 0 := by unfold phi3; omega
  have hO : ∀ t ∈ ordPrimes N q, 1 ≤ (phi3 s).factorization t → t ∈ ordOne N q := by
    intro t ht h1
    obtain ⟨htp, -, ht3, -, -⟩ := mem_ord F ht
    have hd : t ∣ phi3 s := Nat.dvd_of_factorization_pos (by omega)
    exact Finset.mem_filter.mpr ⟨ht, prime_dvd_phi3_mod_three htp ht3 hd⟩
  have hnn : ∀ t ∈ ordOne N q, (0 : ℚ) ≤ ((phi3 s).factorization t : ℚ) / t :=
    fun t _ => by positivity
  obtain ⟨t₁, ht₁, t₂, ht₂, h | h⟩ := two_receivers hk
  · obtain ⟨he, h2⟩ := h
    subst he
    have hp := (mem_ord F ht₁).1
    have hO1 := hO t₁ ht₁ (by omega)
    refine ⟨t₁, hO1, t₁, hO1, ?_, ?_⟩
    · rw [← pow_two]
      exact (hp.pow_dvd_iff_le_factorization hn).mpr h2
    · have hsingle := Finset.single_le_sum hnn hO1
      have h2' : (2 : ℚ) ≤ ((phi3 s).factorization t₁ : ℚ) := by exact_mod_cast h2
      unfold rowWeight
      refine le_trans ?_ hsingle
      calc 1 / (t₁ : ℚ) + 1 / t₁ = 2 / t₁ := by ring
        _ ≤ _ := by gcongr
  · obtain ⟨hne, h1, h2⟩ := h
    have hp1 := (mem_ord F ht₁).1
    have hp2 := (mem_ord F ht₂).1
    have hO1 := hO t₁ ht₁ h1
    have hO2 := hO t₂ ht₂ h2
    refine ⟨t₁, hO1, t₂, hO2, ?_, ?_⟩
    · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp1 hp2).mpr hne)
        (Nat.dvd_of_factorization_pos (by omega)) (Nat.dvd_of_factorization_pos (by omega))
    · have hsub : ({t₁, t₂} : Finset ℕ) ⊆ ordOne N q := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hO1
        · rw [Finset.mem_singleton.mp hx]
          exact hO2
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t ht _ => hnn t ht)
      rw [Finset.sum_pair hne] at hle
      unfold rowWeight
      refine le_trans ?_ hle
      have h1' : (1 : ℚ) ≤ ((phi3 s).factorization t₁ : ℚ) := by exact_mod_cast h1
      have h2' : (1 : ℚ) ≤ ((phi3 s).factorization t₂ : ℚ) := by exact_mod_cast h2
      gcongr

/-- Comparison of squares: if `β ^ 2 ≤ c` and `c a b ≤ x ^ 2`, then
`2 β / x ≤ 1/a + 1/b`. -/
theorem two_mul_div_le {a b x c β : ℚ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hβ : 0 ≤ β)
    (hc : β ^ 2 ≤ c) (h : c * (a * b) ≤ x ^ 2) : 2 * β / x ≤ 1 / a + 1 / b := by
  have hab : 0 < a * b := mul_pos ha hb
  rw [div_add_div _ _ ha.ne' hb.ne', div_le_div_iff₀ hx hab]
  have h3 : 4 * (a * b) ≤ (a + b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h1 : β ^ 2 * (a * b) ≤ x ^ 2 := le_trans (mul_le_mul_of_nonneg_right hc hab.le) h
  have hsq : (2 * β * (a * b)) ^ 2 ≤ ((1 * b + a * 1) * x) ^ 2 := by
    calc (2 * β * (a * b)) ^ 2 = 4 * (a * b) * (β ^ 2 * (a * b)) := by ring
      _ ≤ 4 * (a * b) * x ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (a + b) ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg x)
      _ = ((1 * b + a * 1) * x) ^ 2 := by ring
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq

/-- For `s ≥ B`: `2 β (B/(B+1)) (1/s) ≤ 2 β / (s + 1)`. -/
theorem scale_le {β s : ℚ} (hβ : 0 ≤ β) (hs : 132257 ≤ s) :
    2 * β * (132257 / 132258) * (1 / s) ≤ 2 * β / (s + 1) := by
  rw [mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hs)]

/-- The cost of a row with `k s ≥ 2`, for a constant `c` that bounds `c t₁ t₂` by
`(s + 1) ^ 2` whenever `t₁ t₂` divides the row. -/
theorem row_bound {N q s : ℕ} (F : Fam N q) (hB : 132257 ≤ s) (hk : 2 ≤ rowCount N q s)
    {β c : ℚ} (hβ : 0 ≤ β) (hc : β ^ 2 ≤ c)
    (hdiv : ∀ t₁ t₂ : ℕ, t₁.Prime → t₂.Prime → t₁ ≠ 3 → t₂ ≠ 3 → t₁ * t₂ ∣ phi3 s →
      c * ((t₁ : ℚ) * t₂) ≤ ((s : ℚ) + 1) ^ 2) :
    2 * β * (132257 / 132258) * (1 / (s : ℚ)) ≤ rowWeight N q s := by
  obtain ⟨t₁, ht₁, t₂, ht₂, hd, hle⟩ := row_pair F hk
  obtain ⟨hp1, -, h13, -, -⟩ := mem_ord F (Finset.mem_filter.mp ht₁).1
  obtain ⟨hp2, -, h23, -, -⟩ := mem_ord F (Finset.mem_filter.mp ht₂).1
  have hsB : (132257 : ℚ) ≤ s := by exact_mod_cast hB
  have h1 : (0 : ℚ) < t₁ := by exact_mod_cast hp1.pos
  have h2 : (0 : ℚ) < t₂ := by exact_mod_cast hp2.pos
  calc 2 * β * (132257 / 132258) * (1 / (s : ℚ)) ≤ 2 * β / ((s : ℚ) + 1) := scale_le hβ hsB
    _ ≤ 1 / (t₁ : ℚ) + 1 / t₂ :=
        two_mul_div_le h1 h2 (by linarith) hβ hc (hdiv t₁ t₂ hp1 hp2 h13 h23 hd)
    _ ≤ rowWeight N q s := hle

/-- Rows of `O2` with `k s ≥ 2`: `ρ s ≥ 2 (B/(B+1)) / s`. -/
theorem row_bound_two {N q s : ℕ} (F : Fam N q) (hB : 132257 ≤ s) (hk : 2 ≤ rowCount N q s) :
    2 * 1 * (132257 / 132258) * (1 / (s : ℚ)) ≤ rowWeight N q s := by
  refine row_bound F hB hk (β := 1) (c := 1) zero_le_one (by norm_num)
    fun t₁ t₂ hp1 hp2 _ _ hd => ?_
  have hn : 0 < phi3 s := by unfold phi3; omega
  have hlt : t₁ * t₂ < (s + 1) ^ 2 :=
    lt_of_le_of_lt (Nat.le_of_dvd hn hd) (phi3_lt_succ_sq (by omega))
  have : ((t₁ * t₂ : ℕ) : ℚ) ≤ ((s + 1) ^ 2 : ℕ) := by exact_mod_cast hlt.le
  push_cast at this
  linarith

/-- Rows of `O1` with `k s ≥ 2`: `ρ s ≥ 2 β (B/(B+1)) / s` with `β = 173205/100000`. -/
theorem row_bound_one {N q s : ℕ} (F : Fam N q) (hB : 132257 ≤ s) (h31 : s % 3 = 1)
    (hk : 2 ≤ rowCount N q s) :
    2 * (173205 / 100000) * (132257 / 132258) * (1 / (s : ℚ)) ≤ rowWeight N q s := by
  refine row_bound F hB hk (by norm_num) (c := 3) (by norm_num)
    fun t₁ t₂ hp1 hp2 h13 h23 hd => ?_
  have hn : 0 < phi3 s := by unfold phi3; omega
  have hcop : Nat.Coprime 3 (t₁ * t₂) :=
    Nat.Coprime.mul_right ((Nat.coprime_primes Nat.prime_three hp1).mpr (Ne.symm h13))
      ((Nat.coprime_primes Nat.prime_three hp2).mpr (Ne.symm h23))
  have hd3 : 3 * (t₁ * t₂) ∣ phi3 s :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop ((three_dvd_phi3_iff s).mpr h31) hd
  have hlt : 3 * (t₁ * t₂) < (s + 1) ^ 2 :=
    lt_of_le_of_lt (Nat.le_of_dvd hn hd3) (phi3_lt_succ_sq (by omega))
  have : ((3 * (t₁ * t₂) : ℕ) : ℚ) ≤ ((s + 1) ^ 2 : ℕ) := by exact_mod_cast hlt.le
  push_cast at this
  linarith

/-- The basic inequality in the form used by the corollaries, from the family structure and
the lower bound `B` on the members of `R`. -/
theorem row_ineq_core {N q : ℕ} (F : Fam N q) (hB : ∀ s ∈ ordPrimes N q, 132257 ≤ s) :
    (183 / 250 : ℚ) * recipSum (ordOne N q \ lightRows N q) +
      (132257 / 132258) * recipSum (ordTwo N q \ lightRows N q) ≤
      recipSum (ordOne N q ∩ lightRows N q) := by
  set A := ordOne N q \ lightRows N q with hA
  set C := ordTwo N q \ lightRows N q with hC
  have hheavy : ∀ s, s ∈ ordPrimes N q → s ∉ lightRows N q → 2 ≤ rowCount N q s := by
    intro s hs hl
    by_contra hk
    exact hl (Finset.mem_filter.mpr ⟨hs, by omega⟩)
  have hrowA : ∀ s ∈ A, 2 * (173205 / 100000) * (132257 / 132258) * (1 / (s : ℚ)) ≤
      rowWeight N q s := by
    intro s hs
    obtain ⟨hs1, hsl⟩ := Finset.mem_sdiff.mp hs
    obtain ⟨hsR, h31⟩ := Finset.mem_filter.mp hs1
    exact row_bound_one F (hB s hsR) h31 (hheavy s hsR hsl)
  have hrowC : ∀ s ∈ C, 2 * 1 * (132257 / 132258) * (1 / (s : ℚ)) ≤ rowWeight N q s := by
    intro s hs
    obtain ⟨hs1, hsl⟩ := Finset.mem_sdiff.mp hs
    obtain ⟨hsR, -⟩ := Finset.mem_filter.mp hs1
    exact row_bound_two F (hB s hsR) (hheavy s hsR hsl)
  have hsA : 2 * (173205 / 100000) * (132257 / 132258) * recipSum A ≤
      ∑ s ∈ A, rowWeight N q s := by
    unfold recipSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hrowA
  have hsC : 2 * 1 * (132257 / 132258) * recipSum C ≤ ∑ s ∈ C, rowWeight N q s := by
    unfold recipSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hrowC
  have hdisj : Disjoint A C := by
    refine Finset.disjoint_left.mpr fun s hsA hsC => ?_
    have h1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hsA).1).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hsC).1).2
    omega
  have hsub : A ∪ C ⊆ ordPrimes N q := by
    intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hs).1).1
    · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hs).1).1
  have hU : ∑ s ∈ A ∪ C, rowWeight N q s ≤ ∑ s ∈ ordPrimes N q, rowWeight N q s :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => rowWeight_nonneg N q s)
  rw [Finset.sum_union hdisj] at hU
  have hW := sum_rowWeight_le F
  have hsplit : recipSum (ordOne N q ∩ lightRows N q) + recipSum A = recipSum (ordOne N q) :=
    Finset.sum_inter_add_sum_sdiff _ _ _
  have hA0 : 0 ≤ recipSum A := Finset.sum_nonneg fun _ _ => by positivity
  linarith

/-- `S1 R = S1 (O1 ∩ K1) + S1 (O1 \ K1) + S1 (O2 ∩ K1) + S1 (O2 \ K1)`. -/
theorem recipSum_split {N q : ℕ} (F : Fam N q) :
    recipSum (ordPrimes N q) = recipSum (ordOne N q ∩ lightRows N q) +
      recipSum (ordOne N q \ lightRows N q) + recipSum (ordTwo N q ∩ lightRows N q) +
      recipSum (ordTwo N q \ lightRows N q) := by
  have h2 : (ordPrimes N q).filter (fun p => ¬ p % 3 = 1) = ordTwo N q := by
    refine Finset.filter_congr fun p hp => ?_
    obtain ⟨hpp, -, hp3, -, -⟩ := mem_ord F hp
    have := mod_three_of_prime hpp hp3
    omega
  have hR : recipSum (ordPrimes N q) = recipSum (ordOne N q) + recipSum (ordTwo N q) := by
    unfold recipSum ordOne
    rw [← h2]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h1 : recipSum (ordOne N q ∩ lightRows N q) + recipSum (ordOne N q \ lightRows N q) =
      recipSum (ordOne N q) := Finset.sum_inter_add_sum_sdiff _ _ _
  have h3 : recipSum (ordTwo N q ∩ lightRows N q) + recipSum (ordTwo N q \ lightRows N q) =
      recipSum (ordTwo N q) := Finset.sum_inter_add_sum_sdiff _ _ _
  linarith

/-- The shape of a light row: if `phi3 s = e m` with `e ≤ 3`, `3 ∤ m` and `q ∤ phi3 s`, then
`m` is a prime of `O1`. -/
theorem light_core {N q s e m : ℕ} (F : Fam N q) (hs : s ∈ ordPrimes N q) (hB : 132257 ≤ s)
    (hk : rowCount N q s ≤ 1) (hqs : ¬ q ∣ phi3 s) (hm : phi3 s = e * m) (he : e ≤ 3)
    (h3 : ¬ 3 ∣ m) : m ∈ ordOne N q := by
  have hn : phi3 s ≠ 0 := by unfold phi3; omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    have h4 : phi3 s ≤ 3 := by rw [hm]; omega
    unfold phi3 at h4
    nlinarith
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn (by rw [hm, mul_zero])
  have hmem : ∀ p, p.Prime → p ∣ m → p ∈ ordPrimes N q ∧ 1 ≤ (phi3 s).factorization p := by
    intro p hp hpm
    have hpn : p ∣ phi3 s := hm ▸ Dvd.dvd.mul_left hpm e
    have hpos := hp.factorization_pos_of_dvd hn hpn
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr (phi3_odd s)) (even_iff_two_dvd.mpr hpn)
    have hw : sigmaWeight N s p ≠ 0 := by
      rw [weight_eq F hs]
      omega
    have hpN := mem_primeFactors_of_sigmaWeight_ne_zero F.perf.perfect (mem_ord F hs).2.1 hp2 hw
    refine ⟨Finset.mem_filter.mpr ⟨hpN, ?_, ?_⟩, hpos⟩
    · rintro rfl
      exact h3 hpm
    · rintro rfl
      exact hqs hpn
  have ht := Nat.minFac_prime hm1
  have htm := Nat.minFac_dvd m
  obtain ⟨htR, ht1⟩ := hmem _ ht htm
  have hrow : rowCount N q s = ∑ t ∈ ordPrimes N q, (phi3 s).factorization t := rfl
  have hmt : m = m.minFac := by
    by_contra hne
    obtain ⟨u, hu⟩ := htm
    have hu1 : u ≠ 1 := by
      rintro rfl
      exact hne (hu.trans (mul_one _))
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hm0 (by rw [hu, mul_zero])
    have ht' := Nat.minFac_prime hu1
    have htu : u.minFac ∣ m := hu ▸ Dvd.dvd.mul_left (Nat.minFac_dvd u) _
    have hmn : m ∣ phi3 s := hm ▸ Dvd.intro_left e rfl
    by_cases heq : u.minFac = m.minFac
    · have hdu : m.minFac ∣ u := by
        rw [← heq]
        exact Nat.minFac_dvd u
      have hsq : m.minFac ^ 2 ∣ phi3 s :=
        calc m.minFac ^ 2 = m.minFac * m.minFac := pow_two _
          _ ∣ m.minFac * u := Nat.mul_dvd_mul_left _ hdu
          _ = m := hu.symm
          _ ∣ phi3 s := hmn
      have h2 := (ht.pow_dvd_iff_le_factorization hn).mp hsq
      have := Finset.single_le_sum (fun t _ => Nat.zero_le ((phi3 s).factorization t)) htR
      omega
    · obtain ⟨htR', ht1'⟩ := hmem _ ht' htu
      have hsub : ({m.minFac, u.minFac} : Finset ℕ) ⊆ ordPrimes N q := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact htR
        · rw [Finset.mem_singleton.mp hx]
          exact htR'
      have hle := Finset.sum_le_sum_of_subset (f := fun t => (phi3 s).factorization t) hsub
      rw [Finset.sum_pair (Ne.symm heq)] at hle
      omega
  have hmd : m ∣ phi3 s := hm ▸ Dvd.intro_left e rfl
  have ht3 : m.minFac ≠ 3 := fun h => h3 (h ▸ Nat.minFac_dvd m)
  rw [hmt]
  exact Finset.mem_filter.mpr ⟨htR, prime_dvd_phi3_mod_three ht ht3
    ((Nat.minFac_dvd m).trans hmd)⟩

end RestrainedFourteen

open RestrainedFourteen RestrainedSeven

/-- **Restrained family: the prime row inequality.**
`(183/250) S1 (O1 \ K1) + (132257/132258) S1 (O2 \ K1) ≤ S1 (O1 ∩ K1)`, where `R` is the set of
prime factors other than `3` and `q`, `O1` and `O2` its members that are 1 and 2 modulo 3, `K1`
its members whose row `s ^ 2 + s + 1` holds at most one prime of `R` (with multiplicity), and
`S1 X = ∑ s ∈ X, 1 / s`. This does not close the family: it moves the question to the rows with
at most one ordinary prime. Conditional family result; whether it is in the literature was not
verified. -/
theorem restrained_recip_row_ineq {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    (183 / 250 : ℚ) * recipSum (ordOne N q \ lightRows N q) +
      (132257 / 132258) * recipSum (ordTwo N q \ lightRows N q) ≤
      recipSum (ordOne N q ∩ lightRows N q) := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  refine row_ineq_core F fun s hs => ?_
  obtain ⟨-, hsN, hs3, -, -⟩ := mem_ord F hs
  exact restrained_le_of_ne_three h hq hodd hr hrq hsq hsN hs3

/-- **Restrained family: the reciprocal sum of `R`.**
`S1 R ≤ (433/183) S1 (O1 ∩ K1) + S1 (O2 ∩ K1)`, from `restrained_recip_row_ineq`.
Conditional family result; whether it is in the literature was not verified. -/
theorem restrained_recip_total_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    recipSum (ordPrimes N q) ≤
      (433 / 183 : ℚ) * recipSum (ordOne N q ∩ lightRows N q) +
        recipSum (ordTwo N q ∩ lightRows N q) := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hmain := restrained_recip_row_ineq h hq hodd hr hrq hsq
  have hsplit := recipSum_split F
  have hC0 : 0 ≤ recipSum (ordTwo N q \ lightRows N q) :=
    Finset.sum_nonneg fun _ _ => by positivity
  linarith

/-- **Restrained family: the heavy rows that are 2 modulo 3.**
`S1 (O2 \ K1) ≤ (132258/132257) S1 (O1 ∩ K1)`, from `restrained_recip_row_ineq`.
Conditional family result; whether it is in the literature was not verified. -/
theorem restrained_recip_two_le {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    recipSum (ordTwo N q \ lightRows N q) ≤
      (132258 / 132257 : ℚ) * recipSum (ordOne N q ∩ lightRows N q) := by
  have hmain := restrained_recip_row_ineq h hq hodd hr hrq hsq
  have hA0 : 0 ≤ recipSum (ordOne N q \ lightRows N q) :=
    Finset.sum_nonneg fun _ _ => by positivity
  linarith

/-- **Restrained family: the shape of a light row.** For `s ∈ K1` whose row is not divisible by
`q`: if `s ≡ 2 (mod 3)` the row `s ^ 2 + s + 1` is a prime `t ∈ O1`, and if `s ≡ 1 (mod 3)` it
is `3 t` with `t ∈ O1` (members of `O1` are prime factors of `N`, hence prime).
Conditional family result; whether it is in the literature was not verified. -/
theorem restrained_light_row_shape {N q r s : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hs : s ∈ lightRows N q) (hqs : ¬ q ∣ s ^ 2 + s + 1) :
    (s % 3 = 2 → ∃ t ∈ ordOne N q, s ^ 2 + s + 1 = t) ∧
      (s % 3 = 1 → ∃ t ∈ ordOne N q, s ^ 2 + s + 1 = 3 * t) := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  obtain ⟨hsR, hk⟩ := Finset.mem_filter.mp hs
  obtain ⟨-, hsN, hs3, -, -⟩ := mem_ord F hsR
  have hB := restrained_le_of_ne_three h hq hodd hr hrq hsq hsN hs3
  have hqs' : ¬ q ∣ phi3 s := hqs
  refine ⟨fun h32 => ?_, fun h31 => ?_⟩
  · have h3 : ¬ 3 ∣ phi3 s := fun hd => by
      have := (three_dvd_phi3_iff s).mp hd
      omega
    exact ⟨phi3 s, light_core F hsR hB hk hqs' (one_mul _).symm (by norm_num) h3, rfl⟩
  · obtain ⟨m, hm⟩ := (three_dvd_phi3_iff s).mpr h31
    have h3 : ¬ 3 ∣ m := fun hd => not_nine_dvd_phi3 s (by omega)
    exact ⟨m, light_core F hsR hB hk hqs' hm (by norm_num) h3, hm⟩

end OddPerfect

#print axioms OddPerfect.restrained_recip_row_ineq
#print axioms OddPerfect.restrained_recip_total_le
#print axioms OddPerfect.restrained_recip_two_le
#print axioms OddPerfect.restrained_light_row_shape
#print axioms OddPerfect.RestrainedFourteen.mem_ord
#print axioms OddPerfect.RestrainedFourteen.mod_three_of_prime
#print axioms OddPerfect.RestrainedFourteen.weight_eq
#print axioms OddPerfect.RestrainedFourteen.capacity
#print axioms OddPerfect.RestrainedFourteen.sum_rowWeight_le
#print axioms OddPerfect.RestrainedFourteen.rowWeight_nonneg
#print axioms OddPerfect.RestrainedFourteen.two_receivers
#print axioms OddPerfect.RestrainedFourteen.row_pair
#print axioms OddPerfect.RestrainedFourteen.two_mul_div_le
#print axioms OddPerfect.RestrainedFourteen.scale_le
#print axioms OddPerfect.RestrainedFourteen.row_bound
#print axioms OddPerfect.RestrainedFourteen.row_bound_two
#print axioms OddPerfect.RestrainedFourteen.row_bound_one
#print axioms OddPerfect.RestrainedFourteen.row_ineq_core
#print axioms OddPerfect.RestrainedFourteen.recipSum_split
#print axioms OddPerfect.RestrainedFourteen.light_core
