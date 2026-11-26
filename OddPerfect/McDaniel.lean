import OddPerfect.Euler
import OddPerfect.Abundancy
import OddPerfect.Seed.Example
import OddPerfect.Seed.ThreeFree
import Mathlib.NumberTheory.LucasPrimality

/-!
# McDaniel's theorem

McDaniel (1970): in an odd perfect number `N` with special prime `q`, the exponents of the
other primes cannot all be congruent to 2 modulo 3.

## Case `3 ∣ N`

Every non-special prime `t` has exponent at least 2 and forces every odd divisor of
`t^2+t+1`. The special prime `q` is `1 mod 4`, has odd exponent, and forces every odd
divisor of `q+1`. Primes that are `3 mod 4` are never special. Starting from `3` and `13`,
the tree below branches on whether a prime is special; each leaf exhibits an abundant
divisor of `N` (listed prime powers). Large primes are certified by Lucas witnesses.

```
13 special
  CLOSE 3^2 7^2 13^1 19^2 31^2 127^2 313^1 331^1  abundancy 2.00141
13 ordinary
  61 special
    CLOSE 3^2 7^2 13^2 19^1 31^2 61^1  abundancy 2.01144
  61 ordinary
    97 special
      CLOSE 3^2 7^2 13^2 19^2 31^1 61^2  abundancy 2.01524
    97 ordinary
      3169 special
        CLOSE 3^2 5^2 13^2 31^1  abundancy 2.00205
      3169 ordinary
        3348577 special
          CLOSE 3^2 7^2 13^2 19^1 43^1 61^2 79^2  abundancy 2.01796
        3348577 ordinary
          3737657091169 special
            CLOSE 3^2 5^2 13^2 31^1  abundancy 2.00205
          3737657091169 ordinary
            CLOSE 3^2 7^2 13^2 19^1 31^2 61^2  abundancy 2.01198
```

## Case `3 ∤ N`

Then no non-special prime is `1 mod 3`, so every prime factor of `p^2+p+1` is the special
prime: `p^2+p+1 = q^c` with `c ≥ 1`. Since `q ≥ 13` and `p ≥ 5`, we get `3^c < p`, and
distinct `p` give distinct `c`. Hence the abundancy of `N` is below
`(13/12) * ∏ (1 + 3^(-c)) ≤ (13/12) * (8/5) < 2`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace McDanielAux

private theorem sigma_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = p ^ 2 + p + 1 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]; ring

/-- An odd divisor of the divisor sum of an exact component divides the number. -/
private theorem odd_dvd_of_dvd_sigma {N p d : ℕ} (hN : N.Perfect) (hp : p.Prime) (hd : Odd d)
    (hdiv : d ∣ σ 1 (p ^ N.factorization p)) : d ∣ N := by
  have h2 := hdiv.trans (OPNStarter.component_sigma_dvd hN hp rfl)
  exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hd) h2

/-- A prime with exponent congruent to 2 mod 3 forces every odd divisor of `t^2+t+1`. -/
private theorem ord_dvd {N t d : ℕ} (hN : N.Perfect) (ht : t.Prime) (he : N.factorization t % 3 = 2)
    (hd : Odd d) (hdiv : d ∣ t ^ 2 + t + 1) : d ∣ N := by
  apply odd_dvd_of_dvd_sigma hN ht hd
  refine hdiv.trans ?_
  rw [← sigma_sq ht]
  exact OPNExample.sigma_prime_pow_dvd ht (by omega)

/-- A prime with exponent congruent to 2 mod 3 has its square dividing the number. -/
private theorem ord_sq {N t : ℕ} (hN : N.Perfect) (ht : t.Prime) (he : N.factorization t % 3 = 2) :
    t ^ 2 ∣ N :=
  (ht.pow_dvd_iff_le_factorization hN.2.ne').mpr (by omega)

/-- A prime with odd exponent forces every odd divisor of `q+1`. -/
private theorem spec_dvd {N q d : ℕ} (hN : N.Perfect) (hq : q.Prime) (ho : Odd (N.factorization q))
    (hd : Odd d) (hdiv : d ∣ q + 1) : d ∣ N := by
  apply odd_dvd_of_dvd_sigma hN hq hd
  refine hdiv.trans ?_
  have h1 : σ 1 (q ^ 1) = q + 1 := by
    rw [sigma_one_apply_prime_pow hq]; simp [Finset.sum_range_succ]; ring
  rw [← h1]
  obtain ⟨k, hk⟩ := ho
  exact OPNExample.sigma_prime_pow_dvd hq ⟨k + 1, by omega⟩

/-- One step of the abundant-divisor accumulation. -/
private theorem step {N D p a : ℕ} {A : ℚ} (h : D ∣ N ∧ abundancy D = A) (hp : p.Prime)
    (hpa : p ^ a ∣ N) (hc : ¬ p ∣ D) :
    D * p ^ a ∣ N ∧ abundancy (D * p ^ a) = A * ∑ i ∈ Finset.range (a + 1), ((p : ℚ)⁻¹) ^ i := by
  have hcop : D.Coprime (p ^ a) :=
    Nat.Coprime.pow_right a ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hc)))
  refine ⟨hcop.mul_dvd_of_dvd_of_dvd h.1 hpa, ?_⟩
  rw [abundancy_mul_of_coprime hcop, h.2, abundancy_prime_pow hp]

private theorem start (N : ℕ) : 1 ∣ N ∧ abundancy 1 = 1 := ⟨one_dvd N, by simp [abundancy]⟩


private theorem pr_3 : Nat.Prime 3 := by norm_num

private theorem pr_5 : Nat.Prime 5 := by norm_num

private theorem pr_7 : Nat.Prime 7 := by norm_num

private theorem pr_13 : Nat.Prime 13 := by norm_num

private theorem pr_19 : Nat.Prime 19 := by norm_num

private theorem pr_31 : Nat.Prime 31 := by norm_num

private theorem pr_43 : Nat.Prime 43 := by norm_num

private theorem pr_61 : Nat.Prime 61 := by norm_num

private theorem pr_79 : Nat.Prime 79 := by norm_num

private theorem pr_97 : Nat.Prime 97 := by norm_num

private theorem pr_127 : Nat.Prime 127 := by norm_num

private theorem pr_313 : Nat.Prime 313 := by norm_num

private theorem pr_331 : Nat.Prime 331 := by norm_num

private theorem pr_3169 : Nat.Prime 3169 := by norm_num

private theorem pr_5419 : Nat.Prime 5419 := by norm_num

private theorem pr_1674289 : Nat.Prime 1674289 := by norm_num

private theorem pr_3348577 : Nat.Prime 3348577 := by norm_num

private theorem pr_2 : Nat.Prime 2 := by norm_num

private theorem pr_811 : Nat.Prime 811 := by norm_num

private theorem pr_5351971 : Nat.Prime 5351971 := by norm_num

private theorem pr_26042690887 : Nat.Prime 26042690887 := by
  apply lucas_primality 26042690887 (5 : ZMod 26042690887)
  · change (5 : ZMod 26042690887) ^ 26042690886 = 1
    reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * 3 * 811 * 5351971 at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq pr_2,
      Nat.prime_dvd_prime_iff_eq hq pr_3,
      Nat.prime_dvd_prime_iff_eq hq pr_811,
      Nat.prime_dvd_prime_iff_eq hq pr_5351971] at hd
    rcases hd with (((rfl | rfl) | rfl) | rfl)
    · change (5 : ZMod 26042690887) ^ 13021345443 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 26042690887) ^ 8680896962 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 26042690887) ^ 32111826 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 26042690887) ^ 4866 ≠ 1
      reduce_mod_char
      decide

private theorem pr_11 : Nat.Prime 11 := by norm_num

private theorem pr_151 : Nat.Prime 151 := by norm_num

private theorem pr_12979 : Nat.Prime 12979 := by norm_num

private theorem pr_934415109937 : Nat.Prime 934415109937 := by
  apply lucas_primality 934415109937 (15 : ZMod 934415109937)
  · change (15 : ZMod 934415109937) ^ 934415109936 = 1
    reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * 2 * 2 * 2 * 3 * 3 * 7 * 11 * 43 * 151 * 12979 at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq pr_2,
      Nat.prime_dvd_prime_iff_eq hq pr_3,
      Nat.prime_dvd_prime_iff_eq hq pr_7,
      Nat.prime_dvd_prime_iff_eq hq pr_11,
      Nat.prime_dvd_prime_iff_eq hq pr_43,
      Nat.prime_dvd_prime_iff_eq hq pr_151,
      Nat.prime_dvd_prime_iff_eq hq pr_12979] at hd
    rcases hd with ((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · change (15 : ZMod 934415109937) ^ 467207554968 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 934415109937) ^ 467207554968 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 934415109937) ^ 467207554968 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 934415109937) ^ 467207554968 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 934415109937) ^ 311471703312 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 934415109937) ^ 311471703312 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 934415109937) ^ 133487872848 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 934415109937) ^ 84946828176 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 934415109937) ^ 21730583952 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 934415109937) ^ 6188179536 ≠ 1
      reduce_mod_char
      decide
    · change (15 : ZMod 934415109937) ^ 71994384 ≠ 1
      reduce_mod_char
      decide

private theorem pr_4519 : Nat.Prime 4519 := by norm_num

private theorem pr_3737657091169 : Nat.Prime 3737657091169 := by
  apply lucas_primality 3737657091169 (37 : ZMod 3737657091169)
  · change (37 : ZMod 3737657091169) ^ 3737657091168 = 1
    reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * 2 * 2 * 2 * 2 * 3 * 3 * 7 * 11 * 13 * 19 * 151 * 4519 at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq pr_2,
      Nat.prime_dvd_prime_iff_eq hq pr_3,
      Nat.prime_dvd_prime_iff_eq hq pr_7,
      Nat.prime_dvd_prime_iff_eq hq pr_11,
      Nat.prime_dvd_prime_iff_eq hq pr_13,
      Nat.prime_dvd_prime_iff_eq hq pr_19,
      Nat.prime_dvd_prime_iff_eq hq pr_151,
      Nat.prime_dvd_prime_iff_eq hq pr_4519] at hd
    rcases hd with ((((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · change (37 : ZMod 3737657091169) ^ 1868828545584 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 1868828545584 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 1868828545584 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 1868828545584 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 1868828545584 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 1245885697056 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 1245885697056 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 533951013024 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 339787008288 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 287512083936 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 196718794272 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 24752695968 ≠ 1
      reduce_mod_char
      decide
    · change (37 : ZMod 3737657091169) ^ 827098272 ≠ 1
      reduce_mod_char
      decide

/-- The partial products of `1 + 3^(-c)` over `1 ≤ c ≤ n+1`. -/
private theorem geom_prod_bound (n : ℕ) :
    ∏ c ∈ Finset.Ico 1 (n + 2), (1 + ((1 : ℚ) / 3) ^ c) ≤ 8 / 5 - 4 / 5 * (1 / 3) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_Ico_succ_top (by omega)]
    have hx : 0 ≤ ((1 : ℚ) / 3) ^ (n + 1) := by positivity
    have hpow : ((1 : ℚ) / 3) ^ (n + 1 + 1) = ((1 : ℚ) / 3) ^ (n + 1) / 3 := by ring
    rw [hpow]
    have h1 : 0 ≤ 1 + ((1 : ℚ) / 3) ^ (n + 1) / 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right ih h1]

/-- Over any set of positive exponents, the product of `1 + 3^(-c)` is at most `8/5`. -/
private theorem subset_prod_bound (T : Finset ℕ) (hT : ∀ c ∈ T, 1 ≤ c) :
    ∏ c ∈ T, (1 + ((1 : ℚ) / 3) ^ c) ≤ 8 / 5 := by
  have hsub : T ⊆ Finset.Ico 1 (T.sup id + 2) := by
    intro c hc
    have := Finset.le_sup (f := id) hc
    simp only [Finset.mem_Ico]
    exact ⟨hT c hc, by simp at this; omega⟩
  refine (Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun _ _ => by positivity)
    (fun i _ _ => by
      have : (0 : ℚ) ≤ (1 / 3) ^ i := by positivity
      linarith)).trans ?_
  refine (geom_prod_bound _).trans ?_
  have : (0 : ℚ) ≤ (1 / 3) ^ (T.sup id + 1) := by positivity
  linarith

private theorem pow_bound {c : ℕ} (hc : 2 ≤ c) : 9 ^ c + 3 ^ c + 1 < 13 ^ c := by
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ c hc ih =>
    have h3 : 3 ^ c ≤ 9 ^ c := Nat.pow_le_pow_left (by norm_num) c
    rw [pow_succ, pow_succ, pow_succ]
    omega

/-- If `p^2+p+1 = q^c` with `p ≥ 5` and `q ≥ 13`, then `c ≥ 1` and `3^c < p`. -/
private theorem three_pow_lt {p q c : ℕ} (hp : 5 ≤ p) (hq : 13 ≤ q) (h : p ^ 2 + p + 1 = q ^ c) :
    1 ≤ c ∧ 3 ^ c < p := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp at h
    omega
  refine ⟨Nat.one_le_iff_ne_zero.mpr hc, ?_⟩
  by_contra hle
  push Not at hle
  have h1 : p ^ 2 + p + 1 ≤ 9 ^ c + 3 ^ c + 1 := by
    have : p ^ 2 ≤ (3 ^ c) ^ 2 := Nat.pow_le_pow_left hle 2
    rw [← pow_mul, mul_comm, pow_mul] at this
    norm_num at this
    omega
  have h2 : 13 ^ c ≤ q ^ c := Nat.pow_le_pow_left hq c
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · have : c = 1 := by omega
    subst this
    omega
  · have := pow_bound hc2
    omega

end McDanielAux

open McDanielAux

/-- McDaniel, case `3 ∣ N`: a finite forcing tree closed by abundant divisors. -/
theorem mcdaniel_of_three_dvd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p % 3 = 2) (h3 : 3 ∣ N) : False := by
  have hN := h.perfect
  have hq4 : q % 4 = 1 := by
    obtain ⟨q', -, -, hq'4, -, hev⟩ := exists_special_prime h
    by_cases hqq : q = q'
    · subst hqq; exact hq'4
    · exact absurd (hev q hq hqq) (Nat.not_even_iff_odd.mpr hodd)
  have E : ∀ t, t.Prime → t ∣ N → t ≠ q → N.factorization t % 3 = 2 := fun t ht htN htq =>
    hexp t (Nat.mem_primeFactors.mpr ⟨ht, htN, h.ne_zero⟩) htq
  have ne3 : ∀ t, t % 4 = 3 → t ≠ q := by rintro t ht rfl; omega
  have d3 := h3
  by_cases hs13 : 13 = q
  · subst hs13
    have e3 := E 3 pr_3 d3 (ne3 3 (by norm_num))
    have d13 : 13 ∣ N := ord_dvd hN pr_3 e3 (by decide) (by norm_num)
    have d7 : 7 ∣ N := spec_dvd hN hq hodd (by decide) (by norm_num)
    have e7 := E 7 pr_7 d7 (ne3 7 (by norm_num))
    have d19 : 19 ∣ N := ord_dvd hN pr_7 e7 (by decide) (by norm_num)
    have e19 := E 19 pr_19 d19 (ne3 19 (by norm_num))
    have d127 : 127 ∣ N := ord_dvd hN pr_19 e19 (by decide) (by norm_num)
    have e127 := E 127 pr_127 d127 (ne3 127 (by norm_num))
    have d5419 : 5419 ∣ N := ord_dvd hN pr_127 e127 (by decide) (by norm_num)
    have e5419 := E 5419 pr_5419 d5419 (ne3 5419 (by norm_num))
    have d31 : 31 ∣ N := ord_dvd hN pr_5419 e5419 (by decide) (by norm_num)
    have e31 := E 31 pr_31 d31 (ne3 31 (by norm_num))
    have d313 : 313 ∣ N := ord_dvd hN pr_5419 e5419 (by decide) (by norm_num)
    have d331 : 331 ∣ N := ord_dvd hN pr_31 e31 (by decide) (by norm_num)
    have c := start N
    have c := step c pr_3 (ord_sq hN pr_3 e3) (by norm_num)
    have c := step c pr_7 (ord_sq hN pr_7 e7) (by norm_num)
    have c := step c (a := 1) pr_13 (by rw [pow_one]; exact d13) (by norm_num)
    have c := step c pr_19 (ord_sq hN pr_19 e19) (by norm_num)
    have c := step c pr_31 (ord_sq hN pr_31 e31) (by norm_num)
    have c := step c pr_127 (ord_sq hN pr_127 e127) (by norm_num)
    have c := step c (a := 1) pr_313 (by rw [pow_one]; exact d313) (by norm_num)
    have c := step c (a := 1) pr_331 (by rw [pow_one]; exact d331) (by norm_num)
    exact not_perfect_of_dvd_of_two_lt_abundancy c.1 (by rw [c.2]; norm_num [Finset.sum_range_succ]) hN
  · by_cases hs61 : 61 = q
    · subst hs61
      have e3 := E 3 pr_3 d3 (ne3 3 (by norm_num))
      have d13 : 13 ∣ N := ord_dvd hN pr_3 e3 (by decide) (by norm_num)
      have e13 := E 13 pr_13 d13 hs13
      have d61 : 61 ∣ N := ord_dvd hN pr_13 e13 (by decide) (by norm_num)
      have d31 : 31 ∣ N := spec_dvd hN hq hodd (by decide) (by norm_num)
      have e31 := E 31 pr_31 d31 (ne3 31 (by norm_num))
      have d331 : 331 ∣ N := ord_dvd hN pr_31 e31 (by decide) (by norm_num)
      have e331 := E 331 pr_331 d331 (ne3 331 (by norm_num))
      have d7 : 7 ∣ N := ord_dvd hN pr_331 e331 (by decide) (by norm_num)
      have e7 := E 7 pr_7 d7 (ne3 7 (by norm_num))
      have d19 : 19 ∣ N := ord_dvd hN pr_7 e7 (by decide) (by norm_num)
      have c := start N
      have c := step c pr_3 (ord_sq hN pr_3 e3) (by norm_num)
      have c := step c pr_7 (ord_sq hN pr_7 e7) (by norm_num)
      have c := step c pr_13 (ord_sq hN pr_13 e13) (by norm_num)
      have c := step c (a := 1) pr_19 (by rw [pow_one]; exact d19) (by norm_num)
      have c := step c pr_31 (ord_sq hN pr_31 e31) (by norm_num)
      have c := step c (a := 1) pr_61 (by rw [pow_one]; exact d61) (by norm_num)
      exact not_perfect_of_dvd_of_two_lt_abundancy c.1 (by rw [c.2]; norm_num [Finset.sum_range_succ]) hN
    · by_cases hs97 : 97 = q
      · subst hs97
        have e3 := E 3 pr_3 d3 (ne3 3 (by norm_num))
        have d13 : 13 ∣ N := ord_dvd hN pr_3 e3 (by decide) (by norm_num)
        have e13 := E 13 pr_13 d13 hs13
        have d61 : 61 ∣ N := ord_dvd hN pr_13 e13 (by decide) (by norm_num)
        have e61 := E 61 pr_61 d61 hs61
        have d7 : 7 ∣ N := spec_dvd hN hq hodd (by decide) (by norm_num)
        have e7 := E 7 pr_7 d7 (ne3 7 (by norm_num))
        have d19 : 19 ∣ N := ord_dvd hN pr_7 e7 (by decide) (by norm_num)
        have e19 := E 19 pr_19 d19 (ne3 19 (by norm_num))
        have d127 : 127 ∣ N := ord_dvd hN pr_19 e19 (by decide) (by norm_num)
        have e127 := E 127 pr_127 d127 (ne3 127 (by norm_num))
        have d5419 : 5419 ∣ N := ord_dvd hN pr_127 e127 (by decide) (by norm_num)
        have e5419 := E 5419 pr_5419 d5419 (ne3 5419 (by norm_num))
        have d31 : 31 ∣ N := ord_dvd hN pr_5419 e5419 (by decide) (by norm_num)
        have c := start N
        have c := step c pr_3 (ord_sq hN pr_3 e3) (by norm_num)
        have c := step c pr_7 (ord_sq hN pr_7 e7) (by norm_num)
        have c := step c pr_13 (ord_sq hN pr_13 e13) (by norm_num)
        have c := step c pr_19 (ord_sq hN pr_19 e19) (by norm_num)
        have c := step c (a := 1) pr_31 (by rw [pow_one]; exact d31) (by norm_num)
        have c := step c pr_61 (ord_sq hN pr_61 e61) (by norm_num)
        exact not_perfect_of_dvd_of_two_lt_abundancy c.1 (by rw [c.2]; norm_num [Finset.sum_range_succ]) hN
      · by_cases hs3169 : 3169 = q
        · subst hs3169
          have e3 := E 3 pr_3 d3 (ne3 3 (by norm_num))
          have d13 : 13 ∣ N := ord_dvd hN pr_3 e3 (by decide) (by norm_num)
          have e13 := E 13 pr_13 d13 hs13
          have d5 : 5 ∣ N := spec_dvd hN hq hodd (by decide) (by norm_num)
          have e5 := E 5 pr_5 d5 (by norm_num)
          have d31 : 31 ∣ N := ord_dvd hN pr_5 e5 (by decide) (by norm_num)
          have c := start N
          have c := step c pr_3 (ord_sq hN pr_3 e3) (by norm_num)
          have c := step c pr_5 (ord_sq hN pr_5 e5) (by norm_num)
          have c := step c pr_13 (ord_sq hN pr_13 e13) (by norm_num)
          have c := step c (a := 1) pr_31 (by rw [pow_one]; exact d31) (by norm_num)
          exact not_perfect_of_dvd_of_two_lt_abundancy c.1 (by rw [c.2]; norm_num [Finset.sum_range_succ]) hN
        · by_cases hs3348577 : 3348577 = q
          · subst hs3348577
            have e3 := E 3 pr_3 d3 (ne3 3 (by norm_num))
            have d13 : 13 ∣ N := ord_dvd hN pr_3 e3 (by decide) (by norm_num)
            have e13 := E 13 pr_13 d13 hs13
            have d61 : 61 ∣ N := ord_dvd hN pr_13 e13 (by decide) (by norm_num)
            have e61 := E 61 pr_61 d61 hs61
            have d1674289 : 1674289 ∣ N := spec_dvd hN hq hodd (by decide) (by norm_num)
            have e1674289 := E 1674289 pr_1674289 d1674289 (by norm_num)
            have d934415109937 : 934415109937 ∣ N := ord_dvd hN pr_1674289 e1674289 (by decide) (by norm_num)
            have e934415109937 := E 934415109937 pr_934415109937 d934415109937 (by norm_num)
            have d79 : 79 ∣ N := ord_dvd hN pr_934415109937 e934415109937 (by decide) (by norm_num)
            have e79 := E 79 pr_79 d79 (ne3 79 (by norm_num))
            have d7 : 7 ∣ N := ord_dvd hN pr_79 e79 (by decide) (by norm_num)
            have e7 := E 7 pr_7 d7 (ne3 7 (by norm_num))
            have d43 : 43 ∣ N := ord_dvd hN pr_79 e79 (by decide) (by norm_num)
            have d19 : 19 ∣ N := ord_dvd hN pr_7 e7 (by decide) (by norm_num)
            have c := start N
            have c := step c pr_3 (ord_sq hN pr_3 e3) (by norm_num)
            have c := step c pr_7 (ord_sq hN pr_7 e7) (by norm_num)
            have c := step c pr_13 (ord_sq hN pr_13 e13) (by norm_num)
            have c := step c (a := 1) pr_19 (by rw [pow_one]; exact d19) (by norm_num)
            have c := step c (a := 1) pr_43 (by rw [pow_one]; exact d43) (by norm_num)
            have c := step c pr_61 (ord_sq hN pr_61 e61) (by norm_num)
            have c := step c pr_79 (ord_sq hN pr_79 e79) (by norm_num)
            exact not_perfect_of_dvd_of_two_lt_abundancy c.1 (by rw [c.2]; norm_num [Finset.sum_range_succ]) hN
          · by_cases hs3737657091169 : 3737657091169 = q
            · subst hs3737657091169
              have e3 := E 3 pr_3 d3 (ne3 3 (by norm_num))
              have d13 : 13 ∣ N := ord_dvd hN pr_3 e3 (by decide) (by norm_num)
              have e13 := E 13 pr_13 d13 hs13
              have d5 : 5 ∣ N := spec_dvd hN hq hodd (by decide) (by norm_num)
              have e5 := E 5 pr_5 d5 (by norm_num)
              have d31 : 31 ∣ N := ord_dvd hN pr_5 e5 (by decide) (by norm_num)
              have c := start N
              have c := step c pr_3 (ord_sq hN pr_3 e3) (by norm_num)
              have c := step c pr_5 (ord_sq hN pr_5 e5) (by norm_num)
              have c := step c pr_13 (ord_sq hN pr_13 e13) (by norm_num)
              have c := step c (a := 1) pr_31 (by rw [pow_one]; exact d31) (by norm_num)
              exact not_perfect_of_dvd_of_two_lt_abundancy c.1 (by rw [c.2]; norm_num [Finset.sum_range_succ]) hN
            · have e3 := E 3 pr_3 d3 (ne3 3 (by norm_num))
              have d13 : 13 ∣ N := ord_dvd hN pr_3 e3 (by decide) (by norm_num)
              have e13 := E 13 pr_13 d13 hs13
              have d61 : 61 ∣ N := ord_dvd hN pr_13 e13 (by decide) (by norm_num)
              have e61 := E 61 pr_61 d61 hs61
              have d97 : 97 ∣ N := ord_dvd hN pr_61 e61 (by decide) (by norm_num)
              have e97 := E 97 pr_97 d97 hs97
              have d3169 : 3169 ∣ N := ord_dvd hN pr_97 e97 (by decide) (by norm_num)
              have e3169 := E 3169 pr_3169 d3169 hs3169
              have d3348577 : 3348577 ∣ N := ord_dvd hN pr_3169 e3169 (by decide) (by norm_num)
              have e3348577 := E 3348577 pr_3348577 d3348577 hs3348577
              have d3737657091169 : 3737657091169 ∣ N := ord_dvd hN pr_3348577 e3348577 (by decide) (by norm_num)
              have e3737657091169 := E 3737657091169 pr_3737657091169 d3737657091169 hs3737657091169
              have d26042690887 : 26042690887 ∣ N := ord_dvd hN pr_3737657091169 e3737657091169 (by decide) (by norm_num)
              have e26042690887 := E 26042690887 pr_26042690887 d26042690887 (ne3 26042690887 (by norm_num))
              have d31 : 31 ∣ N := ord_dvd hN pr_26042690887 e26042690887 (by decide) (by norm_num)
              have e31 := E 31 pr_31 d31 (ne3 31 (by norm_num))
              have d331 : 331 ∣ N := ord_dvd hN pr_31 e31 (by decide) (by norm_num)
              have e331 := E 331 pr_331 d331 (ne3 331 (by norm_num))
              have d7 : 7 ∣ N := ord_dvd hN pr_331 e331 (by decide) (by norm_num)
              have e7 := E 7 pr_7 d7 (ne3 7 (by norm_num))
              have d19 : 19 ∣ N := ord_dvd hN pr_7 e7 (by decide) (by norm_num)
              have c := start N
              have c := step c pr_3 (ord_sq hN pr_3 e3) (by norm_num)
              have c := step c pr_7 (ord_sq hN pr_7 e7) (by norm_num)
              have c := step c pr_13 (ord_sq hN pr_13 e13) (by norm_num)
              have c := step c (a := 1) pr_19 (by rw [pow_one]; exact d19) (by norm_num)
              have c := step c pr_31 (ord_sq hN pr_31 e31) (by norm_num)
              have c := step c pr_61 (ord_sq hN pr_61 e61) (by norm_num)
              exact not_perfect_of_dvd_of_two_lt_abundancy c.1 (by rw [c.2]; norm_num [Finset.sum_range_succ]) hN


/-- McDaniel, case `3 ∤ N`: every non-special prime `p` has `p^2+p+1` a power of the special
prime, which forces the non-special primes to grow geometrically and the abundancy to stay
below two. -/
theorem mcdaniel_of_not_three_dvd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p % 3 = 2) (h3 : ¬ 3 ∣ N) :
    False := by
  have hN := h.perfect
  have hq4 : q % 4 = 1 := by
    obtain ⟨q', -, -, hq'4, -, hev⟩ := exists_special_prime h
    by_cases hqq : q = q'
    · subst hqq; exact hq'4
    · exact absurd (hev q hq hqq) (Nat.not_even_iff_odd.mpr hodd)
  have E : ∀ t, t.Prime → t ∣ N → t ≠ q → N.factorization t % 3 = 2 := fun t ht htN htq =>
    hexp t (Nat.mem_primeFactors.mpr ⟨ht, htN, h.ne_zero⟩) htq
  have hqN : q ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq, ?_, h.ne_zero⟩
    exact (hq.dvd_iff_one_le_factorization h.ne_zero).mpr (by obtain ⟨k, hk⟩ := hodd; omega)
  -- A prime other than `q` that is `1 mod 3` would force `3 ∣ N`.
  have three : ∀ r, r.Prime → r ∣ N → r ≠ q → r % 3 = 1 → False := by
    intro r hr hrN hrq hr3
    apply h3
    refine ord_dvd hN hr (E r hr hrN hrq) (by decide) ?_
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.pow_mod, hr3]
  have key : ∀ p ∈ N.primeFactors, p ≠ q →
      5 ≤ p ∧ p ^ 2 + p + 1 = q ^ ((p ^ 2 + p + 1).factorization q) ∧ q % 3 = 1 := by
    intro p hp hpq
    obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp hp
    have hp3 : p ≠ 3 := by rintro rfl; exact h3 hpN
    have hp2 : p ≠ 2 := by rintro rfl; exact h.not_two_dvd hpN
    have hp1 : p % 3 ≠ 1 := three p hpp hpN hpq
    have hp5 : 5 ≤ p := by
      have := hpp.two_le
      by_contra hlt
      push Not at hlt
      interval_cases p <;> omega
    have hoddv : Odd (p ^ 2 + p + 1) := by
      have := Nat.even_mul_succ_self p
      have e : p ^ 2 + p + 1 = p * (p + 1) + 1 := by ring
      rw [e]; exact this.add_one
    have huniq : ∀ {r : ℕ}, r.Prime → r ∣ p ^ 2 + p + 1 → r = q := by
      intro r hr hrd
      have hro : Odd r := hoddv.of_dvd_nat hrd
      have hrN : r ∣ N := ord_dvd hN hpp (E p hpp hpN hpq) hro hrd
      have hr3 : r ≠ 3 := by rintro rfl; exact h3 hrN
      have hrm : r % 3 = 1 := OPNThreeFree.target_mod_three hr hr3 (by
        have e : 1 + p + p ^ 2 = p ^ 2 + p + 1 := by ring
        rw [e]; exact hrd)
      by_contra hrq
      exact three r hr hrN hrq hrm
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (by positivity) huniq
    set c := (p ^ 2 + p + 1).primeFactorsList.length
    have hfc : (p ^ 2 + p + 1).factorization q = c := by
      rw [hpow, hq.factorization_pow]; simp
    rw [hfc]
    refine ⟨hp5, hpow, ?_⟩
    have hc : c ≠ 0 := by
      intro h0
      rw [h0] at hpow
      simp at hpow
      omega
    have hqd : q ∣ p ^ 2 + p + 1 := by
      rw [hpow]; exact dvd_pow_self q hc
    have hq3 : q ≠ 3 := by
      rintro rfl; exact h3 (Nat.mem_primeFactors.mp hqN).2.1
    exact OPNThreeFree.target_mod_three hq hq3 (by
      have e : 1 + p + p ^ 2 = p ^ 2 + p + 1 := by ring
      rw [e]; exact hqd)
  -- `q ≥ 13`.
  set S := N.primeFactors.erase q with hS
  have hcard : 2 ≤ S.card := by
    have := three_le_card_primeFactors h
    rw [hS, Finset.card_erase_of_mem hqN]
    omega
  obtain ⟨p0, hp0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hq13 : 13 ≤ q := by
    have h31 := (key p0 (Finset.mem_of_mem_erase hp0) (Finset.ne_of_mem_erase hp0)).2.2
    have := hq.two_le
    omega
  -- The abundancy computation.
  set cf : ℕ → ℕ := fun p => (p ^ 2 + p + 1).factorization q with hcf
  have hab : abundancy N = 2 := (perfect_iff_abundancy_eq_two h.pos).mp hN
  rw [abundancy_eq_prod_primeFactors h.ne_zero, ← Finset.mul_prod_erase _ _ hqN] at hab
  have hqab : abundancy (q ^ N.factorization q) < 13 / 12 := by
    refine (abundancy_prime_pow_lt hq _).trans_le ?_
    have hq' : (13 : ℚ) ≤ q := by exact_mod_cast hq13
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hnonneg : ∀ n : ℕ, 0 ≤ abundancy n := fun n => by
    unfold abundancy; positivity
  have hrest : ∏ p ∈ S, abundancy (p ^ N.factorization p) ≤ 8 / 5 := by
    calc ∏ p ∈ S, abundancy (p ^ N.factorization p)
        ≤ ∏ p ∈ S, (1 + ((1 : ℚ) / 3) ^ cf p) := by
          apply Finset.prod_le_prod₀ (fun _ _ => hnonneg _)
          intro p hp
          have hpS := Finset.mem_of_mem_erase hp
          obtain ⟨hp5, hpow, -⟩ := key p hpS (Finset.ne_of_mem_erase hp)
          have hpp := Nat.prime_of_mem_primeFactors hpS
          have hlt := (three_pow_lt hp5 hq13 hpow).2
          refine (abundancy_prime_pow_lt hpp _).le.trans ?_
          have h1 : ((3 : ℚ)) ^ cf p ≤ (p : ℚ) - 1 := by
            have : (3 ^ cf p + 1 : ℕ) ≤ p := hlt
            have : ((3 ^ cf p + 1 : ℕ) : ℚ) ≤ p := by exact_mod_cast this
            push_cast at this
            linarith
          have h3pos : (0 : ℚ) < 3 ^ cf p := by positivity
          have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
          rw [div_pow, one_pow, div_le_iff₀ hp1]
          have : 1 ≤ ((p : ℚ) - 1) / 3 ^ cf p := by rw [le_div_iff₀ h3pos]; linarith
          have e : (1 + 1 / (3 : ℚ) ^ cf p) * ((p : ℚ) - 1) = ((p : ℚ) - 1) + ((p : ℚ) - 1) / 3 ^ cf p := by
            ring
          linarith
      _ = ∏ c ∈ S.image cf, (1 + ((1 : ℚ) / 3) ^ c) := by
          rw [Finset.prod_image]
          intro a ha b hb hab'
          have ha' := (key a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha)).2.1
          have hb' := (key b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)).2.1
          have heq : a ^ 2 + a + 1 = b ^ 2 + b + 1 := by
            rw [ha', hb']; simp only [hcf] at hab'; rw [hab']
          rcases lt_trichotomy a b with hlt | hlt | hlt
          · have := Nat.pow_lt_pow_left hlt (two_ne_zero); omega
          · exact hlt
          · have := Nat.pow_lt_pow_left hlt (two_ne_zero); omega
      _ ≤ 8 / 5 := by
          apply subset_prod_bound
          intro c hc
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
          obtain ⟨hp5, hpow, -⟩ := key p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
          exact (three_pow_lt hp5 hq13 hpow).1
  have h0 : 0 ≤ ∏ p ∈ S, abundancy (p ^ N.factorization p) :=
    Finset.prod_nonneg fun _ _ => hnonneg _
  have h0' := hnonneg (q ^ N.factorization q)
  nlinarith


/-- McDaniel (1970): in an odd perfect number with special prime `q`, the exponents of
the other primes are not all congruent to 2 modulo 3. -/
theorem mcdaniel {N q : ℕ} (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p % 3 = 2) : False := by
  by_cases h3 : 3 ∣ N
  · exact mcdaniel_of_three_dvd h hq hodd hexp h3
  · exact mcdaniel_of_not_three_dvd h hq hodd hexp h3

end OddPerfect

#print axioms OddPerfect.mcdaniel_of_three_dvd
#print axioms OddPerfect.mcdaniel_of_not_three_dvd
#print axioms OddPerfect.mcdaniel
