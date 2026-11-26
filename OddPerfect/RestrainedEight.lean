import OddPerfect.RestrainedSeven
import OddPerfect.RestrainedSix
import OddPerfect.Counting
import OddPerfect.Network
import OddPerfect.Valuation

/-!
# Restrained odd perfect numbers: counting, two sources, and the exponent of 3

Conditional family results. Setting of `restrained_not_dvd_of_lt`: `N` is an odd perfect number
with special prime `q`, `r ≠ q` is a further prime, and every prime factor other than `q` and
`r` has exponent exactly 2. The landed results give `r = 3`, `q ≡ 1 (mod 12)`, `6 ≤ v_3(N)`,
and no prime `5 ≤ p < 132257` divides `N`.

* `restrained_omega_ge`: `ω(N) ≥ 38049`. Every prime factor other than 3 is at least
  `B = 132257`, so `2 = σ(N)/N < (3/2) (B/(B-1)) ^ (ω - 1)`, and `3 B ^ 38047 < 4 (B-1) ^ 38047`
  (one kernel evaluation, `pow_lt_38047`).
* `two_mul_card_add_factorization_three_le`: for every odd perfect number,
  `2 ω(N) + v_3(N) ≤ Ω(N) + 3`; with `v_3(N) ≥ 6` this gives `Ω(N) ≥ 76101`
  (`restrained_Omega_ge`).
* `restrained_two_sources`: a prime factor `t ≡ 2 (mod 3)` of `N` satisfies
  `v_t(σ(3 ^ E)) + v_t(σ(q ^ α)) = 2` with `E = v_3(N)`, `α = v_q(N)`: an ordinary component
  `σ(p ^ 2) = p ^ 2 + p + 1` has no prime factor `≡ 2 (mod 3)`.
* `restrained_not_dvd_succ_of_dvd_sigma`: if a prime `5 ≤ s < 132257` divides `σ(3 ^ (d - 1))`
  then `d ∤ E + 1`. Instances for `d = 7, 19, 23, 29, 31` (witnesses `1093, 1597, 47, 59, 683`);
  with `d = 7` the exponent of 3 is at least 12 (`restrained_twelve_le_three`), and then
  `Ω(N) ≥ 76107` (`restrained_Omega_ge_of_twelve`).

No novelty is claimed: Ochem and Zelinsky (arXiv 2607.19746, 2026) treat this family in depth
and prove that the exponent of 3 is at least 23,000,000,000, which is not proved here and which
subsumes the small exponent exclusions of this file. Whether the other statements are in the
literature was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

namespace RestrainedEight

/-- The abundancy of a positive integer is positive. -/
theorem abundancy_pos {n : ℕ} (hn : n ≠ 0) : 0 < abundancy n := by
  unfold abundancy
  have h1 : (0 : ℚ) < σ 1 n := by exact_mod_cast sigma_pos 1 n hn
  have h2 : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  positivity

/-- Every prime factor of size at least `c + 1` has `p/(p-1) ≤ (c+1)/c`. -/
theorem div_pred_le {p c : ℕ} (hc : 1 ≤ c) (hp : c + 1 ≤ p) :
    (p : ℚ) / (p - 1) ≤ ((c + 1 : ℕ) : ℚ) / c := by
  have hc' : (1 : ℚ) ≤ c := by exact_mod_cast hc
  have hp' : (c : ℚ) + 1 ≤ p := by exact_mod_cast hp
  push_cast
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- For an odd perfect number with `3 ∣ N`, the components over `N.primeFactors.erase 3` have
abundancy product above `4/3`. -/
theorem prod_erase_three_gt {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) :
    (4 : ℚ) / 3 < ∏ p ∈ N.primeFactors.erase 3, abundancy (p ^ N.factorization p) := by
  have h3m : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  have hab := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  rw [abundancy_eq_prod_primeFactors h.ne_zero, ← Finset.mul_prod_erase _ _ h3m] at hab
  have h32 := abundancy_prime_pow_lt Nat.prime_three (N.factorization 3)
  norm_num at h32
  simp only [← Nat.factorization_def _ Nat.prime_three] at h32
  have hP : 0 < ∏ p ∈ N.primeFactors.erase 3, abundancy (p ^ N.factorization p) :=
    Finset.prod_pos fun p hp => abundancy_pos (pow_ne_zero _
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).ne_zero)
  have hA : 0 < abundancy (3 ^ N.factorization 3) := abundancy_pos (by positivity)
  set P := ∏ p ∈ N.primeFactors.erase 3, abundancy (p ^ N.factorization p)
  set A := abundancy (3 ^ N.factorization 3)
  nlinarith

/-- **Counting with a lower bound on the prime factors.** Let `N` be an odd perfect number with
`3 ∣ N` whose prime factors other than 3 are all at least `B = c + 1`. If
`3 B ^ k < 4 c ^ k`, then `ω(N) ≥ k + 2`. -/
theorem card_ge_of_min {N B c k : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) (hBc : B = c + 1)
    (hc : 1 ≤ c) (hmin : ∀ p ∈ N.primeFactors, p ≠ 3 → B ≤ p)
    (hpow : 3 * B ^ k < 4 * c ^ k) : k + 2 ≤ N.primeFactors.card := by
  subst hBc
  have h3m : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  set m := (N.primeFactors.erase 3).card with hm
  have hcard : m + 1 = N.primeFactors.card := by
    rw [hm, Finset.card_erase_of_mem h3m]
    have := Finset.card_pos.mpr ⟨3, h3m⟩
    omega
  set x : ℚ := ((c + 1 : ℕ) : ℚ) / c with hx
  have hc' : (1 : ℚ) ≤ c := by exact_mod_cast hc
  have hx1 : 1 ≤ x := by
    rw [hx, le_div_iff₀ (by linarith)]
    push_cast
    linarith
  have hP : ∏ p ∈ N.primeFactors.erase 3, abundancy (p ^ N.factorization p) ≤ x ^ m := by
    rw [hm, ← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun p hp => (abundancy_pos (pow_ne_zero _
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).ne_zero)).le) fun p hp => ?_
    obtain ⟨hp3, hpN⟩ := Finset.mem_erase.mp hp
    exact (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors hpN) _).le.trans
      (div_pred_le hc (hmin p hpN hp3))
  have hgt := prod_erase_three_gt h h3
  by_contra hlt
  have hmk : m ≤ k := by omega
  have hxk : x ^ m ≤ x ^ k := pow_le_pow_right₀ hx1 hmk
  have hq : (3 : ℚ) * ((c + 1 : ℕ) : ℚ) ^ k < 4 * (c : ℚ) ^ k := by exact_mod_cast hpow
  have hv : (0 : ℚ) < (c : ℚ) ^ k := by positivity
  have hkey : (4 : ℚ) / 3 < ((c + 1 : ℕ) : ℚ) ^ k / (c : ℚ) ^ k := by
    rw [← div_pow]
    exact lt_of_lt_of_le hgt (hP.trans hxk)
  rw [lt_div_iff₀ hv] at hkey
  linarith

/-- The one large comparison, `3 · 132257 ^ 38047 < 4 · 132256 ^ 38047`, checked by the kernel
on numbers of about 195,000 digits. -/
theorem pow_lt_38047 : 3 * 132257 ^ 38047 < 4 * 132256 ^ 38047 := by decide +kernel

/-- For a finite set `S` of prime factors of an odd perfect number, `2 |S| ≤ ∑_{p ∈ S} e_p + 1`. -/
theorem two_mul_card_le_sum_add_one {N : ℕ} (h : OddPerfect N) {S : Finset ℕ}
    (hS : S ⊆ N.primeFactors) : 2 * S.card ≤ (∑ p ∈ S, N.factorization p) + 1 := by
  obtain ⟨s, hs, -, -, -, hev⟩ := exists_special_prime h
  have key : ∀ p ∈ S, 2 ≤ N.factorization p + (if p = s then 1 else 0) := by
    intro p hp
    obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp (hS hp)
    have h1 : 1 ≤ N.factorization p := hpp.factorization_pos_of_dvd h.ne_zero hpN
    split_ifs with hps
    · omega
    · obtain ⟨j, hj⟩ := hev p hpp hps
      omega
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' S s (fun _ => 1)] at hsum
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  split_ifs at hsum <;> omega

end RestrainedEight

open RestrainedEight RestrainedSeven

/-- **Counting lemma with the exponent of 3.** For every odd perfect number,
`2 ω(N) + v_3(N) ≤ Ω(N) + 3`. -/
theorem two_mul_card_add_factorization_three_le {N : ℕ} (h : OddPerfect N) :
    2 * ω N + N.factorization 3 ≤ Ω N + 3 := by
  rw [cardDistinctFactors_eq_card_primeFactors, cardFactors_eq_sum_primeFactors]
  by_cases h3 : 3 ∈ N.primeFactors
  · rw [← Finset.add_sum_erase _ _ h3]
    have := two_mul_card_le_sum_add_one h (Finset.erase_subset 3 N.primeFactors)
    rw [Finset.card_erase_of_mem h3] at this
    have := Finset.card_pos.mpr ⟨3, h3⟩
    omega
  · have h0 : N.factorization 3 = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    have := two_mul_card_le_sum_factorization_add_one h
    omega

/-- In the restrained family, every prime factor other than 3 is at least 132257. -/
theorem restrained_le_of_ne_three {N q r p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hp : p ∈ N.primeFactors) (hp3 : p ≠ 3) : 132257 ≤ p := by
  obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd hpN
  have h5 : 5 ≤ p := by
    have := hpp.two_le
    rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h' | h' | h' | h'
    · exact absurd h' hp2
    · exact absurd h' hp3
    · exact absurd (h' ▸ hpp) (by norm_num)
    · exact h'
  by_contra hlt
  exact restrained_not_dvd_of_lt h hq hodd hr hrq hsq hpp h5 (by omega) hpN

/-- In the restrained family, `3 ∣ N`. -/
theorem restrained_three_dvd {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) : 3 ∣ N := by
  have := restrained_six_le_three h hq hodd hr hrq hsq
  exact Nat.dvd_of_factorization_pos (by omega)

/-- **Restrained family: `ω(N) ≥ 38049`.** With the hypotheses of `restrained_not_dvd_of_lt`,
every prime factor other than 3 is at least 132257, and the abundancy
`2 < (3/2) (132257/132256) ^ (ω - 1)` forces `ω(N) ≥ 38049`.
Conditional family result; no novelty is claimed (Ochem and Zelinsky, arXiv 2607.19746, 2026,
treat this family), and whether this bound is in the literature was not verified. -/
theorem restrained_omega_ge {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    38049 ≤ ω N := by
  have hp := pow_lt_38047
  have := card_ge_of_min (B := 132257) (c := 132256) (k := 38047) h
    (restrained_three_dvd h hq hodd hr hrq hsq) rfl (by norm_num)
    (fun p hp hp3 => restrained_le_of_ne_three h hq hodd hr hrq hsq hp hp3) hp
  rw [cardDistinctFactors_eq_card_primeFactors]
  omega

/-- **Restrained family: `Ω(N) ≥ 76101`.** From `ω(N) ≥ 38049`, the landed bound `v_3(N) ≥ 6`,
and `2 ω(N) + v_3(N) ≤ Ω(N) + 3`.
Conditional family result; no novelty is claimed, and whether this bound is in the literature
was not verified. -/
theorem restrained_Omega_ge {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    76101 ≤ Ω N := by
  have h1 := restrained_omega_ge h hq hodd hr hrq hsq
  have h2 := restrained_six_le_three h hq hodd hr hrq hsq
  have h3 := two_mul_card_add_factorization_three_le h
  omega

/-- **Two sources.** In the restrained family, a prime factor `t ≡ 2 (mod 3)` of `N` receives
its two units only from the components of 3 and of `q`:
`v_t(σ(3 ^ E)) + v_t(σ(q ^ α)) = 2` with `E = v_3(N)` and `α = v_q(N)`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_two_sources {N q r t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ht : t ∈ N.primeFactors) (ht3 : t % 3 = 2) :
    padicValNat t (σ 1 (3 ^ N.factorization 3)) + padicValNat t (σ 1 (q ^ N.factorization q))
      = 2 := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  obtain ⟨htp, htN, -⟩ := Nat.mem_primeFactors.mp ht
  have ht2 : t ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd htN
  have htq : t ≠ q := by
    rintro rfl
    have := F.mod12
    omega
  have hne3 : t ≠ 3 := by
    rintro rfl
    norm_num at ht3
  have he := F.sq t ht htq hne3
  have hsum := sigmaWeight_sum_eq h.perfect htp ht2
  rw [he, Finset.sum_eq_add 3 q (by have := F.mod12; omega)] at hsum
  · rw [sigmaWeight_eq_padicValNat _ _ htp, sigmaWeight_eq_padicValNat _ _ htp] at hsum
    exact hsum
  · intro c hc ⟨hc3, hcq⟩
    have hcp := Nat.prime_of_mem_primeFactors hc
    rw [sigmaWeight, F.sq c hc hcq hc3]
    refine Nat.factorization_eq_zero_of_not_dvd fun hdvd => ?_
    have hs : σ 1 (c ^ 2) = 1 + c + c ^ 2 := by
      simp [sigma_one_apply_prime_pow hcp, Finset.sum_range_succ]
    rw [hs] at hdvd
    have := OPNThreeFree.target_mod_three htp hne3 hdvd
    omega
  · intro hc
    have h0 : N.factorization 3 = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    rw [sigmaWeight, h0]
    simp
  · intro hc
    have h0 : N.factorization q = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    rw [sigmaWeight, h0]
    simp

/-- In the restrained family, for a prime factor `t ≡ 2 (mod 3)`, each of the two source
valuations is at most 2, a simple factor `t` of `σ(3 ^ E)` is matched by a simple factor of
`σ(q ^ α)`, and `t ^ 3 ∤ σ(3 ^ E)`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_two_sources_cor {N q r t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ht : t ∈ N.primeFactors) (ht3 : t % 3 = 2) :
    padicValNat t (σ 1 (3 ^ N.factorization 3)) ≤ 2 ∧
      padicValNat t (σ 1 (q ^ N.factorization q)) ≤ 2 ∧
      (padicValNat t (σ 1 (3 ^ N.factorization 3)) = 1 →
        padicValNat t (σ 1 (q ^ N.factorization q)) = 1) ∧
      ¬ t ^ 3 ∣ σ 1 (3 ^ N.factorization 3) := by
  have hs := restrained_two_sources h hq hodd hr hrq hsq ht ht3
  refine ⟨by omega, by omega, fun h1 => by omega, fun hdvd => ?_⟩
  have : Fact t.Prime := ⟨Nat.prime_of_mem_primeFactors ht⟩
  have h3 := (padicValNat_dvd_iff_le (sigma_pos 1 _ (by positivity)).ne').mp hdvd
  rw [← Nat.padicValNat_def] at h3
  omega

/-- **Small primes in `σ(3 ^ (d - 1))`.** In the restrained family, if a prime `5 ≤ s < 132257`
divides `σ(3 ^ (d - 1))` with `d ≥ 1`, then `d ∤ v_3(N) + 1`: otherwise `s ∣ σ(3 ^ E) ∣ 2N`,
against `restrained_not_dvd_of_lt`.
Conditional family result; no novelty is claimed. -/
theorem restrained_not_dvd_succ_of_dvd_sigma {N q r d s : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hd : 1 ≤ d) (hs : s.Prime) (h5 : 5 ≤ s) (hlt : s < 132257)
    (hsd : s ∣ σ 1 (3 ^ (d - 1))) : ¬ d ∣ N.factorization 3 + 1 := by
  intro hdvd
  have hd' : d - 1 + 1 ∣ N.factorization 3 + 1 := by rwa [Nat.sub_add_cancel hd]
  have h2N := (hsd.trans (ForcingClosed.sigma_prime_pow_dvd_of_dvd Nat.prime_three hd')).trans
    (OPNStarter.component_sigma_dvd h.perfect Nat.prime_three rfl)
  have hs2 : s % 2 = 1 := Nat.odd_iff.mp (hs.odd_of_ne_two (by omega))
  exact restrained_not_dvd_of_lt h hq hodd hr hrq hsq hs h5 hlt
    (dvd_of_dvd_two_mul hs2 h2N)

/-- In the restrained family, `7 ∤ v_3(N) + 1`: `σ(3 ^ 6) = 1093` is a prime below 132257.
Conditional family result; no novelty is claimed. -/
theorem restrained_seven_not_dvd_succ {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ¬ 7 ∣ N.factorization 3 + 1 :=
  restrained_not_dvd_succ_of_dvd_sigma (s := 1093) h hq hodd hr hrq hsq (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sigma_one_apply_prime_pow Nat.prime_three, Finset.sum_range_succ,
      Finset.sum_range_zero]; norm_num)

/-- In the restrained family, `19 ∤ v_3(N) + 1`: `1597 ∣ σ(3 ^ 18)`.
Conditional family result; no novelty is claimed. -/
theorem restrained_nineteen_not_dvd_succ {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ¬ 19 ∣ N.factorization 3 + 1 :=
  restrained_not_dvd_succ_of_dvd_sigma (s := 1597) h hq hodd hr hrq hsq (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sigma_one_apply_prime_pow Nat.prime_three, Finset.sum_range_succ,
      Finset.sum_range_zero]; norm_num)

/-- In the restrained family, `23 ∤ v_3(N) + 1`: `47 ∣ σ(3 ^ 22)`.
Conditional family result; no novelty is claimed. -/
theorem restrained_twentythree_not_dvd_succ {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ¬ 23 ∣ N.factorization 3 + 1 :=
  restrained_not_dvd_succ_of_dvd_sigma (s := 47) h hq hodd hr hrq hsq (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sigma_one_apply_prime_pow Nat.prime_three, Finset.sum_range_succ,
      Finset.sum_range_zero]; norm_num)

/-- In the restrained family, `29 ∤ v_3(N) + 1`: `59 ∣ σ(3 ^ 28)`.
Conditional family result; no novelty is claimed. -/
theorem restrained_twentynine_not_dvd_succ {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ¬ 29 ∣ N.factorization 3 + 1 :=
  restrained_not_dvd_succ_of_dvd_sigma (s := 59) h hq hodd hr hrq hsq (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sigma_one_apply_prime_pow Nat.prime_three, Finset.sum_range_succ,
      Finset.sum_range_zero]; norm_num)

/-- In the restrained family, `31 ∤ v_3(N) + 1`: `683 ∣ σ(3 ^ 30)`.
Conditional family result; no novelty is claimed. -/
theorem restrained_thirtyone_not_dvd_succ {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    ¬ 31 ∣ N.factorization 3 + 1 :=
  restrained_not_dvd_succ_of_dvd_sigma (s := 683) h hq hodd hr hrq hsq (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by simp only [sigma_one_apply_prime_pow Nat.prime_three, Finset.sum_range_succ,
      Finset.sum_range_zero]; norm_num)

/-- In the restrained family, `12 ≤ v_3(N)`: the exponent is even and at least 6, and 6, 8,
10 are excluded by `7`, `3` and `11` dividing `e + 1`.
Conditional family result; no novelty is claimed (the bound of Ochem and Zelinsky is far
stronger and not proved here). -/
theorem restrained_twelve_le_three {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    12 ≤ N.factorization 3 := by
  have h6 := restrained_six_le_three h hq hodd hr hrq hsq
  have h3 := restrained_three_not_dvd_succ h hq hodd hr hrq hsq
  have h7 := restrained_seven_not_dvd_succ h hq hodd hr hrq hsq
  have h11 := restrained_eleven_not_dvd_succ h hq hodd hr hrq hsq
  obtain ⟨-, -, ⟨k, hk⟩, -⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  rcases (by omega : N.factorization 3 = 6 ∨ N.factorization 3 = 8 ∨
      N.factorization 3 = 10 ∨ 12 ≤ N.factorization 3) with he | he | he | he
  · exact absurd (by norm_num [he]) h7
  · exact absurd (by norm_num [he]) h3
  · exact absurd (by norm_num [he]) h11
  · exact he

/-- **Restrained family: `Ω(N) ≥ 76107`.** From `ω(N) ≥ 38049`, `v_3(N) ≥ 12` and
`2 ω(N) + v_3(N) ≤ Ω(N) + 3`.
Conditional family result; no novelty is claimed, and whether this bound is in the literature
was not verified. -/
theorem restrained_Omega_ge_of_twelve {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    76107 ≤ Ω N := by
  have h1 := restrained_omega_ge h hq hodd hr hrq hsq
  have h2 := restrained_twelve_le_three h hq hodd hr hrq hsq
  have h3 := two_mul_card_add_factorization_three_le h
  omega

end OddPerfect

#print axioms OddPerfect.RestrainedEight.abundancy_pos
#print axioms OddPerfect.RestrainedEight.div_pred_le
#print axioms OddPerfect.RestrainedEight.prod_erase_three_gt
#print axioms OddPerfect.RestrainedEight.card_ge_of_min
#print axioms OddPerfect.RestrainedEight.pow_lt_38047
#print axioms OddPerfect.RestrainedEight.two_mul_card_le_sum_add_one
#print axioms OddPerfect.two_mul_card_add_factorization_three_le
#print axioms OddPerfect.restrained_le_of_ne_three
#print axioms OddPerfect.restrained_three_dvd
#print axioms OddPerfect.restrained_omega_ge
#print axioms OddPerfect.restrained_Omega_ge
#print axioms OddPerfect.restrained_two_sources
#print axioms OddPerfect.restrained_two_sources_cor
#print axioms OddPerfect.restrained_not_dvd_succ_of_dvd_sigma
#print axioms OddPerfect.restrained_seven_not_dvd_succ
#print axioms OddPerfect.restrained_nineteen_not_dvd_succ
#print axioms OddPerfect.restrained_twentythree_not_dvd_succ
#print axioms OddPerfect.restrained_twentynine_not_dvd_succ
#print axioms OddPerfect.restrained_thirtyone_not_dvd_succ
#print axioms OddPerfect.restrained_twelve_le_three
#print axioms OddPerfect.restrained_Omega_ge_of_twelve
