import OddPerfect.RestrainedNineData
import OddPerfect.RestrainedSeven
import OddPerfect.RestrainedEight

/-!
# Restrained odd perfect numbers: a larger lower bound for the exponent of 3

Setting of `restrained_not_dvd_of_lt`: `N` is an odd perfect number with special prime `q`,
`r ≠ q` is a further prime, and every prime factor other than `q` and `r` has exponent exactly
2. Then `r = 3`, the exponent `E = v_3(N)` is even, and no prime `5 ≤ p < 132257` divides `N`.

If `d ∣ E + 1` then `σ(3 ^ (d - 1)) = (3 ^ d - 1) / 2` divides `σ(3 ^ E)`, which divides `2N`.
For each prime `d` of the list `dList` (every prime `3 ≤ d < 199`), the data module
`RestrainedNineData` holds an exclusion branch for the source `(3 ^ d - 1) / 2`, checked by the
kernel with the checker `RestrainedSeven.chk` and the mask `mask2` of `restrained_not_dvd_of_lt`.
A branch either names a prime divisor below 132257 (`Br.kill`) or continues at a larger prime
divisor (`Br.node`, with a Pratt certificate above `10 ^ 6`), whose sources `t + 1` (case
`t = q`) and `t * t + t + 1` (exponent 2) are closed in turn.

* `restrained_not_dvd_succ_of_odd_not_dvd`: an odd `s ∣ σ(3 ^ (d - 1))` with `s ∤ N` gives
  `d ∤ E + 1` (only `N` odd perfect is used).
* `restrained_not_dvd_succ_of_chk`: an accepted branch for `(3 ^ d - 1) / 2` gives `d ∤ E + 1`.
* `restrained_not_dvd_succ_of_mem`: `d ∤ E + 1` for every `d ∈ dList`.
* `restrained_one_ninety_eight_le_three`: `198 ≤ E`, since the least prime factor of the odd
  number `E + 1` is at least 199; also `restrained_thirtysix_le_three` and `Ω(N) ≥ 76293`.

The branches with a node: `d = 13` (`797161 = σ(3 ^ 12)`), `37` (`13097927`), `59`, `61`, `67`,
`71`, `79`, `101`, `103` and `163`; every other `d` has a prime divisor of `σ(3 ^ (d - 1))`
below 132257. The bound stops at `d = 199`: bounded factoring found no prime factor of
`σ(3 ^ 198) = (3 ^ 199 - 1) / 2`.

No novelty is claimed: Ochem and Zelinsky (arXiv 2607.19746, 2026) treat this family in depth
and prove that the exponent of 3 is at least 23,000,000,000; the bound here is far weaker, is
subsumed by theirs, and theirs is not proved here.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace OddPerfect

namespace RestrainedNine

open RestrainedSeven

/-- `σ(3 ^ k) = (3 ^ (k + 1) - 1) / 2`. -/
theorem sigma_three_pow (k : ℕ) : σ 1 (3 ^ k) = (3 ^ (k + 1) - 1) / 2 := by
  rw [sigma_one_apply_prime_pow Nat.prime_three, Nat.geomSum_eq (by norm_num)]

/-- The primes with their bit set in `mask2` do not divide `N`. -/
theorem mask2_sound {N q : ℕ} (F : Fam N q) (h5 : ¬ 5 ∣ N) (h7 : ¬ 7 ∣ N) :
    ∀ t, mask2.testBit t = true → t.Prime → ¬ t ∣ N := by
  have h0 : ∀ t, (160 : ℕ).testBit t = true → t.Prime → ¬ t ∣ N := fun t ht _ => by
    rcases testBit_start ht with rfl | rfl
    · exact h5
    · exact h7
  exact rowsOK_sound F mask1 rows2 mask2 rows2_ok (rowsOK_sound F 160 rows1 mask1 rows1_ok h0)

/-- Soundness of `dCover`: every prime in the range is in the list. -/
theorem dCover_sound {L D : List ℕ} {lo n : ℕ} (h : dCover L D lo n = true) {p : ℕ}
    (hp : p.Prime) (hlo : lo ≤ p) (hhi : p < lo + n) : p ∈ L := by
  simp only [dCover, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at h
  rcases h p ⟨hlo, hhi⟩ with hL | ⟨d, -, ⟨h2, hlt⟩, hdm⟩
  · exact hL
  · exfalso
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hdm) with rfl | rfl <;> omega

end RestrainedNine

open RestrainedSeven RestrainedNine

/-- **Generalized exclusion of divisors of `E + 1`.** For an odd perfect number `N`, if an odd
`s` divides `σ(3 ^ (d - 1))` with `d ≥ 1` and `s ∤ N`, then `d ∤ v_3(N) + 1`: otherwise
`s ∣ σ(3 ^ (d - 1)) ∣ σ(3 ^ v_3(N)) ∣ 2N`. -/
theorem restrained_not_dvd_succ_of_odd_not_dvd {N d s : ℕ} (h : OddPerfect N) (hd : 1 ≤ d)
    (hs : s % 2 = 1) (hsd : s ∣ σ 1 (3 ^ (d - 1))) (hsN : ¬ s ∣ N) :
    ¬ d ∣ N.factorization 3 + 1 := by
  intro hdvd
  have hd' : d - 1 + 1 ∣ N.factorization 3 + 1 := by rwa [Nat.sub_add_cancel hd]
  have h2N := (hsd.trans (ForcingClosed.sigma_prime_pow_dvd_of_dvd Nat.prime_three hd')).trans
    (OPNStarter.component_sigma_dvd h.perfect Nat.prime_three rfl)
  exact hsN (dvd_of_dvd_two_mul hs h2N)

/-- **Exclusion of `d ∣ E + 1` by a checked branch.** In the restrained family, if the branch
`b` is accepted by `chk mask2 0` for the source `(3 ^ d - 1) / 2 = σ(3 ^ (d - 1))`, then
`d ∤ v_3(N) + 1`.
Conditional family result; no novelty is claimed. -/
theorem restrained_not_dvd_succ_of_chk {N q r d : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) {b : Br}
    (hb : chk mask2 0 ((3 ^ d - 1) / 2) b = true) : ¬ d ∣ N.factorization 3 + 1 := by
  obtain ⟨F, h5, h7⟩ := fam_of h hq hodd hr hrq hsq
  intro hdvd
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [zero_dvd_iff] at hdvd
      omega
    · exact hd
  have hd' : d - 1 + 1 ∣ N.factorization 3 + 1 := by rwa [Nat.sub_add_cancel hd]
  have h2N := (ForcingClosed.sigma_prime_pow_dvd_of_dvd Nat.prime_three hd').trans
    (OPNStarter.component_sigma_dvd h.perfect Nat.prime_three rfl)
  rw [sigma_three_pow, Nat.sub_add_cancel hd] at h2N
  exact chk_sound F (mask2_sound F h5 h7) b 0 _ hb h2N (Or.inl rfl)

/-- **The list of excluded `d`.** In the restrained family, `d ∤ v_3(N) + 1` for every `d` in
`dList` (the primes `3 ≤ d < 199`), each by a kernel checked branch of `dRows`.
Conditional family result; no novelty is claimed. -/
theorem restrained_not_dvd_succ_of_mem {N q r d : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hd : d ∈ dList) :
    ¬ d ∣ N.factorization 3 + 1 := by
  unfold dList at hd
  obtain ⟨⟨d', b⟩, hmem, rfl⟩ := List.mem_map.mp hd
  have hok := List.all_eq_true.mp dRows_ok _ hmem
  exact restrained_not_dvd_succ_of_chk h hq hodd hr hrq hsq hok

/-- **Restrained family: `198 ≤ v_3(N)`.** The exponent `E = v_3(N)` is even and at least 6,
so the least prime factor `p` of `E + 1` is odd; every prime `3 ≤ p < 199` is in `dList` and does
not divide `E + 1`, so `199 ≤ p ≤ E + 1`.
Conditional family result; no novelty is claimed: the bound of Ochem and Zelinsky
(arXiv 2607.19746, 2026), 23,000,000,000, is far stronger and is not proved here. -/
theorem restrained_one_ninety_eight_le_three {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    198 ≤ N.factorization 3 := by
  have h6 := restrained_six_le_three h hq hodd hr hrq hsq
  obtain ⟨-, -, ⟨k, hk⟩, -⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  set m := N.factorization 3 + 1 with hm
  have hm1 : m ≠ 1 := by omega
  have hp := Nat.minFac_prime hm1
  have hpm := Nat.minFac_dvd m
  have hp2 : m.minFac ≠ 2 := by
    intro h2
    rw [h2] at hpm
    omega
  by_contra hlt
  have hle := Nat.minFac_le (show 0 < m by omega)
  have hmem := dCover_sound dCover_ok hp (by have := hp.two_le; omega) (by omega)
  exact restrained_not_dvd_succ_of_mem h hq hodd hr hrq hsq hmem hpm

/-- **Restrained family: `36 ≤ v_3(N)`** (first milestone, from `13 ∤ v_3(N) + 1`; a
corollary of `restrained_one_ninety_eight_le_three`).
Conditional family result; no novelty is claimed. -/
theorem restrained_thirtysix_le_three {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    36 ≤ N.factorization 3 := by
  have := restrained_one_ninety_eight_le_three h hq hodd hr hrq hsq
  omega

/-- **Restrained family: `Ω(N) ≥ 76293`.** From `ω(N) ≥ 38049`,
`restrained_one_ninety_eight_le_three` and `2 ω(N) + v_3(N) ≤ Ω(N) + 3`.
Conditional family result; no novelty is claimed. -/
theorem restrained_Omega_ge_of_one_ninety_eight {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    76293 ≤ Ω N := by
  have h1 := restrained_omega_ge h hq hodd hr hrq hsq
  have h2 := restrained_one_ninety_eight_le_three h hq hodd hr hrq hsq
  have h3 := two_mul_card_add_factorization_three_le h
  omega

end OddPerfect

#print axioms OddPerfect.RestrainedNine.sigma_three_pow
#print axioms OddPerfect.RestrainedNine.mask2_sound
#print axioms OddPerfect.RestrainedNine.dCover_sound
#print axioms OddPerfect.restrained_not_dvd_succ_of_odd_not_dvd
#print axioms OddPerfect.restrained_not_dvd_succ_of_chk
#print axioms OddPerfect.restrained_not_dvd_succ_of_mem
#print axioms OddPerfect.restrained_one_ninety_eight_le_three
#print axioms OddPerfect.restrained_thirtysix_le_three
#print axioms OddPerfect.restrained_Omega_ge_of_one_ninety_eight
