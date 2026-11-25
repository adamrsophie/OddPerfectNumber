import OddPerfect.SignedRepunit
import OddPerfect.SignedRepunitJacobi
import OddPerfect.EulerIndexSupport

/-!
# The half power statement and the prime support of the Euler index

This module proves the proposition `HalfPowerNotSquare` of `OddPerfect.EulerIndexSupport`,
exactly as defined there: for a prime `q ≡ 1 (mod 4)` and an odd `ℓ ≥ 3`, the number
`(q ^ ℓ + 1) / 2` is not a square. This is arithmetic (no odd perfect number). Source status:
for odd `ℓ ≥ 5` it is a case of a published theorem (M. A. Bennett and C. M. Skinner, Canad. J.
Math. 56 (2004), Theorem 1.1, page 24, page checked: `x ^ n + y ^ n = 2 z ^ 2` has no solution
in nonzero pairwise coprime integers with `x > y` for `n ≥ 4`, apart from two listed solutions,
both with `y = -1`). For
`ℓ = 3` no published source was checked. Nothing new is claimed. The proof here is elementary,
self contained, and does not use that theorem.

Method, for a prime `p ∣ ℓ` and `u = q ^ (ℓ / p)`: with `F = (u ^ p + 1) / (u + 1)` we get
`((u + 1) / 2) * F = z ^ 2` and `F ≡ p (mod u + 1)`, so the gcd of the two factors divides `p`.
Hence `F` is a square, which `alternating_sum_prime_pow_ne_sq` rules out, or `F` is `p` times a
square, which `alternating_sum_ne_prime_mul_sq` rules out.

As a corollary, the Euler index of every odd perfect number has at least two distinct prime
factors. This is a lower bound only; it does not settle the odd perfect number conjecture,
which remains open.
-/

namespace OddPerfect

/-- If `A * F = t ^ 2` and `gcd(A, F) ∣ p` for a prime `p`, then `F` is a square, or `p ∣ A`
and `F` is `p` times a square. -/
private lemma eisa_sq_or_mul_sq {A F t p : ℕ} (hp : p.Prime) (hg : Nat.gcd A F ∣ p)
    (h : A * F = t ^ 2) : IsSquare F ∨ (p ∣ A ∧ ∃ s, F = p * s ^ 2) := by
  rcases (Nat.dvd_prime hp).mp hg with h1 | h1
  · left
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow
      (Nat.isUnit_iff.mpr (Nat.Coprime.symm h1)) (by rw [mul_comm]; exact h)
    exact ⟨d, by rw [hd, sq]⟩
  · right
    obtain ⟨A', hA⟩ : p ∣ A := h1 ▸ Nat.gcd_dvd_left A F
    obtain ⟨F', hF⟩ : p ∣ F := h1 ▸ Nat.gcd_dvd_right A F
    refine ⟨⟨A', hA⟩, ?_⟩
    have hc : Nat.Coprime A' F' := by
      have h2 : p * Nat.gcd A' F' = p * 1 := by
        rw [← Nat.gcd_mul_left, ← hA, ← hF, h1, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hp.pos h2
    have hpt : p ∣ t := hp.dvd_of_dvd_pow ⟨p * A' * F', by rw [← h, hA, hF]; ring⟩
    obtain ⟨s, rfl⟩ := hpt
    have hAF : A' * F' = s ^ 2 := by
      have h3 : p ^ 2 * (A' * F') = p ^ 2 * s ^ 2 := by rw [← mul_pow, ← h, hA, hF]; ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h3
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow
      (Nat.isUnit_iff.mpr hc.symm) (by rw [mul_comm]; exact hAF)
    exact ⟨d, by rw [hF, hd]⟩

/-- For odd `p` with `(u + 1) * F = u ^ p + 1`, `u + 1` divides `F - p` in `ℤ`. -/
private lemma eisa_dvd_sub {u p F : ℕ} (hp : Odd p) (hF : u ^ p + 1 = (u + 1) * F) :
    ((u : ℤ) + 1) ∣ (F : ℤ) - p := by
  have hgs := geom_sum_mul (-(u : ℤ)) p
  have hneg : (-(u : ℤ)) ^ p = -((u : ℤ) ^ p) := hp.neg_pow _
  have hFz : ((u : ℤ) + 1) * F = (u : ℤ) ^ p + 1 := by exact_mod_cast hF.symm
  have hu0 : ((u : ℤ) + 1) ≠ 0 := by positivity
  have hsum : (F : ℤ) = ∑ i ∈ Finset.range p, (-(u : ℤ)) ^ i := by
    apply mul_left_cancel₀ hu0
    rw [hFz]
    linear_combination hgs + hneg
  have hd : -(u : ℤ) - 1 ∣ ∑ i ∈ Finset.range p, ((-(u : ℤ)) ^ i - 1) :=
    Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow (-(u : ℤ)) 1 i
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    ← hsum] at hd
  have hx : -(u : ℤ) - 1 = -((u : ℤ) + 1) := by ring
  rw [hx, neg_dvd] at hd
  exact hd

/-- **The half power statement.** `HalfPowerNotSquare` holds: for a prime `q ≡ 1 (mod 4)` and
an odd `ℓ ≥ 3`, `(q ^ ℓ + 1) / 2` is not a square. Arithmetic only (no odd perfect number).
For odd `ℓ ≥ 5` this is a case of Theorem 1.1 of Bennett and Skinner (Canad. J. Math. 56
(2004), page checked); for `ℓ = 3` no published source was checked. Nothing new is claimed.
The proof is elementary: a coprime split at a prime `p ∣ ℓ`, then
`alternating_sum_prime_pow_ne_sq` and `alternating_sum_ne_prime_mul_sq`. -/
theorem halfPowerNotSquare : HalfPowerNotSquare := by
  intro q L hq hq4 hL hL3 ⟨z, hz⟩
  have h2 : 2 ∣ q ^ L + 1 := by
    have : q ^ L % 2 = 1 := by
      rw [Nat.pow_mod, show q % 2 = 1 by omega]; simp
    omega
  have hy : q ^ L + 1 = 2 * z ^ 2 := by rw [sq, ← hz, Nat.mul_div_cancel' h2]
  set p := L.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpL : p ∣ L := Nat.minFac_dvd L
  have hpo : Odd p := Odd.of_dvd_nat hL hpL
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hpo with ⟨j, hj⟩
    omega
  have hL0 : L ≠ 0 := by omega
  have hLh : L = L / p * p := (Nat.div_mul_cancel hpL).symm
  have hh : L / p ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hLh
    exact hL0 hLh
  set u := q ^ (L / p) with hu
  have hqL : q ^ L = u ^ p := by rw [hu, ← pow_mul, ← hLh]
  have hu4 : u % 4 = 1 := by rw [hu, Nat.pow_mod, hq4]; norm_num
  have hq5 : 5 ≤ q := by
    have := hq.two_le
    omega
  obtain ⟨F, hF⟩ : u + 1 ∣ u ^ p + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow u 1 hpo
  obtain ⟨A, hA⟩ : ∃ A, u + 1 = 2 * A := ⟨(u + 1) / 2, by omega⟩
  have hAF : A * F = z ^ 2 := by
    have h2 : 2 * (A * F) = 2 * z ^ 2 := by rw [← mul_assoc, ← hA, ← hF, ← hqL, hy]
    omega
  have hg : Nat.gcd A F ∣ p := by
    have hdz := eisa_dvd_sub hpo hF
    have h1 : ((Nat.gcd A F : ℕ) : ℤ) ∣ (u : ℤ) + 1 := by
      have : Nat.gcd A F ∣ u + 1 := (Nat.gcd_dvd_left A F).trans ⟨2, by rw [hA]; ring⟩
      exact_mod_cast this
    have h2 : ((Nat.gcd A F : ℕ) : ℤ) ∣ (F : ℤ) := Int.natCast_dvd_natCast.mpr
      (Nat.gcd_dvd_right A F)
    have h3 := dvd_sub h2 (h1.trans hdz)
    rw [sub_sub_cancel] at h3
    exact Int.natCast_dvd_natCast.mp h3
  rcases eisa_sq_or_mul_sq hp hg hAF with ⟨r, hr⟩ | ⟨-, s, hs⟩
  · exact alternating_sum_prime_pow_ne_sq hq hq5 hh hu4 hpo hp3
      (show u ^ p + 1 = (u + 1) * r ^ 2 by rw [hF, hr, sq])
  · exact alternating_sum_ne_prime_mul_sq hu4 hp (by omega) (by rw [hF, hs])

/-- **The Euler index has at least two prime factors.** For an odd perfect number
`N = q ^ k * m ^ 2` with special prime `q` and `q ∤ m`, the Euler index `σ(m ^ 2) / q ^ k` has at
least two distinct prime factors. This is the conditional theorem
`two_le_card_primeFactors_eulerIndex_of_halfPowerNotSquare` with its hypothesis discharged by
`halfPowerNotSquare`. It is a lower bound only, for every odd perfect number. Nothing new is
claimed; no published source was checked for this exact corollary. The odd perfect number
conjecture is not affected. -/
theorem two_le_card_primeFactors_eulerIndex {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    2 ≤ (eulerIndex q k m).primeFactors.card :=
  two_le_card_primeFactors_eulerIndex_of_halfPowerNotSquare halfPowerNotSquare h hq hN hqm

end OddPerfect

#print axioms OddPerfect.halfPowerNotSquare
#print axioms OddPerfect.two_le_card_primeFactors_eulerIndex
