import OddPerfect.LedgerParity
import OddPerfect.SquareRow

/-!
# Parity of incoming valuations for all exponents

Let `N` be an odd perfect number with special prime `q`, `k = ω(N)`, `m` the number of pairs
`(p, r)` of prime factors with `r ∣ σ(p ^ e_p)`, and `D_q` the number of senders into `q`.
`OddPerfect/LedgerParity.lean` proves `s_2 + D_q + 2 k ≤ 2 m + 2` for the set of rows of exponent
exactly 2, because `σ(p ^ 2)` is never a square. By `OddPerfect/SquareRow.lean`, `σ(p ^ e)` with
`p` odd and `e > 0` even is a square only for `3 ^ 4`. So every ordinary row other than the row
`3 ^ 4` has an odd entry, and the same counting gives, with `R` the set of ordinary prime factors
other than `3` when `e_3 = 4`:
`|R| + D_q + 2 k ≤ 2 m + 2`. Consequently `3 k ≤ 2 m + 3` for every odd perfect number, and
`3 k ≤ 2 m + 2` when `e_3 ≠ 4`; no condition on the exponents is needed.

Sanity remark: read the same way (rows `σ(p ^ e_p)`, edges `r ∣ σ(p ^ e_p)`), every even perfect
number `N = 2 ^ (n - 1) (2 ^ n - 1)` satisfies the inequality too: its edges are `2 → 2 ^ n - 1` and
`2 ^ n - 1 → 2`, so `k = m = 2` and `3 k = 6 ≤ 2 m + 2`. The inequality is not expected to exclude
anything by itself.

Whether this result is new was not verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N : ℕ}

private theorem odd_sigma_prime_pow_of_even {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : Even e) :
    Odd (σ 1 (p ^ e)) := by
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  rw [sigma_one_apply_prime_pow hp, Nat.odd_iff, Finset.sum_nat_mod]
  have : ∀ i ∈ Finset.range (e + 1), p ^ i % 2 = 1 := fun i _ => by
    rw [Nat.pow_mod, hpo, one_pow, Nat.one_mod]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  obtain ⟨j, rfl⟩ := he
  omega

/-- **Every ordinary row except `3 ^ 4` has an odd entry.** If `p ≠ q` is a prime factor of an odd
perfect number `N` with special prime `q`, and not both `p = 3` and `v_3(N) = 4`, then some prime
factor `r` of `N` receives an odd valuation `v_r(σ(p ^ e_p))`. -/
theorem exists_odd_sigmaWeight_of_ne_three_pow_four (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) {p : ℕ} (hp : p ∈ N.primeFactors) (hpq : p ≠ q)
    (h34 : ¬ (p = 3 ∧ N.factorization 3 = 4)) :
    ∃ r ∈ N.primeFactors, Odd (sigmaWeight N p r) := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
  have hev := even_factorization_of_ne h hq hodd hp' hpq
  have he0 : N.factorization p ≠ 0 :=
    (hp'.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)).ne'
  obtain ⟨r, hr, hro⟩ := exists_prime_odd_factorization_sigma hp' hp2 hev he0
    (fun h3 => h34 ⟨h3.1, h3.1 ▸ h3.2⟩)
  have hrd : r ∣ σ 1 (p ^ N.factorization p) := Nat.dvd_of_factorization_pos hro.pos.ne'
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr (odd_sigma_prime_pow_of_even hp' hp2 hev)
      (even_iff_two_dvd.mpr hrd)
  exact ⟨r, Nat.mem_primeFactors.mpr ⟨hr, OPNStarter.force_prime h.perfect hp' rfl hr hr2 hrd,
    h.ne_zero⟩, hro⟩

/-- **Ordinary rows and parity, all exponents.** Let `N` be an odd perfect number with special
prime `q`, `k = ω(N)`, `m` the number of pairs `(p, r)` of prime factors with `r ∣ σ(p ^ e_p)`,
`D_q` the number of senders into `q`, and `R` the set of prime factors `p ≠ q` with
`¬ (p = 3 ∧ e_3 = 4)`. Then `|R| + D_q + 2 k ≤ 2 m + 2`.
Whether this result is new was not verified against the literature. -/
theorem card_rows_add_le (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ((N.primeFactors.erase q).filter (fun p => ¬ (p = 3 ∧ N.factorization 3 = 4))).card
      + (N.primeFactors.filter fun p => q ∣ σ 1 (p ^ N.factorization p)).card
      + 2 * N.primeFactors.card ≤
    2 * ((N.primeFactors ×ˢ N.primeFactors).filter
      (fun x : ℕ × ℕ => x.2 ∣ σ 1 (x.1 ^ N.factorization x.1))).card + 2 := by
  classical
  have hqP : q ∈ N.primeFactors :=
    Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  rw [card_edges_eq_sum_inDegree]
  change _ + inDegree N q + _ ≤ _
  set P := N.primeFactors
  set S := (P.erase q).filter (fun p => ¬ (p = 3 ∧ N.factorization 3 = 4)) with hS
  have hSP : ∀ p ∈ S, p ∈ P ∧ p ≠ q ∧ ¬ (p = 3 ∧ N.factorization 3 = 4) := fun p hp => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    exact ⟨Finset.mem_of_mem_erase h1, Finset.ne_of_mem_erase h1, h2⟩
  set od := fun r => (S.filter fun p => Odd (sigmaWeight N p r)).card with hod
  -- each ordinary row other than `3 ^ 4` has an odd entry
  have hrows : S.card ≤ ∑ r ∈ P, od r := by
    have h1 : S.card ≤ ∑ p ∈ S, (P.filter fun r => Odd (sigmaWeight N p r)).card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨hpP, hpq, h34⟩ := hSP p hp
      obtain ⟨r, hr, hro⟩ := exists_odd_sigmaWeight_of_ne_three_pow_four h hq hodd hpP hpq h34
      exact Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hro⟩⟩
    refine h1.trans_eq ?_
    simp only [hod, Finset.card_filter]
    exact Finset.sum_comm
  have hod_le : ∀ r, od r ≤ inDegree N r := fun r => by
    refine Finset.card_le_card fun p hp => ?_
    obtain ⟨hpS, hw⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(hSP p hpS).1, Nat.dvd_of_factorization_pos hw.pos.ne'⟩
  have hord : ∀ r ∈ P.erase q, od r + 2 ≤ 2 * inDegree N r := by
    intro r hr
    obtain ⟨hrq, hrP⟩ := Finset.mem_erase.mp hr
    have h1 := one_le_inDegree h hrP
    have h2 := hod_le r
    rcases Nat.eq_zero_or_pos (od r) with h0 | h0
    · omega
    · obtain ⟨p, hp⟩ := Finset.card_pos.mp h0
      obtain ⟨hpS, hw⟩ := Finset.mem_filter.mp hp
      have := two_le_inDegree_of_odd h hq hodd hrP hrq (hSP p hpS).1 hw
      omega
  have hsum := Finset.sum_le_sum hord
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem hqP, smul_eq_mul,
    ← Finset.mul_sum] at hsum
  have hodq := Finset.add_sum_erase P od hqP
  have hm := Finset.add_sum_erase P (inDegree N) hqP
  have hq1 := hod_le q
  have hk : 1 ≤ P.card := Finset.card_pos.mpr ⟨q, hqP⟩
  have : (P.card - 1) * 2 + 2 = 2 * P.card := by omega
  omega

/-- **Corollary, all exponents.** For every odd perfect number `N` with special prime `q`,
`3 ω(N) ≤ 2 m + 3`, where `m` is the number of pairs `(p, r)` of prime factors with
`r ∣ σ(p ^ e_p)`. No condition on the exponents is needed.
Whether this result is new was not verified against the literature. -/
theorem three_mul_card_le (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    3 * N.primeFactors.card ≤
      2 * ((N.primeFactors ×ˢ N.primeFactors).filter
        (fun x : ℕ × ℕ => x.2 ∣ σ 1 (x.1 ^ N.factorization x.1))).card + 3 := by
  classical
  have hmain := card_rows_add_le h hq hodd
  have hqP : q ∈ N.primeFactors :=
    Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := N.primeFactors.erase q) (fun p => ¬ (p = 3 ∧ N.factorization 3 = 4))
  rw [Finset.card_erase_of_mem hqP] at hsplit
  have hex : ((N.primeFactors.erase q).filter
      (fun p => ¬ ¬ (p = 3 ∧ N.factorization 3 = 4))).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    push Not at ha' hb'
    rw [ha'.1, hb'.1]
  have hD := one_le_inDegree h hqP
  have hk : 1 ≤ N.primeFactors.card := Finset.card_pos.mpr ⟨q, hqP⟩
  unfold inDegree at hD
  omega

/-- **Corollary, `e_3 ≠ 4`.** For an odd perfect number `N` with special prime `q` and
`v_3(N) ≠ 4`, `3 ω(N) ≤ 2 m + 2`, where `m` is the number of pairs `(p, r)` of prime factors with
`r ∣ σ(p ^ e_p)`. This is the exponent free form of `three_mul_card_le_of_card_ne_two_le` with
`j = 0`.
Whether this result is new was not verified against the literature. -/
theorem three_mul_card_le_of_factorization_three_ne_four (h : OddPerfect N) {q : ℕ}
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (h3 : N.factorization 3 ≠ 4) :
    3 * N.primeFactors.card ≤
      2 * ((N.primeFactors ×ˢ N.primeFactors).filter
        (fun x : ℕ × ℕ => x.2 ∣ σ 1 (x.1 ^ N.factorization x.1))).card + 2 := by
  have hmain := card_rows_add_le h hq hodd
  have hqP : q ∈ N.primeFactors :=
    Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  have hall : (N.primeFactors.erase q).filter (fun p => ¬ (p = 3 ∧ N.factorization 3 = 4)) =
      N.primeFactors.erase q :=
    Finset.filter_true_of_mem fun p _ hp => h3 hp.2
  rw [hall, Finset.card_erase_of_mem hqP] at hmain
  have hD := one_le_inDegree h hqP
  have hk : 1 ≤ N.primeFactors.card := Finset.card_pos.mpr ⟨q, hqP⟩
  unfold inDegree at hD
  omega

end OddPerfect

#print axioms OddPerfect.exists_odd_sigmaWeight_of_ne_three_pow_four
#print axioms OddPerfect.card_rows_add_le
#print axioms OddPerfect.three_mul_card_le
#print axioms OddPerfect.three_mul_card_le_of_factorization_three_ne_four
