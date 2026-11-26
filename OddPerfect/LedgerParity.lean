import OddPerfect.Network
import OddPerfect.Phi3
import OddPerfect.SpecialPrime

/-!
# Parity of incoming valuations and exponent two rows

Let `N` be an odd perfect number with special prime `q`, `k = ω(N)`, and let `m` be the number
of pairs `(p, r)` of prime factors with `r ∣ σ(p ^ e_p)` (the edges of the divisor sum network;
every odd prime dividing some `σ(p ^ e_p)` divides `N`). Write `D_q` for the number of senders
into `q` and `s_2` for the number of prime factors `p ≠ q` with `e_p = 2`.

For such a row `σ(p ^ 2) = p ^ 2 + p + 1` is not a square, so some prime factor `r` of `N`
receives an odd valuation from `p`. If `r ≠ q`, the total valuation `e_r` received by `r` is
even, so a second sender into `r` exists. Hence an ordinary receiver hit by an odd exponent two
row has indegree at least 2, and counting rows by receivers gives
`s_2 + D_q + 2 k ≤ 2 m + 2`, that is `s_2 ≤ 2 (m - k) + 2 - D_q`. The proof does not use
Ljunggren's theorem on `1 + x + ⋯ + x ^ n = y ^ 2`.

Corollary: if at most `j` prime factors `p ≠ q` have `e_p ≠ 2`, then `3 k ≤ 2 m + j + 2`.

Whether these results are new was not verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N : ℕ}

private theorem lp_isSquare {n : ℕ} (hn : n ≠ 0) (h : ∀ p, Even (n.factorization p)) :
    IsSquare n := by
  set m := n.factorization.prod fun p e => p ^ (e / 2)
  have hm : m ^ 2 = n := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    simp only [m, Finsupp.prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, Nat.div_mul_cancel (h p).two_dvd]
  exact ⟨m, by rw [← hm, sq]⟩

/-- An exponent two row has an odd entry: if `e_p = 2`, some prime factor `r` of `N` receives
an odd valuation `v_r(σ(p ^ 2))`, since `σ(p ^ 2) = p ^ 2 + p + 1` is not a square. -/
theorem exists_odd_sigmaWeight_of_factorization_eq_two (h : OddPerfect N) {p : ℕ}
    (hp : p ∈ N.primeFactors) (he : N.factorization p = 2) :
    ∃ r ∈ N.primeFactors, Odd (sigmaWeight N p r) := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  by_contra hno
  push Not at hno
  apply not_isSquare_phi3 hp'.one_lt.le
  rw [← sigma_prime_sq hp']
  refine lp_isSquare (sigma_pos 1 _ (pow_ne_zero _ hp'.ne_zero)).ne' fun r => ?_
  by_cases hr : r ∈ N.primeFactors
  · have := hno r hr
    rw [sigmaWeight, he] at this
    exact this
  · by_contra hev
    have hpos : 0 < (σ 1 (p ^ 2)).factorization r := by
      rcases Nat.eq_zero_or_pos ((σ 1 (p ^ 2)).factorization r) with h0 | h0
      · exact absurd (h0 ▸ ⟨0, rfl⟩) hev
      · exact h0
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors
      (Nat.support_factorization _ ▸ Finsupp.mem_support_iff.mpr hpos.ne')
    have hrd : r ∣ σ 1 (p ^ 2) := Nat.dvd_of_factorization_pos hpos.ne'
    have hr2 : r ≠ 2 := by
      rintro rfl
      have := phi3_odd p
      rw [← sigma_prime_sq hp'] at this
      exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr hrd)
    exact hr (Nat.mem_primeFactors.mpr ⟨hrp, OPNStarter.force_prime h.perfect hp' he hrp hr2 hrd,
      h.ne_zero⟩)

/-- The number of senders into `r`: prime factors `p` of `N` with `r ∣ σ(p ^ e_p)`. -/
def inDegree (N r : ℕ) : ℕ :=
  (N.primeFactors.filter fun p => r ∣ σ 1 (p ^ N.factorization p)).card

/-- The number of edges of the divisor sum network, counted by receivers. -/
theorem card_edges_eq_sum_inDegree (N : ℕ) :
    ((N.primeFactors ×ˢ N.primeFactors).filter
      (fun x : ℕ × ℕ => x.2 ∣ σ 1 (x.1 ^ N.factorization x.1))).card =
      ∑ r ∈ N.primeFactors, inDegree N r := by
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [inDegree, Finset.card_filter]

/-- Every prime factor of an odd perfect number has at least one sender. -/
theorem one_le_inDegree (h : OddPerfect N) {r : ℕ} (hr : r ∈ N.primeFactors) :
    1 ≤ inDegree N r := by
  have hr2 : r ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hr)
  obtain ⟨p, -, hp, -, hd⟩ := exists_sigmaEdge_into h.perfect hr hr2
  exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hd⟩⟩

/-- Parity at an ordinary receiver: if a prime factor `r ≠ q` receives an odd valuation from
some sender, it has at least two senders. -/
theorem two_le_inDegree_of_odd (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) {r p : ℕ} (hr : r ∈ N.primeFactors) (hrq : r ≠ q)
    (hp : p ∈ N.primeFactors) (hw : Odd (sigmaWeight N p r)) : 2 ≤ inDegree N r := by
  have hr' := Nat.prime_of_mem_primeFactors hr
  have hr2 : r ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hr)
  have hpd : r ∣ σ 1 (p ^ N.factorization p) := Nat.dvd_of_factorization_pos hw.pos.ne'
  by_contra hlt
  push Not at hlt
  have hsum := sigmaWeight_sum_eq h.perfect hr' hr2
  rw [Finset.sum_eq_single p (fun p' hp' hne => ?_) (fun hn => absurd hp hn)] at hsum
  · exact (Nat.not_even_iff_odd.mpr hw) (hsum ▸ even_factorization_of_ne h hq hodd hr' hrq)
  · by_contra hw'
    have hd' : r ∣ σ 1 (p' ^ N.factorization p') := Nat.dvd_of_factorization_pos hw'
    have : 1 < inDegree N r := Finset.one_lt_card.mpr ⟨p', Finset.mem_filter.mpr ⟨hp', hd'⟩,
      p, Finset.mem_filter.mpr ⟨hp, hpd⟩, hne⟩
    omega

/-- **Exponent two rows and parity.** Let `N` be an odd perfect number with special prime `q`,
`k = ω(N)`, `m` the number of pairs `(p, r)` of prime factors with `r ∣ σ(p ^ e_p)`, `D_q` the
number of senders into `q`, and `s_2` the number of prime factors `p ≠ q` with `e_p = 2`. Then
`s_2 + D_q + 2 k ≤ 2 m + 2`, i.e. `s_2 ≤ 2 (m - k) + 2 - D_q`.
Whether this result is new was not verified against the literature. -/
theorem card_sq_rows_add_le (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ((N.primeFactors.erase q).filter (fun p => N.factorization p = 2)).card
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
  set S2 := (P.erase q).filter (fun p => N.factorization p = 2) with hS2
  have hS2P : ∀ p ∈ S2, p ∈ P ∧ N.factorization p = 2 := fun p hp => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    exact ⟨Finset.mem_of_mem_erase h1, h2⟩
  set od := fun r => (S2.filter fun p => Odd (sigmaWeight N p r)).card with hod
  -- each exponent two row has an odd entry
  have hrows : S2.card ≤ ∑ r ∈ P, od r := by
    have h1 : S2.card ≤ ∑ p ∈ S2, (P.filter fun r => Odd (sigmaWeight N p r)).card := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨hpP, he⟩ := hS2P p hp
      obtain ⟨r, hr, hro⟩ := exists_odd_sigmaWeight_of_factorization_eq_two h hpP he
      exact Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hro⟩⟩
    refine h1.trans_eq ?_
    simp only [hod, Finset.card_filter]
    exact Finset.sum_comm
  have hod_le : ∀ r, od r ≤ inDegree N r := fun r => by
    refine Finset.card_le_card fun p hp => ?_
    obtain ⟨hpS, hw⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(hS2P p hpS).1, Nat.dvd_of_factorization_pos hw.pos.ne'⟩
  have hord : ∀ r ∈ P.erase q, od r + 2 ≤ 2 * inDegree N r := by
    intro r hr
    obtain ⟨hrq, hrP⟩ := Finset.mem_erase.mp hr
    have h1 := one_le_inDegree h hrP
    have h2 := hod_le r
    rcases Nat.eq_zero_or_pos (od r) with h0 | h0
    · omega
    · obtain ⟨p, hp⟩ := Finset.card_pos.mp h0
      obtain ⟨hpS, hw⟩ := Finset.mem_filter.mp hp
      have := two_le_inDegree_of_odd h hq hodd hrP hrq (hS2P p hpS).1 hw
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

/-- **Corollary.** If at most `j` prime factors `p ≠ q` of an odd perfect number `N` have
`e_p ≠ 2`, then `3 ω(N) ≤ 2 m + j + 2` with `m` the number of pairs `(p, r)` of prime factors
with `r ∣ σ(p ^ e_p)`. In particular, if every `p ≠ q` has `e_p = 2`, then `3 ω(N) ≤ 2 m + 2`.
Whether this result is new was not verified against the literature. -/
theorem three_mul_card_le_of_card_ne_two_le (h : OddPerfect N) {q j : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hj : ((N.primeFactors.erase q).filter (fun p => N.factorization p ≠ 2)).card ≤ j) :
    3 * N.primeFactors.card ≤
      2 * ((N.primeFactors ×ˢ N.primeFactors).filter
        (fun x : ℕ × ℕ => x.2 ∣ σ 1 (x.1 ^ N.factorization x.1))).card + j + 2 := by
  have hmain := card_sq_rows_add_le h hq hodd
  have hqP : q ∈ N.primeFactors :=
    Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := N.primeFactors.erase q) (fun p => N.factorization p = 2)
  rw [Finset.card_erase_of_mem hqP] at hsplit
  have hD := one_le_inDegree h hqP
  have hk : 1 ≤ N.primeFactors.card := Finset.card_pos.mpr ⟨q, hqP⟩
  unfold inDegree at hD
  simp only [ne_eq] at hj
  omega

end OddPerfect

#print axioms OddPerfect.exists_odd_sigmaWeight_of_factorization_eq_two
#print axioms OddPerfect.card_edges_eq_sum_inDegree
#print axioms OddPerfect.one_le_inDegree
#print axioms OddPerfect.two_le_inDegree_of_odd
#print axioms OddPerfect.card_sq_rows_add_le
#print axioms OddPerfect.three_mul_card_le_of_card_ne_two_le
