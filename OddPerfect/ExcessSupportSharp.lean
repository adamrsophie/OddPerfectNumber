import OddPerfect.UnconditionalSupport

/-!
# Prime factors against total excess: the rows through the special prime

Let `N` be an odd perfect number with special prime `q` of exponent `a`, and let
`T = ∑ (v_p(N) / 2 - 1)` over the prime factors `p ≠ q` be the total excess. The library proves
`ω(N) ≤ 5 * T + 7` for every special prime (`card_primeFactors_le_five_excess_add_seven`).

The counting behind that bound lets a square prime `p` (an ordinary prime of exponent 2) be
paid by one unit of weight at an ordinary receiver: a prime factor `r ≠ q`, `r ≠ 3` with
`r ≡ 1 (mod 3)` (`ordReceivers`). The slope 5 comes from receivers of exponent 4, each paid
by four such rows. Split the square primes by the weight `recvWeight` they send to the ordinary
receivers:

* weight 0: escape rows (at most two, `card_escapeRows_le_two`);
* weight 1 and no weight at `q`: then `phi3 p` is `r` or `3 * r` for a receiver `r`, and
  `p ↦ r` is injective (`card_freeRows_le`);
* weight 1 and some weight at `q`: the rows through `q` (`throughRows`), not capped here;
* weight at least 2.

This gives, for every special prime and with no special exponent,
`2 * ω(N) + 3 * v_3(σ(q ^ a)) ≤ 7 * T + 13 + #(rows through q)`
(`two_mul_card_primeFactors_add_three_mul_le`). So the slope drops from 5 to 7/2 except for
the rows through `q`; a cap on those rows is what an improvement of `ω(N) ≤ 5 * T + 7` itself
needs. The bound for `ω(N)` alone is not improved here.

The source of the count is the proof of the published inequality named in `ExcessSupport`. The
total excess is not bounded, and the odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The ordinary receivers: prime factors `r ≠ q`, `r ≠ 3` with `r ≡ 1 (mod 3)`. -/
def ordReceivers (N q : ℕ) : Finset ℕ :=
  N.primeFactors.filter fun r => r ≠ q ∧ r ≠ 3 ∧ r % 3 = 1

/-- The weight that `p` sends to the ordinary receivers. -/
def recvWeight (N q p : ℕ) : ℕ := ∑ r ∈ ordReceivers N q, sigmaWeight N p r

/-- The free rows: square primes that send weight exactly 1 to the ordinary receivers and no
weight to `q`. -/
def freeRows (N q : ℕ) : Finset ℕ :=
  (squarePrimes N q).filter fun p => recvWeight N q p = 1 ∧ sigmaWeight N p q = 0

/-- The rows through `q`: square primes that send weight exactly 1 to the ordinary receivers
and some weight to `q`. -/
def throughRows (N q : ℕ) : Finset ℕ :=
  (squarePrimes N q).filter fun p => recvWeight N q p = 1 ∧ sigmaWeight N p q ≠ 0

/-- The part of `phi3 p` prime to 3. -/
def rowCore (p : ℕ) : ℕ := if 3 ∣ phi3 p then phi3 p / 3 else phi3 p

private theorem mem_squarePrimes' {N q p : ℕ} : p ∈ squarePrimes N q ↔
    p ∈ N.primeFactors ∧ p ≠ q ∧ N.factorization p = 2 := by
  simp only [squarePrimes, Finset.mem_filter]

private theorem sigmaWeight_sq {N q p r : ℕ} (hp : p ∈ squarePrimes N q) :
    sigmaWeight N p r = (phi3 p).factorization r := by
  obtain ⟨hpN, -, he⟩ := mem_squarePrimes'.mp hp
  rw [sigmaWeight, he, sigma_prime_sq (Nat.prime_of_mem_primeFactors hpN)]

private theorem phi3_ne_zero' (p : ℕ) : phi3 p ≠ 0 := by unfold phi3; omega

/-- A prime factor `t ≠ 3`, `t ≠ q` of `phi3 p`, for a square prime `p`, is an ordinary
receiver with weight at least 1 from `p`. -/
private theorem receiver_of_dvd {N q p t : ℕ} (h : OddPerfect N) (hp : p ∈ squarePrimes N q)
    (ht : t.Prime) (htd : t ∣ phi3 p) (ht3 : t ≠ 3) (htq : t ≠ q) :
    t ∈ ordReceivers N q ∧ 1 ≤ sigmaWeight N p t := by
  have hw : 1 ≤ sigmaWeight N p t := by
    rw [sigmaWeight_sq hp]
    exact ht.factorization_pos_of_dvd (phi3_ne_zero' p) htd
  have h1 : t % 3 = 1 := prime_dvd_phi3_mod_three ht ht3 htd
  have htN : t ∈ N.primeFactors :=
    mem_primeFactors_of_sigmaWeight_ne_zero h.perfect (mem_squarePrimes'.mp hp).1 (by omega)
      (by omega)
  exact ⟨Finset.mem_filter.mpr ⟨htN, htq, ht3, h1⟩, hw⟩

private theorem le_recvWeight {N q p r : ℕ} (hr : r ∈ ordReceivers N q) :
    sigmaWeight N p r ≤ recvWeight N q p :=
  Finset.single_le_sum (f := fun r => sigmaWeight N p r) (fun _ _ => Nat.zero_le _) hr

/-- A square prime that is not an escape row sends weight at least 1 to the ordinary
receivers. -/
theorem one_le_recvWeight {N q p : ℕ} (h : OddPerfect N) (hp : p ∈ squarePrimes N q)
    (hne : ¬ ∀ r ∈ (phi3 p).primeFactors, r = 3 ∨ r = q) : 1 ≤ recvWeight N q p := by
  push Not at hne
  obtain ⟨r, hr, hr3, hrq⟩ := hne
  obtain ⟨hR, hw⟩ := receiver_of_dvd h hp (Nat.prime_of_mem_primeFactors hr)
    (Nat.dvd_of_mem_primeFactors hr) hr3 hrq
  exact hw.trans (le_recvWeight hR)

/-- Conservation at the ordinary receivers: the square primes send them at most their total
exponent. -/
theorem sum_recvWeight_le {N q : ℕ} (h : OddPerfect N) :
    ∑ p ∈ squarePrimes N q, recvWeight N q p ≤
      ∑ r ∈ ordReceivers N q, N.factorization r := by
  simp only [recvWeight]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun r hr => ?_
  obtain ⟨hrN, -, -, hr1⟩ := Finset.mem_filter.mp hr
  rw [← sigmaWeight_sum_eq h.perfect (Nat.prime_of_mem_primeFactors hrN) (by omega)]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The row count with weights: `2 * #square primes ≤ 2 * #escape rows + #rows through q +
#free rows + ∑ v_r(N)` over the ordinary receivers. -/
theorem two_mul_card_squarePrimes_le {N q : ℕ} (h : OddPerfect N) :
    2 * (squarePrimes N q).card ≤ 2 * (escapeRows N q).card + (throughRows N q).card +
      (freeRows N q).card + ∑ r ∈ ordReceivers N q, N.factorization r := by
  have hpt : ∀ p ∈ squarePrimes N q, 2 ≤ recvWeight N q p +
      (if recvWeight N q p = 1 ∧ sigmaWeight N p q ≠ 0 then 1 else 0) +
      (if recvWeight N q p = 1 ∧ sigmaWeight N p q = 0 then 1 else 0) +
      2 * (if ∀ r ∈ (phi3 p).primeFactors, r = 3 ∨ r = q then 1 else 0) := by
    intro p hp
    by_cases hesc : ∀ r ∈ (phi3 p).primeFactors, r = 3 ∨ r = q
    · rw [if_pos hesc]
      omega
    · have := one_le_recvWeight h hp hesc
      rw [if_neg hesc]
      split_ifs <;> omega
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hsum
  have e1 : (throughRows N q).card = ∑ p ∈ squarePrimes N q,
      (if recvWeight N q p = 1 ∧ sigmaWeight N p q ≠ 0 then 1 else 0) := Finset.card_filter _ _
  have e2 : (freeRows N q).card = ∑ p ∈ squarePrimes N q,
      (if recvWeight N q p = 1 ∧ sigmaWeight N p q = 0 then 1 else 0) := Finset.card_filter _ _
  have e3 : (escapeRows N q).card = ∑ p ∈ squarePrimes N q,
      (if ∀ r ∈ (phi3 p).primeFactors, r = 3 ∨ r = q then 1 else 0) := Finset.card_filter _ _
  have := sum_recvWeight_le (q := q) h
  omega

/-- `phi3 p` is `rowCore p` or `3 * rowCore p`. -/
theorem phi3_eq_rowCore (p : ℕ) : phi3 p = rowCore p ∨ phi3 p = 3 * rowCore p := by
  unfold rowCore
  split_ifs with h3
  · exact Or.inr (Nat.mul_div_cancel' h3).symm
  · exact Or.inl rfl

private theorem not_three_dvd_rowCore (p : ℕ) : ¬ 3 ∣ rowCore p := by
  unfold rowCore
  split_ifs with h3
  · rintro ⟨c, hc⟩
    exact not_nine_dvd_phi3 p ⟨c, by rw [← Nat.mul_div_cancel' h3, hc]; ring⟩
  · exact h3

/-- For a free row `p`, the part of `phi3 p` prime to 3 is a prime and an ordinary
receiver. -/
theorem rowCore_mem_of_mem_freeRows {N q p : ℕ} (h : OddPerfect N)
    (hp : p ∈ freeRows N q) : (rowCore p).Prime ∧ rowCore p ∈ ordReceivers N q := by
  obtain ⟨hpS, hw1, hwq⟩ := Finset.mem_filter.mp hp
  have hn3 := not_three_dvd_rowCore p
  have hnd : rowCore p ∣ phi3 p := by
    rcases phi3_eq_rowCore p with e | e
    · rw [e]
    · rw [e]; exact dvd_mul_left _ _
  have hn0 : rowCore p ≠ 0 := fun h0 => phi3_ne_zero' p (Nat.eq_zero_of_zero_dvd (h0 ▸ hnd))
  have hn1 : rowCore p ≠ 1 := by
    intro h1
    have hp2 := (Nat.prime_of_mem_primeFactors (mem_squarePrimes'.mp hpS).1).two_le
    have h7 : 7 ≤ phi3 p := by unfold phi3; nlinarith
    rcases phi3_eq_rowCore p with e | e <;> rw [h1] at e <;> omega
  have hrec : ∀ {d : ℕ}, d.Prime → d ∣ rowCore p →
      d ∈ ordReceivers N q ∧ 1 ≤ sigmaWeight N p d := by
    intro d hd hdn
    have hdp := hdn.trans hnd
    refine receiver_of_dvd h hpS hd hdp ?_ ?_
    · rintro rfl
      exact hn3 hdn
    · rintro rfl
      have := hd.factorization_pos_of_dvd (phi3_ne_zero' p) hdp
      rw [← sigmaWeight_sq hpS] at this
      omega
  obtain ⟨d0, hd0, hd0n⟩ : ∃ d, d.Prime ∧ d ∣ rowCore p :=
    ⟨_, Nat.minFac_prime hn1, Nat.minFac_dvd _⟩
  obtain ⟨hR0, -⟩ := hrec hd0 hd0n
  have huniq : ∀ {d : ℕ}, d.Prime → d ∣ rowCore p → d = d0 := by
    intro d hd hdn
    by_contra hne
    obtain ⟨hR, hw⟩ := hrec hd hdn
    obtain ⟨-, hw0⟩ := hrec hd0 hd0n
    have hsub : ({d, d0} : Finset ℕ) ⊆ ordReceivers N q := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hR
      · exact hR0
    have hle : ∑ r ∈ ({d, d0} : Finset ℕ), sigmaWeight N p r ≤ recvWeight N q p :=
      Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_pair hne] at hle
    omega
  obtain ⟨k, hk⟩ : ∃ k, rowCore p = d0 ^ k :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn0 huniq⟩
  have hd03 : d0 ≠ 3 := fun e => hn3 (e ▸ hd0n)
  have hfac : (phi3 p).factorization d0 = k := by
    rcases phi3_eq_rowCore p with e | e
    · rw [e, hk, hd0.factorization_pow, Finsupp.single_eq_same]
    · have h30 : (3 : ℕ).factorization d0 = 0 := Nat.factorization_eq_zero_of_not_dvd
        (fun hd => hd03 ((Nat.prime_dvd_prime_iff_eq hd0 Nat.prime_three).mp hd))
      rw [e, Nat.factorization_mul (by norm_num) hn0, Finsupp.add_apply, h30, zero_add, hk,
        hd0.factorization_pow, Finsupp.single_eq_same]
  have hk1 : k = 1 := by
    have h1 := le_recvWeight (p := p) hR0
    rw [sigmaWeight_sq hpS, hfac, hw1] at h1
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (by rw [hk, h0, pow_zero]) hn1
    · omega
  have hc : rowCore p = d0 := by rw [hk, hk1, pow_one]
  exact ⟨by rw [hc]; exact hd0, by rw [hc]; exact hR0⟩

/-- At most one free row per ordinary receiver: `#free rows ≤ #ordinary receivers`. -/
theorem card_freeRows_le {N q : ℕ} (h : OddPerfect N) :
    (freeRows N q).card ≤ (ordReceivers N q).card := by
  refine Finset.card_le_card_of_injOn rowCore
    (fun p hp => (rowCore_mem_of_mem_freeRows h hp).2) ?_
  intro a ha b hb hab
  have hS : ∀ {x}, x ∈ freeRows N q → x.Prime := fun hx =>
    Nat.prime_of_mem_primeFactors (mem_squarePrimes'.mp (Finset.mem_filter.mp hx).1).1
  have hca := (rowCore_mem_of_mem_freeRows h ha).1
  have hcb := (rowCore_mem_of_mem_freeRows h hb).1
  have hab' : rowCore a = rowCore b := hab
  rcases phi3_eq_rowCore a with ea | ea <;> rcases phi3_eq_rowCore b with eb | eb
  · exact phi3_strictMono.injective (by rw [ea, eb, hab'])
  · have hpa : (phi3 a).Prime := by rw [ea]; exact hca
    exact absurd (show phi3 b = 3 * phi3 a by rw [eb, ea, hab'])
      (no_phi3_eq_three_mul_phi3 (hS hb) hpa)
  · have hpb : (phi3 b).Prime := by rw [eb]; exact hcb
    exact absurd (show phi3 a = 3 * phi3 b by rw [ea, eb, hab'])
      (no_phi3_eq_three_mul_phi3 (hS ha) hpb)
  · exact phi3_strictMono.injective (by rw [ea, eb, hab'])

private theorem sum_ite_three (N : ℕ) (g : ℕ → ℕ) (hg : g 0 = 0) :
    ∑ p ∈ N.primeFactors, (if p = 3 then g (N.factorization p) else 0) =
      g (N.factorization 3) := by
  rw [Finset.sum_ite_eq']
  split_ifs with h3
  · rfl
  · rw [Finsupp.notMem_support_iff.mp (by rw [Nat.support_factorization]; exact h3), hg]

/-- The receivers with their count: with `C` the square primes that are 1 modulo 3, `E` the
prime factors `p ≠ q` of exponent at least 4 and `b = v_3(N)`,
`∑ v_r(N) + #receivers + 2 * #E + (3 * b if b ≥ 4) ≤ 3 * #C + 7 * T + (7 if b ≥ 4)`. -/
theorem receivers_add_le {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ∑ r ∈ ordReceivers N q, N.factorization r + (ordReceivers N q).card +
        2 * ((N.primeFactors.erase q).filter fun p => 4 ≤ N.factorization p).card +
        (if 4 ≤ N.factorization 3 then 3 * N.factorization 3 else 0) ≤
      3 * ((squarePrimes N q).filter fun p => p % 3 = 1).card +
        7 * ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) +
        (if 4 ≤ N.factorization 3 then 7 else 0) := by
  have h3q : (3 : ℕ) ≠ q := by
    rintro rfl
    have := (special_mod_four h hq hodd).1
    omega
  have hpt : ∀ p ∈ N.primeFactors,
      (if p ≠ q ∧ p ≠ 3 ∧ p % 3 = 1 then N.factorization p else 0) +
        (if p ≠ q ∧ p ≠ 3 ∧ p % 3 = 1 then 1 else 0) +
        2 * (if p ≠ q ∧ 4 ≤ N.factorization p then 1 else 0) +
        (if p = 3 then (if 4 ≤ N.factorization p then 3 * N.factorization p else 0) else 0) ≤
      3 * (if (p ≠ q ∧ N.factorization p = 2) ∧ p % 3 = 1 then 1 else 0) +
        7 * (if p ≠ q then N.factorization p / 2 - 1 else 0) +
        (if p = 3 then (if 4 ≤ N.factorization p then 7 else 0) else 0) := by
    intro p hp
    by_cases hpq : p = q
    · split_ifs <;> omega
    · obtain ⟨j, hj⟩ :=
        even_factorization_of_ne h hq hodd (Nat.prime_of_mem_primeFactors hp) hpq
      have hpos := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd h.ne_zero
        (Nat.dvd_of_mem_primeFactors hp)
      split_ifs <;> omega
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hsum
  have e1 : ∑ r ∈ ordReceivers N q, N.factorization r = ∑ p ∈ N.primeFactors,
      (if p ≠ q ∧ p ≠ 3 ∧ p % 3 = 1 then N.factorization p else 0) := Finset.sum_filter _ _
  have e2 : (ordReceivers N q).card = ∑ p ∈ N.primeFactors,
      (if p ≠ q ∧ p ≠ 3 ∧ p % 3 = 1 then 1 else 0) := Finset.card_filter _ _
  have e3 : ((N.primeFactors.erase q).filter fun p => 4 ≤ N.factorization p).card =
      ∑ p ∈ N.primeFactors, (if p ≠ q ∧ 4 ≤ N.factorization p then 1 else 0) := by
    rw [← Finset.filter_ne', Finset.filter_filter, Finset.card_filter]
  have e4 : ((squarePrimes N q).filter fun p => p % 3 = 1).card =
      ∑ p ∈ N.primeFactors,
        (if (p ≠ q ∧ N.factorization p = 2) ∧ p % 3 = 1 then 1 else 0) := by
    rw [squarePrimes, Finset.filter_filter, Finset.card_filter]
  have e5 : ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) =
      ∑ p ∈ N.primeFactors, (if p ≠ q then N.factorization p / 2 - 1 else 0) := by
    rw [← Finset.filter_ne', Finset.sum_filter]
  have e6 : ∑ p ∈ N.primeFactors,
      (if p = 3 then (if 4 ≤ N.factorization p then 3 * N.factorization p else 0) else 0) =
      (if 4 ≤ N.factorization 3 then 3 * N.factorization 3 else 0) :=
    sum_ite_three N (fun e => if 4 ≤ e then 3 * e else 0) (by simp)
  have e7 : ∑ p ∈ N.primeFactors,
      (if p = 3 then (if 4 ≤ N.factorization p then 7 else 0) else 0) =
      (if 4 ≤ N.factorization 3 then 7 else 0) :=
    sum_ite_three N (fun e => if 4 ≤ e then 7 else 0) (by simp)
  omega

/-- For every special prime `q` of an odd perfect number `N` with exponent `a`, and `T` the
total excess, `2 * ω(N) + 3 * v_3(σ(q ^ a)) ≤ 7 * T + 13 + #(rows through q)`. Unconditional.
The total excess is not bounded, and the rows through `q` are not capped here. -/
theorem two_mul_card_primeFactors_add_three_mul_le {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    2 * N.primeFactors.card + 3 * padicValNat 3 (σ 1 (q ^ N.factorization q)) ≤
      7 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 13 +
        (throughRows N q).card := by
  have hD := card_primeFactors_le_split h hq hodd
  have hK := two_mul_card_squarePrimes_le (q := q) h
  have hI := card_freeRows_le (N := N) (q := q) h
  have hP := receivers_add_le h hq hodd
  have hB := card_squarePrimes_one_add_le h hq hodd
  have hE := card_escapeRows_le_two h hq hodd
  have h3q : (3 : ℕ) ≠ q := by
    rintro rfl
    have := (special_mod_four h hq hodd).1
    omega
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd Nat.prime_three h3q
  split_ifs at hP <;> omega

/-- For every special prime, `2 * ω(N) ≤ 7 * T + 13 + #(rows through q)`, where `T` is the
total excess. The total excess is not bounded. -/
theorem two_mul_card_primeFactors_le_seven_excess_add_throughRows {N q : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    2 * N.primeFactors.card ≤
      7 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 13 +
        (throughRows N q).card := by
  have := two_mul_card_primeFactors_add_three_mul_le h hq hodd
  omega

end OddPerfect

#print axioms OddPerfect.one_le_recvWeight
#print axioms OddPerfect.sum_recvWeight_le
#print axioms OddPerfect.two_mul_card_squarePrimes_le
#print axioms OddPerfect.phi3_eq_rowCore
#print axioms OddPerfect.rowCore_mem_of_mem_freeRows
#print axioms OddPerfect.card_freeRows_le
#print axioms OddPerfect.receivers_add_le
#print axioms OddPerfect.two_mul_card_primeFactors_add_three_mul_le
#print axioms OddPerfect.two_mul_card_primeFactors_le_seven_excess_add_throughRows
