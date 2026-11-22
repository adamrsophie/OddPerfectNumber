import OddPerfect.LedgerPrime
import OddPerfect.LedgerParityTwo
import OddPerfect.Zsigmondy

/-!
# Pure prime power rows

A row of a number `N` at a prime factor `p` is *pure* if `σ(p ^ e_p) = r ^ w` for a prime `r`
(then `w ≥ 1` automatically). This module extends the facts known for rows with prime value
(`OddPerfect/LedgerPrime.lean`) to rows whose value is a prime power.

Scope: this module excludes nothing and removes no family of odd perfect numbers. It records
local facts about a pure row, a growth property of the full components along pure rows of an
odd perfect number, the absence of cycles of pure rows, and a fan-out inequality for the family
in which every ordinary row is pure.

* Local facts (for an odd prime `p` and an even exponent `e > 0`): the index `e + 1` is prime,
  the receiver satisfies `r ≡ 1 (mod e + 1)` (this only needs `e ≥ 2`), and the weight `w` is
  odd except for `σ(3 ^ 4) = 11 ^ 2`.
* Growth: along a pure row `p → r` of an odd perfect number, `p ^ e_p < r ^ e_r`. No parity
  hypothesis on `e_p` is needed: the special row cannot be pure, since `σ(q ^ e_q)` is even and
  `v_2(σ(N)) = 1` while `σ(q ^ e_q) ≥ 4`.
* No cycles: the relation `PureEdge N` has no cycle (`¬ TransGen (PureEdge N) p p`).
  In a general odd perfect number a maximal path of pure rows ends at the special prime or at a
  row with at least two receivers, so the absence of cycles among pure rows does not make the
  whole divisibility graph a forest.
* Fan-out: if every ordinary row is pure, then `|R| + D_q ≤ 2 d_q`, where `R` is the set of
  ordinary prime factors other than `3` when `e_3 = 4`, `D_q` is the number of senders into the
  special prime `q`, and `d_q` the number of prime factors of `N` dividing `σ(q ^ e_q)`. The
  inequality can hold with equality in the abstract; it is not a contradiction.

Whether these results are new was not verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- A prime dividing `r ^ w` for a prime `r` is `r`. -/
private theorem eq_of_prime_dvd_prime_pow {t r w : ℕ} (ht : t.Prime) (hr : r.Prime)
    (h : t ∣ r ^ w) : t = r :=
  (Nat.prime_dvd_prime_iff_eq ht hr).mp (ht.dvd_of_dvd_pow h)

/-- **Prime index.** If `p` is an odd prime, `e > 0` is even and `σ(p ^ e) = r ^ w` for a prime
`r`, then `e + 1` is prime. -/
theorem prime_succ_of_sigma_prime_pow_eq_prime_pow {p e r w : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : Even e) (he0 : e ≠ 0) (hr : r.Prime) (hrow : σ 1 (p ^ e) = r ^ w) :
    (e + 1).Prime := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨j, hj⟩ := he
  have hn3 : 3 ≤ e + 1 := by omega
  by_contra hnp
  have hlt := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
  have hap := Nat.minFac_prime (show e + 1 ≠ 1 by omega)
  have had := Nat.minFac_dvd (e + 1)
  have ha3 : 3 ≤ (e + 1).minFac := by
    have := hap.two_le
    rcases Nat.lt_or_ge (e + 1).minFac 3 with h | h
    · have h2 : (e + 1).minFac = 2 := by omega
      rw [h2] at had
      omega
    · exact h
  obtain ⟨t₁, ht₁, hd₁, ho₁, -⟩ := exists_prime_dvd_sigma_orderOf_eq hp hp3 ha3 had
  obtain ⟨t₂, ht₂, hd₂, ho₂, -⟩ := exists_prime_dvd_sigma_orderOf_eq hp hp3 hn3 (dvd_refl _)
  rw [hrow] at hd₁ hd₂
  rw [eq_of_prime_dvd_prime_pow ht₁ hr hd₁] at ho₁
  rw [eq_of_prime_dvd_prime_pow ht₂ hr hd₂] at ho₂
  omega

/-- **Receiver modulo the index.** If `p` is an odd prime, `e ≥ 2` and `σ(p ^ e) = r ^ w` for a
prime `r`, then `r ≡ 1 (mod e + 1)`; in particular `r ≠ e + 1`. -/
theorem receiver_mod_index_of_pure {p e r w : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he2 : 2 ≤ e)
    (hr : r.Prime) (hrow : σ 1 (p ^ e) = r ^ w) : r % (e + 1) = 1 := by
  obtain ⟨t, ht, hd, -, hmod⟩ := exists_prime_dvd_sigma_orderOf_eq hp
    (by have := hp.two_le; omega) (by omega : 3 ≤ e + 1) (dvd_refl _)
  rw [hrow] at hd
  rw [← eq_of_prime_dvd_prime_pow ht hr hd]
  exact hmod

/-- **Odd weight.** If `p` is an odd prime, `e > 0` is even and `σ(p ^ e) = r ^ w` for a prime
`r`, then `w` is odd, except for `σ(3 ^ 4) = 11 ^ 2`. -/
theorem odd_weight_or_three_pow_four {p e r w : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : Even e)
    (he0 : e ≠ 0) (hr : r.Prime) (hrow : σ 1 (p ^ e) = r ^ w) :
    Odd w ∨ (p = 3 ∧ e = 4 ∧ r = 11 ∧ w = 2) := by
  rcases Nat.even_or_odd w with ⟨j, hj⟩ | hw
  · right
    have hsq : IsSquare (σ 1 (p ^ e)) := ⟨r ^ j, by rw [hrow, hj, pow_add]⟩
    obtain ⟨rfl, rfl⟩ := (isSquare_sigma_prime_pow_iff hp hp2 he he0).mp hsq
    have h121 : σ 1 (3 ^ 4) = 11 ^ 2 := by
      rw [sigma_one_apply_prime_pow Nat.prime_three]
      simp [Finset.sum_range_succ]
    rw [h121] at hrow
    have hw0 : w ≠ 0 := by
      rintro rfl
      norm_num at hrow
    have hr11 : r = 11 :=
      eq_of_prime_dvd_prime_pow hr (by norm_num) (hrow ▸ dvd_pow_self r hw0)
    subst hr11
    exact ⟨rfl, rfl, rfl, ((Nat.pow_right_inj (by norm_num)).mp hrow).symm⟩
  · exact Or.inl hw

/-- **The receiver of a pure row.** If `p` is a prime factor of an odd perfect number `N` and
`σ(p ^ e_p) = r ^ w` for a prime `r`, then `r` is a prime factor of `N` and `1 ≤ w ≤ e_r`. -/
theorem receiver_of_pure_row {N p r w : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors)
    (hr : r.Prime) (hrow : σ 1 (p ^ N.factorization p) = r ^ w) :
    r ∈ N.primeFactors ∧ w ≠ 0 ∧ w ≤ N.factorization r := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  have he0 : N.factorization p ≠ 0 :=
    (hp'.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)).ne'
  have hlt : p < r ^ w := hrow ▸ lt_sigma_prime_pow hp' he0
  have hdvd : r ^ w ∣ 2 * N := hrow ▸ OPNStarter.component_sigma_dvd h.perfect hp' rfl
  have hp2 := hp'.two_le
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hlt
    omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    rcases Nat.lt_or_ge w 2 with hw | hw
    · have : w = 1 := by omega
      subst this
      omega
    · have h4 : 2 * 2 ∣ 2 * N :=
        (show 2 * 2 ∣ 2 ^ w from ⟨2 ^ (w - 2), by rw [← pow_two, ← pow_add]; congr 1; omega⟩).trans
          hdvd
      exact h.not_two_dvd ((Nat.mul_dvd_mul_iff_left (by norm_num)).mp h4)
  have hcop : Nat.Coprime (r ^ w) 2 :=
    Nat.Coprime.pow_left w ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  have hN : r ^ w ∣ N := hcop.dvd_of_dvd_mul_left hdvd
  exact ⟨Nat.mem_primeFactors.mpr ⟨hr, (dvd_pow_self r hw0).trans hN, h.ne_zero⟩, hw0,
    (hr.pow_dvd_iff_le_factorization h.ne_zero).mp hN⟩

/-- **Growth along a pure row.** If `p` is a prime factor of an odd perfect number `N` and
`σ(p ^ e_p) = r ^ w` for a prime `r`, then `p ^ e_p < r ^ e_r`. -/
theorem component_lt_of_pure_row {N p r w : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors)
    (hr : r.Prime) (hrow : σ 1 (p ^ N.factorization p) = r ^ w) :
    p ^ N.factorization p < r ^ N.factorization r := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  have he0 : N.factorization p ≠ 0 :=
    (hp'.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)).ne'
  obtain ⟨-, -, hwle⟩ := receiver_of_pure_row h hp hr hrow
  have hσ : p ^ N.factorization p < σ 1 (p ^ N.factorization p) := by
    rw [sigma_one_apply_prime_pow hp', Finset.sum_range_succ]
    have : 0 < ∑ i ∈ Finset.range (N.factorization p), p ^ i :=
      Finset.sum_pos (fun i _ => pow_pos hp'.pos i) (Finset.nonempty_range_iff.mpr he0)
    omega
  rw [hrow] at hσ
  exact hσ.trans_le (Nat.pow_le_pow_right hr.pos hwle)

/-- The pure row relation of `N`: `p` and `r` are prime factors of `N` and
`σ(p ^ e_p)` is a power of `r`. -/
def PureEdge (N p r : ℕ) : Prop :=
  p ∈ N.primeFactors ∧ r ∈ N.primeFactors ∧ ∃ w, σ 1 (p ^ N.factorization p) = r ^ w

/-- Along a path of pure rows of an odd perfect number the full component strictly grows. -/
theorem component_lt_of_transGen_pureEdge {N a b : ℕ} (h : OddPerfect N)
    (hab : Relation.TransGen (PureEdge N) a b) :
    a ^ N.factorization a < b ^ N.factorization b := by
  induction hab with
  | single hab =>
    obtain ⟨ha, hb, w, hw⟩ := hab
    exact component_lt_of_pure_row h ha (Nat.prime_of_mem_primeFactors hb) hw
  | tail _ hbc ih =>
    obtain ⟨hb, hc, w, hw⟩ := hbc
    exact ih.trans (component_lt_of_pure_row h hb (Nat.prime_of_mem_primeFactors hc) hw)

/-- **No cycle of pure rows.** In an odd perfect number no prime factor reaches itself along a
path of pure rows. -/
theorem not_transGen_pureEdge_self {N : ℕ} (h : OddPerfect N) (p : ℕ) :
    ¬ Relation.TransGen (PureEdge N) p p := fun hp =>
  lt_irrefl _ (component_lt_of_transGen_pureEdge h hp)

/-- **Fan-out when every ordinary row is pure.** Let `N` be an odd perfect number with special
prime `q`. If `σ(p ^ e_p)` is a prime power for every prime factor `p ≠ q`, then
`|R| + D_q ≤ 2 d_q`, where `R` is the set of prime factors `p ≠ q` other than `3` when `e_3 = 4`,
`D_q` the number of senders into `q`, and `d_q` the number of prime factors of `N` dividing
`σ(q ^ e_q)`. That every ordinary row is pure is a case hypothesis, not known to hold.
Whether this result is new was not verified against the literature. -/
theorem card_add_inDegree_le_of_all_pure {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hpure : ∀ p ∈ N.primeFactors, p ≠ q → ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) :
    ((N.primeFactors.erase q).filter (fun p => ¬ (p = 3 ∧ N.factorization 3 = 4))).card
      + inDegree N q
      ≤ 2 * (N.primeFactors.filter (fun r => r ∣ σ 1 (q ^ N.factorization q))).card := by
  have hqP : q ∈ N.primeFactors :=
    Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  have hmain := card_rows_add_le h hq hodd
  have hm : ((N.primeFactors ×ˢ N.primeFactors).filter
      (fun x : ℕ × ℕ => x.2 ∣ σ 1 (x.1 ^ N.factorization x.1))).card =
      ∑ p ∈ N.primeFactors,
        (N.primeFactors.filter fun r => r ∣ σ 1 (p ^ N.factorization p)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.card_filter]
  have hone : ∀ p ∈ N.primeFactors.erase q,
      (N.primeFactors.filter fun r => r ∣ σ 1 (p ^ N.factorization p)).card = 1 := by
    intro p hp
    obtain ⟨hpq, hpP⟩ := Finset.mem_erase.mp hp
    obtain ⟨r, w, hr, hrow⟩ := hpure p hpP hpq
    obtain ⟨hrP, hw0, -⟩ := receiver_of_pure_row h hpP hr hrow
    refine Finset.card_eq_one.mpr ⟨r, Finset.ext fun t => ?_⟩
    rw [Finset.mem_filter, Finset.mem_singleton, hrow]
    constructor
    · rintro ⟨htP, htd⟩
      exact eq_of_prime_dvd_prime_pow (Nat.prime_of_mem_primeFactors htP) hr htd
    · rintro rfl
      exact ⟨hrP, dvd_pow_self t hw0⟩
  have hsplit := Finset.add_sum_erase N.primeFactors
    (fun p => (N.primeFactors.filter fun r => r ∣ σ 1 (p ^ N.factorization p)).card) hqP
  rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_erase_of_mem hqP] at hsplit
  have hk : 1 ≤ N.primeFactors.card := Finset.card_pos.mpr ⟨q, hqP⟩
  rw [hm] at hmain
  unfold inDegree
  omega

end OddPerfect

#print axioms OddPerfect.prime_succ_of_sigma_prime_pow_eq_prime_pow
#print axioms OddPerfect.receiver_mod_index_of_pure
#print axioms OddPerfect.odd_weight_or_three_pow_four
#print axioms OddPerfect.receiver_of_pure_row
#print axioms OddPerfect.component_lt_of_pure_row
#print axioms OddPerfect.component_lt_of_transGen_pureEdge
#print axioms OddPerfect.not_transGen_pureEdge_self
#print axioms OddPerfect.card_add_inDegree_le_of_all_pure
