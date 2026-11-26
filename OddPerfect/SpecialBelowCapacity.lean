import OddPerfect.LargestPrimeCap
import OddPerfect.SpecialRank

/-!
# Rows of the primes below a prime `q` carry a bounded weight at `q`

Restricted result; no published source was checked; novelty not verified.

Let `q` be a prime and `N` a natural number whose prime factors below `q` all have exponent at
most `E`. Then the rows of those prime factors carry a total weight of at most `E ^ 3` at `q`:
`Σ_{p ∣ N, p < q} v_q(σ(p ^ v_p(N))) ≤ E ^ 3`.

* `sum_sigmaWeight_below_le_cube`: the bound for every `N`; perfection is not used.
* `sum_sigmaWeight_below_special_le_cube`: the same bound stated for an odd perfect number.
  It generalizes `sum_sigmaWeight_below_special_le_nine` (exponents `2` or `4`, bound `9`) to an
  arbitrary cap `E`, with the weaker bound `E ^ 3`.

The argument. Let `u < q` be a prime with exponent `e ≤ E`.

* Weight of one row: `σ(u ^ e) ≤ (u + 1) ^ e ≤ q ^ e`, so `v_q(σ(u ^ e)) ≤ e ≤ E`.
* Number of rows of positive weight: if `q ∣ σ(u ^ e) = 1 + u + ... + u ^ e`, then the residue
  of `u` in the field `ZMod q` is a root of `G_e = 1 + X + ... + X ^ e`, hence of the nonzero
  polynomial `F = G_0 G_1 ... G_E` of degree at most `0 + 1 + ... + E ≤ E ^ 2`. Distinct
  numbers below `q` have distinct residues, so there are at most `E ^ 2` such rows.
* So the total is at most `E * E ^ 2 = E ^ 3`.

Nothing is excluded by this lemma on its own. The odd perfect number conjecture is open, and
nothing here decides it.
-/

open ArithmeticFunction Polynomial
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem specialBelowCapacity_natCast_injOn {P : ℕ} (s : Finset ℕ)
    (hs : ∀ u ∈ s, u < P) : Set.InjOn (fun u : ℕ => (u : ZMod P)) (s : Set ℕ) := by
  intro a ha b hb hab
  simp only at hab
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hs a ha),
    Nat.mod_eq_of_lt (hs b hb)] at hab

/-- One row: for primes `u < q`, `v_q(σ(u ^ e)) ≤ e`. -/
private theorem specialBelowCapacity_row_le {u q e : ℕ} (hu : u.Prime) (hq : q.Prime)
    (huq : u < q) : (σ 1 (u ^ e)).factorization q ≤ e := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hne : σ 1 (u ^ e) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hu.ne_zero)).ne'
  have hd : q ^ (e + 1) ∣ σ 1 (u ^ e) := (hq.pow_dvd_iff_le_factorization hne).mpr hlt
  have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd
  have h2 := sigma_prime_pow_le_succ_pow hu e
  have h3 : (u + 1) ^ e ≤ q ^ e := Nat.pow_le_pow_left huq e
  have h4 : q ^ e < q ^ (e + 1) := Nat.pow_lt_pow_right hq.one_lt (by omega)
  omega

/-- Let `q` be a prime and let every prime factor `p < q` of `N` have exponent at most `E`.
Then the rows of the prime factors below `q` carry at most `E ^ 3` at `q`. -/
theorem sum_sigmaWeight_below_le_cube {N q E : ℕ} (hq : q.Prime)
    (hE : ∀ p ∈ N.primeFactors, p < q → N.factorization p ≤ E) :
    ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ E ^ 3 := by
  have : Fact q.Prime := ⟨hq⟩
  set U := N.primeFactors.filter (· < q) with hU
  set S := U.filter (fun p => sigmaWeight N p q ≠ 0) with hS
  have hdata : ∀ p ∈ S, p.Prime ∧ p ∈ N.primeFactors ∧ p < q ∧ sigmaWeight N p q ≠ 0 := by
    intro p hp
    obtain ⟨hpU, hw⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hpU
    exact ⟨Nat.prime_of_mem_primeFactors hp', hp', hpq, hw⟩
  -- the polynomial `F = Π_{e ≤ E} (1 + X + ... + X ^ e)` over `ZMod q`
  set G : ℕ → (ZMod q)[X] := fun e => ∑ i ∈ Finset.range (e + 1), X ^ i with hG
  set F : (ZMod q)[X] := ∏ e ∈ Finset.range (E + 1), G e with hFdef
  have hF : F ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e _ => (monic_geom_sum_X (Nat.succ_ne_zero e)).ne_zero
  have hdeg : F.natDegree ≤ E ^ 2 := by
    refine le_trans (natDegree_prod_le (Finset.range (E + 1)) G) ?_
    have hGe : ∀ e ∈ Finset.range (E + 1), (G e).natDegree ≤ e := fun e _ =>
      natDegree_sum_le_of_forall_le _ _ fun i hi =>
        (natDegree_X_pow_le i).trans (by rw [Finset.mem_range] at hi; omega)
    refine (Finset.sum_le_sum hGe).trans ?_
    have h2 := Finset.sum_range_id_mul_two (E + 1)
    rw [Nat.add_sub_cancel] at h2
    nlinarith
  have hroot : ∀ p ∈ S, (p : ZMod q) ∈ F.roots.toFinset := by
    intro p hp
    obtain ⟨hpp, hp', hpq, hw⟩ := hdata p hp
    have hd : q ∣ σ 1 (p ^ N.factorization p) := Nat.dvd_of_factorization_pos hw
    have h0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [sigma_one_apply_prime_pow hpp] at h0
    push_cast at h0
    rw [Multiset.mem_toFinset, mem_roots hF, IsRoot.def, hFdef, eval_prod]
    refine Finset.prod_eq_zero (i := N.factorization p)
      (Finset.mem_range.mpr (by have := hE p hp' hpq; omega)) ?_
    simpa [hG, eval_finsetSum] using h0
  have hcard : S.card ≤ E ^ 2 := by
    have hinj := specialBelowCapacity_natCast_injOn S fun p hp => (hdata p hp).2.2.1
    rw [← Finset.card_image_of_injOn hinj]
    calc _ ≤ F.roots.toFinset.card := Finset.card_le_card fun x hx => by
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
            exact hroot p hp
      _ ≤ Multiset.card F.roots := Multiset.toFinset_card_le _
      _ ≤ F.natDegree := card_roots' F
      _ ≤ E ^ 2 := hdeg
  have hw : ∀ p ∈ S, sigmaWeight N p q ≤ E := fun p hp => by
    obtain ⟨hpp, hp', hpq, -⟩ := hdata p hp
    exact (specialBelowCapacity_row_le hpp hq hpq).trans (hE p hp' hpq)
  have hfilt := Finset.sum_filter_ne_zero (s := U) (f := fun p => sigmaWeight N p q)
  rw [← hfilt]
  calc _ ≤ S.card • E := Finset.sum_le_card_nsmul _ _ _ hw
    _ ≤ E ^ 2 * E := by rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ hcard
    _ = E ^ 3 := by ring

/-- Capacity at a prime `q` for an odd perfect number: if every prime factor `p < q` of `N` has
exponent at most `E`, the rows of the prime factors below `q` carry at most `E ^ 3` at `q`.
The proof does not use perfection (see `sum_sigmaWeight_below_le_cube`). -/
theorem sum_sigmaWeight_below_special_le_cube {N q E : ℕ} (_h : OddPerfect N) (hq : q.Prime)
    (hE : ∀ p ∈ N.primeFactors, p < q → N.factorization p ≤ E) :
    ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ E ^ 3 :=
  sum_sigmaWeight_below_le_cube hq hE

end OddPerfect

#print axioms OddPerfect.sum_sigmaWeight_below_le_cube
#print axioms OddPerfect.sum_sigmaWeight_below_special_le_cube
