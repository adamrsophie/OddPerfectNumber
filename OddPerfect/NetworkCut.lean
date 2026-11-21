import OddPerfect.Network

/-!
# The exact balance across a cut of the prime support

For an odd perfect `N` with prime support `P` and a subset `A ⊆ P`, the divisor sum of the
`A` part of `N` factors exactly through the weights of the divisor sum network: the weight
entering `A` from `P \ A` and the weight leaving `A` into `P \ A` are tied by one identity.
Together with `1 < σ(M_A) / M_A < 2` this gives two sided bounds.

These are exact restatements of the conservation laws of `OddPerfect.Network` plus the
abundancy bounds of the two coprime parts: an interface for certificates, not a new
obstruction.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The `A` part of `N`: `∏ p ∈ A, p ^ v_p(N)`. -/
def cutPart (N : ℕ) (A : Finset ℕ) : ℕ := ∏ p ∈ A, p ^ N.factorization p

/-- The total weight from `A` into the prime `2`. -/
def cutTwo (N : ℕ) (A : Finset ℕ) : ℕ := ∑ p ∈ A, sigmaWeight N p 2

/-- The weight leaving `A`: `∏ q ∈ P \ A, q ^ (∑ p ∈ A, w(p, q))`. -/
def cutOut (N : ℕ) (A : Finset ℕ) : ℕ :=
  ∏ q ∈ N.primeFactors \ A, q ^ (∑ p ∈ A, sigmaWeight N p q)

/-- The weight entering `A`: `∏ q ∈ A, q ^ (∑ p ∈ P \ A, w(p, q))`. -/
def cutIn (N : ℕ) (A : Finset ℕ) : ℕ :=
  ∏ q ∈ A, q ^ (∑ p ∈ N.primeFactors \ A, sigmaWeight N p q)

/-- The divisor sum of one component factors over `2` and the prime support. -/
private theorem sigma_component_eq {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) :
    σ 1 (p ^ N.factorization p) =
      2 ^ sigmaWeight N p 2 * ∏ q ∈ N.primeFactors, q ^ sigmaWeight N p q := by
  set s := σ 1 (p ^ N.factorization p) with hs
  have hs0 : s ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne'
  have h2 : (2 : ℕ) ∉ N.primeFactors := fun h2 => h.not_two_dvd (Nat.dvd_of_mem_primeFactors h2)
  have hsupp : s.factorization.support ⊆ insert 2 N.primeFactors := by
    intro q hq
    by_cases hq2 : q = 2
    · exact hq2 ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (mem_primeFactors_of_sigmaWeight_ne_zero h.perfect hp hq2 (Finsupp.mem_support_iff.mp hq))
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hs0]
  rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _), Finset.prod_insert h2]
  rfl

/-- The divisor sum of the `A` part is `2 ^ δ_A` times the product of the weights out of `A`. -/
private theorem sigma_cutPart_eq {N : ℕ} (h : OddPerfect N) {A : Finset ℕ}
    (hA : A ⊆ N.primeFactors) :
    σ 1 (cutPart N A) =
      2 ^ cutTwo N A * ∏ q ∈ N.primeFactors, q ^ (∑ p ∈ A, sigmaWeight N p q) := by
  unfold cutPart cutTwo
  rw [isMultiplicative_sigma.map_prod _ _ ?_]
  · rw [Finset.prod_congr rfl fun p hp => sigma_component_eq h (hA hp), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Finset.prod_comm]
    congr 1
    exact Finset.prod_congr rfl fun q _ => Finset.prod_pow_eq_pow_sum _ _ _
  · intro x hx y hy hxy
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors (hA hx))
      (Nat.prime_of_mem_primeFactors (hA hy)) hxy

/-- The exact cut identity `σ(M_A) · I_A = 2 ^ δ_A · O_A · M_A`. This is a restatement of
conservation at every odd prime together with support closure; it is an interface for
certificates, not a new obstruction. -/
theorem sigma_cut_mul {N : ℕ} (h : OddPerfect N) {A : Finset ℕ} (hA : A ⊆ N.primeFactors) :
    σ 1 (cutPart N A) * cutIn N A = 2 ^ cutTwo N A * cutOut N A * cutPart N A := by
  rw [sigma_cutPart_eq h hA, ← Finset.prod_sdiff hA, mul_assoc, mul_assoc, mul_assoc]
  congr 2
  unfold cutIn cutPart
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q hq => ?_
  have hq' := Nat.prime_of_mem_primeFactors (hA hq)
  have hq2 : q ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors (hA hq))
  rw [← pow_add, add_comm, Finset.sum_sdiff hA, sigmaWeight_sum_eq h.perfect hq' hq2]

/-- The total weight from `A` into `2` is at most one, since the total over all of the
prime support is exactly one. -/
theorem cutTwo_le_one {N : ℕ} (h : OddPerfect N) {A : Finset ℕ} (hA : A ⊆ N.primeFactors) :
    cutTwo N A ≤ 1 := by
  rw [← sigmaWeight_sum_two h]
  exact Finset.sum_le_sum_of_subset hA

private theorem lt_sigma {n : ℕ} (h : 1 < n) : n < σ 1 n := by
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have hmem := Nat.one_mem_properDivisors_iff_one_lt.mpr h
  have hle : 1 ≤ ∑ i ∈ n.properDivisors, i :=
    Finset.single_le_sum (fun (i : ℕ) (_ : i ∈ n.properDivisors) => Nat.zero_le i) hmem
  omega

private theorem one_lt_cutPart {N : ℕ} {A : Finset ℕ} (hA : A ⊆ N.primeFactors)
    (hne : A.Nonempty) : 1 < cutPart N A := by
  unfold cutPart
  obtain ⟨x, hx⟩ := hne
  have hx' := Nat.prime_of_mem_primeFactors (hA hx)
  have he : N.factorization x ≠ 0 :=
    Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hA hx)
  have h0 : ∏ y ∈ A, y ^ N.factorization y ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun y hy =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hA hy)).ne_zero
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Finset.dvd_prod_of_mem
    (fun y => y ^ N.factorization y) hx)
  have : 1 < x ^ N.factorization x := Nat.one_lt_pow he hx'.one_lt
  omega

/-- For a nonempty proper `A`, `M_A < σ(M_A) < 2 M_A`. -/
private theorem cutPart_abundancy {N : ℕ} (h : OddPerfect N) {A : Finset ℕ}
    (hA : A ⊆ N.primeFactors) (hne : A.Nonempty) (hpr : A ≠ N.primeFactors) :
    cutPart N A < σ 1 (cutPart N A) ∧ σ 1 (cutPart N A) < 2 * cutPart N A := by
  classical
  have hB : N.primeFactors \ A ⊆ N.primeFactors := Finset.sdiff_subset
  have hBne : (N.primeFactors \ A).Nonempty :=
    Finset.sdiff_nonempty.mpr fun hsub => hpr (Finset.Subset.antisymm hA hsub)
  set a := cutPart N A with ha
  set b := cutPart N (N.primeFactors \ A) with hb
  have hab : a * b = N := by
    rw [ha, hb, cutPart, cutPart, mul_comm, Finset.prod_sdiff hA]
    exact (Nat.prod_primeFactors_pow_factorization h.ne_zero).symm
  have hcop : a.Coprime b := by
    refine Nat.Coprime.prod_left fun x hx => Nat.Coprime.prod_right fun y hy => ?_
    refine Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors (hA hx))
      (Nat.prime_of_mem_primeFactors (hB hy)) ?_
    rintro rfl
    exact (Finset.mem_sdiff.mp hy).2 hx
  have ha1 : 1 < a := one_lt_cutPart hA hne
  have hb1 : 1 < b := one_lt_cutPart hB hBne
  have hmul : σ 1 a * σ 1 b = 2 * (a * b) := by
    rw [← isMultiplicative_sigma.map_mul_of_coprime hcop, hab]
    exact h.sigma_eq
  have hla := lt_sigma ha1
  have hlb := lt_sigma hb1
  refine ⟨hla, ?_⟩
  by_contra hc
  rw [not_lt] at hc
  have : 2 * a * b < σ 1 a * σ 1 b :=
    calc 2 * a * b < 2 * a * σ 1 b := by
            exact Nat.mul_lt_mul_of_pos_left hlb (by omega)
      _ ≤ σ 1 a * σ 1 b := Nat.mul_le_mul_right _ hc
  rw [hmul] at this
  linarith

private theorem cutIn_pos {N : ℕ} {A : Finset ℕ} (hA : A ⊆ N.primeFactors) : 0 < cutIn N A :=
  Finset.prod_pos fun _ hq => pow_pos (Nat.prime_of_mem_primeFactors (hA hq)).pos _

private theorem cutOut_pos {N : ℕ} (A : Finset ℕ) : 0 < cutOut N A :=
  Finset.prod_pos fun _ hq =>
    pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1).pos _

/-- Two sided balance across a nonempty proper cut. With no weight from `A` into `2`, the
weight leaving `A` exceeds the weight entering it by a factor strictly between `1` and `2`;
with the single unit of weight into `2` inside `A`, the roles swap. This restates the cut
identity `sigma_cut_mul` together with `1 < σ(M_A) / M_A < 2`; it is an interface for
certificates, not a new obstruction. -/
theorem cut_balance {N : ℕ} (h : OddPerfect N) {A : Finset ℕ} (hA : A ⊆ N.primeFactors)
    (hne : A.Nonempty) (hpr : A ≠ N.primeFactors) :
    (cutTwo N A = 0 → cutIn N A < cutOut N A ∧ cutOut N A < 2 * cutIn N A) ∧
    (cutTwo N A = 1 → cutOut N A < cutIn N A ∧ cutIn N A < 2 * cutOut N A) := by
  have hid := sigma_cut_mul h hA
  obtain ⟨hlo, hhi⟩ := cutPart_abundancy h hA hne hpr
  have hM := one_lt_cutPart hA hne
  have hI := cutIn_pos (N := N) hA
  have hO := cutOut_pos (N := N) A
  set M := cutPart N A
  set S := σ 1 M
  set I := cutIn N A
  set O := cutOut N A
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · rw [h0, pow_zero, one_mul] at hid
    constructor
    · by_contra hc
      rw [not_lt] at hc
      have : M * I < S * I := Nat.mul_lt_mul_of_pos_right hlo hI
      nlinarith
    · by_contra hc
      rw [not_lt] at hc
      have : S * I < 2 * M * I := Nat.mul_lt_mul_of_pos_right hhi hI
      nlinarith
  · rw [h1, pow_one] at hid
    constructor
    · by_contra hc
      rw [not_lt] at hc
      have : S * I < 2 * M * I := Nat.mul_lt_mul_of_pos_right hhi hI
      nlinarith
    · by_contra hc
      rw [not_lt] at hc
      have : M * I < S * I := Nat.mul_lt_mul_of_pos_right hlo hI
      nlinarith

end OddPerfect

#print axioms OddPerfect.sigma_cut_mul
#print axioms OddPerfect.cutTwo_le_one
#print axioms OddPerfect.cut_balance
