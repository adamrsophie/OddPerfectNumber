import OddPerfect.Basic
import OddPerfect.Seed.Cut
import Mathlib.Logic.Relation

/-!
# The divisor sum network of a perfect number

For a perfect number `N`, put a weighted directed graph on its prime factors: the weight
of `p → q` is the exponent of `q` in the divisor sum of the full `p` component of `N`.
Perfection gives exact conservation at every vertex and strong connectivity.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Weight of the edge `p → q`: the exponent of `q` in `σ(p ^ v_p(N))`. -/
def sigmaWeight (N p q : ℕ) : ℕ := (σ 1 (p ^ N.factorization p)).factorization q

/-- There is an edge `p → q` when both are prime factors of `N` and `q` divides the
divisor sum of the full `p` component. -/
def SigmaEdge (N p q : ℕ) : Prop :=
  p ∈ N.primeFactors ∧ q ∈ N.primeFactors ∧ q ∣ σ 1 (p ^ N.factorization p)

private theorem sigma_pow_ne_zero {p e : ℕ} (hp : p.Prime) : σ 1 (p ^ e) ≠ 0 :=
  (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'

private theorem not_dvd_sigma_pow {p e : ℕ} (hp : p.Prime) : ¬ p ∣ σ 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ', pow_zero]
  intro h
  have hsum : p ∣ ∑ k ∈ Finset.range e, p ^ (k + 1) :=
    Finset.dvd_sum fun k _ => dvd_pow_self p k.succ_ne_zero
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hsum).mp h))

/-- Conservation at an odd prime: the incoming weights add up to the exponent of `q`. -/
theorem sigmaWeight_sum_eq {N q : ℕ} (hN : N.Perfect) (hq : q.Prime) (hq2 : q ≠ 2) :
    ∑ p ∈ N.primeFactors, sigmaWeight N p q = N.factorization q := by
  have h := OPNStarter.valuation_balance hN q
  rw [Nat.factorization_eq_zero_of_not_dvd
    (fun hd => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd)), zero_add] at h
  exact h.symm

/-- For an odd perfect number the incoming weights at `2` add up to exactly one. -/
theorem sigmaWeight_sum_two {N : ℕ} (h : OddPerfect N) :
    ∑ p ∈ N.primeFactors, sigmaWeight N p 2 = 1 := by
  have hb := OPNStarter.valuation_balance h.perfect 2
  rw [Nat.factorization_eq_zero_of_not_dvd h.not_two_dvd,
    Nat.Prime.factorization_self Nat.prime_two] at hb
  exact hb.symm

/-- There are no self loops. -/
theorem sigmaWeight_self {N p : ℕ} (hp : p.Prime) : sigmaWeight N p p = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (not_dvd_sigma_pow hp)

/-- No weight leaks out of the prime factors, except possibly to `2`. -/
theorem mem_primeFactors_of_sigmaWeight_ne_zero {N p q : ℕ} (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hq2 : q ≠ 2) (hw : sigmaWeight N p q ≠ 0) :
    q ∈ N.primeFactors := by
  have hq : q.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization _ ▸
    Finsupp.mem_support_iff.mpr hw)
  exact Nat.mem_primeFactors.mpr ⟨hq, OPNStarter.force_prime hN
    (Nat.prime_of_mem_primeFactors hp) rfl hq hq2 (Nat.dvd_of_factorization_pos hw),
    hN.2.ne'⟩

/-- Between prime factors, an edge is exactly a nonzero weight. -/
theorem sigmaEdge_iff_sigmaWeight_ne_zero {N p q : ℕ} (hp : p ∈ N.primeFactors)
    (hq : q ∈ N.primeFactors) : SigmaEdge N p q ↔ sigmaWeight N p q ≠ 0 := by
  have hq' := Nat.prime_of_mem_primeFactors hq
  have hne := sigma_pow_ne_zero (e := N.factorization p) (Nat.prime_of_mem_primeFactors hp)
  unfold SigmaEdge sigmaWeight
  rw [Ne, Nat.factorization_eq_zero_iff]
  constructor
  · rintro ⟨-, -, hd⟩
    rintro (h | h | h)
    · exact h hq'
    · exact h hd
    · exact hne h
  · intro h
    refine ⟨hp, hq, ?_⟩
    by_contra hd
    exact h (Or.inr (Or.inl hd))

/-- Every odd prime factor receives an edge from a different prime factor. -/
theorem exists_sigmaEdge_into {N q : ℕ} (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq2 : q ≠ 2) : ∃ p, p ≠ q ∧ SigmaEdge N p q := by
  have hq' := Nat.prime_of_mem_primeFactors hq
  have hsum := sigmaWeight_sum_eq hN hq' hq2
  have hpos : N.factorization q ≠ 0 :=
    Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hq)
  rw [← hsum] at hpos
  obtain ⟨p, hp, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
  refine ⟨p, fun hpq => hw (by subst hpq; exact sigmaWeight_self hq'), ?_⟩
  exact (sigmaEdge_iff_sigmaWeight_ne_zero hp hq).mpr hw

/-- For an odd perfect number every prime factor sends an edge to a different prime factor. -/
theorem exists_sigmaEdge_out {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) :
    ∃ q, q ≠ p ∧ SigmaEdge N p q := by
  have hp' := Nat.prime_of_mem_primeFactors hp
  set s := σ 1 (p ^ N.factorization p) with hs
  have hs0 : s ≠ 0 := sigma_pow_ne_zero hp'
  -- the exponent of `2` in `s` is at most one
  have hw2 : s.factorization 2 ≤ 1 := by
    rw [← sigmaWeight_sum_two h]
    exact Finset.single_le_sum (f := fun r => sigmaWeight N r 2) (fun _ _ => Nat.zero_le _) hp
  -- `s ≥ 1 + p ≥ 4`
  have hp3 : 3 ≤ p := by
    have h2 : p ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
    have := hp'.two_le
    omega
  have hs3 : 3 ≤ s := by
    have he : N.factorization p ≠ 0 :=
      Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hp)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero he
    rw [hs, hk, sigma_one_apply_prime_pow hp', Finset.sum_range_succ', pow_zero]
    have : p ^ (0 + 1) ≤ ∑ i ∈ Finset.range (k + 1), p ^ (i + 1) :=
      Finset.single_le_sum (f := fun i => p ^ (i + 1)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr k.succ_pos)
    simp only [zero_add, pow_one] at this
    omega
  -- the odd part of `s` exceeds one
  set m := ordCompl[2] s with hm
  have hm1 : m ≠ 1 := by
    intro h1
    have hsplit := Nat.ordProj_mul_ordCompl_eq_self s 2
    rw [← hm, h1, mul_one] at hsplit
    have : 2 ^ s.factorization 2 ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hw2
    omega
  have hmdvd : m ∣ s := Nat.ordCompl_dvd s 2
  have hm0 : m ≠ 0 := fun h0 => hs0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hmdvd))
  set q := m.minFac
  have hq : q.Prime := Nat.minFac_prime hm1
  have hqs : q ∣ s := (Nat.minFac_dvd m).trans hmdvd
  have hq2 : q ≠ 2 := by
    intro h2
    have hd : q ∣ m := Nat.minFac_dvd m
    rw [h2] at hd
    exact Nat.not_dvd_ordCompl Nat.prime_two hs0 hd
  have hqN : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, OPNStarter.force_prime h.perfect hp' rfl hq hq2 hqs,
      h.ne_zero⟩
  refine ⟨q, fun hqp => not_dvd_sigma_pow hp' (hqp ▸ hqs), hp, hqN, hqs⟩

private theorem mem_of_prime_dvd_prod {T : Finset ℕ} {N r : ℕ} (hT : T ⊆ N.primeFactors)
    (hr : r.Prime) (hd : r ∣ ∏ x ∈ T, x ^ N.factorization x) : r ∈ T := by
  obtain ⟨x, hx, hrx⟩ := (hr.prime.dvd_finsetProd_iff _).mp hd
  have hx' := Nat.prime_of_mem_primeFactors (hT hx)
  rwa [(Nat.prime_dvd_prime_iff_eq hr hx').mp (hr.dvd_of_dvd_pow hrx)]

private theorem one_lt_prod {T : Finset ℕ} {N : ℕ} (hT : T ⊆ N.primeFactors)
    (hne : T.Nonempty) : 1 < ∏ x ∈ T, x ^ N.factorization x := by
  obtain ⟨x, hx⟩ := hne
  have hx' := Nat.prime_of_mem_primeFactors (hT hx)
  have he : N.factorization x ≠ 0 :=
    Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hT hx)
  have h0 : ∏ y ∈ T, y ^ N.factorization y ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun y hy =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hT hy)).ne_zero
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Finset.dvd_prod_of_mem
    (fun y => y ^ N.factorization y) hx)
  have : 1 < x ^ N.factorization x := Nat.one_lt_pow he hx'.one_lt
  omega

/-- For any nonempty proper subset `S` of the prime factors there is an edge from the
complement into `S`. Applying this to the complement gives an edge out of `S`. -/
theorem exists_sigmaEdge_crossing {N : ℕ} (hN : N.Perfect) {S : Finset ℕ}
    (hS : S ⊆ N.primeFactors) (hne : S.Nonempty) (hne' : (N.primeFactors \ S).Nonempty) :
    ∃ p ∈ N.primeFactors \ S, ∃ q ∈ S, SigmaEdge N p q := by
  classical
  set T := N.primeFactors \ S with hTdef
  have hT : T ⊆ N.primeFactors := Finset.sdiff_subset
  set a := ∏ r ∈ S, r ^ N.factorization r with ha
  set b := ∏ r ∈ T, r ^ N.factorization r with hb
  have hab : a * b = N := by
    rw [ha, hb, mul_comm, Finset.prod_sdiff hS]
    exact (Nat.prod_primeFactors_pow_factorization hN.2.ne').symm
  have hcop : a.Coprime b := by
    refine Nat.Coprime.prod_left fun x hx => Nat.Coprime.prod_right fun y hy => ?_
    refine Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors (hS hx))
      (Nat.prime_of_mem_primeFactors (hT hy)) ?_
    rintro rfl
    exact (Finset.mem_sdiff.mp hy).2 hx
  have ha1 : 1 < a := one_lt_prod hS hne
  have hb1 : 1 < b := one_lt_prod hT hne'
  obtain ⟨r, hr, p, hp, hdvd⟩ :=
    OPNCut.exists_crossing_component ha1 hb1 hcop (hab ▸ hN)
  have hr' := Nat.prime_of_mem_primeFactors hr
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hrS : r ∈ S := mem_of_prime_dvd_prod hS hr' (Nat.dvd_of_mem_primeFactors hr)
  have hpT : p ∈ T := mem_of_prime_dvd_prod hT hp' (Nat.dvd_of_mem_primeFactors hp)
  -- `p` does not divide `a`, so its exponent in `b` equals its exponent in `N`
  have hpa : a.factorization p = 0 := by
    refine Nat.factorization_eq_zero_of_not_dvd fun hd => ?_
    exact (Finset.mem_sdiff.mp hpT).2 (mem_of_prime_dvd_prod hS hp' hd)
  have hbN : b.factorization p = N.factorization p := by
    rw [← hab, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply, hpa, zero_add]
  rw [hbN] at hdvd
  exact ⟨p, hpT, r, hrS, hT hpT, hS hrS, hdvd⟩

/-- The network is strongly connected: every prime factor reaches every other. -/
theorem sigmaEdge_reflTransGen {N : ℕ} (hN : N.Perfect) {p q : ℕ}
    (hp : p ∈ N.primeFactors) (hq : q ∈ N.primeFactors) :
    Relation.ReflTransGen (SigmaEdge N) p q := by
  classical
  set S := N.primeFactors.filter fun r => Relation.ReflTransGen (SigmaEdge N) r q
  by_contra hpq
  have hpS : p ∈ N.primeFactors \ S := by simp [S, hp, hpq]
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_sigmaEdge_crossing hN (Finset.filter_subset _ _)
    ⟨q, Finset.mem_filter.mpr ⟨hq, .refl⟩⟩ ⟨p, hpS⟩
  have hyq := (Finset.mem_filter.mp hy).2
  have hxS : x ∉ S := (Finset.mem_sdiff.mp hx).2
  exact hxS (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1, Relation.ReflTransGen.head hxy hyq⟩)

end OddPerfect

#print axioms OddPerfect.sigmaWeight_sum_eq
#print axioms OddPerfect.sigmaWeight_sum_two
#print axioms OddPerfect.sigmaWeight_self
#print axioms OddPerfect.mem_primeFactors_of_sigmaWeight_ne_zero
#print axioms OddPerfect.sigmaEdge_iff_sigmaWeight_ne_zero
#print axioms OddPerfect.exists_sigmaEdge_into
#print axioms OddPerfect.exists_sigmaEdge_out
#print axioms OddPerfect.exists_sigmaEdge_crossing
#print axioms OddPerfect.sigmaEdge_reflTransGen
