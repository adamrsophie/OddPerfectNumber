import OddPerfect.LargestPrimeCapacity
import OddPerfect.Pratt

/-!
# A root table criterion for a prime that is not the largest prime factor

Let `N` be an odd perfect number and `P` a prime factor of `N` with `P - 1 = 2 ^ a · m`.
Suppose every prime factor of `N` is at most `P`. Since `P ∣ σ(N) = 2 N` and
`σ(P ^ e) ≡ 1 (mod P)`, some prime factor `p ≠ P` sends `P`, that is `P ∣ σ(p ^ e_p)`. By
`sender_largest_data`, `p < P` and the order `t` of `p` modulo `P` is not divisible by `4`;
as `t ∣ 2 ^ a · m`, this gives `t ∣ 2 m`, so `p ^ (2 m) ≡ 1 (mod P)`.

* `exists_primeFactor_gt_of_no_prime_root`: if no prime `p < P` satisfies
  `p ^ (2 m) ≡ 1 (mod P)`, then `N` has a prime factor larger than `P`.
* `mem_of_pow_eq_one_of_nodup`: in an integral domain, a list of `n` distinct `n`th roots of
  unity contains every `n`th root of unity. So a table of `2 m` residues decides the
  hypothesis of the criterion.
* `exists_primeFactor_gt_167772161`: for `P = 167772161 = 5 · 2 ^ 25 + 1` the tenth roots of
  unity are `1, 124765, 2596626, 36505748, 38977608, 128794553, 131266413, 165175535,
  167647396, 167772160`, none of them prime. So `167772161` divides an odd perfect number only
  together with a larger prime factor.
* `exists_primeFactor_gt_12289`: the same for `12289 = 3 · 2 ^ 12 + 1`, whose sixth roots of
  unity are `1, 6048, 6049, 6240, 6241, 12288`.

The method is elementary and of a known type (orders of residues and the count of roots of a
polynomial over a field). Context: `167772161` exceeds `10 ^ 8`, the published lower bound for
the largest prime factor of an odd perfect number (Goto and Ohno), so that bound does not
decide this prime. These theorems exclude isolated values; they do not bound the largest prime
factor in general.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## The root table lemma -/

/-- In an integral domain, if `L` is a list of `n` distinct elements with `x ^ n = 1` for each,
then every `y` with `y ^ n = 1` is in `L`. -/
theorem mem_of_pow_eq_one_of_nodup {K : Type*} [CommRing K] [IsDomain K] {n : ℕ} (hn : 0 < n)
    {L : List K} (hL : L.Nodup) (hlen : L.length = n) (hroot : ∀ x ∈ L, x ^ n = 1)
    {y : K} (hy : y ^ n = 1) : y ∈ L := by
  by_contra hyL
  have hnd : (y :: L).Nodup := List.nodup_cons.mpr ⟨hyL, hL⟩
  have hle : ((y :: L : List K) : Multiset K) ≤ Polynomial.nthRoots n (1 : K) := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnd)]
    intro x hx
    rw [Polynomial.mem_nthRoots hn]
    rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx
    · exact hy
    · exact hroot x hx
  have h1 := Multiset.card_le_card hle
  have h2 := Polynomial.card_nthRoots n (1 : K)
  rw [Multiset.coe_card, List.length_cons, hlen] at h1
  omega

/-- A table over `ℕ`: if `L` lists `n` distinct residues below `P` with `r ^ n ≡ 1 (mod P)`,
none of them prime, then no prime `p < P` has `p ^ n ≡ 1 (mod P)`. -/
private theorem no_prime_root_of_table {P n : ℕ} [Fact P.Prime] (hn : 0 < n) (L : List ℕ)
    (hL : L.Nodup) (hlt : ∀ r ∈ L, r < P) (hlen : L.length = n)
    (hroot : ∀ r ∈ L, r ^ n % P = 1) (hnp : ∀ r ∈ L, ¬ r.Prime) :
    ∀ p, p.Prime → p < P → (p : ZMod P) ^ n ≠ 1 := by
  have inj : ∀ a b : ℕ, a < P → b < P → (a : ZMod P) = b → a = b := fun a b ha hb hab => by
    rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
  intro p hp hpP hpow
  have hmem := mem_of_pow_eq_one_of_nodup hn (L := L.map (fun r : ℕ => (r : ZMod P)))
    (hL.map_on fun a ha b hb hab => inj a b (hlt a ha) (hlt b hb) hab)
    (by rw [List.length_map, hlen])
    (fun x hx => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      rw [← Nat.cast_pow, ← ZMod.natCast_mod, hroot r hr, Nat.cast_one])
    hpow
  obtain ⟨r, hr, hre⟩ := List.mem_map.mp hmem
  obtain rfl := inj r p (hlt r hr) hpP hre
  exact hnp r hr hp

/-! ## The criterion -/

/-- If `t ∣ 2 ^ a · m` and `4 ∤ t`, then `t ∣ 2 m`. -/
private theorem dvd_two_mul_of_dvd' {t a m : ℕ} (h : t ∣ 2 ^ a * m) (h4 : ¬ 4 ∣ t) :
    t ∣ 2 * m := by
  rcases Nat.even_or_odd t with ⟨s, hs⟩ | ho
  · have hso : Odd s := by
      rcases Nat.even_or_odd s with ⟨u, hu⟩ | hu
      · exact absurd ⟨u, by omega⟩ h4
      · exact hu
    have hst : s ∣ 2 ^ a * m := Nat.dvd_trans ⟨2, by omega⟩ h
    have hsm : s ∣ m :=
      (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hso)).dvd_of_dvd_mul_left hst
    rw [hs, ← two_mul]
    exact Nat.mul_dvd_mul_left 2 hsm
  · exact ((Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr ho)).dvd_of_dvd_mul_left h).mul_left 2

/-- Root criterion. Let `N` be an odd perfect number and `P` a prime dividing `N`, with
`P - 1 = 2 ^ a · m`. If no prime `p < P` satisfies `p ^ (2 m) ≡ 1 (mod P)`, then `N` has a
prime factor larger than `P`. -/
theorem exists_primeFactor_gt_of_no_prime_root {N P a m : ℕ} (h : OddPerfect N)
    (hPp : P.Prime) (hd : P ∣ N) (hm : P - 1 = 2 ^ a * m)
    (hno : ∀ p, p.Prime → p < P → (p : ZMod P) ^ (2 * m) ≠ 1) :
    ∃ r ∈ N.primeFactors, P < r := by
  have hP : P ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hPp, hd, h.odd.pos.ne'⟩
  have hP2 : P ≠ 2 := by
    have := Nat.odd_iff.mp (h.odd.of_dvd_nat hd)
    omega
  by_contra hc
  push Not at hc
  have hpos : N.factorization P ≠ 0 := Finsupp.mem_support_iff.mp hP
  apply hpos
  rw [factorization_eq_sum_erase h.perfect hPp hP2]
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hpP, hpN⟩ := Finset.mem_erase.mp hp
  rw [Nat.padicValNat_def]
  refine padicValNat.eq_zero_of_not_dvd fun hdv => ?_
  obtain ⟨hlt, -, -, h4, -⟩ := sender_largest_data h hP hc hpN hpP hdv
  have : Fact P.Prime := ⟨hPp⟩
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have hp0 : (p : ZMod P) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hh
    have := Nat.le_of_dvd hpp.pos hh
    omega
  have htP := ZMod.orderOf_dvd_card_sub_one hp0
  rw [hm] at htP
  exact hno p hpp hlt (orderOf_dvd_iff_pow_eq_one.mp (dvd_two_mul_of_dvd' htP h4))

/-! ## The prime `167772161` -/

/-- `167772161 = 5 · 2 ^ 25 + 1` is prime, with primitive root `3`. -/
theorem prime_167772161 : Nat.Prime 167772161 :=
  Pratt.prime_of_checkPrime (c := [(167772161, 3,
    [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5])])
    (by decide +kernel)

private theorem table_167772161_nodup : [1, 124765, 2596626, 36505748, 38977608, 128794553,
    131266413, 165175535, 167647396, 167772160].Nodup := by decide +kernel

private theorem table_167772161_roots : ∀ r ∈ [1, 124765, 2596626, 36505748, 38977608,
    128794553, 131266413, 165175535, 167647396, 167772160], r ^ 10 % 167772161 = 1 := by
  decide +kernel

private theorem table_167772161_lt : ∀ r ∈ [1, 124765, 2596626, 36505748, 38977608,
    128794553, 131266413, 165175535, 167647396, 167772160], r < 167772161 := by
  decide +kernel

private theorem table_167772161_not_prime : ∀ r ∈ [1, 124765, 2596626, 36505748, 38977608,
    128794553, 131266413, 165175535, 167647396, 167772160], ¬ r.Prime := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- `167772161` divides an odd perfect number `N` only together with a larger prime factor.
This excludes one isolated value of the largest prime factor; it does not bound the largest
prime factor in general. -/
theorem exists_primeFactor_gt_167772161 {N : ℕ} (h : OddPerfect N) (hd : 167772161 ∣ N) :
    ∃ p ∈ N.primeFactors, 167772161 < p := by
  have : Fact (167772161).Prime := ⟨prime_167772161⟩
  exact exists_primeFactor_gt_of_no_prime_root h prime_167772161 hd (a := 25) (m := 5)
    (by norm_num) (no_prime_root_of_table (by norm_num) _ table_167772161_nodup
      table_167772161_lt rfl table_167772161_roots table_167772161_not_prime)

/-! ## The prime `12289` -/

/-- `12289 = 3 · 2 ^ 12 + 1` is prime, with primitive root `11`. -/
theorem prime_12289 : Nat.Prime 12289 :=
  Pratt.prime_of_checkPrime (c := [(12289, 11, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3])])
    (by decide +kernel)

/-- `12289` divides an odd perfect number `N` only together with a larger prime factor: its
sixth roots of unity `1, 6048, 6049, 6240, 6241, 12288` are not prime. -/
theorem exists_primeFactor_gt_12289 {N : ℕ} (h : OddPerfect N) (hd : 12289 ∣ N) :
    ∃ p ∈ N.primeFactors, 12289 < p := by
  have : Fact (12289).Prime := ⟨prime_12289⟩
  refine exists_primeFactor_gt_of_no_prime_root h prime_12289 hd (a := 12) (m := 3)
    (by norm_num) (no_prime_root_of_table (by norm_num) [1, 6048, 6049, 6240, 6241, 12288]
      (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) ?_)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-! ## Control -/

/-- The method declines for `P = 13 = 2 ^ 2 · 3 + 1`: the prime `3` satisfies
`3 ^ 6 ≡ 1 (mod 13)`, so the hypothesis of the criterion fails; and indeed
`σ(3 ^ 2) = 13`. -/
example : 13 - 1 = 2 ^ 2 * 3 ∧ 1 + 3 + 3 ^ 2 = 13 ∧
    ¬ ∀ p : ℕ, p.Prime → p < 13 → (p : ZMod 13) ^ (2 * 3) ≠ 1 :=
  ⟨by norm_num, by norm_num, fun hno => hno 3 Nat.prime_three (by norm_num) (by decide)⟩

end OddPerfect

#print axioms OddPerfect.mem_of_pow_eq_one_of_nodup
#print axioms OddPerfect.exists_primeFactor_gt_of_no_prime_root
#print axioms OddPerfect.prime_167772161
#print axioms OddPerfect.exists_primeFactor_gt_167772161
#print axioms OddPerfect.prime_12289
#print axioms OddPerfect.exists_primeFactor_gt_12289
