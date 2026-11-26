import OddPerfect.EulerIndexPairShortRows

/-!
# Two prime Euler index: the sender row of length 7 with `v = 0`

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`. `eulerIndex_pair_short_rows` labels them `(t, u)` with `σ(t ^ e) = q u ^ v`,
`σ(u ^ f) = t ^ j` (`e = v_t(N)`, `f = v_u(N)`, `j` odd, `0 < j < e`), and in the branch
`v = 0` gives `q = σ(t ^ e)` and `e ≥ 6`. `eulerIndex_pair_cofactor` gives
`q + 1 = 2 u ^ d w ^ 2` with `u ∤ w`.

* `sigma_prime_sixth_row_even`: if `σ(t ^ 6) = q`, `q + 1 = 2 u ^ d w ^ 2` with `u ∤ w`,
  `u` an odd prime, and `σ(u ^ f) = t ^ j` with `j ∈ {1, 3, 5}` and `f ≥ 2`, then `d` is even.
  Write `F(X) = X ^ 6 + ... + X + 2`. For odd `d`, `u ∣ F(t)` and `t ^ j ≡ 1 (mod u)`; the
  identities `A_j F + C_j (X ^ j - 1) = 8, 8, 88` give `j = 5` and `u = 11`. Then
  `t ^ 5 ≡ σ(11 ^ f) ≡ 133 (mod 1331)`, and every residue `t` modulo 1331 with this property
  and `11 ∣ F(t)` has `F(t) ≡ 847 = 7 * 11 ^ 2`, so `v_11(q + 1) = 2`, against `d` odd.
* `eulerIndex_pair_six_half_square`: the conclusion of `eulerIndex_pair_short_rows`, and in
  the branch `v = 0` with `e = 6` the number `σ(t ^ 6) + 1` is twice a square.
* `eulerIndex_pair_ten_le_of_no_six`: under the explicit arithmetic hypothesis `hsix` that no
  odd prime `p` has `σ(p ^ 6) + 1 = 2 z ^ 2`, the branch `v = 0` has `e ≥ 10` (as `e + 1` is
  prime, `e = 8` is impossible). The hypothesis `hsix` is not proved here.

Restricted result; no published source was checked; novelty not verified. The setting is
special exponent 1 with the Euler index supported on exactly two primes; this case is not
excluded here, and nothing here proves or disproves the odd perfect number conjecture.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairSixParity

/-- `σ(u ^ f) ≡ 1 (mod u)`. -/
private theorem eisp_row_one {u f : ℕ} (hu : u.Prime) :
    ((σ 1 (u ^ f) : ℕ) : ZMod u) = 1 := by
  rw [sigma_one_apply_prime_pow hu, sum_range_succ']
  push_cast
  simp

/-- `σ(t ^ 6) = t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 1`. -/
private theorem eisp_sigma_six {t : ℕ} (ht : t.Prime) :
    σ 1 (t ^ 6) = t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 1 := by
  rw [sigma_one_apply_prime_pow ht]
  simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one]
  ring

/-- `10 R_n(11) + 1 = 11 ^ n`. -/
private theorem eisp_geom_eleven (n : ℕ) : 10 * ∑ i ∈ range n, 11 ^ i + 1 = 11 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; linarith

/-- The finite check modulo `1331`: a fifth root of `133` with `11 ∣ F(r)` has
`F(r) ≡ 847`. -/
private theorem eisp_mod_1331 : ∀ r, r < 1331 → r ^ 5 % 1331 = 133 →
    (r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 2) % 11 = 0 →
    (r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 2) % 1331 = 847 := by
  decide +kernel

/-- A swapped labeling would give `q ∣ t ^ j`, so the two labelings agree. -/
private theorem eisp_label {N q m r s t u t' u' j v' : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (htu : ({t, u} : Finset ℕ) = {r, s}) (htu' : ({t', u'} : Finset ℕ) = {r, s})
    (hne' : t' ≠ u') (hB : σ 1 (u ^ N.factorization u) = t ^ j)
    (hA' : σ 1 (t' ^ N.factorization t') = q * u' ^ v') : t' = t ∧ u' = u := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have htJ : t ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  have ht : t.Prime := Nat.prime_of_mem_primeFactors htJ
  have htm : t ∣ m := ht.dvd_of_dvd_pow
    ((Nat.dvd_of_mem_primeFactors htJ).trans (eulerIndex_dvd_sq h hq hN1 hqm))
  have ht' : t' ∈ ({t, u} : Finset ℕ) := by rw [htu, ← htu']; simp
  have hu' : u' ∈ ({t, u} : Finset ℕ) := by rw [htu, ← htu']; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht' hu'
  rcases ht' with h1 | h1
  · refine ⟨h1, ?_⟩
    rcases hu' with h2 | h2
    · exact absurd (h1.trans h2.symm) hne'
    · exact h2
  · exfalso
    rw [h1, hB] at hA'
    have hqt : q ∣ t := hq.dvd_of_dvd_pow (Dvd.intro _ hA'.symm)
    rw [(Nat.prime_dvd_prime_iff_eq hq ht).mp hqt] at hqm
    exact hqm htm

/-- An outsider is a prime of `N` other than `q`, `t`, `u`. -/
private theorem eisp_mem_out {N q r s t u p : ℕ} (htu : ({t, u} : Finset ℕ) = {r, s})
    (hp : p ∈ N.primeFactors \ {q, r, s}) :
    p ∈ N.primeFactors ∧ p ≠ q ∧ p ≠ t ∧ p ≠ u := by
  rw [Finset.mem_sdiff, ← htu] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

/-- A prime dividing `2 ^ 3 * c` with `c ∈ {1, 11}` is `2` or `11`. -/
private theorem eisp_prime_dvd {u c : ℕ} (hu : u.Prime) (hu2 : u ≠ 2) (hc : c = 1 ∨ c = 11)
    (h : ((2 ^ 3 * c : ℕ) : ZMod u) = 0) : c = 11 ∧ u = 11 := by
  rcases (Nat.Prime.dvd_mul hu).mp ((ZMod.natCast_eq_zero_iff _ _).mp h) with h2 | h2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hu Nat.prime_two).mp (hu.dvd_of_dvd_pow h2)) hu2
  · rcases hc with rfl | rfl
    · exact absurd (Nat.dvd_one.mp h2) hu.one_lt.ne'
    · exact ⟨rfl, (Nat.prime_dvd_prime_iff_eq hu (by norm_num)).mp h2⟩

end EulerIndexPairSixParity

open EulerIndexPairSixParity

/-- **Sender row of length 7, parity of the cofactor exponent.** Let `t`, `u` be primes, `u`
odd, with `σ(t ^ 6) = q`, `q + 1 = 2 u ^ d w ^ 2`, `u ∤ w`, and `σ(u ^ f) = t ^ j` with
`j ∈ {1, 3, 5}` and `f ≥ 2`. Then `d` is even. Restricted result; no published source was
checked; novelty not verified. -/
theorem sigma_prime_sixth_row_even {t u q d w j f : ℕ} (ht : t.Prime) (hu : u.Prime)
    (hu2 : u ≠ 2) (hrow : σ 1 (t ^ 6) = q) (hd : q + 1 = 2 * u ^ d * w ^ 2) (huw : ¬ u ∣ w)
    (hj : j = 1 ∨ j = 3 ∨ j = 5) (hf : 2 ≤ f) (hcol : σ 1 (u ^ f) = t ^ j) : Even d := by
  by_contra hde
  have hd0 : d ≠ 0 := by rintro rfl; exact hde ⟨0, rfl⟩
  have hF : t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2 = 2 * u ^ d * w ^ 2 := by
    rw [← hd, ← hrow, eisp_sigma_six ht]
  have hdvd : u ∣ t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2 :=
    hF ▸ dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self u hd0) 2) _
  have htj : (t : ZMod u) ^ j = 1 := by
    have h1 := eisp_row_one (f := f) hu
    rw [hcol] at h1
    exact_mod_cast h1
  have hq0 : (t : ZMod u) ^ 6 + (t : ZMod u) ^ 5 + (t : ZMod u) ^ 4 + (t : ZMod u) ^ 3 +
      (t : ZMod u) ^ 2 + t + 2 = 0 := by
    have h1 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h1
    exact h1
  -- the three identities: `j = 5` and `u = 11`
  obtain ⟨hj5, hu11⟩ : j = 5 ∧ u = 11 := by
    set x : ZMod u := (t : ZMod u) with hx
    rcases hj with rfl | rfl | rfl
    · have h8 : ((2 ^ 3 * 1 : ℕ) : ZMod u) = 0 := by
        push_cast
        linear_combination hq0 + (-x ^ 5 - 2 * x ^ 4 - 3 * x ^ 3 - 4 * x ^ 2 - 5 * x - 6) * htj
      exact absurd (eisp_prime_dvd hu hu2 (Or.inl rfl) h8).1 (by norm_num)
    · have h8 : ((2 ^ 3 * 1 : ℕ) : ZMod u) = 0 := by
        push_cast
        linear_combination (-x ^ 2 - x + 3) * hq0 +
          (x ^ 5 + 2 * x ^ 4 - x ^ 3 + x - 2) * htj
      exact absurd (eisp_prime_dvd hu hu2 (Or.inl rfl) h8).1 (by norm_num)
    · have h88 : ((2 ^ 3 * 11 : ℕ) : ZMod u) = 0 := by
        push_cast
        linear_combination (-x ^ 4 - 9 * x ^ 3 + 7 * x ^ 2 - 25 * x + 39) * hq0 +
          (x ^ 5 + 10 * x ^ 4 + 3 * x ^ 3 + 28 * x ^ 2 - 11 * x - 10) * htj
      exact ⟨rfl, (eisp_prime_dvd hu hu2 (Or.inr rfl) h88).2⟩
  subst hj5 hu11
  -- `t ^ 5 ≡ σ(11 ^ f) ≡ 133 (mod 1331)`
  have ht5 : t ^ 5 % 1331 = 133 := by
    have hgeo := eisp_geom_eleven (f + 1)
    have hs11 := sigma_one_apply_prime_pow (i := f) (by norm_num : (11 : ℕ).Prime)
    rw [hcol] at hs11
    rw [← hs11] at hgeo
    obtain ⟨c, hc⟩ := pow_dvd_pow 11 (show 3 ≤ f + 1 by omega)
    rw [hc, show (11 : ℕ) ^ 3 = 1331 by norm_num] at hgeo
    omega
  -- reduce `t` modulo `1331`
  have hm := Nat.mod_modEq t 1331
  have hc : (t % 1331) ^ 6 + (t % 1331) ^ 5 + (t % 1331) ^ 4 + (t % 1331) ^ 3 +
      (t % 1331) ^ 2 + t % 1331 + 2 ≡
      t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2 [MOD 1331] :=
    (((((hm.pow 6).add (hm.pow 5)).add (hm.pow 4)).add (hm.pow 3)).add (hm.pow 2)).add hm
      |>.add_right 2
  rw [Nat.ModEq] at hc
  have hr5 : (t % 1331) ^ 5 % 1331 = 133 := by rw [← Nat.pow_mod]; exact ht5
  generalize hA : t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 + t ^ 2 + t + 2 = A at hF hdvd hc
  generalize hB : (t % 1331) ^ 6 + (t % 1331) ^ 5 + (t % 1331) ^ 4 + (t % 1331) ^ 3 +
    (t % 1331) ^ 2 + t % 1331 + 2 = B at hc
  have hB11 : B % 11 = 0 := by omega
  have h847 := eisp_mod_1331 (t % 1331) (Nat.mod_lt _ (by norm_num)) hr5 (hB ▸ hB11)
  rw [hB, hc] at h847
  -- `v_11(A) = 2` against `d` odd
  rcases (show d = 1 ∨ 3 ≤ d by
    rcases Nat.even_or_odd d with he | ⟨k, hk⟩
    · exact absurd he hde
    · omega) with rfl | h3
  · have h121 : 121 ∣ A := Nat.dvd_of_mod_eq_zero (by
      rw [← Nat.mod_mod_of_dvd A (by norm_num : 121 ∣ 1331), h847])
    rw [hF, show 2 * 11 ^ 1 * w ^ 2 = 11 * (2 * w ^ 2) by ring,
      show (121 : ℕ) = 11 * 11 by norm_num] at h121
    have h11 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h121
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h11 with h2 | h2
    · norm_num at h2
    · exact huw (Nat.Prime.dvd_of_dvd_pow (by norm_num) h2)
  · obtain ⟨c, hc'⟩ := pow_dvd_pow 11 h3
    rw [hc', show (11 : ℕ) ^ 3 = 1331 by norm_num] at hF
    have h1331 : 1331 ∣ A := ⟨2 * c * w ^ 2, by rw [hF]; ring⟩
    rw [Nat.mod_eq_zero_of_dvd h1331] at h847
    exact absurd h847 (by norm_num)

variable {N q m r s : ℕ}

/-- **Two prime index, the sender row of length 7.** Let `N = q m ^ 2` be an odd perfect
number with special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index
`J = σ(m ^ 2) / q` has exactly the two prime factors `r ≠ s`. For the labeling `(t, u)` of
`eulerIndex_pair_short_rows`, all of its conclusions hold, `t` is an odd prime, and in the
branch `v = 0` with `v_t(N) = 6` the number `σ(t ^ 6) + 1` is twice a square.
Restricted result; no published source was checked; novelty not verified. This case is not
excluded here. -/
theorem eulerIndex_pair_six_half_square (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧ t.Prime ∧ t ≠ 2 ∧ ∃ v j,
      σ 1 (t ^ N.factorization t) = q * u ^ v ∧ 0 < j ∧ Odd j ∧
      σ 1 (u ^ N.factorization u) = t ^ j ∧ j < N.factorization t ∧
      (N.factorization t + 1).Prime ∧
      ((v = 0 ∧ σ 1 (t ^ N.factorization t) = q ∧ 6 ≤ N.factorization t ∧
          (N.factorization t = 6 → ∃ z, σ 1 (t ^ 6) + 1 = 2 * z ^ 2)) ∨
        (v = 1 ∧ u = N.factorization t + 1 ∧ 5 ≤ u ∧ t % u = 1 ∧ q % u = 1 ∧
          q + 1 = 2 * (∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2)) := by
  obtain ⟨t, u, htu, hne, v, j, hA, hj, hjo, hB, hje, hp, hcases⟩ :=
    eulerIndex_pair_short_rows h hq hN hqm hr hs hrs hJ
  obtain ⟨t', u', htu', hne', ⟨v', hA'⟩, -, -, -, hf1, -, -, -, -, -, d, hd⟩ :=
    eulerIndex_pair_cofactor h hq hN hqm hr hs hrs hJ
  obtain ⟨h1, h2⟩ := eisp_label h hq hN hqm hJ htu htu' hne' hB hA'
  rw [h2] at hf1 hd
  set w := ∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2) with hwdef
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hJm := eulerIndex_dvd_sq h hq hN1 hqm
  have hfacts : ∀ p ∈ ({t, u} : Finset ℕ), p.Prime ∧ p ≠ 2 ∧ p ≠ q := by
    intro p hp
    rw [htu, ← hJ] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpJ := Nat.dvd_of_mem_primeFactors hp
    have hpm : p ∣ m := hpp.dvd_of_dvd_pow (hpJ.trans hJm)
    refine ⟨hpp, ?_, ?_⟩
    · rintro rfl
      exact (Nat.not_even_iff_odd.mpr (odd_eulerIndex h hq hN1 hqm)) (even_iff_two_dvd.mpr hpJ)
    · rintro rfl; exact hqm hpm
  obtain ⟨ht, ht2, htq⟩ := hfacts t (by simp)
  obtain ⟨hu, hu2, huq⟩ := hfacts u (by simp)
  refine ⟨t, u, htu, hne, ht, ht2, v, j, hA, hj, hjo, hB, hje, hp, ?_⟩
  rcases hcases with ⟨hv, hq0, he6⟩ | hright
  · left
    refine ⟨hv, hq0, he6, fun he => ?_⟩
    have hvq : N.factorization q = 1 := by
      rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
        hq.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd))]
    have hodd : Odd (N.factorization q) := by rw [hvq]; exact odd_one
    have hfe : Even (N.factorization u) := even_factorization_of_ne h hq hodd hu huq
    have hf0 : N.factorization u ≠ 0 := fun h0 => by
      rw [h0] at hf1; exact Nat.not_prime_one hf1
    have huw : ¬ u ∣ w := by
      intro huw'
      obtain ⟨p, hp, hpd⟩ := (hu.prime.dvd_finsetProd_iff _).mp huw'
      obtain ⟨hpN, -, -, hpu⟩ := eisp_mem_out htu hp
      exact hpu ((Nat.prime_dvd_prime_iff_eq hu (Nat.prime_of_mem_primeFactors hpN)).mp
        (hu.dvd_of_dvd_pow hpd)).symm
    rw [he] at hq0 hje
    have hj135 : j = 1 ∨ j = 3 ∨ j = 5 := by obtain ⟨i, hi⟩ := hjo; omega
    obtain ⟨k, hk⟩ := sigma_prime_sixth_row_even ht hu hu2 hq0 hd huw hj135
      (by obtain ⟨c, hc⟩ := hfe; omega) hB
    refine ⟨u ^ k * w, ?_⟩
    rw [hq0, hd, hk, pow_add]
    ring
  · exact Or.inr hright

/-- **Two prime index, the sender row of length 7 excluded under an arithmetic hypothesis.**
In the setting of `eulerIndex_pair_six_half_square`, assume `hsix`: no odd prime `p` and no
`z` satisfy `σ(p ^ 6) + 1 = 2 z ^ 2` (this hypothesis is NOT proved here). Then for the same
labeling the branch `v = 0` has `v_t(N) ≥ 10`. Restricted result; no published source was
checked; novelty not verified. This case is not excluded here. -/
theorem eulerIndex_pair_ten_le_of_no_six (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hsix : ∀ p, p.Prime → p ≠ 2 → ∀ z, σ 1 (p ^ 6) + 1 ≠ 2 * z ^ 2) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧ t.Prime ∧ t ≠ 2 ∧ ∃ v j,
      σ 1 (t ^ N.factorization t) = q * u ^ v ∧ 0 < j ∧ Odd j ∧
      σ 1 (u ^ N.factorization u) = t ^ j ∧ j < N.factorization t ∧
      (N.factorization t + 1).Prime ∧
      ((v = 0 ∧ σ 1 (t ^ N.factorization t) = q ∧ 10 ≤ N.factorization t) ∨
        (v = 1 ∧ u = N.factorization t + 1 ∧ 5 ≤ u ∧ t % u = 1 ∧ q % u = 1 ∧
          q + 1 = 2 * (∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2)) := by
  obtain ⟨t, u, htu, hne, ht, ht2, v, j, hA, hj, hjo, hB, hje, hp, hcases⟩ :=
    eulerIndex_pair_six_half_square h hq hN hqm hr hs hrs hJ
  refine ⟨t, u, htu, hne, ht, ht2, v, j, hA, hj, hjo, hB, hje, hp, ?_⟩
  rcases hcases with ⟨hv, hq0, he6, hsq⟩ | hright
  · left
    refine ⟨hv, hq0, ?_⟩
    have hvq : N.factorization q = 1 := by
      have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
      rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
        hq.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd))]
    have htq : t ≠ q := by
      rintro rfl
      rw [hvq] at he6
      omega
    have he : Even (N.factorization t) :=
      even_factorization_of_ne h hq (by rw [hvq]; exact odd_one) ht htq
    obtain ⟨k, hk⟩ := he
    rcases (show N.factorization t = 6 ∨ N.factorization t = 8 ∨ 10 ≤ N.factorization t by
      omega) with h6 | h8 | h10
    · obtain ⟨z, hz⟩ := hsq h6
      exact absurd hz (hsix t ht ht2 z)
    · rw [h8] at hp
      norm_num at hp
    · exact h10
  · exact Or.inr hright

end OddPerfect

#print axioms OddPerfect.sigma_prime_sixth_row_even
#print axioms OddPerfect.eulerIndex_pair_six_half_square
#print axioms OddPerfect.eulerIndex_pair_ten_le_of_no_six
