import OddPerfect.EulerIndexPairShortRows
import OddPerfect.PureRows
import OddPerfect.OmegaSevenFinal

/-!
# Two prime Euler index: the emitter exponent is at least 6

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`. `eulerIndex_pair_short_rows` labels them `(t, u)` with `σ(t ^ e) = q u ^ v`,
`σ(u ^ f) = t ^ j` (`e = v_t(N)`, `f = v_u(N)`), `e + 1` prime, and either `v = 0` and
`e ≥ 6`, or `v = 1`, `u = e + 1` and `u ≥ 5`.

* `sigma_prime_pow_ne_five_pow`: for an odd prime `p` and `g ≥ 2`, `σ(p ^ g)` is never a
  power of `5`. By `receiver_mod_index_of_pure`, `5 ≡ 1 (mod g + 1)`, so `g = 3`; then
  `σ(p ^ 3)` is a sum of four odd numbers, hence even.
* `eulerIndex_pair_emitter_six`: `e ≥ 6` in both branches. In the branch `v = 1` with
  `e < 6`, `e` is even and `e + 1 ≥ 5`, so `e = 4` and `u = 5`. Every prime `p` of `N`
  outside `{q, r, s}` (an outsider) has `σ(p ^ g) = t ^ x u ^ y` with `g ≥ 2` even, and the
  first lemma forces `x ≥ 1`. There are at least four outsiders
  (`seven_le_card_primeFactors`), so the valuation count `e = j + Σ x` of
  `eulerIndex_pair_t_count` gives `e ≥ 5`, against `e = 4`.
* `eulerIndex_pair_not_palette`: the two index primes cannot both have exponent `2` or `4`
  in `N`, since `t` is one of them and `v_t(N) ≥ 6`. This closes the case left open by
  `eulerIndex_pair_palette`.

Restricted result; no published source was checked; novelty not verified. These results
assume special exponent 1 and an Euler index supported on exactly two primes; they do not
exclude this case, and nothing here proves or disproves the odd perfect number conjecture.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairEmitterSix

/-- A swapped labeling would give `q ∣ t ^ j`, so the two labelings agree. -/
private theorem emsix_label {N q m r s t u t' u' j v' : ℕ} (h : OddPerfect N) (hq : q.Prime)
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
private theorem emsix_mem_out {N q r s t u p : ℕ} (htu : ({t, u} : Finset ℕ) = {r, s})
    (hp : p ∈ N.primeFactors \ {q, r, s}) :
    p ∈ N.primeFactors ∧ p ≠ q ∧ p ≠ t ∧ p ≠ u := by
  rw [Finset.mem_sdiff, ← htu] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

end EulerIndexPairEmitterSix

open EulerIndexPairEmitterSix

/-- **No row of an odd prime power is a power of `5`.** For an odd prime `p`, `g ≥ 2` and
every `w`, `σ(p ^ g) ≠ 5 ^ w`. Elementary; nothing new is claimed. -/
theorem sigma_prime_pow_ne_five_pow {p g w : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 2 ≤ g) :
    σ 1 (p ^ g) ≠ 5 ^ w := by
  intro h
  have hmod := receiver_mod_index_of_pure hp hp2 hg (by norm_num) h
  have hg3 : g = 3 := by
    rcases Nat.lt_or_ge g 5 with h5 | h5
    · interval_cases g <;> omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hmod
      omega
  subst hg3
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hs : σ 1 (p ^ 3) = 1 + p + (p ^ 2 + p ^ 3) := by
    rw [sigma_one_apply_prime_pow hp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    ring
  have he : Even (σ 1 (p ^ 3)) := by
    rw [hs]
    exact (odd_one.add_odd hpo).add (hpo.pow.add_odd hpo.pow)
  rw [h] at he
  exact (Nat.not_even_iff_odd.mpr (Odd.pow (by decide : Odd 5))) he

variable {N q m r s : ℕ}

/-- **Two prime index, the emitter exponent is at least 6.** Let `N = q m ^ 2` be an odd
perfect number with special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index
`J = σ(m ^ 2) / q` has exactly the two prime factors `r ≠ s`. For the labeling `(t, u)` of
`eulerIndex_pair_short_rows`, all of its conclusions hold, and moreover `v_t(N) ≥ 6` in both
branches. Restricted result (special exponent 1, index supported on exactly two primes); it
does not exclude this case. No published source was checked; novelty not verified. -/
theorem eulerIndex_pair_emitter_six (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧ ∃ v j,
      σ 1 (t ^ N.factorization t) = q * u ^ v ∧ 0 < j ∧ Odd j ∧
      σ 1 (u ^ N.factorization u) = t ^ j ∧ j < N.factorization t ∧
      (N.factorization t + 1).Prime ∧ 6 ≤ N.factorization t ∧
      ((v = 0 ∧ σ 1 (t ^ N.factorization t) = q ∧ 6 ≤ N.factorization t) ∨
        (v = 1 ∧ u = N.factorization t + 1 ∧ 5 ≤ u ∧ t % u = 1 ∧ q % u = 1 ∧
          q + 1 = 2 * (∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2)) := by
  obtain ⟨t, u, htu, hne, v, j, hA, hj, hjo, hB, hje, hp, hcases⟩ :=
    eulerIndex_pair_short_rows h hq hN hqm hr hs hrs hJ
  refine ⟨t, u, htu, hne, v, j, hA, hj, hjo, hB, hje, hp, ?_, hcases⟩
  rcases hcases with ⟨-, -, h6⟩ | ⟨-, hue, hu5', -, -, -⟩
  · exact h6
  by_contra hlt
  -- basic facts
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hJm := eulerIndex_dvd_sq h hq hN1 hqm
  have htJ : t ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  have huJ : u ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  have ht : t.Prime := Nat.prime_of_mem_primeFactors htJ
  have hu : u.Prime := Nat.prime_of_mem_primeFactors huJ
  have htq : t ≠ q := by
    rintro rfl
    exact hqm (ht.dvd_of_dvd_pow ((Nat.dvd_of_mem_primeFactors htJ).trans hJm))
  have hvq : N.factorization q = 1 := by
    rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
      hq.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd))]
  have hodd : Odd (N.factorization q) := by rw [hvq]; exact odd_one
  have he : Even (N.factorization t) := even_factorization_of_ne h hq hodd ht htq
  have he4 : N.factorization t = 4 := by obtain ⟨k, hk⟩ := he; omega
  have hu5 : u = 5 := by omega
  -- the valuation count at `t`, for the same labeling
  obtain ⟨t'', u'', htu'', hne'', ⟨v'', hA''⟩, -, -, j'', -, -, hB'', hcount, -⟩ :=
    eulerIndex_pair_t_count h hq hN hqm hr hs hrs hJ
  obtain ⟨h1', h2'⟩ := emsix_label h hq hN hqm hJ htu htu'' hne'' hB hA''
  rw [h1', h2'] at hB''
  rw [h1'] at hcount
  have hjj : j'' = j := by
    rw [hB] at hB''
    exact Nat.pow_right_injective ht.two_le hB''.symm
  rw [hjj] at hcount
  -- the outsider rows, for the same labeling
  obtain ⟨t', u', htu', hne', ⟨v', hA'⟩, -, -, -, -, -, -, -, -, hrest, -⟩ :=
    eulerIndex_pair_cofactor h hq hN hqm hr hs hrs hJ
  obtain ⟨h1, h2⟩ := emsix_label h hq hN hqm hJ htu htu' hne' hB hA'
  rw [h1, h2] at hrest
  set O := N.primeFactors \ {q, r, s} with hOdef
  -- at least four outsiders
  have hcard : 4 ≤ O.card := by
    have h7 := seven_le_card_primeFactors h
    have h3' : ({q, r, s} : Finset ℕ).card ≤ 3 := Finset.card_le_three
    have := Finset.le_card_sdiff ({q, r, s} : Finset ℕ) N.primeFactors
    rw [← hOdef] at this
    omega
  -- every outsider row is divisible by `t`
  have hone : ∀ p ∈ O, 1 ≤ (σ 1 (p ^ N.factorization p)).factorization t := by
    intro p hpO
    obtain ⟨hpN, hpq, hpt, hpu⟩ := emsix_mem_out htu hpO
    obtain ⟨⟨x, y, hxy⟩, -, -⟩ := hrest p hpN hpq hpt hpu
    have hfx : (σ 1 (p ^ N.factorization p)).factorization t = x := by
      rw [hxy, Nat.factorization_mul (pow_ne_zero _ ht.ne_zero) (pow_ne_zero _ hu.ne_zero),
        Finsupp.add_apply, ht.factorization_pow, hu.factorization_pow,
        Finsupp.single_eq_same, Finsupp.single_apply, if_neg hne.symm, add_zero]
    rw [hfx]
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · exfalso
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpN
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hpN)
      have hge : Even (N.factorization p) := even_factorization_of_ne h hq hodd hpp hpq
      have hg0 : N.factorization p ≠ 0 :=
        (hpp.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hpN)).ne'
      have hg2 : 2 ≤ N.factorization p := by obtain ⟨c, hc⟩ := hge; omega
      rw [pow_zero, one_mul, hu5] at hxy
      exact sigma_prime_pow_ne_five_pow hpp hp2 hg2 hxy
    · exact hx
  have hsum := Finset.card_nsmul_le_sum O _ 1 hone
  rw [smul_eq_mul, mul_one] at hsum
  omega

/-- **Two prime index, the exponents 2 and 4 do not occur together.** In the setting of
`eulerIndex_pair_emitter_six`, the two prime factors `r` and `s` of the Euler index cannot
both have exponent `2` or `4` in `N`. Restricted result (special exponent 1, index supported
on exactly two primes); it does not exclude this case. No published source was checked;
novelty not verified. -/
theorem eulerIndex_pair_not_palette (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ¬ ((N.factorization r = 2 ∨ N.factorization r = 4) ∧
      (N.factorization s = 2 ∨ N.factorization s = 4)) := by
  rintro ⟨hr', hs'⟩
  obtain ⟨t, u, htu, -, _v, _j, -, -, -, -, -, -, h6, -⟩ :=
    eulerIndex_pair_emitter_six h hq hN hqm hr hs hrs hJ
  have ht : t ∈ ({r, s} : Finset ℕ) := by rw [← htu]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl <;> omega

end OddPerfect

#print axioms OddPerfect.sigma_prime_pow_ne_five_pow
#print axioms OddPerfect.eulerIndex_pair_emitter_six
#print axioms OddPerfect.eulerIndex_pair_not_palette
