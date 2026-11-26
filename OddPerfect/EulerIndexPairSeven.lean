import OddPerfect.EulerIndexPairEmitterTen
import OddPerfect.NagellPrime
import OddPerfect.NotThreeNine
import OddPerfect.SquareRow

/-!
# Two prime Euler index: emitter exponent at least 10 in both branches

Restricted result; no published source was checked; novelty not verified.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`, labeled `(t, u)` with `σ(t ^ e) = q u ^ v` and `σ(u ^ f) = t ^ j`
(`e = v_t(N)`, `f = v_u(N)`). `eulerIndex_pair_emitter_ten` gives `v = 0` and `e ≥ 10`, or
`v = 1` and `u = e + 1 ≥ 7`.

* `three_pow_ne_seven_pow_add_two`: `3 ^ X ≠ 7 ^ Y + 2` for `Y ≥ 2`. Modulo `49` the power
  `3 ^ X` must be `2`, which fixes `X` modulo `42`; modulo `29` no class of `X` modulo `84`
  and of `Y` modulo `7` fits. Checked by the kernel on residues.
* `sigma_prime_pow_ne_seven_pow`: for an odd prime `p` and `g ≥ 2`, `σ(p ^ g)` is never a
  power of `7`. By `receiver_mod_index_of_pure`, `g + 1` divides `6`, so `g = 2` or `g = 5`;
  `σ(p ^ 5)` is even, and `p ^ 2 + p + 1 = 7 ^ w` forces `w = 1` and `p = 2`.
* `eulerIndex_pair_emitter_ten_all`: `e ≥ 10` in both branches, and `u ≥ 11` when `v = 1`.
  In the branch `v = 1` with `e = 6` (`u = 7`) every outsider row is divisible by `t`, the
  valuation count gives `6 = j + A` with `A = 5` and `j = 1`, so `N` has at most eight prime
  factors and `3 ∣ N`. The row of `3` is `σ(3 ^ g) = t ^ x` with `x ∈ {1, 2}` (`7` never
  divides `σ(3 ^ g)` for even `g`); `x = 2` gives `t = 11`, against `t ≡ 1 (mod 7)`, and
  `x = 1` gives `σ(3 ^ g) = σ(7 ^ f)`, that is `3 ^ (g + 2) = 7 ^ (f + 1) + 2`.

The case is not excluded: `e ≥ 10` remains in both branches. The odd perfect number
conjecture is open, and nothing here proves or disproves it.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairSeven

/-- Reduction of an exponent modulo a period. -/
private theorem eipsv_pow_mod {a n c : ℕ} (h : a ^ n ≡ 1 [MOD c]) (b r : ℕ) :
    a ^ (n * b + r) % c = a ^ r % c := by
  have := (h.pow b).mul_right (a ^ r)
  rw [one_pow, one_mul, ← pow_mul, ← pow_add] at this
  exact this

/-- The residue check behind `three_pow_ne_seven_pow_add_two`. -/
private theorem eipsv_res : ∀ r, r < 84 → ∀ s, s < 7 →
    ¬ (3 ^ r % 49 = 2 ∧ 3 ^ r % 29 = (49 * 7 ^ s + 2) % 29) := by
  decide +kernel

/-- `2 R_n(3) + 1 = 3 ^ n`. -/
private theorem eipsv_geom_three (n : ℕ) : 2 * ∑ i ∈ range n, 3 ^ i + 1 = 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; linarith

/-- `6 R_n(7) + 1 = 7 ^ n`. -/
private theorem eipsv_geom_seven (n : ℕ) : 6 * ∑ i ∈ range n, 7 ^ i + 1 = 7 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; linarith

/-- A swapped labeling would give `q ∣ t ^ j`, so the two labelings agree. -/
private theorem eipsv_label {N q m r s t u t' u' j v' : ℕ} (h : OddPerfect N) (hq : q.Prime)
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
private theorem eipsv_mem_out {N q r s t u p : ℕ} (htu : ({t, u} : Finset ℕ) = {r, s})
    (hp : p ∈ N.primeFactors \ {q, r, s}) :
    p ∈ N.primeFactors ∧ p ≠ q ∧ p ≠ t ∧ p ≠ u := by
  rw [Finset.mem_sdiff, ← htu] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

end EulerIndexPairSeven

open EulerIndexPairSeven

/-- **No power of `3` exceeds a higher power of `7` by `2`.** For all `X` and all `Y ≥ 2`,
`3 ^ X ≠ 7 ^ Y + 2`. Elementary congruences modulo `49` and `29`; nothing new is claimed. -/
theorem three_pow_ne_seven_pow_add_two {X Y : ℕ} (hY : 2 ≤ Y) : 3 ^ X ≠ 7 ^ Y + 2 := by
  intro h
  obtain ⟨a, r, hr, rfl⟩ : ∃ a r, r < 84 ∧ X = 84 * a + r :=
    ⟨X / 84, X % 84, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod X 84).symm⟩
  obtain ⟨b, s, hs, rfl⟩ : ∃ b s, s < 7 ∧ Y = 7 * b + s + 2 :=
    ⟨(Y - 2) / 7, (Y - 2) % 7, Nat.mod_lt _ (by norm_num), by omega⟩
  have h7 : 7 ^ (7 * b + s + 2) = 49 * 7 ^ (7 * b + s) := by ring
  rw [h7] at h
  have e49 := eipsv_pow_mod (a := 3) (n := 84) (c := 49) (by unfold Nat.ModEq; norm_num) a r
  have e29 := eipsv_pow_mod (a := 3) (n := 84) (c := 29) (by unfold Nat.ModEq; norm_num) a r
  have f29 := eipsv_pow_mod (a := 7) (n := 7) (c := 29) (by unfold Nat.ModEq; norm_num) b s
  exact eipsv_res r hr s hs ⟨by omega, by omega⟩

/-- **No row of an odd prime power is a power of `7`.** For an odd prime `p`, `g ≥ 2` and
every `w`, `σ(p ^ g) ≠ 7 ^ w`. Elementary given `phi3_eq_prime_pow_exponent`; nothing new
is claimed. -/
theorem sigma_prime_pow_ne_seven_pow {p g w : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 2 ≤ g) :
    σ 1 (p ^ g) ≠ 7 ^ w := by
  intro h
  have hmod := receiver_mod_index_of_pure hp hp2 hg (by norm_num) h
  have hg25 : g = 2 ∨ g = 5 := by
    rcases Nat.lt_or_ge g 7 with h7 | h7
    · interval_cases g <;> omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hmod
      omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases hg25 with rfl | rfl
  · have hs : σ 1 (p ^ 2) = phi3 p := by
      rw [sigma_one_apply_prime_pow hp]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, phi3]
      ring
    rw [hs] at h
    have hw : 1 ≤ w := by
      rcases Nat.eq_zero_or_pos w with rfl | hw
      · simp only [phi3, pow_zero] at h
        omega
      · exact hw
    have hw1 := phi3_eq_prime_pow_exponent (by norm_num) hp hw h
    subst hw1
    simp only [phi3, pow_one] at h
    have : 9 ≤ p ^ 2 := by nlinarith
    omega
  · have hpo : Odd p := hp.odd_of_ne_two hp2
    have hs : σ 1 (p ^ 5) = 1 + p + (p ^ 2 + p ^ 3) + (p ^ 4 + p ^ 5) := by
      rw [sigma_one_apply_prime_pow hp]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
      ring
    have he : Even (σ 1 (p ^ 5)) := by
      rw [hs]
      exact ((odd_one.add_odd hpo).add (hpo.pow.add_odd hpo.pow)).add
        (hpo.pow.add_odd hpo.pow)
    rw [h] at he
    exact (Nat.not_even_iff_odd.mpr (Odd.pow (by decide : Odd 7))) he

variable {N q m r s : ℕ}

/-- **Two prime index: emitter exponent at least 10 in both branches.** Let `N = q m ^ 2` be
an odd perfect number with special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler
index `J = σ(m ^ 2) / q` has exactly the two prime factors `r ≠ s`. For the labeling `(t, u)`
of `eulerIndex_pair_emitter_ten`, all of its conclusions hold, `v_t(N) ≥ 10` in both
branches, and `u ≥ 11` in the branch `v = 1`. Restricted result (special exponent 1, index
supported on exactly two primes); it does not exclude this case. No published source was
checked; novelty not verified. -/
theorem eulerIndex_pair_emitter_ten_all (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧ t.Prime ∧ t ≠ 2 ∧ ∃ v j,
      σ 1 (t ^ N.factorization t) = q * u ^ v ∧ 0 < j ∧ Odd j ∧
      σ 1 (u ^ N.factorization u) = t ^ j ∧ j < N.factorization t ∧
      (N.factorization t + 1).Prime ∧ 10 ≤ N.factorization t ∧
      ((v = 0 ∧ σ 1 (t ^ N.factorization t) = q ∧ 10 ≤ N.factorization t) ∨
        (v = 1 ∧ u = N.factorization t + 1 ∧ 11 ≤ u ∧ t % u = 1 ∧ q % u = 1 ∧
          q + 1 = 2 * (∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2)) := by
  obtain ⟨t, u, htu, hne, ht, ht2, v, j, hA, hj, hjo, hB, hje, hp, hcases⟩ :=
    eulerIndex_pair_emitter_ten h hq hN hqm hr hs hrs hJ
  -- the branch `v = 1` with `e = 6` is impossible
  have key : u = N.factorization t + 1 → t % u = 1 → q % u = 1 →
      N.factorization t ≠ 6 := by
    intro hu htu1 hqu1 he6
    have hu7 : u = 7 := by omega
    subst hu7
    have h7p : (7 : ℕ).Prime := by norm_num
    have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
    have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
    have hJm := eulerIndex_dvd_sq h hq hN1 hqm
    have hvq : N.factorization q = 1 := by
      rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
        hq.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd))]
    have hodd : Odd (N.factorization q) := by rw [hvq]; exact odd_one
    -- the valuation count at `t`, for the same labeling
    obtain ⟨t'', u'', htu'', hne'', ⟨v'', hA''⟩, -, -, j'', -, -, hB'', hcount, hAodd, -⟩ :=
      eulerIndex_pair_t_count h hq hN hqm hr hs hrs hJ
    obtain ⟨h1', h2'⟩ := eipsv_label h hq hN hqm hJ htu htu'' hne'' hB hA''
    rw [h1', h2'] at hB''
    rw [h1'] at hcount hAodd
    have hjj : j'' = j := by
      rw [hB] at hB''
      exact Nat.pow_right_injective ht.two_le hB''.symm
    rw [hjj, he6] at hcount
    -- the outsider rows, for the same labeling
    obtain ⟨t', u', htu', hne', ⟨v', hA'⟩, -, -, -, -, -, -, -, -, hrest, -⟩ :=
      eulerIndex_pair_cofactor h hq hN hqm hr hs hrs hJ
    obtain ⟨h1, h2⟩ := eipsv_label h hq hN hqm hJ htu htu' hne' hB hA'
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
      obtain ⟨hpN, hpq, hpt, hpu⟩ := eipsv_mem_out htu hpO
      obtain ⟨⟨x, y, hxy⟩, -, -⟩ := hrest p hpN hpq hpt hpu
      have hfx : (σ 1 (p ^ N.factorization p)).factorization t = x := by
        rw [hxy, Nat.factorization_mul (pow_ne_zero _ ht.ne_zero) (pow_ne_zero _ h7p.ne_zero),
          Finsupp.add_apply, ht.factorization_pow, h7p.factorization_pow,
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
        rw [pow_zero, one_mul] at hxy
        exact sigma_prime_pow_ne_seven_pow hpp hp2 hg2 hxy
      · exact hx
    have hsum := Finset.card_nsmul_le_sum O _ 1 hone
    rw [smul_eq_mul, mul_one] at hsum
    -- hence `A = 5` and `j = 1`
    set A := ∑ p ∈ O, (σ 1 (p ^ N.factorization p)).factorization t with hAdef
    have hA5 : A = 5 := by
      obtain ⟨k, hk⟩ := hAodd
      obtain ⟨i, hi⟩ := hjo
      omega
    have hj1 : j = 1 := by omega
    -- `3 ∣ N`
    have h3N : 3 ∣ N := by
      by_contra h3
      have h9 := nine_le_card_primeFactors_of_not_three_dvd h h3
      have h3' : ({q, r, s} : Finset ℕ).card ≤ 3 := Finset.card_le_three
      have := Finset.card_le_card_sdiff_add_card (s := N.primeFactors) (t := {q, r, s})
      rw [← hOdef] at this
      omega
    have h3N' : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3N, h.ne_zero⟩
    have h3q : (3 : ℕ) ≠ q := by intro h3; omega
    have h3t : (3 : ℕ) ≠ t := by intro h3; omega
    have h3u : (3 : ℕ) ≠ 7 := by norm_num
    have h3O : 3 ∈ O := by
      rw [hOdef, Finset.mem_sdiff, ← htu]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h3N', h3q, h3t, h3u⟩
    -- the exponent of `t` in the row of `3` is `1` or `2`
    have hx1 := hone 3 h3O
    have hx2 : (σ 1 (3 ^ N.factorization 3)).factorization t ≤ 2 := by
      have hsplit : (σ 1 (3 ^ N.factorization 3)).factorization t +
          ∑ p ∈ O.erase 3, (σ 1 (p ^ N.factorization p)).factorization t = A := by
        rw [hAdef]
        exact Finset.add_sum_erase O (fun p => (σ 1 (p ^ N.factorization p)).factorization t) h3O
      have hone' : ∀ p ∈ O.erase 3, 1 ≤ (σ 1 (p ^ N.factorization p)).factorization t :=
        fun p hp => hone p (Finset.mem_of_mem_erase hp)
      have hs' := Finset.card_nsmul_le_sum (O.erase 3) _ 1 hone'
      rw [smul_eq_mul, mul_one] at hs'
      have hc := Finset.card_erase_of_mem h3O
      omega
    -- the row of `3`
    obtain ⟨⟨x, y, hxy⟩, -, -⟩ := hrest 3 h3N' h3q h3t h3u
    have hge : Even (N.factorization 3) :=
      even_factorization_of_ne h hq hodd Nat.prime_three h3q
    have hg0 : N.factorization 3 ≠ 0 :=
      (Nat.prime_three.factorization_pos_of_dvd h.ne_zero h3N).ne'
    have hgeo3 : 2 * σ 1 (3 ^ N.factorization 3) + 1 = 3 ^ (N.factorization 3 + 1) := by
      rw [sigma_one_apply_prime_pow Nat.prime_three]
      exact eipsv_geom_three _
    -- `7 ∤ σ(3 ^ g)` for even `g`
    have h7 : ¬ 7 ∣ σ 1 (3 ^ N.factorization 3) := by
      intro hd
      obtain ⟨c, hc⟩ := hd
      have hm7 := eipsv_pow_mod (a := 3) (n := 6) (c := 7) (by unfold Nat.ModEq; norm_num)
        ((N.factorization 3 + 1) / 6) ((N.factorization 3 + 1) % 6)
      rw [Nat.div_add_mod] at hm7
      obtain ⟨k, hk⟩ := hge
      have hr6 : (N.factorization 3 + 1) % 6 = 1 ∨ (N.factorization 3 + 1) % 6 = 3 ∨
          (N.factorization 3 + 1) % 6 = 5 := by omega
      rcases hr6 with h6 | h6 | h6 <;> rw [h6] at hm7 <;> norm_num at hm7 <;>
        simp only [← Nat.factorization_def _ Nat.prime_three] at hm7 <;> omega
    have hy0 : y = 0 := by
      by_contra hy
      exact h7 (hxy ▸ dvd_mul_of_dvd_right (dvd_pow_self 7 hy) _)
    rw [hy0, pow_zero, mul_one] at hxy
    have hxx : (σ 1 (3 ^ N.factorization 3)).factorization t = x := by
      rw [hxy, ht.factorization_pow, Finsupp.single_eq_same]
    rw [hxx] at hx1 hx2
    rcases (show x = 1 ∨ x = 2 by omega) with rfl | rfl
    · -- `σ(3 ^ g) = σ(7 ^ f)`
      rw [hj1] at hB
      have hgeo7 : 6 * σ 1 (7 ^ N.factorization 7) + 1 = 7 ^ (N.factorization 7 + 1) := by
        rw [sigma_one_apply_prime_pow h7p]
        exact eipsv_geom_seven _
      have h7J : (7 : ℕ) ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
      have h7N : 7 ∣ N := (Nat.dvd_of_mem_primeFactors h7J).trans
        (hJm.trans (hN ▸ dvd_mul_left _ _))
      have hf1 : 1 ≤ N.factorization 7 := h7p.factorization_pos_of_dvd h.ne_zero h7N
      have hpow : 3 ^ (N.factorization 3 + 2) = 3 ^ (N.factorization 3 + 1) * 3 := pow_succ _ _
      rw [pow_one] at hxy hB
      exact three_pow_ne_seven_pow_add_two (X := N.factorization 3 + 2)
        (Y := N.factorization 7 + 1) (by omega) (by omega)
    · -- `σ(3 ^ g)` a square
      have hsq : IsSquare (σ 1 (3 ^ N.factorization 3)) := ⟨t, by rw [hxy]; ring⟩
      obtain ⟨-, hg4⟩ :=
        (isSquare_sigma_prime_pow_iff Nat.prime_three (by norm_num) hge hg0).mp hsq
      rw [hg4] at hxy
      have h121 : σ 1 (3 ^ 4) = 11 ^ 2 := by
        rw [sigma_one_apply_prime_pow Nat.prime_three]
        simp [Finset.sum_range_succ]
      rw [h121] at hxy
      have ht11 : t = 11 := Nat.pow_left_injective (by norm_num : 2 ≠ 0) hxy.symm
      rw [ht11] at htu1
      norm_num at htu1
  refine ⟨t, u, htu, hne, ht, ht2, v, j, hA, hj, hjo, hB, hje, hp, ?_, ?_⟩
  · rcases hcases with ⟨-, -, h10⟩ | ⟨-, hu, h7, h1, h2, -⟩
    · exact h10
    · have hne6 := key hu h1 h2
      rcases (show N.factorization t = 6 ∨ N.factorization t = 7 ∨ N.factorization t = 8 ∨
          N.factorization t = 9 ∨ 10 ≤ N.factorization t by omega) with h6 | h6 | h6 | h6 | h6
      · exact absurd h6 hne6
      all_goals first
        | exact h6
        | (rw [h6] at hp; norm_num at hp)
  · rcases hcases with hl | ⟨hv, hu, h7, h1, h2, h3⟩
    · exact Or.inl hl
    · have hne6 := key hu h1 h2
      refine Or.inr ⟨hv, hu, ?_, h1, h2, h3⟩
      rcases (show N.factorization t = 6 ∨ N.factorization t = 7 ∨ N.factorization t = 8 ∨
          N.factorization t = 9 ∨ 10 ≤ N.factorization t by omega) with h6 | h6 | h6 | h6 | h6
      · exact absurd h6 hne6
      all_goals first
        | omega
        | (rw [h6] at hp; norm_num at hp)

end OddPerfect

#print axioms OddPerfect.three_pow_ne_seven_pow_add_two
#print axioms OddPerfect.sigma_prime_pow_ne_seven_pow
#print axioms OddPerfect.eulerIndex_pair_emitter_ten_all
