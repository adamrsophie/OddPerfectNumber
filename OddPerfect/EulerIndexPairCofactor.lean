import OddPerfect.EulerIndexPairPalette
import OddPerfect.EulerIndexPairOutside

/-!
# Two prime Euler index: the cofactor of `q + 1`

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`. `eulerIndex_pair_pure_exponent_odd` labels them `(t, u)` with `σ(t ^ e) = q u ^ v`
and `σ(u ^ f) = t ^ j` (`e = v_t(N)`, `f = v_u(N)`, `j` odd), `t ∤ q + 1`, and shows that
every other prime `p` of `N` (an outsider, `p ∉ {q, r, s}`) has `σ(p ^ g) = t ^ x u ^ y` and
`p ^ g ∣ q + 1`. Write `w = ∏ p ^ (v_p(N) / 2)` over the outsiders.

* `eulerIndex_pair_cofactor`: `q + 1 = 2 u ^ d w ^ 2` for some `d`. The cofactor
  `(q + 1) / (2 w ^ 2)` divides `m ^ 2`, its prime factors are not `t` and not an outsider
  (an outsider already has its full power `p ^ v_p(N)` in `w ^ 2`), so it is a power of `u`.
* `eulerIndex_pair_t_count`: `v_t(N) = j + A` with `A = Σ v_t(σ(p ^ v_p(N)))` over the
  outsiders, read off from `σ(N) = 2 N`; `A` is odd, and `σ(w ^ 2) = t ^ A u ^ b`.
* `eulerIndex_pair_character`: modulo `t`, `q u ^ v ≡ 1` and `2 (1 + u ^ v)` is a nonzero
  square. Multiply `q + 1 = 2 u ^ d w ^ 2` by `u ^ v`; `u` has odd order modulo `t`, so it is a
  square modulo `t`.

These are restricted results (special exponent 1, Euler index supported on exactly two
primes). They do not exclude this case. Their novelty has not been verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairCofactor

/-- A prime does not divide `σ(p ^ g) = 1 + p + ... + p ^ g`. -/
private lemma eipc_not_dvd_row {p g : ℕ} (hp : p.Prime) : ¬ p ∣ σ 1 (p ^ g) := by
  intro hd
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ', pow_zero] at hd
  have h2 : p ∣ ∑ i ∈ Finset.range g, p ^ (i + 1) :=
    Finset.dvd_sum fun i _ => dvd_pow_self p (Nat.succ_ne_zero i)
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h2).mp hd))

/-- Every prime other than `q` has even exponent in `q * m ^ 2`. -/
private lemma eipc_even {q m p : ℕ} (hq : q.Prime) (hm : m ≠ 0) (hpq : p ≠ q) :
    Even ((q * m ^ 2).factorization p) := by
  rw [Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
    hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq), zero_add,
    Nat.factorization_pow]
  exact ⟨m.factorization p, by simp [two_mul]⟩

/-- Halving even exponents: `(∏ p ^ (g p / 2)) ^ 2 = ∏ p ^ g p`. -/
private lemma eipc_prod_sq {O : Finset ℕ} {g : ℕ → ℕ} (hg : ∀ p ∈ O, Even (g p)) :
    (∏ p ∈ O, p ^ (g p / 2)) ^ 2 = ∏ p ∈ O, p ^ g p := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp (hg p hp))]

/-- An outsider is a prime of `N` other than `q`, `t`, `u`. -/
private lemma eipc_mem_out {N q r s t u p : ℕ} (htu : ({t, u} : Finset ℕ) = {r, s})
    (hp : p ∈ N.primeFactors \ {q, r, s}) :
    p ∈ N.primeFactors ∧ p ≠ q ∧ p ≠ t ∧ p ≠ u := by
  rw [Finset.mem_sdiff, ← htu] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

/-- The facts used for a prime of the Euler index. -/
private lemma eipc_index_prime {N q m p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p ∈ (eulerIndex q 1 m).primeFactors) :
    p.Prime ∧ p ∣ m ∧ p ≠ q ∧ p ≠ 2 ∧ p ∈ N.primeFactors ∧
      Even (N.factorization p) := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpm : p ∣ m := hpp.dvd_of_dvd_pow
    ((Nat.dvd_of_mem_primeFactors hp).trans (eulerIndex_dvd_sq h hq hN1 hqm))
  have hpq : p ≠ q := by rintro rfl; exact hqm hpm
  have hpN : p ∣ N := hN ▸ dvd_mul_of_dvd_right (dvd_pow hpm two_ne_zero) q
  refine ⟨hpp, hpm, hpq, ?_, Nat.mem_primeFactors.mpr ⟨hpp, hpN, h.ne_zero⟩,
    hN ▸ eipc_even hq hm hpq⟩
  rintro rfl
  exact h.not_two_dvd hpN

end EulerIndexPairCofactor

open EulerIndexPairCofactor

variable {N q m r s : ℕ}

/-- **Two prime index, the cofactor of `q + 1`.** Let `N = q m ^ 2` be an odd perfect number
with special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q`
has exactly the two prime factors `r ≠ s`. For the labeling `(t, u)` of
`eulerIndex_pair_pure_exponent_odd`, all of its conclusions hold, and moreover
`q + 1 = 2 u ^ d w ^ 2` for some `d`, where `w = ∏ p ^ (v_p(N) / 2)` over the primes `p ∣ N`
outside `{q, r, s}`. This is a restricted result (special exponent 1, index supported on
exactly two primes); it does not exclude this case. Its novelty has not been verified. -/
theorem eulerIndex_pair_cofactor (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (∃ j, 0 < j ∧ Odd j ∧ σ 1 (u ^ N.factorization u) = t ^ j) ∧ ¬ t ∣ q + 1 ∧
      (eulerIndex q 1 m).factorization t = N.factorization t ∧
      (N.factorization u + 1).Prime ∧ orderOf (u : ZMod t) = N.factorization u + 1 ∧
      t % (2 * (N.factorization u + 1)) = 1 ∧
      ((N.factorization t + 1).Prime ∨ ∃ p, p.Prime ∧ N.factorization t + 1 = p ^ 2) ∧
      (orderOf (q : ZMod t) = 1 ∨ orderOf (q : ZMod t) = N.factorization u + 1) ∧
      (∀ p ∈ N.primeFactors, p ≠ q → p ≠ t → p ≠ u →
        (∃ x y, σ 1 (p ^ N.factorization p) = t ^ x * u ^ y) ∧
        p ^ N.factorization p ∣ q + 1 ∧
        ((N.factorization p + 1).Prime ∨ ∃ P, P.Prime ∧ N.factorization p + 1 = P ^ 2)) ∧
      ∃ d, q + 1 = 2 * u ^ d *
        (∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2 := by
  obtain ⟨t, u, htu, hne, hA, hB, h3, h4, hf1, hord, hmod, hE, hordq, hrest⟩ :=
    eulerIndex_pair_pure_exponent_odd h hq hN hqm hr hs hrs hJ
  refine ⟨t, u, htu, hne, hA, hB, h3, h4, hf1, hord, hmod, hE, hordq, hrest, ?_⟩
  set J := eulerIndex q 1 m with hJdef
  set O := N.primeFactors \ {q, r, s} with hOdef
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hJ2 : (q + 1) * J = 2 * m ^ 2 := by
    have := sigma_special_mul_eulerIndex h hq hN1 hqm
    rw [sigma_one_apply_prime_pow hq] at this
    simpa [Finset.sum_range_succ, add_comm] using this
  have hbr : ∀ p, p ≠ q → N.factorization p = (m ^ 2).factorization p := by
    intro p hp
    rw [hN, Nat.factorization_mul hq.ne_zero hn0, Finsupp.add_apply,
      hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hp), zero_add]
  have hD := eulerIndex_pair_outside_prod_dvd h hq hN hqm hr hs hrs hJ
  rw [← hOdef] at hD
  set W := ∏ p ∈ O, p ^ N.factorization p with hWdef
  obtain ⟨K, hK⟩ := hD
  have hWKJ : W * K * J = m ^ 2 :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (by rw [← hJ2, hK]; ring)
  have hK0 : K ≠ 0 := by rintro rfl; rw [mul_zero] at hK; omega
  have huniq : ∀ {p : ℕ}, p.Prime → p ∣ K → p = u := by
    intro p hp hpK
    have hWK : W * K ∣ m ^ 2 := ⟨J, hWKJ.symm⟩
    have hpm2 : p ∣ m ^ 2 := (dvd_mul_of_dvd_right hpK W).trans hWK
    have hpm : p ∣ m := hp.dvd_of_dvd_pow hpm2
    have hpq1 : p ∣ q + 1 := hK ▸ dvd_mul_of_dvd_right hpK _
    by_contra hpu
    have hpt : p ≠ t := by rintro rfl; exact h3 hpq1
    have hpq : p ≠ q := by rintro rfl; exact hqm hpm
    have hpN : p ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hN ▸ dvd_mul_of_dvd_right hpm2 q, h.ne_zero⟩
    have hpO : p ∈ O := by
      rw [hOdef, Finset.mem_sdiff, ← htu]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hpN, hpq, hpt, hpu⟩
    have hpW : p ^ N.factorization p ∣ W :=
      Finset.dvd_prod_of_mem (fun p => p ^ N.factorization p) hpO
    have hpp : p ^ (N.factorization p + 1) ∣ m ^ 2 := by
      rw [pow_succ]; exact (mul_dvd_mul hpW hpK).trans hWK
    have := (hp.pow_dvd_iff_le_factorization hn0).mp hpp
    rw [hbr p hpq] at this
    omega
  obtain ⟨d, hd⟩ : ∃ d, K = u ^ d := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hK0 huniq⟩
  have hev : ∀ p ∈ O, Even (N.factorization p) := fun p hp =>
    hN ▸ eipc_even hq hm (eipc_mem_out htu hp).2.1
  refine ⟨d, ?_⟩
  rw [eipc_prod_sq hev, hK, hd]
  ring

/-- **Two prime index, the valuation count at `t`.** In the setting of
`eulerIndex_pair_cofactor`, for the same labeling `(t, u)`, with `j` the exponent in
`σ(u ^ v_u(N)) = t ^ j` and `A = Σ v_t(σ(p ^ v_p(N)))` over the primes `p ∣ N` outside
`{q, r, s}`, we have `v_t(N) = j + A`, `A` is odd, some outside row is divisible by `t`,
and `σ(w ^ 2) = t ^ A u ^ b` for some `b` (so `t ∣ σ(w ^ 2)`), where
`w = ∏ p ^ (v_p(N) / 2)` over the same primes.
This is a restricted result (special exponent 1, index supported on exactly two primes); it
does not exclude this case. Its novelty has not been verified. -/
theorem eulerIndex_pair_t_count (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧ ¬ t ∣ q + 1 ∧
      orderOf (u : ZMod t) = N.factorization u + 1 ∧
      ∃ j, 0 < j ∧ Odd j ∧ σ 1 (u ^ N.factorization u) = t ^ j ∧
      N.factorization t = j + ∑ p ∈ N.primeFactors \ {q, r, s},
        (σ 1 (p ^ N.factorization p)).factorization t ∧
      Odd (∑ p ∈ N.primeFactors \ {q, r, s}, (σ 1 (p ^ N.factorization p)).factorization t) ∧
      (∃ p ∈ N.primeFactors \ {q, r, s}, t ∣ σ 1 (p ^ N.factorization p)) ∧
      t ∣ σ 1 ((∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2) ∧
      ∃ b, σ 1 ((∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2) =
        t ^ (∑ p ∈ N.primeFactors \ {q, r, s}, (σ 1 (p ^ N.factorization p)).factorization t) *
          u ^ b := by
  obtain ⟨t, u, htu, hne, hA, ⟨j, hj, hjo, hB⟩, h3, -, -, hord, -, -, -, hrest, -⟩ :=
    eulerIndex_pair_cofactor h hq hN hqm hr hs hrs hJ
  set O := N.primeFactors \ {q, r, s} with hOdef
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have htJ : t ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  have huJ : u ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  obtain ⟨ht, -, htq, ht2, htN, hte⟩ := eipc_index_prime h hq hN hqm htJ
  obtain ⟨hu, -, huq, -, huN, -⟩ := eipc_index_prime h hq hN hqm huJ
  have hqN : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hN ▸ dvd_mul_right q _, h.ne_zero⟩
  have hrow : ∀ p ∈ O, σ 1 (p ^ N.factorization p) =
      t ^ (σ 1 (p ^ N.factorization p)).factorization t *
        u ^ (σ 1 (p ^ N.factorization p)).factorization u := by
    intro p hp
    obtain ⟨hpN, hpq, hpt, hpu⟩ := eipc_mem_out htu hp
    obtain ⟨x, y, hxy⟩ := (hrest p hpN hpq hpt hpu).1
    rw [hxy, Nat.factorization_mul (pow_ne_zero _ ht.ne_zero) (pow_ne_zero _ hu.ne_zero),
      Finsupp.add_apply, Finsupp.add_apply, ht.factorization_pow, hu.factorization_pow,
      Finsupp.single_eq_same, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne,
      Finsupp.single_eq_of_ne hne.symm, add_zero, zero_add]
  -- the count at `t`
  have hcount : N.factorization t =
      j + ∑ p ∈ O, (σ 1 (p ^ N.factorization p)).factorization t := by
    have hprod : σ 1 N = ∏ p ∈ N.primeFactors, σ 1 (p ^ N.factorization p) := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ h.ne_zero,
        Nat.prod_factorization_eq_prod_primeFactors]
    have hfac : (2 * N).factorization t =
        ∑ p ∈ N.primeFactors, (σ 1 (p ^ N.factorization p)).factorization t := by
      rw [← h.sigma_eq, hprod, Nat.factorization_prod
        (fun p hp => (sigma_pos 1 _
          (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne'),
        Finsupp.finsetSum_apply]
    rw [Nat.factorization_mul (by norm_num) h.ne_zero, Finsupp.add_apply,
      Nat.prime_two.factorization, Finsupp.single_apply, if_neg (Ne.symm ht2), zero_add] at hfac
    have hsub : ({q, r, s} : Finset ℕ) ⊆ N.primeFactors := by
      rw [← htu]
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hqN
      · exact htN
      · exact huN
    rw [← Finset.sum_sdiff hsub, ← hOdef, ← htu, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨htq.symm, huq.symm⟩), Finset.sum_pair hne] at hfac
    have hvq : N.factorization q = 1 := by
      rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
        hq.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd))]
    have hσq : σ 1 (q ^ N.factorization q) = q + 1 := by
      rw [hvq, sigma_one_apply_prime_pow hq, Finset.sum_range_succ, Finset.sum_range_one,
        pow_zero, pow_one, add_comm]
    rw [hσq, Nat.factorization_eq_zero_of_not_dvd h3,
      Nat.factorization_eq_zero_of_not_dvd (eipc_not_dvd_row ht), hB, ht.factorization_pow,
      Finsupp.single_eq_same] at hfac
    omega
  set A := ∑ p ∈ O, (σ 1 (p ^ N.factorization p)).factorization t with hAdef
  have hAodd : Odd A := by
    obtain ⟨k, hk⟩ := hte
    obtain ⟨i, hi⟩ := hjo
    exact Nat.odd_iff.mpr (by omega)
  have hA0 : A ≠ 0 := by rintro h0; rw [h0] at hAodd; exact absurd hAodd (by decide)
  have hshape : σ 1 ((∏ p ∈ O, p ^ (N.factorization p / 2)) ^ 2) =
      t ^ A * u ^ ∑ p ∈ O, (σ 1 (p ^ N.factorization p)).factorization u := by
    have hev : ∀ p ∈ O, Even (N.factorization p) := fun p hp =>
      hN ▸ eipc_even hq hm (eipc_mem_out htu hp).2.1
    rw [eipc_prod_sq hev, isMultiplicative_sigma.map_prod (fun p => p ^ N.factorization p) O
      (fun a ha b hb hab => Nat.coprime_pow_primes _ _
        (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp ha).1)
        (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hb).1) hab),
      Finset.prod_congr rfl hrow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.prod_pow_eq_pow_sum]
  refine ⟨t, u, htu, hne, hA, h3, hord, j, hj, hjo, hB, hcount, hAodd, ?_,
    ?_, _, hshape⟩
  · obtain ⟨p, hp, hp0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA0
    exact ⟨p, hp, Nat.dvd_of_factorization_pos hp0⟩
  · rw [hshape]
    exact dvd_mul_of_dvd_left (dvd_pow_self t hA0) _

/-- **Two prime index, a character condition.** In the setting of `eulerIndex_pair_cofactor`,
for the same labeling `(t, u)` with `σ(t ^ v_t(N)) = q u ^ v`, we have `q u ^ v ≡ 1 (mod t)`,
and `2 (1 + u ^ v)` is a nonzero square modulo `t`. This is a restricted result (special
exponent 1, index supported on exactly two primes); it does not exclude this case. Its novelty
has not been verified. -/
theorem eulerIndex_pair_character (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧ ¬ t ∣ q + 1 ∧
      (∃ j, 0 < j ∧ Odd j ∧ σ 1 (u ^ N.factorization u) = t ^ j) ∧
      ∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v ∧ ((q * u ^ v : ℕ) : ZMod t) = 1 ∧
        IsSquare ((2 * (1 + u ^ v) : ℕ) : ZMod t) ∧
        ((2 * (1 + u ^ v) : ℕ) : ZMod t) ≠ 0 := by
  obtain ⟨t, u, htu, hne, ⟨v, hA⟩, hB, h3, -, -, hord, -, -, -, -, d, hd⟩ :=
    eulerIndex_pair_cofactor h hq hN hqm hr hs hrs hJ
  set w := ∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2) with hwdef
  have htJ : t ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  have huJ : u ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  obtain ⟨ht, -, -, ht2, -, -⟩ := eipc_index_prime h hq hN hqm htJ
  obtain ⟨hu, -, -, -, -, hfe⟩ := eipc_index_prime h hq hN hqm huJ
  have := Fact.mk ht
  have hA1 : ((σ 1 (t ^ N.factorization t) : ℕ) : ZMod t) = 1 := by
    rw [sigma_one_apply_prime_pow ht, Finset.sum_range_succ']
    push_cast
    simp
  have hqu : (q : ZMod t) * (u : ZMod t) ^ v = 1 := by
    rw [← hA1, hA]; push_cast; ring
  -- `u` is a square modulo `t`
  obtain ⟨k, hk⟩ := hfe
  have hu1 : (u : ZMod t) ^ (N.factorization u + 1) = 1 := by
    rw [← hord]; exact pow_orderOf_eq_one _
  have hU : ((u : ZMod t) ^ (k + 1)) ^ 2 = u := by
    rw [← pow_mul, show (k + 1) * 2 = (N.factorization u + 1) + 1 by omega, pow_succ, hu1,
      one_mul]
  have hcast : (q : ZMod t) + 1 = 2 * (u : ZMod t) ^ d * (w : ZMod t) ^ 2 := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod t)) hd
  have hkey : ((2 * (1 + u ^ v) : ℕ) : ZMod t) =
      (2 * (w : ZMod t) * ((u : ZMod t) ^ (k + 1)) ^ (d + v)) ^ 2 := by
    calc ((2 * (1 + u ^ v) : ℕ) : ZMod t)
        = 2 * (((q : ZMod t) + 1) * (u : ZMod t) ^ v) := by
          push_cast; rw [add_mul, hqu, one_mul]
      _ = 4 * (((u : ZMod t) ^ (k + 1)) ^ 2) ^ (d + v) * (w : ZMod t) ^ 2 := by
          rw [hcast, hU]; ring
      _ = (2 * (w : ZMod t) * ((u : ZMod t) ^ (k + 1)) ^ (d + v)) ^ 2 := by ring
  have h20 : (2 : ZMod t) ≠ 0 := by
    intro h0
    have h2 : ((2 : ℕ) : ZMod t) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact ht2 ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_two).mp h2)
  have hw0 : (w : ZMod t) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro htw
    obtain ⟨p, hp, hpd⟩ := (ht.prime.dvd_finsetProd_iff _).mp htw
    obtain ⟨hpN, -, hpt, -⟩ := EulerIndexPairCofactor.eipc_mem_out htu hp
    exact hpt ((Nat.prime_dvd_prime_iff_eq ht (Nat.prime_of_mem_primeFactors hpN)).mp
      (ht.dvd_of_dvd_pow hpd)).symm
  have hu0 : (u : ZMod t) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro htu'
    exact hne ((Nat.prime_dvd_prime_iff_eq ht hu).mp htu')
  refine ⟨t, u, htu, hne, h3, hB, v, hA, by push_cast; exact hqu, ?_, ?_⟩
  · exact ⟨_, by rw [hkey, sq]⟩
  · rw [hkey]
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero h20 hw0) (pow_ne_zero _ (pow_ne_zero _ hu0)))

end OddPerfect

#print axioms OddPerfect.eulerIndex_pair_cofactor
#print axioms OddPerfect.eulerIndex_pair_t_count
#print axioms OddPerfect.eulerIndex_pair_character
