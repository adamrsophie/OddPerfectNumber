import OddPerfect.EulerIndexPairSplit

/-!
# Two prime Euler index: the sender row has prime length

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`. The landed labeling `(t, u)` has `σ(t ^ e) = q u ^ v` and `σ(u ^ f) = t ^ j` with
`e = v_t(N)`, `f = v_u(N)`, `j` odd, `j < e`, and `u` of order `f + 1 ≥ 3` modulo `t`;
`eulerIndex_pair_split` splits the cases `e + 1` prime and `e + 1 = P ^ 2`.

Write `R_n(x) = ∑ i < n, x ^ i`, so `R_(a b)(x) = R_a(x) R_b(x ^ a)`.

* `sigma_row_not_prime_sq` (arithmetic): `e + 1` is not the square of a prime.
  In the case `u = P`, `t ≡ 1 (mod u)`, `v = 2`, both factors of
  `R_u(t) R_u(t ^ u) = q u ^ 2` are divisible by `u`, so one of them equals `u`, but both
  exceed `u`. In the case where `t` has order `P` modulo `u`, `R_P(t ^ P) ≡ P (mod u)` is prime
  to `u`, so it equals `q` and `R_P(t) = u ^ v`; then `v = 1` because
  `t ^ j = σ(u ^ f) ≡ 1 + u (mod u ^ 2)`, and `R_P(t) = u` contradicts `u ≢ 1 (mod t)`.
* `sigma_row_special_mod_of_one` (arithmetic): if `σ(t ^ e) = q u`, `u = e + 1` and
  `t ≡ 1 (mod u)` with `u` an odd prime, then `R_u(t) ≡ u (mod u ^ 2)`, so `q ≡ 1 (mod u)`.
* `eulerIndex_pair_prime_length`: `e + 1` is prime, and either `σ(t ^ e) = q`, or `v = 1`,
  `u = e + 1`, `t ≡ q ≡ 1 (mod u)` and `q + 1 = 2 w ^ 2`.

These are restricted results (special exponent 1, Euler index supported on exactly two
primes). They do not exclude this case. Their novelty has not been verified.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairPrimeLength

/-- `R_(a b)(r) = R_a(r) * R_b(r ^ a)`. -/
private theorem eippl_geom_mul (r a b : ℕ) :
    ∑ i ∈ range (a * b), r ^ i = (∑ i ∈ range a, r ^ i) * ∑ i ∈ range b, (r ^ a) ^ i := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h2 : ∑ x ∈ range a, r ^ (a * b + x) = (∑ i ∈ range a, r ^ i) * (r ^ a) ^ b := by
      rw [sum_mul]
      exact sum_congr rfl fun i _ => by rw [pow_add, pow_mul]; ring
    rw [mul_add_one, sum_range_add, ih, sum_range_succ, mul_add, h2]

/-- A geometric sum with base at least `2` and at least two terms exceeds its length. -/
private theorem eippl_gt {x n : ℕ} (hx : 2 ≤ x) (hn : 2 ≤ n) : n < ∑ i ∈ range n, x ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ]
  have h1 : k ≤ ∑ i ∈ range k, x ^ i := by
    have := sum_le_sum (s := range k) (f := fun _ => 1) (g := fun i => x ^ i)
      (fun i _ => Nat.pos_of_ne_zero (pow_ne_zero _ (by omega)))
    simpa using this
  have h2 : 2 ≤ x ^ k := le_trans hx (le_self_pow (by omega) (by omega))
  omega

/-- If `x ≡ 1`, then `R_n(x) ≡ n`. -/
private theorem eippl_cast_one {R : Type*} [CommRing R] {x : ℕ} (hx : (x : R) = 1) (n : ℕ) :
    ((∑ i ∈ range n, x ^ i : ℕ) : R) = n := by
  push_cast
  simp [hx]

/-- `R_(k + 1)(t) ≡ 1 (mod t)`. -/
private theorem eippl_cast_mod_self (t k : ℕ) :
    ((∑ i ∈ range (k + 1), t ^ i : ℕ) : ZMod t) = 1 := by
  rw [sum_range_succ']
  push_cast
  simp

/-- `(u : ZMod (u ^ 2)) ^ 2 = 0`. -/
private theorem eippl_sq_zero (u : ℕ) : (u : ZMod (u ^ 2)) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

/-- From `t % u = 1`, `t ≡ 1` in `ZMod u`. -/
private theorem eippl_cast_of_mod {t u : ℕ} (hu : 1 < u) (h : t % u = 1) : (t : ZMod u) = 1 := by
  have := (ZMod.natCast_eq_natCast_iff' t 1 u).mpr (by rw [h, Nat.mod_eq_of_lt hu])
  simpa using this

/-- The case `u = P`, `t ≡ 1 (mod u)`, `v = 2` is impossible. -/
private theorem eippl_caseA {t u q : ℕ} (ht : t.Prime) (hu : u.Prime) (hq : q.Prime)
    (htu1 : t % u = 1) (hrow : ∑ i ∈ range (u ^ 2), t ^ i = q * u ^ 2) : False := by
  have ht1 : (t : ZMod u) = 1 := eippl_cast_of_mod hu.one_lt htu1
  have htu : ((t ^ u : ℕ) : ZMod u) = 1 := by push_cast; rw [ht1, one_pow]
  have hA : u ∣ ∑ i ∈ range u, t ^ i :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by rw [eippl_cast_one ht1, ZMod.natCast_self])
  have hB : u ∣ ∑ i ∈ range u, (t ^ u) ^ i :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by rw [eippl_cast_one htu, ZMod.natCast_self])
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  rw [sq, eippl_geom_mul, ha, hb] at hrow
  have hab : a * b = q := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hu.pos hu.pos)
    calc u * u * (a * b) = u * a * (u * b) := by ring
      _ = q * (u * u) := hrow
      _ = u * u * q := by ring
  have hgA := eippl_gt ht.two_le hu.two_le
  have hgB := eippl_gt (x := t ^ u) (le_trans ht.two_le (le_self_pow ht.one_lt.le hu.ne_zero))
    hu.two_le
  rw [ha] at hgA
  rw [hb] at hgB
  rcases Nat.prime_mul_iff.mp (hab ▸ hq) with ⟨-, h1⟩ | ⟨-, h1⟩
  · rw [h1, mul_one] at hgB; exact lt_irrefl _ hgB
  · rw [h1, mul_one] at hgA; exact lt_irrefl _ hgA

/-- The case where `t` has prime order `P` modulo `u` and `e + 1 = P ^ 2` is impossible. -/
private theorem eippl_caseB {t u q P v f j : ℕ} (ht : t.Prime) (hu : u.Prime) (hq : q.Prime)
    (hP : P.Prime) (hrow : ∑ i ∈ range (P ^ 2), t ^ i = q * u ^ v) (hf : f ≠ 0)
    (hcol : ∑ i ∈ range (f + 1), u ^ i = t ^ j) (hPj : P ∣ j)
    (hord : orderOf (t : ZMod u) = P) (hordu : orderOf (u : ZMod t) ≠ 1) : False := by
  have := Fact.mk hu
  have htP : (t : ZMod u) ^ P = 1 := hord ▸ pow_orderOf_eq_one _
  have hPu : (P : ZMod u) ≠ 0 := by
    intro h0
    have huP : u = P := (Nat.prime_dvd_prime_iff_eq hu hP).mp ((ZMod.natCast_eq_zero_iff _ _).mp h0)
    subst huP
    rw [ZMod.pow_card] at htP
    rw [orderOf_eq_one_iff.mpr htP] at hord
    exact hu.one_lt.ne hord
  set C := ∑ i ∈ range P, (t ^ P) ^ i with hCdef
  set A := ∑ i ∈ range P, t ^ i with hAdef
  have hCu : ¬ u ∣ C := by
    rw [← ZMod.natCast_eq_zero_iff, hCdef,
      eippl_cast_one (by push_cast; exact htP)]
    exact hPu
  rw [sq, eippl_geom_mul] at hrow
  have hCq : C ∣ q := by
    have hcop : Nat.Coprime C (u ^ v) :=
      (Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hu).mpr hCu)).symm
    exact hcop.dvd_of_dvd_mul_right (Dvd.intro_left A hrow)
  have htP2 : 2 ≤ t ^ P := le_trans ht.two_le (le_self_pow ht.one_lt.le hP.ne_zero)
  have hCq' : C = q := by
    rcases hq.eq_one_or_self_of_dvd C hCq with h1 | h1
    · have := eippl_gt htP2 hP.two_le
      rw [← hCdef, h1] at this
      have := hP.two_le
      omega
    · exact h1
  have hAu : A = u ^ v := by
    apply Nat.eq_of_mul_eq_mul_right hq.pos
    rw [← hCq', hrow, hCq']
    ring
  have hgA : P < A := eippl_gt ht.two_le hP.two_le
  rcases Nat.lt_or_ge v 2 with hv | hv
  · interval_cases v
    · rw [hAu, pow_zero] at hgA
      have := hP.two_le
      omega
    · apply hordu
      apply orderOf_eq_one_iff.mpr
      obtain ⟨k, hk⟩ : ∃ k, P = k + 1 := ⟨P - 1, by have := hP.two_le; omega⟩
      have h1 := eippl_cast_mod_self t k
      rw [← hk, ← hAdef, hAu, pow_one] at h1
      exact h1
  · obtain ⟨w, rfl⟩ : ∃ w, v = w + 2 := ⟨v - 2, by omega⟩
    have hA0 : ∑ i ∈ range P, (t : ZMod (u ^ 2)) ^ i = 0 := by
      have h1 : ((A : ℕ) : ZMod (u ^ 2)) = 0 := by
        rw [hAu]; push_cast; rw [pow_add, eippl_sq_zero, mul_zero]
      rw [hAdef] at h1
      push_cast at h1
      exact h1
    have hg := geom_sum_mul (t : ZMod (u ^ 2)) P
    rw [hA0, zero_mul] at hg
    have htP' : (t : ZMod (u ^ 2)) ^ P = 1 := by linear_combination -hg
    have htj : (t : ZMod (u ^ 2)) ^ j = 1 := by
      obtain ⟨k, rfl⟩ := hPj
      rw [pow_mul, htP', one_pow]
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hc := congrArg (fun n : ℕ => (n : ZMod (u ^ 2))) hcol
    push_cast at hc
    rw [htj, sum_range_succ', sum_range_succ'] at hc
    have hz : ∀ i : ℕ, (u : ZMod (u ^ 2)) ^ (i + 1 + 1) = 0 := fun i => by
      rw [show i + 1 + 1 = i + 2 by omega, pow_add, eippl_sq_zero, mul_zero]
    simp only [hz, sum_const_zero, zero_add, pow_zero, pow_one] at hc
    have hu0 : (u : ZMod (u ^ 2)) = 0 := by linear_combination hc
    have hdv := Nat.le_of_dvd hu.pos ((ZMod.natCast_eq_zero_iff _ _).mp hu0)
    have := hu.two_le
    rw [sq] at hdv
    nlinarith

/-- Every prime other than `q` has even exponent in `q * m ^ 2`. -/
private theorem eippl_even {q m p : ℕ} (hq : q.Prime) (hm : m ≠ 0) (hpq : p ≠ q) :
    Even ((q * m ^ 2).factorization p) := by
  rw [Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
    hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq), zero_add,
    Nat.factorization_pow]
  exact ⟨m.factorization p, by simp [two_mul]⟩

end EulerIndexPairPrimeLength

open EulerIndexPairPrimeLength

/-- **Sender row, no square length.** Let `t`, `u`, `q` be primes, `t` and `u` odd, `t ≠ u`,
`u ≠ q`, `e` even, `σ(t ^ e) = q u ^ v`, `σ(u ^ f) = t ^ j` with `f ≠ 0` and `0 < j < e + 1`,
and suppose `u ≢ 1 (mod t)` (the order of `u` modulo `t` is not 1). Then `e + 1` is not the
square of a prime. Elementary; nothing new is claimed. -/
theorem sigma_row_not_prime_sq {t u q e v f j : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) (hu : u.Prime)
    (hu2 : u ≠ 2) (hq : q.Prime) (htu : t ≠ u) (huq : u ≠ q) (he : Even e)
    (hrow : σ 1 (t ^ e) = q * u ^ v) (hj : 0 < j) (hje : j < e + 1) (hf : f ≠ 0)
    (hcol : σ 1 (u ^ f) = t ^ j) (hord : orderOf (u : ZMod t) ≠ 1) :
    ¬ ∃ P, P.Prime ∧ e + 1 = P ^ 2 := by
  rintro ⟨P, hP, hPe⟩
  have := Fact.mk hu
  have htj : (t : ZMod u) ^ j = 1 := by
    have h1 : ((σ 1 (u ^ f) : ℕ) : ZMod u) = 1 := by
      rw [sigma_one_apply_prime_pow hu, sum_range_succ']
      push_cast
      simp
    rw [hcol] at h1
    exact_mod_cast h1
  have hsplit := (sigma_row_split ht ht2 hu hu2 hq htu huq he hrow hj hje htj).2 P hP hPe
  rw [sigma_one_apply_prime_pow ht, hPe] at hrow
  rw [sigma_one_apply_prime_pow hu] at hcol
  rcases hsplit with ⟨hv, huP, hmod⟩ | ⟨-, hPj, hordt⟩
  · rw [hv, ← huP] at hrow
    exact eippl_caseA ht hu hq hmod hrow
  · exact eippl_caseB ht hu hq hP hrow hf hcol hPj hordt hord

/-- **Sender row of length `u`, the special prime modulo `u`.** Let `t`, `u` be primes, `u` odd,
`σ(t ^ e) = q u`, `u = e + 1` and `t ≡ 1 (mod u)`. Then `σ(t ^ e) ≡ u (mod u ^ 2)`, so
`q ≡ 1 (mod u)`. Elementary; nothing new is claimed. -/
theorem sigma_row_special_mod_of_one {t u q e : ℕ} (ht : t.Prime) (hu : u.Prime) (hu2 : u ≠ 2)
    (hrow : σ 1 (t ^ e) = q * u) (hue : u = e + 1) (htu : t % u = 1) : q % u = 1 := by
  obtain ⟨k, hk⟩ := hu.eq_two_or_odd'.resolve_left hu2
  obtain ⟨c, hc⟩ : ∃ c, t = u * c + 1 := by
    have := Nat.div_add_mod t u
    rw [htu] at this
    exact ⟨t / u, this.symm⟩
  have htc : (t : ZMod (u ^ 2)) = 1 + c * u := by rw [hc]; push_cast; ring
  have hpow : ∀ i : ℕ,
      (t : ZMod (u ^ 2)) ^ i = 1 + (i : ZMod (u ^ 2)) * ((c : ZMod (u ^ 2)) * u) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ (t : ZMod (u ^ 2)) i, ih, htc]
      push_cast
      linear_combination ((i : ZMod (u ^ 2)) * c ^ 2) * eippl_sq_zero u
  have hS : (∑ i ∈ range u, i) = u * k := by
    have h2 := sum_range_id_mul_two u
    rw [show u - 1 = 2 * k by omega] at h2
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
    rw [h2]; ring
  have hSz : (∑ i ∈ range u, (i : ZMod (u ^ 2))) = (u : ZMod (u ^ 2)) * k := by
    have := congrArg (Nat.cast : ℕ → ZMod (u ^ 2)) hS
    push_cast at this
    exact this
  have hsum : ((σ 1 (t ^ e) : ℕ) : ZMod (u ^ 2)) = u := by
    rw [sigma_one_apply_prime_pow ht, ← hue]
    push_cast
    rw [sum_congr rfl (fun i _ => hpow i), sum_add_distrib, ← sum_mul, hSz]
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    linear_combination ((k : ZMod (u ^ 2)) * c) * eippl_sq_zero u
  rw [hrow] at hsum
  have hmod : q * u ≡ u [MOD u ^ 2] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hsum
  have h1 : q ≡ 1 [MOD u] := by
    apply Nat.ModEq.mul_left_cancel' hu.ne_zero
    rw [mul_comm u q, mul_one, ← sq]
    exact hmod
  rw [Nat.ModEq, Nat.mod_eq_of_lt hu.one_lt] at h1
  exact h1

/-- A swapped labeling would give `q ∣ t ^ j`, so the two labelings agree. -/
private theorem eippl_label {N q m r s t u t' u' j v' : ℕ} (h : OddPerfect N) (hq : q.Prime)
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

variable {N q m r s : ℕ}

/-- **Two prime index, the sender row has prime length.** Let `N = q m ^ 2` be an odd perfect
number with special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index
`J = σ(m ^ 2) / q` has exactly the two prime factors `r ≠ s`. For the labeling `(t, u)` of
`eulerIndex_pair_split`, with `e = v_t(N)`, `σ(t ^ e) = q u ^ v`, `σ(u ^ v_u(N)) = t ^ j`, `j`
odd and `j < e`, the number `e + 1` is prime, and either `v = 0` and `σ(t ^ e) = q`, or
`v = 1`, `u = e + 1`, `t ≡ 1 (mod u)`, `q ≡ 1 (mod u)` and `q + 1 = 2 w ^ 2`, where
`w = ∏ p ^ (v_p(N) / 2)` over the primes `p ∣ N` outside `{q, r, s}`. This is a restricted
result (special exponent 1, index supported on exactly two primes); it does not exclude this
case. Its novelty has not been verified. -/
theorem eulerIndex_pair_prime_length (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧ ∃ v j,
      σ 1 (t ^ N.factorization t) = q * u ^ v ∧ 0 < j ∧ Odd j ∧
      σ 1 (u ^ N.factorization u) = t ^ j ∧ j < N.factorization t ∧
      (N.factorization t + 1).Prime ∧
      ((v = 0 ∧ σ 1 (t ^ N.factorization t) = q) ∨
        (v = 1 ∧ u = N.factorization t + 1 ∧ t % u = 1 ∧ q % u = 1 ∧
          q + 1 = 2 * (∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2)) := by
  obtain ⟨t, u, htu, hne, v, j, hA, hj, hjo, hB, hje, hp1, -⟩ :=
    eulerIndex_pair_split h hq hN hqm hr hs hrs hJ
  obtain ⟨t', u', htu', hne', ⟨v', hA'⟩, -, -, -, hf1, hord, -, hE, -, -, d, hd⟩ :=
    eulerIndex_pair_cofactor h hq hN hqm hr hs hrs hJ
  obtain ⟨h1, h2⟩ := eippl_label h hq hN hqm hJ htu htu' hne' hB hA'
  rw [h1, h2] at hord
  rw [h1] at hE
  rw [h2] at hf1 hd
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
  have he : Even (N.factorization t) := hN ▸ eippl_even hq hm htq
  have hf0 : N.factorization u ≠ 0 := fun h0 => by
    rw [h0] at hf1; exact Nat.not_prime_one hf1
  have hord1 : orderOf (u : ZMod t) ≠ 1 := by rw [hord]; omega
  have hp : (N.factorization t + 1).Prime :=
    hE.resolve_right (sigma_row_not_prime_sq ht ht2 hu hu2 hq hne huq he hA hj (by omega) hf0
      hB hord1)
  refine ⟨t, u, htu, hne, v, j, hA, hj, hjo, hB, hje, hp, ?_⟩
  rcases hp1 hp with hv | ⟨hv, hue, htu1⟩
  · exact Or.inl hv
  right
  have hqu : q % u = 1 := by
    rw [hv, pow_one] at hA
    exact sigma_row_special_mod_of_one ht hu hu2 hA hue htu1
  have hd0 : d = 0 := by
    by_contra hd0
    have hdvd : u ∣ q + 1 := hd ▸ dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (dvd_pow_self u hd0) 2) _
    have hq' : q + 1 = u * (q / u) + 2 := by
      have := Nat.div_add_mod q u
      rw [hqu] at this
      generalize q / u = c at this ⊢
      omega
    rw [hq'] at hdvd
    have h2 := Nat.le_of_dvd (by norm_num) ((Nat.dvd_add_right (dvd_mul_right u _)).mp hdvd)
    have := hu.two_le
    omega
  rw [hd0, pow_zero, mul_one] at hd
  exact ⟨hv, hue, htu1, hqu, hd⟩

end OddPerfect

#print axioms OddPerfect.sigma_row_not_prime_sq
#print axioms OddPerfect.sigma_row_special_mod_of_one
#print axioms OddPerfect.eulerIndex_pair_prime_length
