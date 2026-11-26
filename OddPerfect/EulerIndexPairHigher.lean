import OddPerfect.EulerIndexSupportAll
import OddPerfect.EulerIndexOmegaSigned

/-!
# An Euler index with exactly two prime factors, special exponent above one

Let `N = q ^ a * m ^ 2` be an odd perfect number in Euler's form, with `q` the special prime,
`q ∤ m` and `a ≠ 1`, and suppose that the Euler index `J = eulerIndex q a m` has exactly two
prime factors `r` and `s`. Put `L = (a + 1) / 2`, `R = ∑ i < L, q ^ i`, `C = (q ^ L + 1) / 2`,
`B = (q + 1) / 2` and `A = (q ^ L + 1) / (q + 1)`, so that `σ(q ^ a) / 2 = R C` and `C = B A`.
This module proves that the special row has the following shape (restricted case, necessary
conditions only; the case is not excluded).

* `L` is prime, and `r`, `s` both have odd valuation in `J`.
* For one of them, called `t`, `R = t x ^ 2`, and `t = L` or `t ≡ 1 (mod 2 L)`.
* For the other, called `u`: `u ≠ L`, `u ≡ 1 (mod 2 L)`, and either `q + 1 = 2 z ^ 2` and
  `A = u w ^ 2`, or `q + 1 = 2 L z ^ 2` and `A = L u w ^ 2`.

Method. `J R C = m ^ 2`, so the primes of odd valuation in `R C` lie in `{r, s}`. `R` and `C` are
coprime and neither is a square (`geom_sum_prime_pow_ne_sq`, `halfPowerNotSquare`), so each
has exactly one prime of odd valuation. `A ≡ L (mod q + 1)` bounds `gcd(B, A)` by `L`; if
`L ∣ q + 1` then `v_L(A) = 1` by lifting the exponent. `A` is neither a square nor `L` times a
square (`alternating_sum_prime_pow_ne_sq`, `alternating_sum_ne_prime_mul_sq`). The congruences
come from the order of `q` modulo `t` and of `-q` modulo `u`.

This holds for every odd perfect number in the restricted case named above. It gives necessary
conditions only and does not exclude the case; the novelty is not verified. The odd perfect
number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairHigher

/-- The special prime is `1 (mod 4)` and so is its exponent. -/
private lemma eiph_special_facts {N q a m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) : q % 4 = 1 ∧ a % 4 = 1 := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hfac : N.factorization q = a := by
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
      Finsupp.smul_apply, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  have ha : Odd a := by
    rcases Nat.even_or_odd a with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  have h4 := special_mod_four h hq (hfac ▸ ha)
  rwa [hfac] at h4

/-- A prime of odd valuation is a prime factor. -/
private lemma eiph_mem_of_odd {n t : ℕ} (ho : Odd (n.factorization t)) :
    t ∈ n.primeFactors := by
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  intro h0
  rw [h0] at ho
  exact Nat.not_odd_zero ho

/-- A prime of odd valuation divides the number. -/
private lemma eiph_dvd_of_odd {n t : ℕ} (ho : Odd (n.factorization t)) : t ∣ n :=
  Nat.dvd_of_mem_primeFactors (eiph_mem_of_odd ho)

/-- If `J H = M ^ 2`, then `J` and `H` have the same primes of odd valuation. -/
private lemma eiph_odd_iff {J H M t : ℕ} (hJ : J ≠ 0) (hH : H ≠ 0) (he : J * H = M ^ 2) :
    Odd (J.factorization t) ↔ Odd (H.factorization t) := by
  have h2 := congrArg (fun n => n.factorization t) he
  simp only [Nat.factorization_mul hJ hH, Nat.factorization_pow, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul] at h2
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

/-- A prime dividing one of two coprime numbers does not divide the other. -/
private lemma eiph_not_dvd {X Y p : ℕ} (hc : Nat.Coprime X Y) (hp : p.Prime) (hpY : p ∣ Y) :
    ¬ p ∣ X := fun hpX => hp.ne_one (Nat.dvd_one.mp (by
  rw [← hc.gcd_eq_one]; exact Nat.dvd_gcd hpX hpY))

/-- The valuation of a coprime product at a prime of the second factor. -/
private lemma eiph_fact_right {X Y p : ℕ} (hX : X ≠ 0) (hY : Y ≠ 0) (hc : Nat.Coprime X Y)
    (hp : p.Prime) (hpY : p ∣ Y) : (X * Y).factorization p = Y.factorization p := by
  rw [Nat.factorization_mul hX hY, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (eiph_not_dvd hc hp hpY), zero_add]

/-- A nonzero number whose primes of odd valuation all equal `t` is a square or `t` times a
square. -/
private lemma eiph_sq_or {n t : ℕ} (hn : n ≠ 0)
    (h : ∀ p, p.Prime → Odd (n.factorization p) → p = t) :
    (∃ x, n = x ^ 2) ∨ ∃ x, n = t * x ^ 2 := by
  obtain ⟨d, b, hd, hsf⟩ := Nat.sq_mul_squarefree n
  have hb : b ≠ 0 := by rintro rfl; apply hn; rw [← hd]; simp
  have hd0 : d ≠ 0 := hsf.ne_zero
  have hodd : ∀ p, p.Prime → p ∣ d → p = t := by
    intro p hp hpd
    apply h p hp
    rw [← hd, Nat.factorization_mul (pow_ne_zero 2 hb) hd0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_one_of_squarefree hsf hp hpd]
    exact ⟨_, rfl⟩
  by_cases hd1 : d = 1
  · left
    exact ⟨b, by rw [← hd, hd1, mul_one]⟩
  · right
    have htp : d.minFac.Prime := Nat.minFac_prime hd1
    have ht := hodd _ htp (Nat.minFac_dvd d)
    obtain ⟨e, he⟩ := Nat.minFac_dvd d
    rw [ht] at he htp
    have he1 : e = 1 := by
      by_contra he1
      have h2 := hodd _ (Nat.minFac_prime he1)
        ((Nat.minFac_dvd e).trans ⟨t, by rw [he]; ring⟩)
      have htt : t * t ∣ d := by
        rw [he]; exact Nat.mul_dvd_mul_left t (h2 ▸ Nat.minFac_dvd e)
      exact htp.one_lt.ne' (Nat.isUnit_iff.mp (hsf t htt))
    exact ⟨b, by rw [← hd, he, he1, mul_one, mul_comm]⟩

/-- A nonzero number that is not a square has a prime of odd valuation. -/
private lemma eiph_exists_odd {n : ℕ} (hn : n ≠ 0) (hns : ∀ y, n ≠ y ^ 2) :
    ∃ p, p.Prime ∧ Odd (n.factorization p) := by
  by_contra hall
  push Not at hall
  rcases eiph_sq_or hn (t := 1)
    (fun p hp ho => absurd ho (Nat.not_odd_iff_even.mpr (hall p hp))) with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact hns y hy
  · exact hns y (by rw [hy, one_mul])

/-- The coprime split: if `X` and `Y` are coprime, every prime of odd valuation in `X Y` is `u`
and `Y` is not a square, then `X` is a square and `Y` is `u` times a square. -/
private lemma eiph_split {X Y u : ℕ} (hX : X ≠ 0) (hY : Y ≠ 0) (hc : Nat.Coprime X Y)
    (hu : ∀ p, p.Prime → Odd ((X * Y).factorization p) → p = u) (hns : ∀ y, Y ≠ y ^ 2) :
    (∃ z, X = z ^ 2) ∧ Odd (Y.factorization u) ∧ ∃ w, Y = u * w ^ 2 := by
  have hYodd : ∀ p, p.Prime → Odd (Y.factorization p) → p = u := fun p hp ho =>
    hu p hp (by rw [eiph_fact_right hX hY hc hp (eiph_dvd_of_odd ho)]; exact ho)
  obtain ⟨p, hp, hpo⟩ := eiph_exists_odd hY hns
  obtain rfl := hYodd p hp hpo
  have hXodd : ∀ p', p'.Prime → Odd (X.factorization p') → p' = 1 := by
    intro p' hp' ho
    exfalso
    have hp'X := eiph_dvd_of_odd ho
    have hp'Y : ¬ p' ∣ Y := eiph_not_dvd hc.symm hp' hp'X
    have he : p' = p := hu p' hp' (by
      rw [Nat.factorization_mul hX hY, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hp'Y, add_zero]
      exact ho)
    exact hp'Y (he ▸ eiph_dvd_of_odd hpo)
  refine ⟨?_, hpo, ?_⟩
  · rcases eiph_sq_or hX hXodd with hs | ⟨x, hx⟩
    · exact hs
    · exact ⟨x, by rw [hx, one_mul]⟩
  · rcases eiph_sq_or hY hYodd with ⟨y, hy⟩ | hs
    · exact absurd hy (hns y)
    · exact hs

/-- For odd `p` with `u ^ p + 1 = (u + 1) * F`, `u + 1` divides `F - p` in `ℤ`. -/
private lemma eiph_dvd_sub {u p F : ℕ} (hp : Odd p) (hF : u ^ p + 1 = (u + 1) * F) :
    ((u : ℤ) + 1) ∣ (F : ℤ) - p := by
  have hgs := geom_sum_mul (-(u : ℤ)) p
  have hneg : (-(u : ℤ)) ^ p = -((u : ℤ) ^ p) := hp.neg_pow _
  have hFz : ((u : ℤ) + 1) * F = (u : ℤ) ^ p + 1 := by exact_mod_cast hF.symm
  have hu0 : ((u : ℤ) + 1) ≠ 0 := by positivity
  have hsum : (F : ℤ) = ∑ i ∈ Finset.range p, (-(u : ℤ)) ^ i := by
    apply mul_left_cancel₀ hu0
    rw [hFz]
    linear_combination hgs + hneg
  have hd : -(u : ℤ) - 1 ∣ ∑ i ∈ Finset.range p, ((-(u : ℤ)) ^ i - 1) :=
    Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow (-(u : ℤ)) 1 i
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    ← hsum] at hd
  have hx : -(u : ℤ) - 1 = -((u : ℤ) + 1) := by ring
  rw [hx, neg_dvd] at hd
  exact hd

/-- A common divisor of `q + 1` and `A` with `q + 1 ∣ A - L` divides `L`. -/
private lemma eiph_dvd_L {g q A L : ℕ} (hd : ((q : ℤ) + 1) ∣ (A : ℤ) - L) (hg1 : g ∣ q + 1)
    (hgA : g ∣ A) : g ∣ L := by
  have h1 : ((g : ℕ) : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hg1
  have h2 : ((g : ℕ) : ℤ) ∣ (A : ℤ) := Int.natCast_dvd_natCast.mpr hgA
  have h3 := dvd_sub h2 (h1.trans hd)
  rw [sub_sub_cancel] at h3
  exact Int.natCast_dvd_natCast.mp h3

/-- If `x ^ L = 1` and `x ≠ 1` modulo an odd prime `t`, `L` prime, then `t ≡ 1 (mod 2 L)`. -/
private lemma eiph_mod_of_order {t L : ℕ} [Fact t.Prime] (hL : L.Prime) (hL2 : L ≠ 2)
    {x : ZMod t} (hx : x ^ L = 1) (hx1 : x ≠ 1) (ht : Odd t) : t % (2 * L) = 1 := by
  have := Fact.mk hL
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hL.ne_zero] at hx
    exact zero_ne_one hx
  have hd : L ∣ t - 1 := orderOf_eq_prime hx hx1 ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have h2 : 2 ∣ t - 1 := by
    obtain ⟨k, hk⟩ := ht
    exact ⟨k, by omega⟩
  have hcop : Nat.Coprime 2 L := (Nat.coprime_primes Nat.prime_two hL).mpr (Ne.symm hL2)
  obtain ⟨k, hk⟩ := hcop.mul_dvd_of_dvd_of_dvd h2 hd
  have ht1 : 1 ≤ t := (Fact.out : t.Prime).one_lt.le
  have hL1 : 1 < 2 * L := by have := hL.two_le; omega
  generalize hM : 2 * L * k = M at hk
  have htM : t = M + 1 := by omega
  rw [htM, ← hM, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt hL1]

/-- The arithmetic core. -/
private lemma eiph_core {q L r s : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) (hL : L.Prime)
    (hL3 : 3 ≤ L) (hrs : r ≠ s)
    (hH : ∀ p, p.Prime →
      Odd (((∑ i ∈ Finset.range L, q ^ i) * ((q ^ L + 1) / 2)).factorization p) →
        p = r ∨ p = s) :
    ∃ t u : ℕ, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      Odd (((∑ i ∈ Finset.range L, q ^ i) * ((q ^ L + 1) / 2)).factorization t) ∧
      Odd (((∑ i ∈ Finset.range L, q ^ i) * ((q ^ L + 1) / 2)).factorization u) ∧
      ∃ x w z : ℕ, ∑ i ∈ Finset.range L, q ^ i = t * x ^ 2 ∧
        (t = L ∨ t % (2 * L) = 1) ∧ u ≠ L ∧ u % (2 * L) = 1 ∧
        ((q + 1 = 2 * z ^ 2 ∧ q ^ L + 1 = (q + 1) * (u * w ^ 2)) ∨
         (q + 1 = 2 * (L * z ^ 2) ∧ q ^ L + 1 = (q + 1) * (L * (u * w ^ 2)))) := by
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hL2 : L ≠ 2 := by omega
  have hLo : Odd L := hL.odd_of_ne_two hL2
  set R := ∑ i ∈ Finset.range L, q ^ i with hRdef
  set C := (q ^ L + 1) / 2 with hCdef
  -- parity and the halves
  have hqL4 : q ^ L % 4 = 1 := by rw [Nat.pow_mod, hq4]; simp
  have h2C : q ^ L + 1 = 2 * C := by rw [hCdef]; omega
  have hCodd : Odd C := Nat.odd_iff.mpr (by omega)
  have hRodd : Odd R := by
    rw [← ZMod.natCast_eq_one_iff_odd, hRdef]
    push_cast
    rw [ZMod.natCast_eq_one_iff_odd.mpr hqo]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact ZMod.natCast_eq_one_iff_odd.mpr hLo
  have hR0 : R ≠ 0 := by rintro h0; rw [h0] at hRodd; exact Nat.not_odd_zero hRodd
  have hC0 : C ≠ 0 := by rintro h0; rw [h0] at hCodd; exact Nat.not_odd_zero hCodd
  -- `q R + 1 = R + q ^ L`
  have hshift : q * R + 1 = R + q ^ L := by
    have h1 : ∑ i ∈ Finset.range (L + 1), q ^ i = R + q ^ L := Finset.sum_range_succ _ _
    have h2 : ∑ i ∈ Finset.range (L + 1), q ^ i = ∑ i ∈ Finset.range L, q ^ (i + 1) + q ^ 0 :=
      Finset.sum_range_succ' _ _
    have h3 : ∑ i ∈ Finset.range L, q ^ (i + 1) = q * R := by
      rw [hRdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => pow_succ' q i
    rw [h3, pow_zero] at h2
    omega
  have hRC : Nat.Coprime R C := by
    have hg : Nat.gcd R C ∣ 2 := by
      have h1 : Nat.gcd R C ∣ R + 2 * C := dvd_add (Nat.gcd_dvd_left R C)
        (dvd_mul_of_dvd_right (Nat.gcd_dvd_right R C) 2)
      have h2 : R + 2 * C = q * R + 2 := by omega
      rw [h2] at h1
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_right (Nat.gcd_dvd_left R C) q)).mp h1
    have hgo : Odd (Nat.gcd R C) := hCodd.of_dvd_nat (Nat.gcd_dvd_right R C)
    have := Nat.le_of_dvd two_pos hg
    obtain ⟨k, hk⟩ := hgo
    show Nat.gcd R C = 1
    omega
  -- neither `R` nor `C` is a square
  have hRns : ∀ y, R ≠ y ^ 2 := by
    intro y hy
    have := geom_sum_prime_pow_ne_sq (y := y) hq hq5 odd_one hLo hL3
    simp only [pow_one] at this
    exact this hy
  have hCns : ∀ y, C ≠ y ^ 2 := fun y hy =>
    halfPowerNotSquare q L hq hq4 hLo hL3 ⟨y, by rw [← hCdef, hy, sq]⟩
  -- the witnesses `t` and `u`
  obtain ⟨t, ht, hto⟩ := eiph_exists_odd hR0 hRns
  obtain ⟨u, hu, huo⟩ := eiph_exists_odd hC0 hCns
  have htR := eiph_dvd_of_odd hto
  have huC := eiph_dvd_of_odd huo
  have htH : Odd ((R * C).factorization t) := by
    rw [mul_comm, eiph_fact_right hC0 hR0 hRC.symm ht htR]; exact hto
  have huH : Odd ((R * C).factorization u) := by
    rw [eiph_fact_right hR0 hC0 hRC hu huC]; exact huo
  have htu : t ≠ u := fun he => eiph_not_dvd hRC hu huC (he ▸ htR)
  have htrs := hH t ht htH
  have hurs := hH u hu huH
  have hRt : ∀ p, p.Prime → Odd (R.factorization p) → p = t := by
    intro p hp ho
    have hpR := eiph_dvd_of_odd ho
    have hpu : p ≠ u := fun he => eiph_not_dvd hRC hu huC (he ▸ hpR)
    have hprs := hH p hp (by rw [mul_comm, eiph_fact_right hC0 hR0 hRC.symm hp hpR]; exact ho)
    omega
  have hCu : ∀ p, p.Prime → Odd (C.factorization p) → p = u := by
    intro p hp ho
    have hpC := eiph_dvd_of_odd ho
    have hpt : p ≠ t := fun he => eiph_not_dvd hRC.symm ht htR (he ▸ hpC)
    have hprs := hH p hp (by rw [eiph_fact_right hR0 hC0 hRC hp hpC]; exact ho)
    omega
  obtain ⟨x, hx⟩ : ∃ x, R = t * x ^ 2 := by
    rcases eiph_sq_or hR0 hRt with ⟨y, hy⟩ | hs
    · exact absurd hy (hRns y)
    · exact hs
  have hset : ({t, u} : Finset ℕ) = {r, s} := by
    rcases htrs with rfl | rfl <;> rcases hurs with rfl | rfl
    · exact absurd rfl htu
    · rfl
    · exact Finset.pair_comm _ _
    · exact absurd rfl htu
  -- the side fact for `t`
  have htside : t = L ∨ t % (2 * L) = 1 := by
    have := Fact.mk ht
    have hR0' : ((R : ℕ) : ZMod t) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr htR
    rw [hRdef] at hR0'
    push_cast at hR0'
    by_cases h1 : (q : ZMod t) = 1
    · left
      rw [h1] at hR0'
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hR0'
      exact (Nat.prime_dvd_prime_iff_eq ht hL).mp ((ZMod.natCast_eq_zero_iff L t).mp hR0')
    · right
      have hpow : (q : ZMod t) ^ L = 1 := by
        have h := geom_sum_mul (q : ZMod t) L
        rw [hR0', zero_mul] at h
        exact (sub_eq_zero.mp h.symm)
      exact eiph_mod_of_order hL hL2 hpow h1 (hRodd.of_dvd_nat htR)
  -- the split of `C`
  set B := (q + 1) / 2 with hBdef
  set A := signedRepunit q L with hAdef
  have h2B : q + 1 = 2 * B := by rw [hBdef]; omega
  have hAmul : (q + 1) * A = q ^ L + 1 := signedRepunit_mul hLo
  have hBA : B * A = C := by
    have : 2 * (B * A) = 2 * C := by rw [← h2C, ← hAmul, h2B]; ring
    omega
  have hB0 : B ≠ 0 := by omega
  have hA0 : A ≠ 0 := by rintro h0; rw [h0] at hBA; omega
  have hAodd : Odd A := (Nat.odd_mul.mp (hBA ▸ hCodd)).2
  have hAL := eiph_dvd_sub hLo hAmul.symm
  have hgBA : Nat.gcd B A ∣ L :=
    eiph_dvd_L hAL ((Nat.gcd_dvd_left B A).trans ⟨2, by rw [h2B]; ring⟩) (Nat.gcd_dvd_right B A)
  have hAns : ∀ y, A ≠ y ^ 2 := by
    intro y hy
    have := alternating_sum_prime_pow_ne_sq (y := y) hq hq5 one_ne_zero
      (by rw [pow_one]; exact hq4) hLo hL3
    simp only [pow_one] at this
    exact this (by rw [← hAmul, hy])
  have hCu' : ∀ p, p.Prime → Odd ((B * A).factorization p) → p = u := by
    rw [hBA]; exact hCu
  -- congruence for a prime `u ∣ A` with `u ≠ L`
  have hucong : u ∣ A → u ≠ L → u % (2 * L) = 1 := by
    intro huA huL
    have := Fact.mk hu
    have hnd : ¬ u ∣ q + 1 := fun hd => huL ((Nat.prime_dvd_prime_iff_eq hu hL).mp
      (eiph_dvd_L hAL hd huA))
    have hz : ((q ^ L + 1 : ℕ) : ZMod u) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (huA.trans ⟨q + 1, by rw [← hAmul]; ring⟩)
    push_cast at hz
    have hpow : (-(q : ZMod u)) ^ L = 1 := by
      rw [hLo.neg_pow]; linear_combination -hz
    have hne : -(q : ZMod u) ≠ 1 := by
      intro he
      apply hnd
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      linear_combination -he
    exact eiph_mod_of_order hL hL2 hpow hne (hAodd.of_dvd_nat huA)
  by_cases hLq : L ∣ q + 1
  · -- `L ∣ q + 1`: `v_L(A) = 1`
    have := Fact.mk hL
    have hLq' : ¬ L ∣ q := by
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq hL hq).mp hd
      subst this
      have h1 : L ∣ 1 := (Nat.dvd_add_right hd).mp hLq
      exact hL.ne_one (Nat.dvd_one.mp h1)
    have hv := padicValNat.pow_add_pow hLo hLq hLq' hLo (y := 1)
    rw [one_pow, ← hAmul, padicValNat.mul (by omega) hA0, padicValNat_self] at hv
    have hvA : padicValNat L A = 1 := by rw [Nat.padicValNat_def]; omega
    obtain ⟨A', hA'⟩ : L ∣ A := by
      have := pow_multiplicity_dvd L A
      rwa [← Nat.padicValNat_def, hvA, pow_one] at this
    have hLA' : ¬ L ∣ A' := by
      rintro ⟨c, hc⟩
      have := pow_succ_padicValNat_not_dvd (p := L) hA0
      rw [← Nat.padicValNat_def, hvA] at this
      exact this ⟨c, by rw [hA', hc]; ring⟩
    have hA'0 : A' ≠ 0 := by rintro rfl; exact hLA' (dvd_zero L)
    have hcop : Nat.Coprime B A' := by
      have hg : Nat.gcd B A' ∣ L := (Nat.gcd_dvd_gcd_of_dvd_right B ⟨L, by
        rw [hA']; ring⟩).trans hgBA
      rcases (Nat.dvd_prime hL).mp hg with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ Nat.gcd_dvd_right B A') hLA'
    have hcop2 : Nat.Coprime (B * L) A' :=
      Nat.Coprime.mul_left hcop ((Nat.Prime.coprime_iff_not_dvd hL).mpr hLA')
    have hA'ns : ∀ y, A' ≠ y ^ 2 := by
      intro y hy
      apply alternating_sum_ne_prime_mul_sq (y := y) hq4 hL hL2
      rw [← hAmul, hA', hy]
    have hCu2 : ∀ p, p.Prime → Odd ((B * L * A').factorization p) → p = u := by
      rw [show B * L * A' = B * A by rw [hA']; ring]; exact hCu'
    obtain ⟨⟨v, hv⟩, huA', w, hw⟩ := eiph_split (by positivity) hA'0 hcop2 hCu2 hA'ns
    have huA'd := eiph_dvd_of_odd huA'
    have huL : u ≠ L := fun he => hLA' (he ▸ huA'd)
    have huA : u ∣ A := huA'd.trans ⟨L, by rw [hA']; ring⟩
    obtain ⟨b, hb⟩ : L ∣ B := by
      have h2L : Nat.Coprime L 2 := (Nat.coprime_primes hL Nat.prime_two).mpr hL2
      exact h2L.dvd_of_dvd_mul_left (h2B ▸ hLq)
    obtain ⟨v', hv'⟩ : L ∣ v := hL.dvd_of_dvd_pow (n := 2) ⟨B, by rw [← hv]; ring⟩
    have hbv : b = v' ^ 2 := by
      have h3 : L ^ 2 * b = L ^ 2 * v' ^ 2 := by
        rw [← mul_pow, ← hv', ← hv, hb]; ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hL.pos 2) h3
    refine ⟨t, u, hset, htu, htH, huH, x, w, v', hx, htside, huL, hucong huA huL, Or.inr ?_⟩
    refine ⟨by rw [h2B, hb, hbv], ?_⟩
    rw [← hAmul, hA', hw]
  · -- `L ∤ q + 1`
    have hcop : Nat.Coprime B A := by
      rcases (Nat.dvd_prime hL).mp hgBA with h1 | h1
      · exact h1
      · exact absurd ((h1 ▸ Nat.gcd_dvd_left B A).trans ⟨2, by rw [h2B]; ring⟩) hLq
    obtain ⟨⟨z, hz⟩, huA, w, hw⟩ := eiph_split hB0 hA0 hcop hCu' hAns
    have huAd := eiph_dvd_of_odd huA
    have hLA : ¬ L ∣ A := by
      intro hd
      have := Fact.mk hL
      apply hLq
      have hz' : ((q ^ L + 1 : ℕ) : ZMod L) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (hd.trans ⟨q + 1, by rw [← hAmul]; ring⟩)
      push_cast at hz'
      rw [ZMod.pow_card] at hz'
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      exact hz'
    have huL : u ≠ L := fun he => hLA (he ▸ huAd)
    refine ⟨t, u, hset, htu, htH, huH, x, w, z, hx, htside, huL, hucong huAd huL, Or.inl ?_⟩
    exact ⟨by rw [h2B, hz], by rw [← hAmul, hw]⟩

end EulerIndexPairHigher

open EulerIndexPairHigher

/-- **The special row of an Euler index with exactly two prime factors, special exponent
above one.** Let `N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`
and `a ≠ 1`, and suppose the Euler index has exactly the two prime factors `r ≠ s`. Put
`L = (a + 1) / 2`. Then `L` is prime and the two primes can be named `t`, `u` so that both have
odd valuation in the index, `∑ i < L, q ^ i = t x ^ 2` with `t = L` or `t ≡ 1 (mod 2 L)`,
`u ≠ L`, `u ≡ 1 (mod 2 L)`, and either `q + 1 = 2 z ^ 2` and `q ^ L + 1 = (q + 1) u w ^ 2`, or
`q + 1 = 2 L z ^ 2` and `q ^ L + 1 = (q + 1) L u w ^ 2`. Restricted case (index with exactly two
prime factors, `a ≠ 1`); necessary conditions only, the case is not excluded; novelty not
verified. -/
theorem eulerIndex_pair_higher {N q a m r s : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (ha : a ≠ 1) (hrs : r ≠ s)
    (hJ : (eulerIndex q a m).primeFactors = {r, s}) :
    ((a + 1) / 2).Prime ∧ ∃ t u : ℕ, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      Odd ((eulerIndex q a m).factorization t) ∧ Odd ((eulerIndex q a m).factorization u) ∧
      ∃ x w z : ℕ, ∑ i ∈ Finset.range ((a + 1) / 2), q ^ i = t * x ^ 2 ∧
        (t = (a + 1) / 2 ∨ t % (2 * ((a + 1) / 2)) = 1) ∧
        u ≠ (a + 1) / 2 ∧ u % (2 * ((a + 1) / 2)) = 1 ∧
        ((q + 1 = 2 * z ^ 2 ∧ q ^ ((a + 1) / 2) + 1 = (q + 1) * (u * w ^ 2)) ∨
         (q + 1 = 2 * ((a + 1) / 2 * z ^ 2) ∧
           q ^ ((a + 1) / 2) + 1 = (q + 1) * ((a + 1) / 2 * (u * w ^ 2)))) := by
  obtain ⟨hq4, ha4⟩ := eiph_special_facts h hq hN hqm
  have hL : ((a + 1) / 2).Prime := prime_half_succ_of_eulerIndex_pair h hq hN hqm ha
    (by rw [hJ, Finset.card_pair_eq_two_iff.mpr hrs])
  refine ⟨hL, ?_⟩
  have hL3 : 3 ≤ (a + 1) / 2 := by omega
  have ha2 : a + 1 = (a + 1) / 2 + (a + 1) / 2 := by omega
  set L := (a + 1) / 2 with hLdef
  -- `J R C = m ^ 2`
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hqL4 : q ^ L % 4 = 1 := by rw [Nat.pow_mod, hq4]; simp
  have h2C : q ^ L + 1 = 2 * ((q ^ L + 1) / 2) := by omega
  have hsig : σ 1 (q ^ a) =
      2 * ((∑ i ∈ Finset.range L, q ^ i) * ((q ^ L + 1) / 2)) := by
    rw [sigma_one_apply_prime_pow hq, ha2, Finset.sum_range_add]
    have : ∑ i ∈ Finset.range L, q ^ (L + i) = q ^ L * ∑ i ∈ Finset.range L, q ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => pow_add q L i
    rw [this]
    calc ∑ i ∈ Finset.range L, q ^ i + q ^ L * ∑ i ∈ Finset.range L, q ^ i
        = (∑ i ∈ Finset.range L, q ^ i) * (q ^ L + 1) := by ring
      _ = (∑ i ∈ Finset.range L, q ^ i) * (2 * ((q ^ L + 1) / 2)) := by rw [← h2C]
      _ = _ := by ring
  have hprod := sigma_special_mul_eulerIndex h hq hN hqm
  rw [hsig] at hprod
  have he : eulerIndex q a m * ((∑ i ∈ Finset.range L, q ^ i) * ((q ^ L + 1) / 2)) = m ^ 2 := by
    have : 2 * (eulerIndex q a m * ((∑ i ∈ Finset.range L, q ^ i) * ((q ^ L + 1) / 2))) =
        2 * m ^ 2 := by rw [← hprod]; ring
    omega
  have hm2 : 0 < m ^ 2 := pow_pos (Nat.pos_of_ne_zero hm) 2
  have hJ0 : eulerIndex q a m ≠ 0 := by
    intro h0; rw [h0, zero_mul] at he; omega
  have hH0 : (∑ i ∈ Finset.range L, q ^ i) * ((q ^ L + 1) / 2) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at he; omega
  have hiff := fun t => eiph_odd_iff (t := t) hJ0 hH0 he
  have hH : ∀ p, p.Prime →
      Odd (((∑ i ∈ Finset.range L, q ^ i) * ((q ^ L + 1) / 2)).factorization p) →
        p = r ∨ p = s := by
    intro p _ ho
    have hmem := eiph_mem_of_odd ((hiff p).mpr ho)
    rw [hJ] at hmem
    simpa using hmem
  obtain ⟨t, u, hset, htu, hto, huo, rest⟩ := eiph_core hq hq4 hL hL3 hrs hH
  exact ⟨t, u, hset, htu, (hiff t).mpr hto, (hiff u).mpr huo, rest⟩

end OddPerfect

#print axioms OddPerfect.eulerIndex_pair_higher
