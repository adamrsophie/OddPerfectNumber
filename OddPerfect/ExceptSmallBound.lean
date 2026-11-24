import OddPerfect.ExceptSmallThree
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A small exceptional prime in an odd perfect number

Call a prime factor `p` of an odd perfect number `N` exceptional when its exponent is even and
at least `4`, and let `h` be the number of exceptional primes. Then some exceptional prime is
at most `max 331 (9 * h ^ 2)`. In particular, if `h ≤ 6`, some exceptional prime is at most
`331`.

Proof. The case `3 ∣ N` is `exceptSmall_three`. Suppose `3 ∤ N` and that every exceptional
prime exceeds `M = max 331 (9 * h ^ 2)`. Let `q` be the special prime. Then:

* every exact square prime `s` is `2` modulo `3`, so every prime factor of `s ^ 2 + s + 1` is
  `q` or exceptional;
* `q ≡ 1 (mod 3)`, `5 ∤ N`, every exact square prime is at least `11`, and `q ≥ 241`
  (the odd number `(q + 1) / 2` is `1` modulo `3` and its prime factors are `2` modulo `3`);
* the numbers `s ^ 2 + s + 1` are distinct and smooth over `D = {q} ∪ H`, where `H` is the set
  of exceptional primes, so a finite Euler product gives
  `1 + ∑ 1 / R(s ^ 2 + s + 1) ≤ ∏_{t ∈ D} (1 - 1 / ⌊√t⌋)⁻¹`, where `R(n)` is the product of
  `⌊√t⌋` over the prime factors `t` of `n` counted with multiplicity, so that `R(n) ^ 2 ≤ n`;
* `1 / (s - 1) ≤ (6 / 5) / R(s ^ 2 + s + 1)` for `s ≥ 11`;
* the Euler product is at most `(15 / 14) * exp (6 / 17) ≤ (15 / 14) * (17 / 16) ^ 6`.

With `2 < ∏ p / (p - 1) ≤ exp (∑ 1 / (p - 1))` this gives
`log 2 < 1 / 240 + 1 / 51 + (6 / 5) * ((15 / 14) * (17 / 16) ^ 6 - 1) < 0.6931471803`,
a contradiction.

This is a restricted result whose novelty was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- A finite Euler product bound: for weights `0 ≤ w t < 1` on a finite set `D` and a finite
set `T` of positive integers whose prime factors lie in `D`, the sum over `T` of the
completely multiplicative weights is at most `∏_{t ∈ D} (1 - w t)⁻¹`. -/
theorem exceptSmall_euler (D : Finset ℕ) (w : ℕ → ℝ) (hw0 : ∀ t ∈ D, 0 ≤ w t)
    (hw1 : ∀ t ∈ D, w t < 1) (T : Finset ℕ) (hT : ∀ n ∈ T, n ≠ 0 ∧ n.primeFactors ⊆ D) :
    ∑ n ∈ T, ∏ t ∈ D, w t ^ n.factorization t ≤ ∏ t ∈ D, (1 - w t)⁻¹ := by
  classical
  set K := T.sup id + 1
  let φ : ℕ → (D → ℕ) := fun n i => n.factorization i
  have hinj : Set.InjOn φ T := by
    intro n hn m hm hnm
    have hn' := hT n hn
    have hm' := hT m hm
    apply Nat.factorization_inj hn'.1 hm'.1
    ext t
    by_cases ht : t ∈ D
    · exact congrFun hnm ⟨t, ht⟩
    · have h1 : t ∉ n.primeFactors := fun h => ht (hn'.2 h)
      have h2 : t ∉ m.primeFactors := fun h => ht (hm'.2 h)
      rw [← Nat.support_factorization] at h1 h2
      rw [Finsupp.notMem_support_iff.mp h1, Finsupp.notMem_support_iff.mp h2]
  have hsub : T.image φ ⊆ Fintype.piFinset (fun _ : D => Finset.range K) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have hle : n ≤ T.sup id := Finset.le_sup (f := id) hn
    have := Nat.factorization_lt (i : ℕ) (hT n hn).1
    simp only [φ, K]
    omega
  calc ∑ n ∈ T, ∏ t ∈ D, w t ^ n.factorization t
      = ∑ n ∈ T, ∏ i : D, w i ^ φ n i := by
        refine Finset.sum_congr rfl fun n _ => ?_
        exact (Finset.prod_coe_sort D (fun t => w t ^ n.factorization t)).symm
    _ = ∑ x ∈ T.image φ, ∏ i : D, w i ^ x i :=
        (Finset.sum_image (f := fun x => ∏ i : D, w i ^ x i) hinj).symm
    _ ≤ ∑ x ∈ Fintype.piFinset (fun _ : D => Finset.range K), ∏ i : D, w i ^ x i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
          Finset.prod_nonneg fun i _ => pow_nonneg (hw0 i i.2) _
    _ = ∏ i : D, ∑ k ∈ Finset.range K, w i ^ k :=
        (Finset.prod_univ_sum (fun _ : D => Finset.range K) fun i k => w i ^ k).symm
    _ ≤ ∏ i : D, (1 - w i)⁻¹ := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finset.sum_nonneg fun k _ => pow_nonneg (hw0 i i.2) _
        · intro i _
          have := geom_sum_Ico_le_of_lt_one (m := 0) (n := K) (hw0 i i.2) (hw1 i i.2)
          rw [Finset.range_eq_Ico]
          simpa [div_eq_mul_inv] using this
    _ = ∏ t ∈ D, (1 - w t)⁻¹ := Finset.prod_coe_sort D (fun t => (1 - w t)⁻¹)

/-- The integer `R(n) = ∏_{t ∈ D} ⌊√t⌋ ^ v_t(n)` satisfies `R(n) ^ 2 ≤ n` when the prime
factors of `n` lie in `D`. -/
theorem exceptSmall_weight_sq_le {D : Finset ℕ} {n : ℕ} (hn : n ≠ 0)
    (hD : n.primeFactors ⊆ D) :
    (∏ t ∈ D, Nat.sqrt t ^ n.factorization t) ^ 2 ≤ n := by
  have hn' : n = ∏ t ∈ D, t ^ n.factorization t := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    exact Finsupp.prod_of_support_subset _ (by rwa [Nat.support_factorization]) _
      (fun _ _ => pow_zero _)
  calc (∏ t ∈ D, Nat.sqrt t ^ n.factorization t) ^ 2
      = ∏ t ∈ D, (Nat.sqrt t ^ 2) ^ n.factorization t := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun t _ => ?_
        ring
    _ ≤ ∏ t ∈ D, t ^ n.factorization t :=
        Finset.prod_le_prod' fun t _ => Nat.pow_le_pow_left (Nat.sqrt_le' t) _
    _ = n := hn'.symm

set_option maxHeartbeats 1000000 in
/-- Let `h` be the number of prime factors of an odd perfect number `N` whose exponent is even
and at least `4`. Then one of these primes is at most `max 331 (9 * h ^ 2)`. A restricted
result whose novelty was not verified. -/
theorem exceptSmall_bound {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, Even (N.factorization p) ∧ 4 ≤ N.factorization p ∧
      p ≤ max 331 (9 * (N.primeFactors.filter fun p =>
        Even (N.factorization p) ∧ 4 ≤ N.factorization p).card ^ 2) := by
  classical
  by_cases h3 : 3 ∣ N
  · obtain ⟨p, hp, he, h4, hle⟩ := exceptSmall_three h h3
    exact ⟨p, hp, he, h4, le_trans hle (le_max_left _ _)⟩
  set Hs := N.primeFactors.filter fun p => Even (N.factorization p) ∧ 4 ≤ N.factorization p
    with hHs
  set hh := Hs.card with hhh
  by_contra hne
  simp only [not_exists, not_and, not_le] at hne
  have hN0 := h.ne_zero
  obtain ⟨q, hq, hqN, hq4, hk, hev⟩ := exists_special_prime h
  have hqodd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
  have mem : ∀ p, p.Prime → p ∣ N → p ∈ N.primeFactors := fun p hp hpN =>
    Nat.mem_primeFactors.mpr ⟨hp, hpN, hN0⟩
  have big : ∀ u ∈ Hs, 331 < u ∧ 9 * hh ^ 2 < u := by
    intro u hu
    rw [hHs, Finset.mem_filter] at hu
    exact max_lt_iff.mp (hne u hu.1 hu.2.1 hu.2.2)
  have nonsp : ∀ p, p.Prime → p ∣ N → p ≠ q → N.factorization p = 2 ∨ p ∈ Hs := by
    intro p hp hpN hpq
    have he := hev p hp hpq
    have h1 := (hp.dvd_iff_one_le_factorization hN0).mp hpN
    by_cases h2 : N.factorization p = 2
    · exact Or.inl h2
    · right
      rw [hHs, Finset.mem_filter]
      refine ⟨mem p hp hpN, he, ?_⟩
      obtain ⟨j, hj⟩ := he
      omega
  have sq : ∀ p, p.Prime → p ∣ N → p ≠ q → p ≤ 331 → N.factorization p = 2 := by
    intro p hp hpN hpq hle
    rcases nonsp p hp hpN hpq with h2 | hH
    · exact h2
    · have := (big p hH).1
      omega
  have mod2 : ∀ s, s.Prime → N.factorization s = 2 → s % 3 = 2 := by
    intro s hs hv
    have hsN : s ∣ N := Nat.dvd_of_factorization_pos (by omega)
    have h0 : s % 3 ≠ 0 := by
      intro h0
      have : s = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
      exact h3 (this ▸ hsN)
    have h1 : s % 3 ≠ 1 := fun h1 => h3 (three_dvd_of_sq_mod_one h.perfect hs hv h1)
    omega
  have hq3 : q % 3 = 1 := by
    have h0 : q % 3 ≠ 0 := by
      intro h0
      have : q = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
      omega
    have h2 : q % 3 ≠ 2 := by
      intro h2
      exact h3 (prime_dvd_of_dvd_succ_special h hq hqodd Nat.prime_three (by norm_num)
        (by omega)).1
    omega
  have h5 : ¬ 5 ∣ N := by
    intro h5
    have v5 := sq 5 Nat.prime_five h5 (by omega) (by norm_num)
    have h31 : 31 ∣ N := OPNStarter.force_prime h.perfect Nat.prime_five v5 (by norm_num)
      (by norm_num) (by rw [sigma_prime_sq Nat.prime_five]; norm_num [phi3])
    have := mod2 31 (by norm_num) (sq 31 (by norm_num) h31 (by omega) (by norm_num))
    omega
  have s11 : ∀ s, s.Prime → N.factorization s = 2 → 11 ≤ s := by
    intro s hs hv
    have hsN : s ∣ N := Nat.dvd_of_factorization_pos (by omega)
    have hm := mod2 s hs hv
    have h2 : s ≠ 2 := by rintro rfl; exact h.not_two_dvd hsN
    have h5' : s ≠ 5 := by rintro rfl; exact h5 hsN
    by_contra hlt
    have : s = 8 := by omega
    subst this
    norm_num at hs
  have hq241 : 241 ≤ q := by
    by_contra hlt
    have hq2 := hq.two_le
    have hn : (q + 1) / 2 ∣ N := half_succ_dvd h hq hqodd
    have fac : ∀ r, r.Prime → r ∣ (q + 1) / 2 → r % 3 = 2 ∧ 11 ≤ r := by
      intro r hr hrn
      have hrle := Nat.le_of_dvd (by omega) hrn
      have hv := sq r hr (hrn.trans hn) (by omega) (by omega)
      exact ⟨mod2 r hr hv, s11 r hr hv⟩
    have hnp : ¬ ((q + 1) / 2).Prime := fun hp => by
      have := (fac _ hp dvd_rfl).1
      omega
    have hn1 : (q + 1) / 2 ≠ 1 := by omega
    set n := (q + 1) / 2 with hndef
    have ha := Nat.minFac_prime hn1
    have had := Nat.minFac_dvd n
    obtain ⟨b, hb⟩ := had
    have hb1 : b ≠ 1 := by
      rintro rfl
      rw [mul_one] at hb
      exact hnp (hb ▸ ha)
    obtain ⟨r, hr, hrb⟩ := Nat.exists_prime_and_dvd hb1
    have hb0 : b ≠ 0 := by rintro rfl; omega
    have hrn : r ∣ n := hb ▸ Dvd.dvd.mul_left hrb _
    have h11a := (fac _ ha (Nat.minFac_dvd n)).2
    have h11b := (fac r hr hrn).2
    have hrb' := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hrb
    have : 121 ≤ n := by rw [hb]; nlinarith
    omega
  have hqH : q ∉ Hs := by
    intro hqH
    rw [hHs, Finset.mem_filter] at hqH
    exact (Nat.not_even_iff_odd.mpr hqodd) hqH.2.1
  set Sq := N.primeFactors.filter fun p => N.factorization p = 2 with hSq
  have hSqmem : ∀ s ∈ Sq, s.Prime ∧ N.factorization s = 2 := by
    intro s hs
    rw [hSq, Finset.mem_filter] at hs
    exact ⟨Nat.prime_of_mem_primeFactors hs.1, hs.2⟩
  have hDsub : ∀ s ∈ Sq, (phi3 s).primeFactors ⊆ insert q Hs := by
    intro s hs r hr
    obtain ⟨hsp, hv⟩ := hSqmem s hs
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrd := Nat.dvd_of_mem_primeFactors hr
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr (phi3_odd s)) (even_iff_two_dvd.mpr hrd)
    have hrN : r ∣ N := OPNStarter.force_prime h.perfect hsp hv hrp hr2
      (by rw [sigma_prime_sq hsp]; exact hrd)
    have hr3 : r ≠ 3 := by rintro rfl; exact h3 hrN
    have hr1 := prime_dvd_phi3_mod_three hrp hr3 hrd
    by_cases hrq : r = q
    · exact hrq ▸ Finset.mem_insert_self _ _
    · rcases nonsp r hrp hrN hrq with h2 | hH
      · have := mod2 r hrp h2
        omega
      · exact Finset.mem_insert_of_mem hH
  -- the real analysis
  set D := insert q Hs with hD
  set w : ℕ → ℝ := fun t => ((Nat.sqrt t : ℕ) : ℝ)⁻¹ with hw
  have hsqq : 15 ≤ Nat.sqrt q := Nat.le_sqrt.mpr (by omega)
  have hsqH : ∀ u ∈ Hs, 18 ≤ Nat.sqrt u ∧ 3 * hh ≤ Nat.sqrt u := by
    intro u hu
    obtain ⟨h1, h2⟩ := big u hu
    exact ⟨Nat.le_sqrt.mpr (by omega), Nat.le_sqrt.mpr (by nlinarith)⟩
  have hsqD : ∀ t ∈ D, 2 ≤ Nat.sqrt t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · omega
    · have := (hsqH t ht).1
      omega
  have hw0 : ∀ t ∈ D, 0 ≤ w t := fun t _ => by positivity
  have hw1 : ∀ t ∈ D, w t < 1 := by
    intro t ht
    have h2 : (2 : ℝ) ≤ (Nat.sqrt t : ℝ) := by exact_mod_cast hsqD t ht
    simp only [hw]
    rw [inv_lt_one₀ (by linarith)]
    linarith
  set W : ℕ → ℝ := fun n => ∏ t ∈ D, w t ^ n.factorization t with hW
  set E := ∏ t ∈ D, (1 - w t)⁻¹ with hE
  -- the Euler product over `1` and the values `phi3 s`
  have hphi1 : ∀ s ∈ Sq, 1 < phi3 s := by
    intro s hs
    have := (hSqmem s hs).1.two_le
    unfold phi3
    nlinarith
  have heuler : 1 + ∑ s ∈ Sq, W (phi3 s) ≤ E := by
    have hT : ∀ n ∈ insert 1 (Sq.image phi3), n ≠ 0 ∧ n.primeFactors ⊆ D := by
      intro n hn
      rcases Finset.mem_insert.mp hn with rfl | hn
      · simp
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
        exact ⟨by have := hphi1 s hs; omega, hDsub s hs⟩
    have h1 : (1 : ℕ) ∉ Sq.image phi3 := by
      intro h1
      obtain ⟨s, hs, hs1⟩ := Finset.mem_image.mp h1
      have := hphi1 s hs
      omega
    have := exceptSmall_euler D w hw0 hw1 _ hT
    rw [Finset.sum_insert h1, Finset.sum_image (phi3_strictMono.injective.injOn)] at this
    simp only [Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, pow_zero,
      Finset.prod_const_one] at this
    exact this
  -- each exact square prime: `1 / (s - 1) ≤ (6 / 5) * W (phi3 s)`
  have hsq_term : ∀ s ∈ Sq, ((s : ℝ) - 1)⁻¹ ≤ 6 / 5 * W (phi3 s) := by
    intro s hs
    obtain ⟨hsp, hv⟩ := hSqmem s hs
    have h11 := s11 s hsp hv
    set P := ∏ t ∈ D, Nat.sqrt t ^ (phi3 s).factorization t with hP
    have hP2 : P ^ 2 ≤ phi3 s :=
      exceptSmall_weight_sq_le (by have := hphi1 s hs; omega) (hDsub s hs)
    have hP0 : 0 < P := Finset.prod_pos fun t ht => pow_pos (by have := hsqD t ht; omega) _
    have h25 : (5 * P) ^ 2 ≤ (6 * (s - 1)) ^ 2 := by
      have : 25 * phi3 s ≤ 36 * (s - 1) ^ 2 := by
        unfold phi3
        obtain ⟨k, rfl⟩ : ∃ k, s = k + 11 := ⟨s - 11, by omega⟩
        rw [show k + 11 - 1 = k + 10 by omega]
        ring_nf
        nlinarith
      nlinarith
    have h56 : 5 * P ≤ 6 * (s - 1) := (Nat.pow_le_pow_iff_left (by norm_num)).mp h25
    have hWP : W (phi3 s) = ((P : ℕ) : ℝ)⁻¹ := by
      show ∏ t ∈ D, w t ^ (phi3 s).factorization t = _
      rw [hP, Nat.cast_prod, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [Nat.cast_pow, inv_pow]
    rw [hWP]
    have hs1 : (1 : ℝ) < s := by exact_mod_cast (by omega : 1 < s)
    have hP' : (0 : ℝ) < P := by exact_mod_cast hP0
    have h56' : (5 : ℝ) * P ≤ 6 * ((s : ℝ) - 1) := by
      have : ((5 * P : ℕ) : ℝ) ≤ ((6 * (s - 1) : ℕ) : ℝ) := by exact_mod_cast h56
      push_cast [Nat.cast_sub (by omega : 1 ≤ s)] at this
      linarith
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    rw [show 6 / 5 * (P : ℝ)⁻¹ * ((s : ℝ) - 1) = (6 * ((s : ℝ) - 1)) / (5 * P) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith
  -- the Euler product is at most `(15 / 14) * (17 / 16) ^ 6`
  have hinv : ∀ r : ℕ, 2 ≤ r → (1 - ((r : ℕ) : ℝ)⁻¹)⁻¹ = 1 + ((r : ℝ) - 1)⁻¹ := by
    intro r hr
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have h1 : (r : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (r : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hEq : (1 - w q)⁻¹ ≤ 15 / 14 := by
    have h15 : (15 : ℝ) ≤ Nat.sqrt q := by exact_mod_cast hsqq
    simp only [hw]
    rw [hinv _ (by omega)]
    have : ((Nat.sqrt q : ℝ) - 1)⁻¹ ≤ 1 / 14 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hHsum : ∑ u ∈ Hs, ((Nat.sqrt u : ℝ) - 1)⁻¹ ≤ 6 / 17 := by
    rcases Nat.eq_zero_or_pos hh with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]
      norm_num
    · have hc : ∀ u ∈ Hs, ((Nat.sqrt u : ℝ) - 1)⁻¹ ≤ 6 / (17 * hh) := by
        intro u hu
        obtain ⟨h1, h2⟩ := hsqH u hu
        have hn : 17 * hh + 6 ≤ 6 * Nat.sqrt u := by omega
        have hn' : (17 : ℝ) * hh + 6 ≤ 6 * Nat.sqrt u := by exact_mod_cast hn
        have h18 : (18 : ℝ) ≤ Nat.sqrt u := by exact_mod_cast h1
        have hhp : (0 : ℝ) < hh := by exact_mod_cast hpos
        rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by positivity)]
        linarith
      calc ∑ u ∈ Hs, ((Nat.sqrt u : ℝ) - 1)⁻¹ ≤ Hs.card • (6 / (17 * (hh : ℝ))) :=
            Finset.sum_le_card_nsmul _ _ _ hc
        _ = 6 / 17 := by
            rw [nsmul_eq_mul, ← hhh]
            have hhp : (hh : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
            field_simp
  have hexp : Real.exp (6 / 17) ≤ (17 / 16) ^ 6 := by
    have h1 : Real.exp (1 / 17) ≤ 17 / 16 := by
      have := Real.add_one_le_exp (-(1 / 17))
      have hpos := Real.exp_pos (-(1 / 17))
      rw [show Real.exp (1 / 17) = (Real.exp (-(1 / 17)))⁻¹ by rw [Real.exp_neg, inv_inv]]
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith
    calc Real.exp (6 / 17) = Real.exp (1 / 17) ^ 6 := by
          rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (17 / 16) ^ 6 := pow_le_pow_left₀ (Real.exp_pos _).le h1 6
  have hEb : E ≤ 15 / 14 * (17 / 16) ^ 6 := by
    have hHprod : ∏ u ∈ Hs, (1 - w u)⁻¹ ≤ Real.exp (6 / 17) := by
      calc ∏ u ∈ Hs, (1 - w u)⁻¹ ≤ ∏ u ∈ Hs, Real.exp (((Nat.sqrt u : ℝ) - 1)⁻¹) := by
            apply Finset.prod_le_prod
            · intro u hu
              exact (inv_pos.mpr (sub_pos.mpr (hw1 u (Finset.mem_insert_of_mem hu)))).le
            · intro u hu
              simp only [hw]
              rw [hinv _ (by have := (hsqH u hu).1; omega), add_comm]
              exact Real.add_one_le_exp _
        _ = Real.exp (∑ u ∈ Hs, ((Nat.sqrt u : ℝ) - 1)⁻¹) := (Real.exp_sum _ _).symm
        _ ≤ Real.exp (6 / 17) := Real.exp_le_exp.mpr hHsum
    have hq0 : 0 ≤ (1 - w q)⁻¹ :=
      (inv_pos.mpr (sub_pos.mpr (hw1 q (Finset.mem_insert_self _ _)))).le
    rw [hE, hD, Finset.prod_insert hqH]
    calc (1 - w q)⁻¹ * ∏ u ∈ Hs, (1 - w u)⁻¹ ≤ 15 / 14 * Real.exp (6 / 17) :=
          mul_le_mul hEq hHprod (Finset.prod_nonneg fun u hu =>
            (inv_pos.mpr (sub_pos.mpr (hw1 u (Finset.mem_insert_of_mem hu)))).le) (by norm_num)
      _ ≤ 15 / 14 * (17 / 16) ^ 6 := by linarith
  -- the reciprocal sum over all prime factors
  set f : ℕ → ℝ := fun p => ((p : ℝ) - 1)⁻¹ with hf
  have hf0 : ∀ p ∈ N.primeFactors, 0 ≤ f p := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    simp only [hf]
    exact (inv_pos.mpr (by linarith)).le
  have hfq : f q ≤ 1 / 240 := by
    have : (241 : ℝ) ≤ q := by exact_mod_cast hq241
    simp only [hf]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hfH : ∑ u ∈ Hs, f u ≤ 1 / 51 := by
    rcases Nat.eq_zero_or_pos hh with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0]
      norm_num
    · have hc : ∀ u ∈ Hs, f u ≤ 1 / (51 * hh) := by
        intro u hu
        obtain ⟨h1, h2⟩ := big u hu
        have hn : 51 * hh + 1 ≤ u := by
          by_cases h6 : hh ≤ 6
          · omega
          · nlinarith
        have hn' : (51 : ℝ) * hh + 1 ≤ u := by exact_mod_cast hn
        have hhp : (0 : ℝ) < hh := by exact_mod_cast hpos
        simp only [hf]
        rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by positivity)]
        linarith
      calc ∑ u ∈ Hs, f u ≤ Hs.card • (1 / (51 * (hh : ℝ))) :=
            Finset.sum_le_card_nsmul _ _ _ hc
        _ = 1 / 51 := by
            rw [nsmul_eq_mul, ← hhh]
            have hhp : (hh : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
            field_simp
  have hfS : ∑ s ∈ Sq, f s ≤ 6 / 5 * (E - 1) := by
    calc ∑ s ∈ Sq, f s ≤ ∑ s ∈ Sq, 6 / 5 * W (phi3 s) := Finset.sum_le_sum hsq_term
      _ = 6 / 5 * ∑ s ∈ Sq, W (phi3 s) := (Finset.mul_sum _ _ _).symm
      _ ≤ 6 / 5 * (E - 1) := by linarith
  have hsplit : ∑ p ∈ N.primeFactors, f p ≤
      1 / 240 + 1 / 51 + 6 / 5 * (15 / 14 * (17 / 16) ^ 6 - 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors
      (fun p => N.factorization p = 2)]
    have hrest : ∑ p ∈ N.primeFactors.filter (fun p => ¬ N.factorization p = 2), f p ≤
        f q + ∑ u ∈ Hs, f u := by
      rw [← Finset.sum_insert hqH]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_filter] at hp
        have hpp := Nat.prime_of_mem_primeFactors hp.1
        have hpN := Nat.dvd_of_mem_primeFactors hp.1
        by_cases hpq : p = q
        · exact hpq ▸ Finset.mem_insert_self _ _
        · rcases nonsp p hpp hpN hpq with h2 | hH
          · exact absurd h2 hp.2
          · exact Finset.mem_insert_of_mem hH
      · intro p hp _
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact hf0 _ (mem _ hq hqN)
        · rw [hHs, Finset.mem_filter] at hp
          exact hf0 _ hp.1
    have : ∑ p ∈ N.primeFactors.filter (fun p => N.factorization p = 2), f p ≤
        6 / 5 * (15 / 14 * (17 / 16) ^ 6 - 1) := by
      rw [← hSq]
      linarith
    linarith
  -- abundancy
  have hN1 : 1 < N := by
    rcases Nat.lt_or_ge 1 N with h1 | h1
    · exact h1
    · have : N = 1 := by have := h.pos; omega
      have hs := h.sigma_eq
      rw [this] at hs
      simp at hs
  have hab : abundancy N = 2 := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  have hlt := abundancy_lt_prod hN1
  rw [hab] at hlt
  have hltR : (2 : ℝ) < ∏ p ∈ N.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    have := (Rat.cast_lt (K := ℝ)).mpr hlt
    push_cast at this
    exact this
  have hprod : ∏ p ∈ N.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ≤
      Real.exp (∑ p ∈ N.primeFactors, f p) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      exact div_nonneg (by linarith) (by linarith)
    · intro p hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have heq : (p : ℝ) / ((p : ℝ) - 1) = f p + 1 := by
        simp only [hf]
        field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
        ring
      rw [heq]
      exact Real.add_one_le_exp _
  have hlog : Real.log 2 < 1 / 240 + 1 / 51 + 6 / 5 * (15 / 14 * (17 / 16) ^ 6 - 1) := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    calc (2 : ℝ) < Real.exp (∑ p ∈ N.primeFactors, f p) := lt_of_lt_of_le hltR hprod
      _ ≤ _ := Real.exp_le_exp.mpr hsplit
  have := Real.log_two_gt_d9
  norm_num at hlog this
  linarith

/-- If an odd perfect number has at most six prime factors with even exponent at least `4`, then
one of them is at most `331`. A restricted result whose novelty was not verified. -/
theorem exceptSmall_bound_of_card_le_six {N : ℕ} (h : OddPerfect N)
    (h6 : (N.primeFactors.filter fun p =>
      Even (N.factorization p) ∧ 4 ≤ N.factorization p).card ≤ 6) :
    ∃ p ∈ N.primeFactors, Even (N.factorization p) ∧ 4 ≤ N.factorization p ∧ p ≤ 331 := by
  obtain ⟨p, hp, he, h4, hle⟩ := exceptSmall_bound h
  refine ⟨p, hp, he, h4, le_trans hle (max_le le_rfl ?_)⟩
  have := Nat.pow_le_pow_left h6 2
  omega

end OddPerfect

#print axioms OddPerfect.exceptSmall_euler
#print axioms OddPerfect.exceptSmall_weight_sq_le
#print axioms OddPerfect.exceptSmall_bound
#print axioms OddPerfect.exceptSmall_bound_of_card_le_six
