import OddPerfect.ExceptSmallTwoTail

/-!
# A small exceptional prime in an odd perfect number, with the constant `2`

Call a prime factor `p` of an odd perfect number `N` exceptional when its exponent is even and
at least `4`, and let `h` be the number of exceptional primes. Then some exceptional prime is
at most `max 331 (2 * h ^ 2)`. In particular, if `h ≤ 12`, some exceptional prime is at most
`331`. This sharpens the constant `9` of `exceptSmall_bound`. It holds for every odd perfect
number; it bounds the least exceptional prime in terms of the unknown count `h`, and no bound on
`h` follows from it.

Proof. The case `3 ∣ N` is `exceptSmall_three`. Suppose `3 ∤ N` and that every exceptional
prime exceeds `M = max 331 (2 * h ^ 2)`. Let `q` be the special prime, `H` the set of exceptional
primes and `S` the set of primes with exponent exactly `2`. Then `q ≡ 1 (mod 12)`, every
`s ∈ S` is `5` modulo `6`, every prime factor of `F(s) = s ^ 2 + s + 1` lies in `{q} ∪ H`, no
prime `r ≤ 331` other than `q` divides `F(s)`, hence `s ≥ 41`, and `q ≥ 673`. Split `S` by the
shape of `F(s)`:

* `F(s)` is a prime of `H`: at most `h` such `s`, all with `s ^ 2 + s + 1 > M`; their sum of
  `1 / (s - 1)` is at most `log (1 + 6 h / (d - 6)) / 6` (`exceptSmallTwo_ap`);
* `F(s)` is a product of two distinct primes of `H` (it is never a square): at most `C(h, 2)` such
  `s`, all with `s > M`; their sum is at most `log (5 / 2) / 6`;
* `q ∣ F(s)`: by the Euler product, their sum is at most `(41 / 40) (1 / 24) (1 - z) ^ (-h)`;
* `F(s)` has at least three prime factors in `H`: by `exceptSmallTwo_tail`, their sum is at most
  `(41 / 40) ((1 - z) ^ (-h) - 1 - h z - C(h + 1, 2) z ^ 2)`.

Here `z` bounds `1 / ⌊√t⌋` for `t ∈ H`. Adding `1 / (q - 1) ≤ 1 / 672` and `h / M` for the primes
of `H`, the total stays below `log 2` (`exceptSmallTwo_numeric`), against
`2 < ∏ p / (p - 1) ≤ exp (∑ 1 / (p - 1))`.

This is a restricted result whose novelty was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace OddPerfect

/-- `4 * C(h, 2) + 6 ≤ M` when `331 ≤ M` and `2 * h ^ 2 ≤ M`. -/
theorem exceptSmallTwo_choose_le (h M : ℕ) (hM1 : 331 ≤ M) (hM2 : 2 * h ^ 2 ≤ M) :
    4 * h.choose 2 + 6 ≤ M := by
  rw [Nat.choose_two_right]
  rcases Nat.lt_or_ge h 3 with hl | hl
  · interval_cases h <;> simp <;> omega
  · have h1 : h * (h - 1) / 2 * 2 ≤ h * (h - 1) := Nat.div_mul_le_self _ _
    have h2 : h * (h - 1) + 3 ≤ h ^ 2 := by
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 3 := ⟨h - 3, by omega⟩
      rw [show k + 3 - 1 = k + 2 by omega]
      ring_nf
      omega
    generalize h * (h - 1) / 2 = X at h1 ⊢
    generalize h * (h - 1) = Y at h1 h2
    generalize h ^ 2 = Z at h2 hM2
    omega

set_option maxHeartbeats 1000000 in
/-- Let `h` be the number of prime factors of an odd perfect number `N` whose exponent is even
and at least `4`. Then one of these primes is at most `max 331 (2 * h ^ 2)`. This holds for every
odd perfect number. It bounds the least such prime in terms of the unknown count `h`; no bound on
`h` follows from it. A restricted result whose novelty was not verified. -/
theorem exceptSmallTwo_bound {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, Even (N.factorization p) ∧ 4 ≤ N.factorization p ∧
      p ≤ max 331 (2 * (N.primeFactors.filter fun p =>
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
  set M := exceptSmallTwoM hh with hM
  have hM1 : 331 ≤ M := le_max_left _ _
  have hM2 : 2 * hh ^ 2 ≤ M := le_max_right _ _
  have big : ∀ u ∈ Hs, M < u := by
    intro u hu
    rw [hHs, Finset.mem_filter] at hu
    exact hne u hu.1 hu.2.1 hu.2.2
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
    · have := big p hH
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
  -- no prime `r ≤ 331` with `r ≡ 3 (mod 4)` divides `phi3 s` for an exact square prime `s`
  have nosmall : ∀ s r, s.Prime → N.factorization s = 2 → r.Prime → r ∣ phi3 s → r ≤ 331 →
      r % 4 = 3 → False := by
    intro s r hs hv hr hrd hr331 hr4
    have hr2 : r ≠ 2 := by rintro rfl; norm_num at hr4
    have hrN : r ∣ N := OPNStarter.force_prime h.perfect hs hv hr hr2
      (by rw [sigma_prime_sq hs]; exact hrd)
    have hr3 : r ≠ 3 := by rintro rfl; exact h3 hrN
    have hrq : r ≠ q := by rintro rfl; omega
    have h1 := mod2 r hr (sq r hr hrN hrq hr331)
    have h2 := prime_dvd_phi3_mod_three hr hr3 hrd
    omega
  have s41 : ∀ s, s.Prime → N.factorization s = 2 → 41 ≤ s ∧ s % 6 = 5 := by
    intro s hs hv
    have hsN : s ∣ N := Nat.dvd_of_factorization_pos (by omega)
    have hm := mod2 s hs hv
    have h2 : s ≠ 2 := by rintro rfl; exact h.not_two_dvd hsN
    have hodd : s % 2 = 1 := (hs.eq_two_or_odd).resolve_left h2
    refine ⟨?_, by omega⟩
    by_contra hlt
    have : s = 5 ∨ s = 11 ∨ s = 17 ∨ s = 23 ∨ s = 29 ∨ s = 35 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · exact nosmall 5 31 hs hv (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
    · exact nosmall 11 7 hs hv (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
    · exact nosmall 17 307 hs hv (by norm_num) (by norm_num [phi3]) (by norm_num)
        (by norm_num)
    · exact nosmall 23 7 hs hv (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
    · exact nosmall 29 67 hs hv (by norm_num) (by norm_num [phi3]) (by norm_num) (by norm_num)
    · norm_num at hs
  have hq673 : 673 ≤ q := by
    by_contra hlt
    have hq2 := hq.two_le
    have hq661 : q ≤ 661 := by omega
    have hn : (q + 1) / 2 ∣ N := half_succ_dvd h hq hqodd
    have fac : ∀ r, r.Prime → r ∣ (q + 1) / 2 → r % 3 = 2 ∧ 41 ≤ r := by
      intro r hr hrn
      have hrle := Nat.le_of_dvd (by omega) hrn
      have hv := sq r hr (hrn.trans hn) (by omega) (by omega)
      exact ⟨mod2 r hr hv, (s41 r hr hv).1⟩
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
    have h41a := (fac _ ha (Nat.minFac_dvd n)).2
    have h41b := (fac r hr hrn).2
    have hrb' := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hrb
    have : 1681 ≤ n := by rw [hb]; nlinarith
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
  have hphi1 : ∀ s ∈ Sq, 1 < phi3 s := by
    intro s hs
    have := (hSqmem s hs).1.two_le
    unfold phi3
    nlinarith
  -- the weights
  set D := insert q Hs with hD
  set w : ℕ → ℝ := fun t => ((Nat.sqrt t : ℕ) : ℝ)⁻¹ with hw
  have hsqq : 25 ≤ Nat.sqrt q := Nat.le_sqrt.mpr (by omega)
  have hsqH : ∀ u ∈ Hs, 18 ≤ Nat.sqrt u := fun u hu =>
    Nat.le_sqrt.mpr (by have := big u hu; omega)
  have hsqD : ∀ t ∈ D, 2 ≤ Nat.sqrt t := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · omega
    · have := hsqH t ht
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
  -- each exact square prime: `1 / (s - 1) ≤ (41 / 40) * W (phi3 s)`
  have hsq_term : ∀ s ∈ Sq, ((s : ℝ) - 1)⁻¹ ≤ 41 / 40 * W (phi3 s) := by
    intro s hs
    obtain ⟨hsp, hv⟩ := hSqmem s hs
    have h41 := (s41 s hsp hv).1
    set P := ∏ t ∈ D, Nat.sqrt t ^ (phi3 s).factorization t with hP
    have hP2 : P ^ 2 ≤ phi3 s :=
      exceptSmall_weight_sq_le (by have := hphi1 s hs; omega) (hDsub s hs)
    have hP0 : 0 < P := Finset.prod_pos fun t ht => pow_pos (by have := hsqD t ht; omega) _
    have hPs : P ≤ s := by
      by_contra hlt
      have : (s + 1) ^ 2 ≤ P ^ 2 := Nat.pow_le_pow_left (by omega) 2
      unfold phi3 at hP2
      nlinarith
    have h56 : 40 * P ≤ 41 * (s - 1) := by omega
    have hWP : W (phi3 s) = ((P : ℕ) : ℝ)⁻¹ := by
      show ∏ t ∈ D, w t ^ (phi3 s).factorization t = _
      rw [hP, Nat.cast_prod, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [Nat.cast_pow, inv_pow]
    rw [hWP]
    have hs1 : (1 : ℝ) < s := by exact_mod_cast (by omega : 1 < s)
    have hP' : (0 : ℝ) < P := by exact_mod_cast hP0
    have h56' : (40 : ℝ) * P ≤ 41 * ((s : ℝ) - 1) := by
      have : ((40 * P : ℕ) : ℝ) ≤ ((41 * (s - 1) : ℕ) : ℝ) := by exact_mod_cast h56
      push_cast [Nat.cast_sub (by omega : 1 ≤ s)] at this
      linarith
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    rw [show 41 / 40 * (P : ℝ)⁻¹ * ((s : ℝ) - 1) = (41 * ((s : ℝ) - 1)) / (40 * P) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith
  -- the numerical parameters
  obtain ⟨z, d1, hz0, hz1, hwz', hd7, hd1, hfinal⟩ := exceptSmallTwo_numeric hh
  have hwz : ∀ u ∈ Hs, w u ≤ z := fun u hu => hwz' u (big u hu)
  have hHw : ∀ t ∈ Hs, 0 ≤ w t ∧ w t ≤ z := fun t ht =>
    ⟨hw0 t (Finset.mem_insert_of_mem ht), hwz t ht⟩
  have hPz : ∏ t ∈ Hs, (1 - w t)⁻¹ ≤ ((1 - z) ^ hh)⁻¹ := exceptSmallTwo_prod_le hz1 w Hs hHw
  have hPz0 : 0 ≤ ((1 - z) ^ hh)⁻¹ := by
    have : 0 < 1 - z := by linarith
    positivity
  set f : ℕ → ℝ := fun p => ((p : ℝ) - 1)⁻¹ with hf
  -- the classes
  set S3a := Sq.filter fun s => q ∣ phi3 s with hS3a
  set S' := Sq.filter fun s => ¬ q ∣ phi3 s with hS'
  set S1 := S'.filter fun s => Ω (phi3 s) = 1 with hS1
  set S'' := S'.filter fun s => ¬ Ω (phi3 s) = 1 with hS''
  set S2 := S''.filter fun s => Ω (phi3 s) = 2 with hS2
  set S3 := S''.filter fun s => ¬ Ω (phi3 s) = 2 with hS3
  have hS'mem : ∀ s ∈ S', s ∈ Sq ∧ ¬ q ∣ phi3 s ∧ (phi3 s).primeFactors ⊆ Hs := by
    intro s hs
    rw [hS', Finset.mem_filter] at hs
    refine ⟨hs.1, hs.2, fun r hr => ?_⟩
    rcases Finset.mem_insert.mp (hDsub s hs.1 hr) with rfl | h'
    · exact absurd (Nat.dvd_of_mem_primeFactors hr) hs.2
    · exact h'
  have hsplit : ∑ s ∈ Sq, f s = ∑ s ∈ S3a, f s + (∑ s ∈ S1, f s + (∑ s ∈ S2, f s +
      ∑ s ∈ S3, f s)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Sq (fun s => q ∣ phi3 s),
      ← Finset.sum_filter_add_sum_filter_not S' (fun s => Ω (phi3 s) = 1),
      ← Finset.sum_filter_add_sum_filter_not S'' (fun s => Ω (phi3 s) = 2)]
  -- class 1: `phi3 s` is a prime of `Hs`
  have hc1 : ∑ s ∈ S1, f s ≤ Real.log (1 + 6 * hh / ((d1 : ℝ) - 6)) / 6 := by
    have hmem1 : ∀ s ∈ S1, s ∈ Sq ∧ phi3 s ∈ Hs := by
      intro s hs
      rw [hS1, Finset.mem_filter] at hs
      obtain ⟨hsq, -, hsub⟩ := hS'mem s hs.1
      have hp : (phi3 s).Prime := cardFactors_eq_one_iff_prime.mp hs.2
      exact ⟨hsq, hsub (Nat.mem_primeFactors.mpr ⟨hp, dvd_rfl, hp.ne_zero⟩)⟩
    have hap := exceptSmallTwo_ap d1 hd7 S1 (by
      intro s hs
      obtain ⟨hsq, hH⟩ := hmem1 s hs
      obtain ⟨hsp, hv⟩ := hSqmem s hsq
      have h41 := s41 s hsp hv
      exact ⟨hd1 s h41.1 (big _ hH), h41.2⟩)
    have hcard : S1.card ≤ hh := Finset.card_le_card_of_injOn phi3
      (fun s hs => (hmem1 s hs).2) (phi3_strictMono.injective.injOn)
    have hd7' : (7 : ℝ) ≤ d1 := by exact_mod_cast hd7
    have hcard' : (S1.card : ℝ) ≤ hh := by exact_mod_cast hcard
    have hlog : Real.log (1 + 6 * S1.card / ((d1 : ℝ) - 6)) ≤
        Real.log (1 + 6 * hh / ((d1 : ℝ) - 6)) := by
      have hnn : 0 ≤ 6 * (S1.card : ℝ) / ((d1 : ℝ) - 6) :=
        div_nonneg (by positivity) (by linarith)
      apply Real.log_le_log (by linarith)
      have : 6 * (S1.card : ℝ) / ((d1 : ℝ) - 6) ≤ 6 * hh / ((d1 : ℝ) - 6) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      linarith
    exact hap.trans (by linarith)
  -- class 2: `phi3 s` is a product of two distinct primes of `Hs`
  have hc2 : ∑ s ∈ S2, f s ≤ Real.log (5 / 2) / 6 := by
    have hmem2 : ∀ s ∈ S2, s ∈ Sq ∧ M + 1 ≤ s ∧
        phi3 s ∈ (Hs.powersetCard 2).image (fun T => T.prod id) := by
      intro s hs
      rw [hS2, Finset.mem_filter, hS'', Finset.mem_filter] at hs
      obtain ⟨hsq, -, hsub⟩ := hS'mem s hs.1.1
      have hn1 : phi3 s ≠ 1 := by have := hphi1 s hsq; omega
      set n := phi3 s with hn
      set p := n.minFac with hp_def
      have hp := Nat.minFac_prime hn1
      have hpn : p ∣ n := Nat.minFac_dvd n
      have hn0 : n ≠ 0 := by have := hphi1 s hsq; omega
      have hm0 : n / p ≠ 0 := by
        intro h0
        rcases Nat.div_eq_zero_iff.mp h0 with h | h
        · exact hp.ne_zero h
        · exact hn0 (Nat.eq_zero_of_dvd_of_lt hpn h)
      have hnm : n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
      have hΩ : Ω n = Ω p + Ω (n / p) := by
        conv_lhs => rw [hnm]
        exact cardFactors_mul hp.ne_zero hm0
      rw [cardFactors_apply_prime hp, hs.2] at hΩ
      have hmp : (n / p).Prime := cardFactors_eq_one_iff_prime.mp (by omega)
      have hpH : p ∈ Hs := hsub (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩)
      have hmH : n / p ∈ Hs := hsub (Nat.mem_primeFactors.mpr ⟨hmp, Nat.div_dvd_of_dvd hpn, hn0⟩)
      have hne' : p ≠ n / p := by
        intro heq
        have hpp : p * p = n := by
          conv_rhs => rw [hnm]
          rw [← heq]
        have hsq2 : p * p = s ^ 2 + s + 1 := by rw [hpp, hn]; rfl
        have hs2 := (hSqmem s hsq).1.two_le
        rcases Nat.lt_or_ge p (s + 1) with hl | hl
        · have : p * p ≤ s * s := Nat.mul_le_mul (by omega) (by omega)
          nlinarith
        · have : (s + 1) * (s + 1) ≤ p * p := Nat.mul_le_mul hl hl
          nlinarith
      refine ⟨hsq, ?_, ?_⟩
      · have h1 := big p hpH
        have h2 := big _ hmH
        have : (M + 1) * (M + 1) ≤ n := by
          rw [hnm]
          exact Nat.mul_le_mul h1 h2
        have : phi3 M < phi3 s := by
          show M ^ 2 + M + 1 < n
          nlinarith
        have := phi3_strictMono.lt_iff_lt.mp this
        omega
      · rw [Finset.mem_image]
        refine ⟨{p, n / p}, Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hne'⟩, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hpH
          · rw [Finset.mem_singleton.mp hx]
            exact hmH
        · rw [Finset.prod_pair hne']
          exact hnm.symm
    have hap := exceptSmallTwo_ap M (by omega) S2 (by
      intro s hs
      obtain ⟨hsq, hsM, -⟩ := hmem2 s hs
      obtain ⟨hsp, hv⟩ := hSqmem s hsq
      exact ⟨hsM, (s41 s hsp hv).2⟩)
    have hcard : S2.card ≤ hh.choose 2 := by
      calc S2.card ≤ ((Hs.powersetCard 2).image (fun T => T.prod id)).card :=
            Finset.card_le_card_of_injOn phi3 (fun s hs => (hmem2 s hs).2.2)
              (phi3_strictMono.injective.injOn)
        _ ≤ (Hs.powersetCard 2).card := Finset.card_image_le
        _ = hh.choose 2 := Finset.card_powersetCard _ _
    have hch := exceptSmallTwo_choose_le hh M hM1 hM2
    have hX : 1 + 6 * (S2.card : ℝ) / ((M : ℝ) - 6) ≤ 5 / 2 := by
      have hc' : (4 : ℝ) * S2.card + 6 ≤ M := by
        have : 4 * S2.card + 6 ≤ M := by omega
        exact_mod_cast this
      have hM331 : (331 : ℝ) ≤ M := by exact_mod_cast hM1
      have hM6 : (0 : ℝ) < (M : ℝ) - 6 := by linarith
      rw [← sub_nonneg, show (5 : ℝ) / 2 - (1 + 6 * (S2.card : ℝ) / ((M : ℝ) - 6)) =
        ((3 / 2) * ((M : ℝ) - 6) - 6 * S2.card) / ((M : ℝ) - 6) by field_simp; ring]
      apply div_nonneg _ hM6.le
      linarith
    have hM7 : (7 : ℝ) ≤ M := by exact_mod_cast (by omega : 7 ≤ M)
    have hnn : 0 ≤ 6 * (S2.card : ℝ) / ((M : ℝ) - 6) :=
      div_nonneg (by positivity) (by linarith)
    have hlog := Real.log_le_log (by linarith) hX
    exact hap.trans (by linarith)
  -- class 3a: `q ∣ phi3 s`
  have hc3a : ∑ s ∈ S3a, f s ≤ 41 / 40 * (((1 - z) ^ hh)⁻¹ / 24) := by
    have hmem : ∀ s ∈ S3a, s ∈ Sq ∧ q ∣ phi3 s := fun s hs => Finset.mem_filter.mp hs
    have hinj : Set.InjOn (fun s => phi3 s / q) S3a := by
      intro s hs s' hs' hss
      have := (Nat.div_left_inj (hmem s hs).2 (hmem s' hs').2).mp hss
      exact phi3_strictMono.injective this
    have hm0 : ∀ s ∈ S3a, phi3 s / q ≠ 0 := by
      intro s hs h0
      obtain ⟨hsq, hqd⟩ := hmem s hs
      rcases Nat.div_eq_zero_iff.mp h0 with h' | h'
      · exact hq.ne_zero h'
      · have := hphi1 s hsq
        exact absurd (Nat.eq_zero_of_dvd_of_lt hqd h') (by omega)
    have hWq : ∀ s ∈ S3a, W (phi3 s) = w q * W (phi3 s / q) := by
      intro s hs
      show ∏ t ∈ D, w t ^ (phi3 s).factorization t = w q * ∏ t ∈ D, w t ^ _
      conv_lhs => rw [← Nat.mul_div_cancel' (hmem s hs).2]
      exact exceptSmallTwo_weight_mul D w hq (Finset.mem_insert_self _ _) (hm0 s hs)
    have heuler : ∑ m ∈ S3a.image (fun s => phi3 s / q), W m ≤ E := by
      apply exceptSmall_euler D w hw0 hw1
      intro m hm
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hm
      refine ⟨hm0 s hs, ?_⟩
      have := hphi1 s (hmem s hs).1
      exact (Nat.primeFactors_mono (Nat.div_dvd_of_dvd (hmem s hs).2) (by omega)).trans
        (hDsub s (hmem s hs).1)
    have hEb : E ≤ (1 - w q)⁻¹ * ((1 - z) ^ hh)⁻¹ := by
      rw [hE, hD, Finset.prod_insert hqH]
      have hq0 : 0 ≤ (1 - w q)⁻¹ :=
        (inv_pos.mpr (sub_pos.mpr (hw1 q (Finset.mem_insert_self _ _)))).le
      exact mul_le_mul_of_nonneg_left hPz hq0
    have hwq : w q ≤ 1 / 25 := by
      have : (25 : ℝ) ≤ Nat.sqrt q := by exact_mod_cast hsqq
      simp only [hw]
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hwq0 : 0 ≤ w q := hw0 q (Finset.mem_insert_self _ _)
    have hwq24 : w q * (1 - w q)⁻¹ ≤ 1 / 24 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
      linarith
    have hS0 : 0 ≤ ∑ m ∈ S3a.image (fun s => phi3 s / q), W m :=
      Finset.sum_nonneg fun m _ => Finset.prod_nonneg fun t ht => pow_nonneg (hw0 t ht) _
    calc ∑ s ∈ S3a, f s ≤ ∑ s ∈ S3a, 41 / 40 * W (phi3 s) :=
          Finset.sum_le_sum fun s hs => hsq_term s (hmem s hs).1
      _ = 41 / 40 * (w q * ∑ m ∈ S3a.image (fun s => phi3 s / q), W m) := by
          rw [Finset.sum_image hinj, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s hs => ?_
          rw [hWq s hs]
      _ ≤ 41 / 40 * (w q * E) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left heuler hwq0
      _ ≤ 41 / 40 * (w q * ((1 - w q)⁻¹ * ((1 - z) ^ hh)⁻¹)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hEb hwq0
      _ = 41 / 40 * ((w q * (1 - w q)⁻¹) * ((1 - z) ^ hh)⁻¹) := by ring
      _ ≤ 41 / 40 * ((1 / 24) * ((1 - z) ^ hh)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hwq24 hPz0
      _ = 41 / 40 * (((1 - z) ^ hh)⁻¹ / 24) := by ring
  -- class 3b: at least three prime factors in `Hs`
  have hc3 : ∑ s ∈ S3, f s ≤ 41 / 40 * exceptSmallTwoTau z hh 3 := by
    have hmem : ∀ s ∈ S3, s ∈ Sq ∧ ¬ q ∣ phi3 s ∧ (phi3 s).primeFactors ⊆ Hs ∧
        3 ≤ Ω (phi3 s) := by
      intro s hs
      rw [hS3, Finset.mem_filter, hS'', Finset.mem_filter] at hs
      obtain ⟨hsq, hqd, hsub⟩ := hS'mem s hs.1.1
      have h0 : Ω (phi3 s) ≠ 0 := by
        intro h0
        rcases cardFactors_eq_zero_iff_eq_zero_or_one.mp h0 with h' | h' <;>
          · have := hphi1 s hsq
            omega
      exact ⟨hsq, hqd, hsub, by omega⟩
    have hWH : ∀ s ∈ S3, W (phi3 s) = ∏ t ∈ Hs, w t ^ (phi3 s).factorization t := by
      intro s hs
      show ∏ t ∈ D, w t ^ (phi3 s).factorization t = _
      rw [hD, Finset.prod_insert hqH, Nat.factorization_eq_zero_of_not_dvd (hmem s hs).2.1,
        pow_zero, one_mul]
    have htail := exceptSmallTwo_tail hz0 hz1 w Hs
      (fun t ht => ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp ht).1, hHw t ht⟩)
      3 le_rfl (S3.image phi3) (by
        intro n hn
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
        obtain ⟨hsq, -, hsub, h3'⟩ := hmem s hs
        exact ⟨by have := hphi1 s hsq; omega, hsub, h3'⟩)
    calc ∑ s ∈ S3, f s ≤ ∑ s ∈ S3, 41 / 40 * W (phi3 s) :=
          Finset.sum_le_sum fun s hs => hsq_term s (hmem s hs).1
      _ = 41 / 40 * ∑ n ∈ S3.image phi3, ∏ t ∈ Hs, w t ^ n.factorization t := by
          rw [Finset.sum_image (phi3_strictMono.injective.injOn), Finset.mul_sum]
          refine Finset.sum_congr rfl fun s hs => ?_
          rw [hWH s hs]
      _ ≤ 41 / 40 * exceptSmallTwoTau z hh 3 :=
          mul_le_mul_of_nonneg_left htail (by norm_num)
  -- the reciprocal sum over all prime factors
  have hf0 : ∀ p ∈ N.primeFactors, 0 ≤ f p := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    simp only [hf]
    exact (inv_pos.mpr (by linarith)).le
  have hfq : f q ≤ 1 / 672 := by
    have : (673 : ℝ) ≤ q := by exact_mod_cast hq673
    simp only [hf]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hfH : ∑ u ∈ Hs, f u ≤ hh / (M : ℝ) := by
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hc : ∀ u ∈ Hs, f u ≤ 1 / (M : ℝ) := by
      intro u hu
      have hu' : (M : ℝ) + 1 ≤ u := by exact_mod_cast (big u hu)
      simp only [hf]
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hM0]
      linarith
    calc ∑ u ∈ Hs, f u ≤ Hs.card • (1 / (M : ℝ)) := Finset.sum_le_card_nsmul _ _ _ hc
      _ = hh / (M : ℝ) := by rw [nsmul_eq_mul, ← hhh]; ring
  have hsum : ∑ p ∈ N.primeFactors, f p ≤ f q + ∑ u ∈ Hs, f u + ∑ s ∈ Sq, f s := by
    rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors
      (fun p => N.factorization p = 2), add_comm]
    apply add_le_add _ (le_of_eq rfl)
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
  have hlog : Real.log 2 < ∑ p ∈ N.primeFactors, f p := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    exact lt_of_lt_of_le hltR hprod
  linarith

/-- If an odd perfect number has at most twelve prime factors with even exponent at least `4`,
then one of them is at most `331`. This holds for every odd perfect number; no bound on the
number of such primes follows from it. A restricted result whose novelty was not verified. -/
theorem exceptSmallTwo_bound_of_card_le_twelve {N : ℕ} (h : OddPerfect N)
    (h12 : (N.primeFactors.filter fun p =>
      Even (N.factorization p) ∧ 4 ≤ N.factorization p).card ≤ 12) :
    ∃ p ∈ N.primeFactors, Even (N.factorization p) ∧ 4 ≤ N.factorization p ∧ p ≤ 331 := by
  obtain ⟨p, hp, he, h4, hle⟩ := exceptSmallTwo_bound h
  refine ⟨p, hp, he, h4, le_trans hle (max_le le_rfl ?_)⟩
  have := Nat.pow_le_pow_left h12 2
  omega

end OddPerfect

#print axioms OddPerfect.exceptSmallTwo_choose_le
#print axioms OddPerfect.exceptSmallTwo_bound
#print axioms OddPerfect.exceptSmallTwo_bound_of_card_le_twelve
