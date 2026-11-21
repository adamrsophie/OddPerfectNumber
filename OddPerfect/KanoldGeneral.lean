import OddPerfect.EqualExponents
import OddPerfect.Zsigmondy
import OddPerfect.Abundancy

/-!
# Kanold's theorem on common divisors of the ordinary exponents plus one

Let `N` be an odd perfect number with special prime `q`. Call a prime factor `p ≠ q`
ordinary and write `e_p = v_p(N)`. Kanold (1941): if `t` divides `e_p + 1` for every
ordinary `p`, then `t ^ 4 ∣ N`. This file proves it in full.

* `dvd_of_dvd_succ`: if an odd prime `l` divides every `e_p + 1`, then `l ∣ N`. If not,
  every `Φ_l(p) = 1 + p + ... + p ^ (l - 1)` with `p` ordinary is a power of `q`
  (`sigma_pred_prime_eq_special_pow`). The growth lemma `lt_of_geom_eq_pow` then shows
  that for ordinary primes `p < p'` one has `Φ_l(p) < p'`: modulo `M = Φ_l(p) = q ^ c`
  both `p` and `p'` are `l`-th roots of unity, the unit group of `ZMod (q ^ c)` is cyclic and
  `p` has order `l`, so `p' ≡ p ^ j (mod M)` with `j < l`, and `p' < M` would give
  `p' = p ^ j`. So the ordinary primes grow faster than squaring and
  `σ(N) / N < (5 / 4) (3 / 2) (121 / 120) < 2` (for `l ≥ 5`; `l = 3` is McDaniel's theorem).
  This avoids the Diophantine statement that `Φ_l(r)` is not a square (Ljunggren), on which
  the reduction `exists_isSquare_sigma_of_not_dvd` relied.
* `pow_four_mul_dvd`: if `l ^ a` divides every `e_p + 1`, then `l ^ (4 a) ∣ N`. If `l` is
  ordinary, `v_l(N) = e_l ≥ l ^ a - 1`. If `l = q`, the primitive prime factors of
  `Φ_{q ^ j}(r)` (`1 ≤ j ≤ a`) for one ordinary `r ≡ 1 (mod q)` give `a + 1` prime factors
  `≡ 1 (mod q)`, each contributing at least `a` to `v_q(N)`; then `v_q(N) ≥ a (a + 1)` and
  `v_q(N) ≡ 1 (mod 4)` finish.
* `pow_four_dvd_of_dvd_succ`: the composite form `t ^ 4 ∣ N`.
* Easy parts of Yamada's `t ^ 5` (arXiv 2312.17059): `pow_five_mul_dvd_of_special` and
  `pow_five_mul_dvd_of_ordinary`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## The growth lemma -/

/-- Growth of primes whose `Φ_l` values are powers of one odd prime. Let `l` be a prime,
`q` an odd prime, and `p < p'` primes with `p' ≠ q` such that `1 + p + ... + p ^ (l - 1)`
and `1 + p' + ... + p' ^ (l - 1)` are both powers of `q`. Then
`1 + p + ... + p ^ (l - 1) < p'`. -/
theorem lt_of_geom_eq_pow {l q p p' c c' : ℕ} (hl : l.Prime) (hq : q.Prime) (hq2 : q ≠ 2)
    (hp : p.Prime) (hp' : p'.Prime) (hpp' : p < p') (hp'q : p' ≠ q)
    (hc : ∑ i ∈ Finset.range l, p ^ i = q ^ c) (hc' : ∑ i ∈ Finset.range l, p' ^ i = q ^ c') :
    ∑ i ∈ Finset.range l, p ^ i < p' := by
  have hl2 := hl.two_le
  -- `p ^ j < Φ_l(p)` for `j < l`
  have hpj : ∀ j < l, p ^ j < ∑ i ∈ Finset.range l, p ^ i := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · calc p ^ 0 < p ^ 0 + p ^ 1 := by have := hp.pos; simp; omega
        _ = ∑ i ∈ ({0, 1} : Finset ℕ), p ^ i := by simp
        _ ≤ _ := Finset.sum_le_sum_of_subset (by
              intro i; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range]
              omega)
    · calc p ^ j < p ^ 0 + p ^ j := by simp
        _ = ∑ i ∈ ({0, j} : Finset ℕ), p ^ i := by rw [Finset.sum_pair (by omega)]
        _ ≤ _ := Finset.sum_le_sum_of_subset (by
              intro i; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range]
              omega)
  have hmono : ∑ i ∈ Finset.range l, p ^ i ≤ ∑ i ∈ Finset.range l, p' ^ i :=
    Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left hpp'.le i
  have hpM : p < q ^ c := by rw [← hc]; simpa using hpj 1 (by omega)
  have hpjM : ∀ j < l, p ^ j < q ^ c := fun j hj => hc ▸ hpj j hj
  rw [hc] at hmono ⊢
  rw [hc'] at hmono
  by_contra hle
  push Not at hle
  have hlt : p' < q ^ c := by
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have hc0 : c ≠ 0 := by rintro rfl; rw [pow_zero] at h; exact hp'.one_lt.ne' h
      have hqd : q ∣ p' := h ▸ dvd_pow_self q hc0
      exact hp'q ((Nat.prime_dvd_prime_iff_eq hq hp').mp hqd).symm
  have hcc : c ≤ c' := (Nat.pow_le_pow_iff_right hq.one_lt).mp hmono
  set M := q ^ c with hM
  have hM0 : M ≠ 0 := by omega
  have : NeZero M := ⟨hM0⟩
  -- `p ^ l = 1` and `p' ^ l = 1` in `ZMod M`
  have key : ∀ x : ℕ, M ∣ ∑ i ∈ Finset.range l, x ^ i → (x : ZMod M) ^ l = 1 := by
    intro x hx
    have h0 : ((∑ i ∈ Finset.range l, x ^ i : ℕ) : ZMod M) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hx
    have := geom_sum_mul (x : ZMod M) l
    push_cast at h0
    rw [h0, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  have hu := key p (hc ▸ dvd_rfl)
  have hv := key p' (hc' ▸ pow_dvd_pow q hcc)
  set u := (IsUnit.of_pow_eq_one hu (by omega)).unit with hu_def
  set v := (IsUnit.of_pow_eq_one hv (by omega)).unit with hv_def
  have hul : u ^ l = 1 := Units.ext (by simp [hu_def, hu])
  have hvl : v ^ l = 1 := Units.ext (by simp [hv_def, hv])
  have hu1 : u ≠ 1 := by
    intro h1
    have h2 : ((p : ℕ) : ZMod M) = ((1 : ℕ) : ZMod M) := by
      have := congrArg Units.val h1
      simpa [hu_def] using this
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hpM, Nat.mod_eq_of_lt (by omega)] at h2
    exact hp.one_lt.ne' h2
  have : Fact l.Prime := ⟨hl⟩
  have hou : orderOf u = l := orderOf_eq_prime hul hu1
  -- the `l`-th roots of unity are the powers of `u`
  classical
  have : IsCyclic (ZMod M)ˣ := ZMod.isCyclic_units_of_prime_pow q hq hq2 c
  have hsub : (Finset.range l).image (fun j => u ^ j) ⊆
      Finset.univ.filter (fun a : (ZMod M)ˣ => a ^ l = 1) := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← pow_mul, mul_comm, pow_mul, hul, one_pow]
  have hcard : ((Finset.range l).image fun j => u ^ j).card = l := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (x := u) (by rw [hou]; simpa using hi)
      (by rw [hou]; simpa using hj) hij
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [hcard]; exact IsCyclic.card_pow_eq_one_le (by omega))
  have hvmem : v ∈ (Finset.range l).image fun j => u ^ j := by
    rw [heq]; simp [hvl]
  obtain ⟨j, hj, hvj⟩ := Finset.mem_image.mp hvmem
  have hcast : ((p' : ℕ) : ZMod M) = ((p ^ j : ℕ) : ZMod M) := by
    have := congrArg Units.val hvj
    push_cast
    simpa [hu_def, hv_def] using this.symm
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hlt,
    Nat.mod_eq_of_lt (hpjM j (Finset.mem_range.mp hj))] at hcast
  rcases j with _ | _ | j
  · rw [pow_zero] at hcast; exact hp'.one_lt.ne' hcast
  · rw [pow_one] at hcast; omega
  · have hpd : p ∣ p' := hcast ▸ dvd_pow_self p (by omega)
    have := (Nat.prime_dvd_prime_iff_eq hp hp').mp hpd
    omega

/-! ## A telescoping product bound -/

/-- `x / (x - 1) ≤ m / (m - 1)` for natural numbers `2 ≤ m ≤ x`. -/
private theorem div_pred_le {m x : ℕ} (hm : 2 ≤ m) (hx : m ≤ x) :
    (x : ℚ) / (x - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hx' : (m : ℚ) ≤ x := by exact_mod_cast hx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- If every element of a finite set of naturals is at least `B ≥ 3` and `x < y` in the set
implies `(x - 1) ^ 2 + 1 ≤ y`, then `∏ x / (x - 1) ≤ (B - 1) / (B - 2)`. -/
private theorem prod_le_of_chain (S : Finset ℕ) : ∀ B : ℕ, 3 ≤ B → (∀ x ∈ S, B ≤ x) →
    (∀ x ∈ S, ∀ y ∈ S, x < y → (x - 1) * (x - 1) + 1 ≤ y) →
    ∏ x ∈ S, ((x : ℚ) / (x - 1)) ≤ ((B : ℚ) - 1) / ((B : ℚ) - 2) := by
  induction S using Finset.induction_on_min with
  | empty =>
    intro B hB _ _
    have : (3 : ℚ) ≤ B := by exact_mod_cast hB
    rw [Finset.prod_empty, le_div_iff₀ (by linarith)]
    linarith
  | insert a s ha ih =>
    intro B hB hmin hchain
    have haB := hmin a (Finset.mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.prod_insert has]
    obtain ⟨u, rfl⟩ : ∃ u, a = u + 1 := ⟨a - 1, by omega⟩
    have h1 := ih (u * u + 1) (by nlinarith)
      (fun y hy => by
        have := hchain (u + 1) (Finset.mem_insert_self _ s) y (Finset.mem_insert_of_mem hy)
          (ha y hy)
        simpa using this)
      (fun x hx y hy hxy => hchain x (Finset.mem_insert_of_mem hx) y
        (Finset.mem_insert_of_mem hy) hxy)
    have hu : (2 : ℚ) ≤ u := by exact_mod_cast (by omega : 2 ≤ u)
    have huB : (B : ℚ) ≤ u + 1 := by exact_mod_cast haB
    have hB' : (3 : ℚ) ≤ B := by exact_mod_cast hB
    have hnn : (0 : ℚ) ≤ ((u + 1 : ℕ) : ℚ) / (((u + 1 : ℕ) : ℚ) - 1) := by
      push_cast; exact div_nonneg (by linarith) (by linarith)
    have key : ((u + 1 : ℕ) : ℚ) / (((u + 1 : ℕ) : ℚ) - 1) *
        ((((u * u + 1 : ℕ) : ℚ) - 1) / (((u * u + 1 : ℕ) : ℚ) - 2)) ≤
        ((B : ℚ) - 1) / ((B : ℚ) - 2) := by
      push_cast
      rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith) (by linarith)]
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℚ) ≤ u) (by linarith : (0 : ℚ) ≤ u + 1))
        (by linarith : (0 : ℚ) ≤ u + 1 - B)]
    exact (mul_le_mul_of_nonneg_left h1 hnn).trans key

/-! ## Kanold's divisibility `l ∣ N` -/

/-- An odd perfect number has an ordinary prime factor. -/
theorem exists_ordinary_prime {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : ∃ p ∈ N.primeFactors, p ≠ q := by
  by_contra hc
  push Not at hc
  exact not_all_components_special_powers h hq hodd fun p hp hpq => absurd (hc p hp) hpq

/-- Kanold's divisibility. Let `N` be an odd perfect number with special prime `q` and `l` an
odd prime with `l ∣ e + 1` for every ordinary exponent `e`. Then `l ∣ N`. -/
theorem dvd_of_dvd_succ {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) : l ∣ N := by
  by_cases hl3 : l = 3
  · subst hl3; exact three_dvd_of_three_dvd_succ h hq hodd hexp
  have hl4 : l ≠ 4 := by rintro rfl; norm_num at hl
  have hl5 : 5 ≤ l := by have := hl.two_le; omega
  by_contra hlN
  have hN0 := h.ne_zero
  have hq4 := (mod_four_special h hq hodd).1
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hq2 : q ≠ 2 := by omega
  have h3 : ∀ p ∈ N.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : p ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
    have := hpp.two_le
    omega
  set O := N.primeFactors.erase q with hO
  have hΦ : ∀ p ∈ O, ∃ c, ∑ i ∈ Finset.range l, p ^ i = q ^ c := by
    intro p hp
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    obtain ⟨c, -, hc⟩ := sigma_pred_prime_eq_special_pow h hq hodd hl hl2 hlN hexp hpN hpq
    rw [sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hpN),
      Nat.sub_add_cancel hl.one_lt.le] at hc
    exact ⟨c, hc⟩
  have hgrow : ∀ p ∈ O, ∀ p' ∈ O, p < p' → ∑ i ∈ Finset.range l, p ^ i < p' := by
    intro p hp p' hp' hlt
    obtain ⟨c, hc⟩ := hΦ p hp
    obtain ⟨c', hc'⟩ := hΦ p' hp'
    exact lt_of_geom_eq_pow hl hq hq2 (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp))
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp')) hlt
      (Finset.ne_of_mem_erase hp') hc hc'
  have hge : ∀ x : ℕ, 1 + x + x ^ 2 + x ^ 3 + x ^ 4 ≤ ∑ i ∈ Finset.range l, x ^ i := by
    intro x
    calc 1 + x + x ^ 2 + x ^ 3 + x ^ 4 = ∑ i ∈ Finset.range 5, x ^ i := by
          simp [Finset.sum_range_succ]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hl5)
  obtain ⟨p₀, hp₀, hp₀q⟩ := exists_ordinary_prime h hq hodd
  have hOne : O.Nonempty := ⟨p₀, Finset.mem_erase.mpr ⟨hp₀q, hp₀⟩⟩
  set p₁ := O.min' hOne with hp₁
  have hp₁O : p₁ ∈ O := O.min'_mem hOne
  have hp₁3 : 3 ≤ p₁ := h3 p₁ (Finset.mem_of_mem_erase hp₁O)
  set rest := O.erase p₁ with hrest
  have hqmem : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos (by
      obtain ⟨k, hk⟩ := hodd; omega), hN0⟩
  have hN1 : 1 < N := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) (Nat.dvd_of_mem_primeFactors hqmem)
    omega
  apply not_perfect_of_prod_le_two hN1 _ h.perfect
  rw [← Finset.mul_prod_erase _ _ hqmem, ← hO, ← Finset.mul_prod_erase _ _ hp₁O, ← hrest]
  have hrestO : ∀ x ∈ rest, p₁ < x ∧ x ∈ O := by
    intro x hx
    obtain ⟨hx1, hxO⟩ := Finset.mem_erase.mp hx
    exact ⟨lt_of_le_of_ne (O.min'_le x hxO) (Ne.symm hx1), hxO⟩
  have b1 : (q : ℚ) / (q - 1) ≤ 5 / 4 := by
    have := div_pred_le (m := 5) (x := q) (by norm_num) hq5
    norm_num at this ⊢; linarith
  have b2 : (p₁ : ℚ) / (p₁ - 1) ≤ 3 / 2 := by
    have := div_pred_le (m := 3) (x := p₁) (by norm_num) hp₁3
    norm_num at this ⊢; linarith
  have b3 : ∏ x ∈ rest, ((x : ℚ) / (x - 1)) ≤ 121 / 120 := by
    have := prod_le_of_chain rest 122 (by norm_num)
      (fun x hx => by
        obtain ⟨hlt, hxO⟩ := hrestO x hx
        have h1 := hgrow p₁ hp₁O x hxO hlt
        have h2 := hge p₁
        have : 121 ≤ 1 + p₁ + p₁ ^ 2 + p₁ ^ 3 + p₁ ^ 4 := by
          have h9 : 9 ≤ p₁ ^ 2 := by nlinarith
          have h27 : 27 ≤ p₁ ^ 3 := by nlinarith
          have h81 : 81 ≤ p₁ ^ 4 := by nlinarith
          omega
        omega)
      (fun x hx y hy hxy => by
        have h1 := hgrow x (hrestO x hx).2 y (hrestO y hy).2 hxy
        have h2 := hge x
        obtain ⟨w, rfl⟩ : ∃ w, x = w + 1 := ⟨x - 1, by have := (hrestO x hx).1; omega⟩
        simp only [Nat.add_sub_cancel]
        nlinarith)
    rwa [show (((122 : ℕ) : ℚ) - 1) / (((122 : ℕ) : ℚ) - 2) = 121 / 120 by norm_num] at this
  have hnn : ∀ x ∈ N.primeFactors, (0 : ℚ) ≤ (x : ℚ) / (x - 1) := by
    intro x hx
    have : (3 : ℚ) ≤ x := by exact_mod_cast h3 x hx
    exact div_nonneg (by linarith) (by linarith)
  have hrest0 : (0 : ℚ) ≤ ∏ x ∈ rest, ((x : ℚ) / (x - 1)) :=
    Finset.prod_nonneg fun x hx =>
      hnn x (Finset.mem_of_mem_erase (hrestO x hx).2)
  calc (q : ℚ) / (q - 1) * ((p₁ : ℚ) / (p₁ - 1) * ∏ x ∈ rest, ((x : ℚ) / (x - 1)))
      ≤ 5 / 4 * (3 / 2 * (121 / 120)) :=
        mul_le_mul b1 (mul_le_mul b2 b3 hrest0 (by norm_num))
          (mul_nonneg (hnn p₁ (Finset.mem_of_mem_erase hp₁O)) hrest0) (by norm_num)
    _ ≤ 2 := by norm_num

/-! ## The size of `v_l(N)` -/

/-- Bernoulli: `k a + 1 ≤ (k + 1) ^ a`. -/
private theorem bernoulli (k a : ℕ) : k * a + 1 ≤ (k + 1) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 : 1 ≤ (k + 1) ^ a := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_left k h1]

/-- The counting engine at the special prime. If `q ^ a ∣ e + 1` for every ordinary exponent
`e`, then at least `a + 1` prime factors of `N` are `≡ 1 (mod q)`, each contributing at
least `a` to `v_q(N)`; hence `a (a + 1) ≤ v_q(N)`. -/
theorem mul_succ_le_factorization_special {N q a : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → q ^ a ∣ N.factorization p + 1) :
    a * (a + 1) ≤ N.factorization q := by
  have : Fact q.Prime := ⟨hq⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have hq4 := (mod_four_special h hq hodd).1
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hq2 : q ≠ 2 := by omega
  -- one ordinary prime `r₀ ≡ 1 (mod q)`
  obtain ⟨p, hp, hpq⟩ := exists_ordinary_prime h hq hodd
  obtain ⟨r₀, hr₀N, -, hr₀⟩ := exists_primeFactor_modEq_one h hp (d := q) (by omega)
    ((dvd_pow_self q ha.ne').trans (hexp p hp hpq))
  have hr₀q : r₀ ≠ q := by rintro rfl; rw [Nat.mod_self] at hr₀; omega
  -- primitive prime factors of `Φ_{q ^ j}(r₀)`
  have hj : ∀ j ∈ Finset.Icc 1 a, ∃ s ∈ N.primeFactors,
      orderOf (r₀ : ZMod s) = q ^ j ∧ s % q ^ j = 1 := by
    intro j hj
    obtain ⟨hj1, hja⟩ := Finset.mem_Icc.mp hj
    exact exists_primeFactor_modEq_one h hr₀N
      (le_trans (by omega) (Nat.le_self_pow (by omega) q))
      ((pow_dvd_pow q hja).trans (hexp r₀ hr₀N hr₀q))
  choose! f hfN hfo hfm using hj
  set S := N.primeFactors.filter (fun p => p % q = 1) with hS
  have hfS : ∀ j ∈ Finset.Icc 1 a, f j % q = 1 := by
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    have := Nat.mod_mod_of_dvd (f j) (dvd_pow_self q (by omega : j ≠ 0))
    rw [hfm j hj, Nat.mod_eq_of_lt (by omega)] at this
    exact this.symm
  have hsub : insert r₀ ((Finset.Icc 1 a).image f) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨hr₀N, hr₀⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨hfN j hj, hfS j hj⟩
  have hinj : Set.InjOn f (Finset.Icc 1 a : Set ℕ) := by
    intro i hi j hj hij
    have := hfo i hi
    rw [hij, hfo j hj] at this
    exact Nat.pow_right_injective (by omega) this.symm
  have hnot : r₀ ∉ (Finset.Icc 1 a).image f := by
    intro hx
    have : Fact r₀.Prime := ⟨Nat.prime_of_mem_primeFactors hr₀N⟩
    obtain ⟨j, hj, hfj⟩ := Finset.mem_image.mp hx
    have := hfo j hj
    rw [hfj, ZMod.natCast_self, orderOf_zero] at this
    exact (pow_ne_zero j (by omega : q ≠ 0)) this.symm
  have hcard : a + 1 ≤ S.card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj,
      Nat.card_Icc, Nat.add_sub_cancel] at this
  have hsum : S.card • a ≤ ∑ p ∈ S, padicValNat q (N.factorization p + 1) := by
    refine Finset.card_nsmul_le_sum S _ a fun p hp => ?_
    obtain ⟨hpN, hp1⟩ := Finset.mem_filter.mp hp
    have hpq : p ≠ q := by rintro rfl; rw [Nat.mod_self] at hp1; omega
    exact (padicValNat_dvd_iff_le (by omega)).mp (hexp p hpN hpq)
  have := sum_padicValNat_succ_le h.perfect hq hq2
  rw [smul_eq_mul] at hsum
  calc a * (a + 1) ≤ S.card * a := by rw [mul_comm]; exact Nat.mul_le_mul_right a hcard
    _ ≤ _ := hsum.trans this

/-- If a prime `l ∣ N` is ordinary and `l ^ a ∣ e + 1` for every ordinary exponent `e`,
then `l ^ a ≤ v_l(N) + 1`. -/
theorem pow_le_factorization_succ_of_ordinary {N q l a : ℕ} (h : OddPerfect N)
    (hl : l.Prime) (hlN : l ∣ N) (hlq : l ≠ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → l ^ a ∣ N.factorization p + 1) :
    l ^ a ≤ N.factorization l + 1 :=
  Nat.le_of_dvd (by omega) (hexp l (Nat.mem_primeFactors.mpr ⟨hl, hlN, h.ne_zero⟩) hlq)

/-- Kanold's `l ^ (4 a) ∣ N`, prime power form, given `l ∣ N`. Let `N` be an odd perfect
number with special prime `q`, `l` an odd prime dividing `N`, and suppose `l ^ a ∣ e + 1` for
every ordinary exponent `e`. Then `l ^ (4 a) ∣ N`. -/
theorem pow_four_mul_dvd_of_dvd {N q l a : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) (hlN : l ∣ N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → l ^ a ∣ N.factorization p + 1) :
    l ^ (4 * a) ∣ N := by
  rw [hl.pow_dvd_iff_le_factorization h.ne_zero]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  by_cases hlq : l = q
  · subst hlq
    have h1 := mul_succ_le_factorization_special h hq hodd hexp
    have h4 := (mod_four_special h hq hodd).2
    by_cases ha3 : 3 ≤ a
    · nlinarith
    · interval_cases a <;> omega
  · have h1 := pow_le_factorization_succ_of_ordinary h hl hlN hlq hexp
    by_cases hl3 : l = 3
    · subst hl3
      exact (mcdaniel h hq hodd fun p hp hpq => by
        have := (dvd_pow_self 3 ha.ne').trans (hexp p hp hpq); omega).elim
    · have hl4 : l ≠ 4 := by rintro rfl; norm_num at hl
      have hl5 : 5 ≤ l := by have := hl.two_le; omega
      have h2 : 4 * a + 1 ≤ 5 ^ a := bernoulli 4 a
      have h3 : 5 ^ a ≤ l ^ a := Nat.pow_le_pow_left hl5 a
      omega

/-- Kanold's theorem, prime power form. Let `N` be an odd perfect number with special prime
`q` and `l` an odd prime with `l ^ a ∣ e + 1` for every ordinary exponent `e`. Then
`l ^ (4 a) ∣ N`. -/
theorem pow_four_mul_dvd {N q l a : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → l ^ a ∣ N.factorization p + 1) :
    l ^ (4 * a) ∣ N := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  exact pow_four_mul_dvd_of_dvd h hq hodd hl hl2
    (dvd_of_dvd_succ h hq hodd hl hl2 fun p hp hpq =>
      (dvd_pow_self l ha.ne').trans (hexp p hp hpq)) hexp

/-- No ordinary exponent plus one is even, so `2 ∤ t` whenever `t` divides all of them. -/
private theorem not_two_dvd_of_dvd_succ {N q t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → t ∣ N.factorization p + 1) : ¬ 2 ∣ t := by
  intro h2
  obtain ⟨p, hp, hpq⟩ := exists_ordinary_prime h hq hodd
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd (Nat.prime_of_mem_primeFactors hp) hpq
  have := h2.trans (hexp p hp hpq)
  omega

/-- Kanold's theorem (1941). If `t ∣ e + 1` for every ordinary exponent `e` of the odd
perfect number `N` with special prime `q`, then `t ^ 4 ∣ N`. -/
theorem pow_four_dvd_of_dvd_succ {N q t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → t ∣ N.factorization p + 1) : t ^ 4 ∣ N := by
  have hN0 := h.ne_zero
  have ht0 : t ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp, hpq⟩ := exists_ordinary_prime h hq hodd
    have := hexp p hp hpq
    simp at this
  have ht2 := not_two_dvd_of_dvd_succ h hq hodd hexp
  refine (Nat.factorization_prime_le_iff_dvd (pow_ne_zero 4 ht0) hN0).mp fun l hl => ?_
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos (t.factorization l) with h0 | hpos
  · simp [h0]
  have hlt : l ∣ t := Nat.dvd_of_factorization_pos hpos.ne'
  have hl2 : l ≠ 2 := fun h2 => ht2 (h2 ▸ hlt)
  have := pow_four_mul_dvd h hq hodd hl hl2 (a := t.factorization l)
    fun p hp hpq => (Nat.ordProj_dvd t l).trans (hexp p hp hpq)
  exact (hl.pow_dvd_iff_le_factorization hN0).mp this

/-! ## Easy cases of Yamada's fifth power -/

/-- Yamada's `q ^ (5 a) ∣ N` at the special prime, for `a ≠ 2, 3`: if `q ^ a ∣ e + 1` for
every ordinary exponent `e`, then `q ^ (5 a) ∣ N`. -/
theorem pow_five_mul_dvd_of_special {N q a : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (ha2 : a ≠ 2) (ha3 : a ≠ 3)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → q ^ a ∣ N.factorization p + 1) :
    q ^ (5 * a) ∣ N := by
  rw [hq.pow_dvd_iff_le_factorization h.ne_zero]
  have h1 := mul_succ_le_factorization_special h hq hodd hexp
  have h4 := (mod_four_special h hq hodd).2
  by_cases ha4 : 4 ≤ a
  · nlinarith
  · interval_cases a <;> omega

/-- Yamada's `l ^ (5 a) ∣ N` for an odd prime `l ≠ q`, when `l ≥ 7` or `a ≥ 2`: if
`l ^ a ∣ e + 1` for every ordinary exponent `e`, then `l ^ (5 a) ∣ N`. -/
theorem pow_five_mul_dvd_of_ordinary {N q l a : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) (hlq : l ≠ q)
    (hla : 7 ≤ l ∨ 2 ≤ a)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → l ^ a ∣ N.factorization p + 1) :
    l ^ (5 * a) ∣ N := by
  rw [hl.pow_dvd_iff_le_factorization h.ne_zero]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have hlN := dvd_of_dvd_succ h hq hodd hl hl2 fun p hp hpq =>
    (dvd_pow_self l ha.ne').trans (hexp p hp hpq)
  have h1 := pow_le_factorization_succ_of_ordinary h hl hlN hlq hexp
  by_cases hl3 : l = 3
  · subst hl3
    exact (mcdaniel h hq hodd fun p hp hpq => by
      have := (dvd_pow_self 3 ha.ne').trans (hexp p hp hpq); omega).elim
  have hl4 : l ≠ 4 := by rintro rfl; norm_num at hl
  have hl5 : 5 ≤ l := by have := hl.two_le; omega
  rcases hla with hl7 | ha2
  · have h2 : 6 * a + 1 ≤ 7 ^ a := bernoulli 6 a
    have h3 : 7 ^ a ≤ l ^ a := Nat.pow_le_pow_left hl7 a
    omega
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have h2 : 4 * b + 1 ≤ 5 ^ b := bernoulli 4 b
    have h3 : 5 ^ (b + 1) ≤ l ^ (b + 1) := Nat.pow_le_pow_left hl5 _
    rw [pow_succ] at h3
    omega

end OddPerfect

#print axioms OddPerfect.lt_of_geom_eq_pow
#print axioms OddPerfect.exists_ordinary_prime
#print axioms OddPerfect.dvd_of_dvd_succ
#print axioms OddPerfect.mul_succ_le_factorization_special
#print axioms OddPerfect.pow_le_factorization_succ_of_ordinary
#print axioms OddPerfect.pow_four_mul_dvd_of_dvd
#print axioms OddPerfect.pow_four_mul_dvd
#print axioms OddPerfect.pow_four_dvd_of_dvd_succ
#print axioms OddPerfect.pow_five_mul_dvd_of_special
#print axioms OddPerfect.pow_five_mul_dvd_of_ordinary
