import OddPerfect.Euler
import OddPerfect.Network
import OddPerfect.Cyclotomic

/-!
# Closed loops through the special prime

If every component divisor sum `σ(p ^ v_p(N))` with `p ≠ q` of an odd perfect number `N`
is a power of the special prime `q`, then conservation of exponents, lifting the exponent,
and a size comparison give a contradiction. Corollaries: the Dandapat, Hunsucker, and
Pomerance result `σ(m ^ 2) ≠ q ^ k`, and the Dris type bound `3 q ^ k < 2 m ^ 2`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private lemma cube_le_five_pow (n : ℕ) : n ^ 3 ≤ 5 ^ n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> norm_num
  · induction n, h using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have : (n + 1) ^ 3 ≤ 5 * n ^ 3 := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        ring_nf
        nlinarith [Nat.zero_le (m ^ 3), Nat.zero_le (m ^ 2)]
      calc (n + 1) ^ 3 ≤ 5 * n ^ 3 := this
        _ ≤ 5 * 5 ^ n := by omega
        _ = 5 ^ (n + 1) := by ring

private lemma one_add_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → ℕ)
    (ht : ∀ i ∈ s, 1 ≤ t i) : 1 + ∑ i ∈ s, (t i - 1) ≤ ∏ i ∈ s, t i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ih' := ih fun i hi => ht i (Finset.mem_insert_of_mem hi)
    obtain ⟨u, hu⟩ : ∃ u, t a = u + 1 := ⟨t a - 1, by have := ht a (Finset.mem_insert_self a s); omega⟩
    rw [hu]
    have hP : 1 ≤ ∏ i ∈ s, t i := by omega
    simp only [Nat.add_sub_cancel]
    nlinarith

private lemma prod_pow_dvd (s : Finset ℕ) (a : ℕ → ℕ) {n : ℕ} (h1 : ∀ r ∈ s, r.Prime)
    (h2 : ∀ r ∈ s, r ^ a r ∣ n) : ∏ r ∈ s, r ^ a r ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert r s hrs ih =>
    rw [Finset.prod_insert hrs]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (h2 r (Finset.mem_insert_self r s))
      (ih (fun x hx => h1 x (Finset.mem_insert_of_mem hx))
        (fun x hx => h2 x (Finset.mem_insert_of_mem hx)))
    refine Nat.Coprime.prod_right fun x hx => ?_
    exact Nat.coprime_pow_primes _ _ (h1 r (Finset.mem_insert_self r s))
      (h1 x (Finset.mem_insert_of_mem hx)) (by rintro rfl; exact hrs hx)

/-- `σ(p ^ (e + 1)) = 1 + p * σ(p ^ e)`. -/
private lemma sigma_pow_succ {p : ℕ} (hp : p.Prime) (e : ℕ) :
    σ 1 (p ^ (e + 1)) = 1 + p * σ 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
    Finset.mul_sum, pow_zero, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma not_dvd_sigma {p : ℕ} (hp : p.Prime) (e : ℕ) : ¬ p ∣ σ 1 (p ^ e) := by
  cases e with
  | zero => simpa using hp.one_lt.ne'
  | succ e =>
    rw [sigma_pow_succ hp]
    intro h
    exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left (dvd_mul_right p _)).mp h))

/-- Step d: lifting the exponent. -/
private lemma pow_pred_dvd_succ {p q e c k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (he : 1 ≤ e) (hc : σ 1 (p ^ e) = q ^ c) (hdvd : p ^ e ∣ σ 1 (q ^ k)) :
    p ^ (e - 1) ∣ k + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  set s := σ 1 (p ^ e')
  have hQ : q ^ c = 1 + p * s := by rw [← hc, sigma_pow_succ hp]
  have hs0 : s ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'
  have hps : ¬ p ∣ s := not_dvd_sigma hp e'
  have hQ1 : 1 < q ^ c := by rw [hQ]; have := Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hs0); omega
  have hvQ : padicValNat p (q ^ c - 1) = 1 := by
    rw [hQ, Nat.add_sub_cancel_left, padicValNat.mul hp.ne_zero hs0, padicValNat_self,
      padicValNat.eq_zero_of_not_dvd hps]
  have hlte := padicValNat.pow_sub_pow (p := p) (x := q ^ c) (y := 1) (hp.odd_of_ne_two hp2) hQ1
    (by rw [hQ, Nat.add_sub_cancel_left]; exact dvd_mul_right p s)
    (by rw [hQ]; intro h; exact hp.one_lt.ne' (Nat.dvd_one.mp
      ((Nat.dvd_add_left (dvd_mul_right p s)).mp h)))
    (n := k + 1) (by omega)
  rw [one_pow, hvQ] at hlte
  have hne : (q ^ c) ^ (k + 1) - 1 ≠ 0 := by
    have := Nat.one_lt_pow (n := k + 1) (by omega) hQ1; omega
  have hd : p ^ (e' + 1) ∣ (q ^ c) ^ (k + 1) - 1 := by
    refine hdvd.trans ((Dvd.intro _ (sigma_prime_pow_mul_pred hq k)).trans ?_)
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one _ _
  have hle := (padicValNat_dvd_iff_le hne).mp hd
  rw [hlte] at hle
  exact (padicValNat_dvd_iff_le (by omega)).mpr (by omega)

/-- Step g: the exponent of `q` is below `p ^ (e - 1)`. -/
private lemma exp_lt {p q e c : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (he : 2 ≤ e)
    (hc : σ 1 (p ^ e) = q ^ c) : c < p ^ (e - 1) := by
  set t := p ^ (e - 1)
  have hpt : p ≤ t := Nat.le_self_pow (by omega) p
  have h1 := sigma_prime_pow_mul_pred hp e
  have h2 : σ 1 (p ^ e) < p ^ (e + 1) := by
    have := Nat.le_mul_of_pos_right (σ 1 (p ^ e)) (show 0 < p - 1 by omega)
    have : 0 < p ^ (e + 1) := pow_pos hp.pos _
    omega
  have h3 : p ^ (e + 1) = t * p ^ 2 := by rw [← pow_add]; congr 1; omega
  have h4 : t * p ^ 2 ≤ t ^ 3 := by
    have := Nat.pow_le_pow_left hpt 2
    calc t * p ^ 2 ≤ t * t ^ 2 := Nat.mul_le_mul_left _ this
      _ = t ^ 3 := by ring
  have h5 : q ^ c < q ^ t := by
    calc q ^ c < p ^ (e + 1) := hc ▸ h2
      _ ≤ 5 ^ t := by rw [h3]; exact h4.trans (cube_le_five_pow t)
      _ ≤ q ^ t := Nat.pow_le_pow_left hq5 t
  exact (Nat.pow_lt_pow_iff_right (by omega)).mp h5

/-- In an odd perfect number, the divisor sums of the components other than the one with
odd exponent cannot all be powers of that special prime. -/
theorem not_all_components_special_powers {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hpow : ∀ p ∈ N.primeFactors, p ≠ q → ∃ c : ℕ, σ 1 (p ^ N.factorization p) = q ^ c) :
    False := by
  classical
  have hN0 := h.ne_zero
  -- a. `q` is the special prime
  obtain ⟨q', -, -, hq4, -, hev⟩ := exists_special_prime h
  have hqq : q = q' := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (hev q hq hne)
  subst hqq
  choose! c hc using hpow
  set k := N.factorization q with hk
  set S := N.primeFactors.erase q with hS
  have hq2 : q ≠ 2 := by omega
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by rw [← hk]; exact hodd.pos.ne')
  -- facts about the other primes
  have hfact : ∀ r ∈ S, r.Prime ∧ r ≠ q ∧ r ∈ N.primeFactors ∧ 3 ≤ r ∧ 2 ≤ N.factorization r := by
    intro r hr
    obtain ⟨hrq, hrN⟩ := Finset.mem_erase.mp hr
    have hrp := Nat.prime_of_mem_primeFactors hrN
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hrN)
    have hpos : N.factorization r ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hrN
    obtain ⟨j, hj⟩ := hev r hrp hrq
    refine ⟨hrp, hrq, hrN, ?_, by omega⟩
    have := hrp.two_le; omega
  have hσq : σ 1 (q ^ k) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
  have hweight : ∀ b ∈ N.primeFactors, b ≠ q → ∀ r, r ≠ q → sigmaWeight N b r = 0 := by
    intro b hb hbq r hrq
    unfold sigmaWeight
    rw [hc b hb hbq, Nat.factorization_pow, hq.factorization]
    simp [Ne.symm hrq]
  -- b, c, d. `r ^ (e_r - 1) ∣ k + 1`
  have hdvd : ∀ r ∈ S, r ^ (N.factorization r - 1) ∣ k + 1 := by
    intro r hr
    obtain ⟨hrp, hrq, hrN, hr3, he2⟩ := hfact r hr
    have hbal := sigmaWeight_sum_eq h.perfect hrp (by omega)
    rw [Finset.sum_eq_single q (fun b hb hbq => hweight b hb hbq r hrq)
      (fun hn => absurd hqmem hn)] at hbal
    have hd : r ^ N.factorization r ∣ σ 1 (q ^ k) :=
      (hrp.pow_dvd_iff_le_factorization hσq).mpr (le_of_eq hbal.symm)
    exact pow_pred_dvd_succ hrp (by omega) hq (by omega) (hc r hrN hrq) hd
  -- e. `2 * ∏ t_r ∣ k + 1`
  set t : ℕ → ℕ := fun r => r ^ (N.factorization r - 1) with ht
  have h2P : 2 * ∏ r ∈ S, t r ∣ k + 1 := by
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (even_iff_two_dvd.mp hodd.add_one)
      (prod_pow_dvd S _ (fun r hr => (hfact r hr).1) hdvd)
    refine Nat.Coprime.prod_right fun r hr => Nat.Coprime.pow_right _ ?_
    obtain ⟨hrp, -, -, hr3, -⟩ := hfact r hr
    exact (Nat.coprime_primes Nat.prime_two hrp).mpr (by omega)
  -- f. `k = ∑ c_r`
  have hksum : k = ∑ r ∈ S, c r := by
    have hbal := sigmaWeight_sum_eq h.perfect hq hq2
    rw [← Finset.add_sum_erase _ _ hqmem, sigmaWeight_self hq, zero_add] at hbal
    rw [hk, ← hbal]
    refine Finset.sum_congr rfl fun r hr => ?_
    obtain ⟨-, hrq, hrN, -, -⟩ := hfact r hr
    unfold sigmaWeight
    rw [hc r hrN hrq, Nat.factorization_pow, hq.factorization]
    simp
  -- g. `c_r < t_r`
  have hlt : ∀ r ∈ S, c r < t r := by
    intro r hr
    obtain ⟨hrp, hrq, hrN, hr3, he2⟩ := hfact r hr
    exact exp_lt hrp hr3 hq5 he2 (hc r hrN hrq)
  -- h. contradiction
  have hle : k ≤ ∑ r ∈ S, (t r - 1) := by
    rw [hksum]
    exact Finset.sum_le_sum fun r hr => by have := hlt r hr; omega
  have hprod := one_add_sum_le_prod S t fun r hr => by have := hlt r hr; omega
  have hP : 0 < ∏ r ∈ S, t r := by omega
  have := Nat.le_of_dvd (by omega) h2P
  omega

/-- Divisor sum of a full prime power component divides the divisor sum of the number. -/
private lemma sigma_component_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    σ 1 (p ^ n.factorization p) ∣ σ 1 n := by
  have hcop := (Nat.coprime_ordCompl hp hn).pow_left (n.factorization p)
  calc σ 1 (ordProj[p] n) ∣ σ 1 (ordProj[p] n) * σ 1 (ordCompl[p] n) := dvd_mul_right _ _
    _ = σ 1 (ordProj[p] n * ordCompl[p] n) :=
      (isMultiplicative_sigma.map_mul_of_coprime hcop).symm
    _ = σ 1 n := by rw [Nat.ordProj_mul_ordCompl_eq_self]

/-- Exponents in the Euler form. -/
private lemma euler_factorization {q k m p : ℕ} (hq : q.Prime) (hm : m ≠ 0) (hqm : ¬ q ∣ m) :
    (q ^ k * m ^ 2).factorization p = (if p = q then k else 0) + (m ^ 2).factorization p := by
  rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm), Finsupp.add_apply,
    Nat.factorization_pow, hq.factorization]
  by_cases hpq : p = q
  · subst hpq; simp
  · simp [hpq]

/-- Dandapat, Hunsucker, and Pomerance: in the Euler form `N = q ^ k * m ^ 2` of an odd
perfect number, `σ(m ^ 2)` is not equal to `q ^ k`. -/
theorem not_sigma_sq_eq_special_pow {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : Odd k) :
    σ 1 (m ^ 2) ≠ q ^ k := by
  intro hσ
  have hm : m ≠ 0 := by rintro rfl; exact h.ne_zero (by simp [hN])
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hqm2 : (m ^ 2).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun hd => hqm (hq.dvd_of_dvd_pow hd)
  refine not_all_components_special_powers h hq ?_ fun p hp hpq => ?_
  · rw [hN, euler_factorization hq hm hqm, if_pos rfl, hqm2, add_zero]; exact hk
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hfp : N.factorization p = (m ^ 2).factorization p := by
      rw [hN, euler_factorization hq hm hqm, if_neg hpq, zero_add]
    rw [hfp]
    have hd := sigma_component_dvd hm2 hpp
    rw [hσ] at hd
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hq).mp hd
    exact ⟨c, hc⟩

/-- `σ(q ^ k)` is even when `q` is odd and `k` is odd. -/
private lemma two_dvd_sigma {q k : ℕ} (hq : q.Prime) (hq2 : q % 2 = 1) (hk : Odd k) :
    2 ∣ σ 1 (q ^ k) := by
  rw [sigma_one_apply_prime_pow hq, Nat.dvd_iff_mod_eq_zero, Finset.sum_nat_mod]
  simp only [Nat.pow_mod, hq2, one_pow, Nat.one_mod, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one]
  obtain ⟨j, rfl⟩ := hk
  omega

/-- Dris type inequality: `3 σ(q ^ k) ≤ 2 m ^ 2` in the Euler form of an odd perfect number. -/
theorem three_mul_sigma_special_le {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : Odd k) :
    3 * σ 1 (q ^ k) ≤ 2 * m ^ 2 := by
  have hm : m ≠ 0 := by rintro rfl; exact h.ne_zero (by simp [hN])
  have hcop : Nat.Coprime (q ^ k) (m ^ 2) :=
    ((hq.coprime_iff_not_dvd.mpr hqm).pow_left k).pow_right 2
  have hmul : σ 1 (q ^ k) * σ 1 (m ^ 2) = 2 * (q ^ k * m ^ 2) := by
    rw [← isMultiplicative_sigma.map_mul_of_coprime hcop, ← hN, h.sigma_eq]
  have hcq : Nat.Coprime (q ^ k) (σ 1 (q ^ k)) :=
    ((hq.coprime_iff_not_dvd.mpr (not_dvd_sigma hq k)).pow_left k)
  obtain ⟨t, ht⟩ : q ^ k ∣ σ 1 (m ^ 2) :=
    hcq.dvd_of_dvd_mul_left ⟨2 * m ^ 2, by rw [hmul]; ring⟩
  have hqk : 0 < q ^ k := pow_pos hq.pos k
  have ht2 : σ 1 (q ^ k) * t = 2 * m ^ 2 := by
    rw [ht] at hmul
    have : (σ 1 (q ^ k) * t) * q ^ k = (2 * m ^ 2) * q ^ k := by
      rw [show (σ 1 (q ^ k) * t) * q ^ k = σ 1 (q ^ k) * (q ^ k * t) by ring, hmul]; ring
    exact Nat.eq_of_mul_eq_mul_right hqk this
  have hNodd := h.odd
  have hmodd : m % 2 = 1 := Nat.odd_iff.mp
    (hNodd.of_dvd_nat (hN ▸ (dvd_pow_self m two_ne_zero).mul_left _))
  have hq2 : q % 2 = 1 := Nat.odd_iff.mp
    (hNodd.of_dvd_nat (hN ▸ (dvd_pow_self q (Nat.pos_of_ne_zero hk.pos.ne').ne').mul_right _))
  obtain ⟨s, hs⟩ := two_dvd_sigma hq hq2 hk
  have htodd : t % 2 = 1 := by
    by_contra hte
    obtain ⟨u, rfl⟩ : 2 ∣ t := Nat.dvd_of_mod_eq_zero (by omega)
    rw [hs] at ht2
    have : m ^ 2 = 2 * (s * u) := by linarith
    have : m ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hmodd]
    omega
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact not_sigma_sq_eq_special_pow h hq hN hqm hk (by rw [ht, mul_one])
  have ht3 : 3 ≤ t := by omega
  calc 3 * σ 1 (q ^ k) ≤ t * σ 1 (q ^ k) := Nat.mul_le_mul_right _ ht3
    _ = 2 * m ^ 2 := by rw [mul_comm, ht2]

/-- In the Euler form of an odd perfect number, `3 q ^ k < 2 m ^ 2`. -/
theorem special_pow_lt_sq {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : Odd k) : 3 * q ^ k < 2 * m ^ 2 := by
  have hle := three_mul_sigma_special_le h hq hN hqm hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := hk.pos; omega⟩
  have : q ^ (k' + 1) < σ 1 (q ^ (k' + 1)) := by
    rw [sigma_one_apply_prime_pow hq, Finset.sum_range_succ, Finset.sum_range_succ', pow_zero]
    omega
  omega

/-- Every odd perfect number has an Euler form `q ^ k * m ^ 2` with `q ≡ k ≡ 1 (mod 4)`
and `3 q ^ k < 2 m ^ 2`. -/
theorem exists_euler_form_with_bound {N : ℕ} (h : OddPerfect N) :
    ∃ q k m : ℕ, q.Prime ∧ N = q ^ k * m ^ 2 ∧ ¬ q ∣ m ∧ q % 4 = 1 ∧ k % 4 = 1 ∧
      3 * q ^ k < 2 * m ^ 2 := by
  obtain ⟨q, k, m, hq, hN, hqm, hq4, hk4⟩ := exists_euler_form h
  exact ⟨q, k, m, hq, hN, hqm, hq4, hk4,
    special_pow_lt_sq h hq hN hqm (Nat.odd_iff.mpr (by omega))⟩

end OddPerfect

#print axioms OddPerfect.not_all_components_special_powers
#print axioms OddPerfect.not_sigma_sq_eq_special_pow
#print axioms OddPerfect.three_mul_sigma_special_le
#print axioms OddPerfect.special_pow_lt_sq
#print axioms OddPerfect.exists_euler_form_with_bound
