import OddPerfect.IndexColumnLower
import OddPerfect.UniformExponents
import OddPerfect.EulerIndexOmegaSigned
import OddPerfect.EulerPart

/-!
# Deep lifts in the equal exponent family

Let `N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`, and suppose
every ordinary exponent equals `l - 1` for an odd prime `l`. Write `J = eulerIndex q a m`,
`L = (a + 1) / 2`, `S = congrPrimes N q l` and `W = otherPrimes N q l` (the ordinary primes
outside the classes `l` and `1` modulo `l`).

* `card_odd_valuation_eulerIndex_le_of_equal_exponents`: at most `l - 1` primes have odd
  valuation in `J`. Every prime factor of `J` lies in `S` or equals `l`, and
  `v_l(J) = |S| = l - 1 - v_l(a + 1)`.
* `not_dvd_special_pred_of_mem_otherPrimes`: no `w ∈ W` divides `q - 1`.
* `two_mul_sum_padicValNat_otherPrimes_le`: `2 ∑_{w ∈ W} v_w(L) ≤ l - 1`.
* `pow_half_dvd_pow_pred_sub_one_of_mem_otherPrimes`: `w ^ ((l - 1) / 2) ∣ q ^ (w - 1) - 1`
  for every `w ∈ W`.

These are restricted results for the family where all ordinary exponents equal `l - 1`. The
family is not excluded; the number of prime factors of `J` is not bounded, and `l` is bounded
only through it. The odd perfect number conjecture remains open. Restricted result; no
published source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EqExpLift

/-- The Euler frame: `m ≠ 0`, `v_q(N) = a`, `a` odd, and `v_p(N) = v_p(m ^ 2)` for `p ≠ q`. -/
private lemma frame {N q a m : ℕ} (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2)
    (hqm : ¬ q ∣ m) :
    m ≠ 0 ∧ N.factorization q = a ∧ Odd a ∧
      ∀ p, p ≠ q → N.factorization p = (m ^ 2).factorization p := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hfac : ∀ p, N.factorization p = (q ^ a).factorization p + (m ^ 2).factorization p := by
    intro p
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply]
  have hqa : N.factorization q = a := by
    rw [hfac, hq.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd)), add_zero]
  refine ⟨hm, hqa, ?_, fun p hp => ?_⟩
  · rcases Nat.even_or_odd a with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  · rw [hfac, hq.factorization_pow, Finsupp.single_apply, ite_eq_right (Ne.symm hp), zero_add]

/-- In this family `l` is an ordinary prime factor of `N`. -/
private lemma index_facts {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    l ∈ N.primeFactors ∧ l ≠ q := by
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => ⟨1, by rw [hexp p hp hpq, hl1, pow_one]⟩
  have hlq := LCol.ne_of_prime_pow_index h hl hodd hidx'
  have hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1 :=
    fun p hp hpq => by rw [hexp p hp hpq, hl1]
  exact ⟨Nat.mem_primeFactors.mpr ⟨hl,
    (dvd_pow_self l (by norm_num : (4 : ℕ) ≠ 0)).trans (pow_four_dvd_of_dvd_succ h hq hodd hcomp),
    h.ne_zero⟩, hlq⟩

/-- A sum of valuations over any set of primes is at most `Ω`. -/
private lemma sum_factorization_le_cardFactors (T : Finset ℕ) (n : ℕ) :
    ∑ p ∈ T, n.factorization p ≤ cardFactors n := by
  rw [cardFactors_eq_sum_factorization, Finsupp.sum]
  exact Finset.sum_le_sum_of_ne_zero fun p _ hp => Finsupp.mem_support_iff.mpr hp

/-- For an odd prime `w`, `v_w(a + 1) = v_w((a + 1) / 2)` when `a` is odd. -/
private lemma factorization_half {a w : ℕ} (ha : Odd a) (hw2 : w ≠ 2) (hwp : w.Prime) :
    (a + 1).factorization w = ((a + 1) / 2).factorization w := by
  obtain ⟨j, rfl⟩ := ha
  have hL : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
  rw [hL, Nat.mul_div_cancel_left _ (by norm_num), Nat.factorization_mul (by norm_num)
    (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd
      (fun hd => hw2 ((Nat.prime_dvd_prime_iff_eq hwp Nat.prime_two).mp hd)), zero_add]

/-- `padicValNat` as a factorization. -/
private lemma padicValNat_eq_factorization {w n : ℕ} (hwp : w.Prime) :
    padicValNat w n = n.factorization w := by
  rw [Nat.factorization_def _ hwp, Nat.padicValNat_def]

/-- Membership in `otherPrimes`, unpacked. -/
private lemma other_facts {N q l w : ℕ} (h : OddPerfect N) (hw : w ∈ otherPrimes N q l) :
    w ∈ N.primeFactors ∧ w.Prime ∧ w ≠ 2 ∧ w ≠ q := by
  obtain ⟨hwN, hwq, -, -⟩ := Finset.mem_filter.mp hw
  exact ⟨hwN, Nat.prime_of_mem_primeFactors hwN,
    fun e => h.not_two_dvd (e ▸ Nat.dvd_of_mem_primeFactors hwN), hwq⟩

end EqExpLift

/-- Equal exponents: at most `l - 1` primes have odd valuation in the Euler index. Let
`N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`, and every
ordinary exponent equal to `l - 1` for an odd prime `l`. Every prime factor of the Euler index
`J` is `l` or an ordinary prime `1` modulo `l`, and `v_l(J) = l - 1 - v_l(a + 1)`. Restricted
result for the family where all ordinary exponents equal `l - 1`; the family is not excluded.
Restricted result; no published source was checked; novelty not verified. -/
theorem card_odd_valuation_eulerIndex_le_of_equal_exponents {N q a m l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    ((eulerIndex q a m).primeFactors.filter
      fun t => Odd ((eulerIndex q a m).factorization t)).card ≤ l - 1 := by
  obtain ⟨hm, hqa, hao, hfm⟩ := EqExpLift.frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  obtain ⟨hlN, hlq⟩ := EqExpLift.index_facts h hq hodd hl hexp
  have hcard := card_congrPrimes_add_padicValNat h hq hodd hl hexp hlN hlq
  rw [hqa] at hcard
  set S := congrPrimes N q l with hS
  set J := eulerIndex q a m
  have hJm : J ∣ m ^ 2 := eulerIndex_dvd_sq h hq hN hqm
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hJ0 : J ≠ 0 := fun h0 => hm2 (Nat.eq_zero_of_zero_dvd (h0 ▸ hJm))
  have hqJ : ¬ q ∣ J := fun hd => hqm (hq.dvd_of_dvd_pow (hd.trans hJm))
  -- Every prime factor of `J` is `l` or lies in `S`.
  have hsupp : ∀ t ∈ J.primeFactors, t = l ∨ t ∈ S := by
    intro t ht
    have htp := Nat.prime_of_mem_primeFactors ht
    have htJ := Nat.dvd_of_mem_primeFactors ht
    have htq : t ≠ q := fun e => hqJ (e ▸ htJ)
    have htN : t ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨htp,
      by rw [hN]; exact (htJ.trans hJm).mul_left _, h.ne_zero⟩
    have hσ : σ 1 (m ^ 2) = q ^ a * J := sigma_sq_eq_mul_eulerIndex h hq hN hqm
    have htσ : t ∣ σ 1 (m ^ 2) := hσ ▸ htJ.mul_left _
    rw [isMultiplicative_sigma.multiplicative_factorization _ hm2, Finsupp.prod] at htσ
    obtain ⟨p, hp, hpd⟩ := htp.prime.exists_mem_finset_dvd htσ
    rw [Nat.support_factorization] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpm : p ∣ m ^ 2 := Nat.dvd_of_mem_primeFactors hp
    have hpq : p ≠ q := fun e => hqm (hq.dvd_of_dvd_pow (e ▸ hpm))
    have hpN : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp,
      by rw [hN]; exact hpm.mul_left _, h.ne_zero⟩
    rw [← hfm p hpq, hexp p hpN hpq] at hpd
    rcases prime_dvd_sigma_prime_pow_of_prime_length hpp htp hl hpd with e | e
    · exact Or.inl e
    · right
      rw [hS, congrPrimes, Finset.mem_filter]
      exact ⟨htN, htq, e⟩
  -- The valuation of `l` in `J`.
  have hval : J.factorization l + padicValNat l (a + 1) = l - 1 := by
    have he := sigma_special_mul_eulerIndex h hq hN hqm
    have hσ0 : σ 1 (q ^ a) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
    have hf := congrArg (fun n => n.factorization l) he
    rw [Nat.factorization_mul hσ0 hJ0, Nat.factorization_mul two_ne_zero hm2,
      Finsupp.add_apply, Finsupp.add_apply] at hf
    have h2l : (2 : ℕ).factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd
      (fun hd => hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp hd))
    have hml : (m ^ 2).factorization l = l - 1 := by rw [← hfm l hlq, hexp l hlN hlq]
    have hql := special_mod_eq_one h hq hodd hl hexp hlq
    have hv := padicValNat_sigma_of_mod_eq_one hq hl hl2 hql (a := a)
    have hσl : (σ 1 (q ^ a)).factorization l = padicValNat l (a + 1) := by
      rw [← hv, EqExpLift.padicValNat_eq_factorization hl]
    omega
  set O := J.primeFactors.filter fun t => Odd (J.factorization t)
  by_cases hlO : l ∈ O
  · have hodl : Odd (J.factorization l) := (Finset.mem_filter.mp hlO).2
    have hsub : O ⊆ insert l S := fun t ht => by
      rcases hsupp t (Finset.mem_filter.mp ht).1 with e | e
      · exact e ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem e
    have hc := Finset.card_le_card hsub
    have hci := Finset.card_insert_le l S
    obtain ⟨u, hu⟩ := hodl
    obtain ⟨v, hv⟩ := hl.even_sub_one hl2
    omega
  · have hsub : O ⊆ S := fun t ht => by
      rcases hsupp t (Finset.mem_filter.mp ht).1 with e | e
      · exact absurd (e ▸ ht) hlO
      · exact e
    have hc := Finset.card_le_card hsub
    omega

/-- Equal exponents: no ordinary prime outside the classes `l` and `1` modulo `l` divides
`q - 1`. Let `N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`, and
every ordinary exponent equal to `l - 1` for an odd prime `l`. Restricted result for the
family where all ordinary exponents equal `l - 1`; the family is not excluded. Restricted
result; no published source was checked; novelty not verified. -/
theorem not_dvd_special_pred_of_mem_otherPrimes {N q a m l w : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : w ∈ otherPrimes N q l) : ¬ w ∣ q - 1 := by
  intro hwd
  obtain ⟨-, hqa, hao, -⟩ := EqExpLift.frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  obtain ⟨-, hwp, hw2, -⟩ := EqExpLift.other_facts h hw
  have hqw : q % w = 1 := by
    have hmod : 1 ≡ q [MOD w] := (Nat.modEq_iff_dvd' hq.one_lt.le).mpr hwd
    unfold Nat.ModEq at hmod
    rw [Nat.mod_eq_of_lt hwp.one_lt] at hmod
    exact hmod.symm
  have hv := padicValNat_succ_of_mem_otherPrimes_of_mod_eq_one h hq hodd hl hexp hw hqw
  rw [hqa, EqExpLift.padicValNat_eq_factorization hwp,
    EqExpLift.factorization_half hao hw2 hwp] at hv
  have hΩ : l - 1 ≤ cardFactors ((a + 1) / 2) := by
    have := EqExpLift.sum_factorization_le_cardFactors {w} ((a + 1) / 2)
    rw [Finset.sum_singleton, hv] at this
    exact this
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [show (1 + 1) / 2 = 1 by rfl, Nat.factorization_one, Finsupp.zero_apply] at hv
    omega
  have h1 := cardFactors_add_one_le_card_odd_valuation_eulerIndex h hq hN hqm ha1
  have h2 := card_odd_valuation_eulerIndex_le_of_equal_exponents h hq hN hqm hl hl2 hexp
  omega

/-- Equal exponents: `2 ∑_{w ∈ W} v_w((a + 1) / 2) ≤ l - 1`, where `W = otherPrimes N q l`
collects the ordinary primes outside the classes `l` and `1` modulo `l`. Let
`N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`, and every
ordinary exponent equal to `l - 1` for an odd prime `l`. Restricted result for the family
where all ordinary exponents equal `l - 1`; the family is not excluded. Restricted result; no
published source was checked; novelty not verified. -/
theorem two_mul_sum_padicValNat_otherPrimes_le {N q a m l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    2 * ∑ w ∈ otherPrimes N q l, padicValNat w ((a + 1) / 2) ≤ l - 1 := by
  have h1 := cardFactors_add_signed_le_card_odd_valuation_eulerIndex h hq hN hqm
  have h2 := card_odd_valuation_eulerIndex_le_of_equal_exponents h hq hN hqm hl hl2 hexp
  have hconv : ∑ w ∈ otherPrimes N q l, padicValNat w ((a + 1) / 2) =
      ∑ w ∈ otherPrimes N q l, ((a + 1) / 2).factorization w :=
    Finset.sum_congr rfl fun w hw =>
      EqExpLift.padicValNat_eq_factorization (EqExpLift.other_facts h hw).2.1
  have hA : ∑ w ∈ otherPrimes N q l, ((a + 1) / 2).factorization w ≤
      ∑ p ∈ ((a + 1) / 2).primeFactors.filter (fun p => ¬ p ∣ q - 1),
        ((a + 1) / 2).factorization p := by
    refine Finset.sum_le_sum_of_ne_zero fun w hw hne => ?_
    refine Finset.mem_filter.mpr ⟨?_, not_dvd_special_pred_of_mem_otherPrimes h hq hN hqm hl hl2
      hexp hw⟩
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr hne
  have hB := EqExpLift.sum_factorization_le_cardFactors (otherPrimes N q l) ((a + 1) / 2)
  omega

/-- Equal exponents: every ordinary prime `w` outside the classes `l` and `1` modulo `l`
satisfies `w ^ ((l - 1) / 2) ∣ q ^ (w - 1) - 1`. Let `N = q ^ a * m ^ 2` be an odd perfect
number with special prime `q`, `q ∤ m`, and every ordinary exponent equal to `l - 1` for an odd
prime `l`. Restricted result for the family where all ordinary exponents equal `l - 1`; the
family is not excluded, and `l` is bounded only through the number of prime factors of `J`.
Restricted result; no published source was checked; novelty not verified. -/
theorem pow_half_dvd_pow_pred_sub_one_of_mem_otherPrimes {N q a m l w : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : w ∈ otherPrimes N q l) : w ^ ((l - 1) / 2) ∣ q ^ (w - 1) - 1 := by
  obtain ⟨-, hqa, hao, -⟩ := EqExpLift.frame h hq hN hqm
  have hodd : Odd (N.factorization q) := hqa ▸ hao
  obtain ⟨-, hwp, hw2, hwq⟩ := EqExpLift.other_facts h hw
  have : Fact w.Prime := ⟨hwp⟩
  have hnd := not_dvd_special_pred_of_mem_otherPrimes h hq hN hqm hl hl2 hexp hw
  have hq0 : (q : ZMod w) ≠ 0 := by
    intro h0
    exact hwq ((Nat.prime_dvd_prime_iff_eq hwp hq).mp ((ZMod.natCast_eq_zero_iff _ _).mp h0))
  have hdw : orderOf (q : ZMod w) ∣ w - 1 := ZMod.orderOf_dvd_card_sub_one hq0
  have hw3 : 3 ≤ w := by have := hwp.two_le; omega
  have hd0 : orderOf (q : ZMod w) ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hdw
    omega
  have hd1 : orderOf (q : ZMod w) ≠ 1 := by
    intro h1
    have hc : (q : ZMod w) = 1 := orderOf_eq_one_iff.mp h1
    have hmod := (ZMod.natCast_eq_natCast_iff' q 1 w).mp (by simpa using hc)
    exact hnd ((Nat.modEq_iff_dvd' hq.one_lt.le).mp hmod.symm)
  obtain ⟨hdvd, hv⟩ :=
    padicValNat_of_mem_otherPrimes_of_one_lt_orderOf h hq hodd hl hexp hw (by omega)
  rw [hqa] at hdvd hv
  set d := orderOf (q : ZMod w)
  have hdlt : d < w := Nat.lt_of_le_of_lt (Nat.le_of_dvd (by omega) hdw) (by omega)
  have hwd : ¬ w ∣ d := fun hh => by have := Nat.le_of_dvd (by omega) hh; omega
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; omega
  have hk' : (a + 1) / d = k := by rw [hk, Nat.mul_div_cancel_left _ (by omega)]
  have hqd : 1 < q ^ d := Nat.one_lt_pow hd0 hq.one_lt
  have hqd0 : q ^ d - 1 ≠ 0 := by omega
  rw [hk', EqExpLift.padicValNat_eq_factorization hwp,
    EqExpLift.padicValNat_eq_factorization hwp] at hv
  -- `v_w(k) = v_w(L)`.
  have hkL : k.factorization w = ((a + 1) / 2).factorization w := by
    rw [← EqExpLift.factorization_half hao hw2 hwp, hk, Nat.factorization_mul hd0 hk0,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hwd, zero_add]
  -- The bound of `two_mul_sum_padicValNat_otherPrimes_le` at the single prime `w`.
  have h3 := two_mul_sum_padicValNat_otherPrimes_le h hq hN hqm hl hl2 hexp
  have hsingle : padicValNat w ((a + 1) / 2) ≤
      ∑ x ∈ otherPrimes N q l, padicValNat x ((a + 1) / 2) :=
    Finset.single_le_sum (f := fun x => padicValNat x ((a + 1) / 2))
      (fun _ _ => Nat.zero_le _) hw
  rw [EqExpLift.padicValNat_eq_factorization hwp] at hsingle
  have hpow : w ^ ((l - 1) / 2) ∣ q ^ d - 1 := by
    rw [hwp.pow_dvd_iff_le_factorization hqd0]
    omega
  exact hpow.trans (Nat.pow_sub_one_dvd_pow_sub_one q hdw)

end OddPerfect

#print axioms OddPerfect.card_odd_valuation_eulerIndex_le_of_equal_exponents
#print axioms OddPerfect.not_dvd_special_pred_of_mem_otherPrimes
#print axioms OddPerfect.two_mul_sum_padicValNat_otherPrimes_le
#print axioms OddPerfect.pow_half_dvd_pow_pred_sub_one_of_mem_otherPrimes
