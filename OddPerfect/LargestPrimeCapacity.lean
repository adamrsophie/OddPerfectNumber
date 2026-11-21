import OddPerfect.LargestPrimeOrder
import Mathlib.RingTheory.IntegralDomain

/-!
# A capacity bound for the exponent of the largest prime factor

Let `N` be an odd perfect number with largest prime factor `P`, and write
`P - 1 = 2 ^ a · m` with `m` odd. A *sender* is a prime factor `p ≠ P` with
`P ∣ σ(p ^ e_p)`. Its order `t = ord_P(p)` is at least `3` (as `p < P`, `p` is not `±1`
modulo `P`), divides `e_p + 1 < P`, and is not divisible by `4` (Euler's form). So `t = d` or
`t = 2 d` with `d` odd, `d > 1`, `d ∣ m`; the signed residue `±p` has order exactly `d`, and
the map `p ↦ ±p` is injective on senders (two odd numbers below `P` never add up to `P`).
There are `φ(d)` residues of order `d`, so at most `φ(d)` senders belong to `d`.

The weight of a sender is `v_P(σ(p ^ e_p)) = v_P(p ^ t - 1) = v_P(Φ_t(p))`, and
`0 < Φ_t(p) < (p + 1) ^ φ(t) ≤ P ^ φ(t)` gives weight at most `φ(t) - 1 = φ(d) - 1`. Adding
up through the ledger `e_P = Σ_p v_P(σ(p ^ e_p))`:

* `factorization_largest_le_sum_totient`:
  `e_P ≤ Σ_{d ∣ m, d > 1} φ(d) (φ(d) - 1)`.
* `card_senders_largest_le`: there are at most `m - 1` senders.
* `largest_sub_one_odd_part_ne_one`, `factorization_largest_le_two_of_odd_part_three`: the
  cases `m = 1` and `m = 3`, which recover `largest_prime_sub_one_ne_two_pow` and
  `factorization_largest_le_two`.

Controls (why the hypotheses matter): `σ(3 ^ 4) = 11 ^ 2`, so a weight need not be `1`;
`v_13(σ(3 ^ 38)) = 2` while `v_13(Φ_3(3)) = 1`, so `e_p + 1 < P` is needed; modulo `7` the
residues `5` (order `6`) and `23` (order `3`) have signed images `-5 = 2` and `23 = 2`, so
`p < P` is needed for injectivity; `Φ_30(3) = 8401 > 3 ^ 8`, so the height bound needs `p + 1`;
and `7 ∣ σ(13)` is a sender of order `2` into a prime that is not the largest.
-/

open ArithmeticFunction Polynomial
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Cyclotomic values -/

/-- Height of a cyclotomic value: for `t ≥ 3` and `p > 1`,
`0 < Φ_t(p) < (p + 1) ^ φ(t)` in `ℤ`. -/
theorem cyclotomic_eval_int_pos_lt {t p : ℕ} (ht : 3 ≤ t) (hp : 1 < p) :
    0 < (cyclotomic t ℤ).eval (p : ℤ) ∧
      (cyclotomic t ℤ).eval (p : ℤ) < ((p : ℤ) + 1) ^ t.totient := by
  refine ⟨cyclotomic_pos' t (by exact_mod_cast hp), ?_⟩
  have h := cyclotomic_eval_lt_add_one_pow_totient ht (q := (p : ℝ)) (by exact_mod_cast hp)
  have e : (cyclotomic t ℝ).eval (p : ℝ) = (((cyclotomic t ℤ).eval (p : ℤ) : ℤ) : ℝ) := by
    have := cyclotomic.eval_apply (p : ℤ) t (Int.castRingHom ℝ)
    simpa using this
  rw [e] at h
  exact_mod_cast h

private theorem pow_sub_one_eq_mul_prod {t : ℕ} (ht : 0 < t) (x : ℤ) :
    x ^ t - 1 = (cyclotomic t ℤ).eval x * ∏ u ∈ t.properDivisors, (cyclotomic u ℤ).eval x := by
  have h := congrArg (eval x) (prod_cyclotomic_eq_X_pow_sub_one ht ℤ)
  rw [← Nat.cons_self_properDivisors ht.ne', Finset.prod_cons, eval_mul, eval_prod] at h
  simpa using h.symm

/-- Weight bound: if `p < P` are primes and the order `t` of `p` modulo `P` is at least `3`,
then `v_P(p ^ t - 1) < φ(t)`. Only the factor `Φ_t(p)` of `p ^ t - 1` is divisible by `P`,
and `Φ_t(p) < (p + 1) ^ φ(t) ≤ P ^ φ(t)`. -/
theorem padicValNat_pow_orderOf_sub_one_lt_totient {p P : ℕ} (hp : p.Prime) (hP : P.Prime)
    (hpP : p < P) (ht : 3 ≤ orderOf (p : ZMod P)) :
    padicValNat P (p ^ orderOf (p : ZMod P) - 1) < (orderOf (p : ZMod P)).totient := by
  have : Fact P.Prime := ⟨hP⟩
  set t := orderOf (p : ZMod P) with htdef
  have hp0 : (p : ZMod P) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hh; have := Nat.le_of_dvd hp.pos hh; omega
  have htP : t < P := by
    have := Nat.le_of_dvd (by have := hP.two_le; omega) (ZMod.orderOf_dvd_card_sub_one hp0)
    omega
  have hPz : Prime (P : ℤ) := Nat.prime_iff_prime_int.mp hP
  -- `P` does not divide the other factors
  have hQ : ¬ (P : ℤ) ∣ ∏ u ∈ t.properDivisors, (cyclotomic u ℤ).eval (p : ℤ) := by
    rw [hPz.dvd_finsetProd_iff]
    rintro ⟨u, hu, hdu⟩
    have hu0 := Nat.pos_of_mem_properDivisors hu
    have hut := (Nat.mem_properDivisors.mp hu).2
    have := (orderOf_eq_of_dvd_cyclotomic_eval hP hdu fun hh => by
      have := Nat.le_of_dvd hu0 hh; omega).1
    omega
  by_contra hw
  push Not at hw
  have hpt : 1 ≤ p ^ t := Nat.one_le_pow _ _ hp.pos
  have h1 : P ^ t.totient ∣ p ^ t - 1 :=
    (pow_dvd_pow P hw).trans pow_padicValNat_dvd
  have h2 : ((P : ℤ)) ^ t.totient ∣ (p : ℤ) ^ t - 1 := by
    have := Int.natCast_dvd_natCast.mpr h1
    push_cast [hpt] at this
    exact this
  rw [pow_sub_one_eq_mul_prod (by omega)] at h2
  have hcop : IsCoprime ((P : ℤ) ^ t.totient)
      (∏ u ∈ t.properDivisors, (cyclotomic u ℤ).eval (p : ℤ)) :=
    ((hPz.coprime_iff_not_dvd).mpr hQ).pow_left
  have h3 := hcop.dvd_of_dvd_mul_right h2
  obtain ⟨hpos, hlt⟩ := cyclotomic_eval_int_pos_lt ht hp.one_lt
  have h4 := Int.le_of_dvd hpos h3
  have h5 : ((p : ℤ) + 1) ^ t.totient ≤ (P : ℤ) ^ t.totient :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hpP) _
  omega

/-! ## Signed residues -/

/-- If `x` has order `2 d` modulo an odd prime with `d` odd, then `-x` has order `d`. -/
theorem orderOf_neg_of_orderOf_eq_two_mul {P : ℕ} [Fact P.Prime] (hP2 : P ≠ 2) {x : ZMod P}
    {d : ℕ} (hd : Odd d) (hx : orderOf x = 2 * d) : orderOf (-x) = d := by
  have hx2 : x ^ (2 * d) = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxd : x ^ d = -1 := by
    have : (x ^ d - 1) * (x ^ d + 1) = 0 := by
      rw [show 2 * d = d * 2 by ring, pow_mul] at hx2
      linear_combination hx2
    rcases mul_eq_zero.mp this with h | h
    · have := orderOf_dvd_of_pow_eq_one (sub_eq_zero.mp h)
      rw [hx] at this
      have := Nat.le_of_dvd hd.pos this
      have := hd.pos
      omega
    · exact eq_neg_of_add_eq_zero_left h
  have hnd : (-x) ^ d = 1 := by rw [hd.neg_pow, hxd, neg_neg]
  have hdv := orderOf_dvd_of_pow_eq_one hnd
  have hoodd : Odd (orderOf (-x)) := hd.of_dvd_nat hdv
  have hneg1 : orderOf (-1 : ZMod P) = 2 := by
    rw [orderOf_neg_one, ZMod.ringChar_zmod_n, if_neg hP2]
  have hmul : orderOf ((-1 : ZMod P) * -x) = orderOf (-1 : ZMod P) * orderOf (-x) :=
    (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [hneg1]; exact (Nat.coprime_two_left).mpr hoodd)
  rw [show (-1 : ZMod P) * -x = x by ring, hneg1, hx] at hmul
  omega

/-! ## Senders into the largest prime factor -/

variable {N : ℕ}

private theorem odd_of_mem (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) :
    p % 2 = 1 :=
  Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))

/-- Data of a sender `p` into the largest prime factor `P`: `p < P`, `p` odd, its order `t`
modulo `P` satisfies `3 ≤ t`, `4 ∤ t`, and the weight is `v_P(p ^ t - 1)`. -/
theorem sender_largest_data (h : OddPerfect N) {P p : ℕ} (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hp : p ∈ N.primeFactors) (hpP : p ≠ P)
    (hd : P ∣ σ 1 (p ^ N.factorization p)) :
    p < P ∧ p % 2 = 1 ∧ 3 ≤ orderOf (p : ZMod P) ∧ ¬ 4 ∣ orderOf (p : ZMod P) ∧
      padicValNat P (σ 1 (p ^ N.factorization p)) =
        padicValNat P (p ^ orderOf (p : ZMod P) - 1) := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have : Fact P.Prime := ⟨hPp⟩
  have hP2 := odd_of_mem h hP
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hlt : p < P := lt_of_le_of_ne (hmax p hp) hpP
  have hp2 := odd_of_mem h hp
  have he := two_mul_factorization_add_three_le h hp hmax
  set e := N.factorization p with hedef
  set t := orderOf (p : ZMod P) with htdef
  have hdd := (dvd_sigma_prime_pow_iff hpp hPp hpP).mp hd
  have ht1 : t ≠ 1 := fun h1 => by
    rw [← htdef, if_pos h1] at hdd
    have := Nat.le_of_dvd (by omega) hdd
    omega
  rw [← htdef, if_neg ht1] at hdd
  have ht0 : t ≠ 0 := fun h0 => by rw [h0, zero_dvd_iff] at hdd; omega
  have ht2 : t ≠ 2 := fun h2 => by
    have hsq : (p : ZMod P) ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
    have hne1 : (p : ZMod P) ≠ 1 := fun h => ht1 (by rw [htdef, h, orderOf_one])
    have : ((p : ZMod P) - 1) * ((p : ZMod P) + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · exact hne1 (sub_eq_zero.mp h)
    · have hd1 : P ∣ p + 1 := (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast; exact h)
      have := Nat.le_of_dvd (by omega) hd1
      omega
  have h4 : ¬ 4 ∣ t := fun h4 => by
    obtain ⟨c, hc⟩ := h4.trans hdd
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ho
    · omega
    · have := (special_mod_four h hpp ho).2
      omega
  refine ⟨hlt, hp2, by omega, h4, ?_⟩
  rw [padicValNat_sigma_prime_pow_of_orderOf_dvd hpp hPp (by omega) hpP (by omega) hdd]
  have hq : padicValNat P ((e + 1) / t) = 0 := padicValNat.eq_zero_of_not_dvd fun hh => by
    have := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (by omega) hdd) (by omega)) hh
    have := Nat.div_le_self (e + 1) t
    omega
  rw [hq, add_zero]

/-- The odd part `d` of an order `t` with `4 ∤ t`: `t` itself if `t` is odd, else `t / 2`. -/
private def oddPart (t : ℕ) : ℕ := if t % 2 = 1 then t else t / 2

private theorem oddPart_spec {t : ℕ} (ht : 3 ≤ t) (h4 : ¬ 4 ∣ t) :
    Odd (oddPart t) ∧ 3 ≤ oddPart t ∧ oddPart t ∣ t ∧
      (oddPart t).totient = t.totient ∧ (t % 2 = 0 → t = 2 * oddPart t) := by
  unfold oddPart
  split_ifs with h
  · exact ⟨Nat.odd_iff.mpr h, ht, dvd_rfl, rfl, by omega⟩
  · have hodd : Odd (t / 2) := Nat.odd_iff.mpr (by omega)
    have ht2 : t = 2 * (t / 2) := by omega
    refine ⟨hodd, by omega, ⟨2, by omega⟩, ?_, fun _ => ht2⟩
    conv_rhs => rw [ht2]
    exact (Nat.totient_two_mul_of_odd hodd).symm

/-- The signed residue of `p`: `p` when its order is odd, `-p` otherwise. -/
private noncomputable def signedRes (P p : ℕ) : ZMod P :=
  if orderOf (p : ZMod P) % 2 = 1 then (p : ZMod P) else -(p : ZMod P)

private theorem orderOf_signedRes {P p : ℕ} [Fact P.Prime] (hP2 : P ≠ 2)
    (ht : 3 ≤ orderOf (p : ZMod P)) (h4 : ¬ 4 ∣ orderOf (p : ZMod P)) :
    orderOf (signedRes P p) = oddPart (orderOf (p : ZMod P)) := by
  obtain ⟨hodd, -, -, -, h2⟩ := oddPart_spec ht h4
  unfold signedRes
  split_ifs with h
  · unfold oddPart; rw [if_pos h]
  · exact orderOf_neg_of_orderOf_eq_two_mul hP2 hodd (h2 (by omega))

private theorem signedRes_inj {P p p' : ℕ} (hP2 : P % 2 = 1) (hp : p < P) (hp' : p' < P)
    (hp2 : p % 2 = 1) (hp2' : p' % 2 = 1) (h : signedRes P p = signedRes P p') : p = p' := by
  have eq : ∀ a b : ℕ, a < P → b < P → (a : ZMod P) = b → a = b := fun a b ha hb hab => by
    rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
  have key2 : ∀ a b : ℕ, a < P → b < P → a % 2 = 1 → b % 2 = 1 →
      (a : ZMod P) = -(b : ZMod P) → False := by
    intro a b ha hb ha2 hb2 hab
    have : P ∣ a + b := (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast; rw [hab]; ring)
    obtain ⟨c, hc⟩ := this
    rcases c with _ | _ | c
    · omega
    · omega
    · have := Nat.mul_le_mul_left P (show 2 ≤ c + 1 + 1 by omega); omega
  unfold signedRes at h
  split_ifs at h
  · exact eq _ _ hp hp' h
  · exact (key2 _ _ hp hp' hp2 hp2' h).elim
  · exact (key2 _ _ hp' hp hp2' hp2 h.symm).elim
  · exact eq _ _ hp hp' (neg_inj.mp h)

/-- The senders into `P`. -/
private theorem sum_senders' (h : OddPerfect N) {P : ℕ} (hP : P ∈ N.primeFactors) :
    N.factorization P = ∑ p ∈ (N.primeFactors.erase P).filter
      (fun p => P ∣ σ 1 (p ^ N.factorization p)), padicValNat P (σ 1 (p ^ N.factorization p)) := by
  have hP2 : P ≠ 2 := by have := odd_of_mem h hP; omega
  rw [factorization_eq_sum_erase h.perfect (Nat.prime_of_mem_primeFactors hP) hP2,
    Finset.sum_filter_of_ne]
  intro p _ hne
  by_contra hd
  exact hne (padicValNat.eq_zero_of_not_dvd hd)

/-- Everything about the senders at once: each sender `p` has odd class `d = oddPart(ord p)`
in `m.divisors.erase 1`, weight at most `φ(d) - 1`, and at most `φ(d)` senders share `d`. -/
private theorem senders_classes (h : OddPerfect N) {P a m : ℕ} (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hm : P - 1 = 2 ^ a * m) (hmo : Odd m) :
    let S := (N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p))
    let K := fun p : ℕ => oddPart (orderOf (p : ZMod P))
    (∀ p ∈ S, K p ∈ m.divisors.erase 1) ∧
    (∀ p ∈ S, padicValNat P (σ 1 (p ^ N.factorization p)) ≤ (K p).totient - 1) ∧
    (∀ d ∈ m.divisors.erase 1, (S.filter (fun p => K p = d)).card ≤ d.totient) := by
  intro S K
  have hPp := Nat.prime_of_mem_primeFactors hP
  have : Fact P.Prime := ⟨hPp⟩
  have hP2 := odd_of_mem h hP
  have hP2' : P ≠ 2 := by omega
  have hmem : ∀ p ∈ S, p ∈ N.primeFactors ∧ p ≠ P ∧ P ∣ σ 1 (p ^ N.factorization p) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_erase] at hp
    exact ⟨hp.1.2, hp.1.1, hp.2⟩
  have hdata := fun p (hp : p ∈ S) =>
    sender_largest_data h hP hmax (hmem p hp).1 (hmem p hp).2.1 (hmem p hp).2.2
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun d hd => ?_⟩
  · obtain ⟨hlt, -, ht, h4, -⟩ := hdata p hp
    obtain ⟨hodd, h3, hdvt, -, -⟩ := oddPart_spec ht h4
    have hp0 : (p : ZMod P) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hh
      have := Nat.le_of_dvd (Nat.prime_of_mem_primeFactors (hmem p hp).1).pos hh
      omega
    have htP := ZMod.orderOf_dvd_card_sub_one hp0
    rw [hm] at htP
    have hKm : K p ∣ m :=
      (Nat.Coprime.pow_right a ((Nat.coprime_two_right).mpr hodd)).dvd_of_dvd_mul_left
        (hdvt.trans htP)
    exact Finset.mem_erase.mpr ⟨by show oddPart _ ≠ 1; omega, Nat.mem_divisors.mpr ⟨hKm, by
      rintro rfl; exact absurd hmo (by decide)⟩⟩
  · obtain ⟨hlt, -, ht, h4, hw⟩ := hdata p hp
    obtain ⟨-, -, -, htot, -⟩ := oddPart_spec ht h4
    rw [hw]
    have := padicValNat_pow_orderOf_sub_one_lt_totient
      (Nat.prime_of_mem_primeFactors (hmem p hp).1) hPp hlt ht
    show _ ≤ (oddPart _).totient - 1
    omega
  · -- injection into the units of order `d`
    classical
    let g : ℕ → (ZMod P)ˣ := fun p =>
      if hz : signedRes P p = 0 then 1 else Units.mk0 (signedRes P p) hz
    have hne : ∀ p ∈ S, signedRes P p ≠ 0 := by
      intro p hp hz
      obtain ⟨-, -, ht, -, -⟩ := hdata p hp
      have hp0 : (p : ZMod P) = 0 := by
        unfold signedRes at hz
        split_ifs at hz
        · exact hz
        · exact neg_eq_zero.mp hz
      rw [hp0, orderOf_eq_zero_iff'.mpr] at ht
      · omega
      · intro n hn h0
        rw [zero_pow hn.ne'] at h0
        exact zero_ne_one h0
    have hg : ∀ p ∈ S, (g p : ZMod P) = signedRes P p := by
      intro p hp
      simp only [g, dif_neg (hne p hp), Units.val_mk0]
    have hdm : d ∣ Fintype.card (ZMod P)ˣ := by
      rw [ZMod.card_units, hm]
      exact (Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase hd)).mul_left _
    rw [← IsCyclic.card_orderOf_eq_totient hdm]
    refine Finset.card_le_card_of_injOn g (fun p hp => ?_) (fun p hp p' hp' hpp' => ?_)
    · obtain ⟨hpS, hKd⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, -, ht, h4, -⟩ := hdata p hpS
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← orderOf_units, hg p hpS, orderOf_signedRes hP2' ht h4]
      exact hKd
    · obtain ⟨hpS, -⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp'S, -⟩ := Finset.mem_filter.mp hp'
      obtain ⟨hlt, hp2, -⟩ := hdata p hpS
      obtain ⟨hlt', hp2', -⟩ := hdata p' hp'S
      have := congrArg Units.val hpp'
      rw [hg p hpS, hg p' hp'S] at this
      exact signedRes_inj hP2 hlt hlt' hp2 hp2' this

/-! ## The capacity bound -/

/-- Capacity of the largest prime factor. Let `P` be the largest prime factor of an odd perfect
number `N` and `P - 1 = 2 ^ a · m` with `m` odd. Then
`e_P ≤ Σ_{d ∣ m, d ≠ 1} φ(d) (φ(d) - 1)`. -/
theorem factorization_largest_le_sum_totient (h : OddPerfect N) {P a m : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * m) (hmo : Odd m) :
    N.factorization P ≤ ∑ d ∈ m.divisors.erase 1, d.totient * (d.totient - 1) := by
  obtain ⟨hK, hw, hc⟩ := senders_classes h hP hmax hm hmo
  rw [sum_senders' h hP]
  set S := (N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p))
  set K := fun p : ℕ => oddPart (orderOf (p : ZMod P))
  calc ∑ p ∈ S, padicValNat P (σ 1 (p ^ N.factorization p))
      ≤ ∑ p ∈ S, ((K p).totient - 1) := Finset.sum_le_sum hw
    _ = ∑ d ∈ m.divisors.erase 1, ∑ p ∈ S with K p = d, ((K p).totient - 1) :=
        (Finset.sum_fiberwise_of_maps_to hK _).symm
    _ = ∑ d ∈ m.divisors.erase 1, (S.filter (fun p => K p = d)).card * (d.totient - 1) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2],
          Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ d ∈ m.divisors.erase 1, d.totient * (d.totient - 1) :=
        Finset.sum_le_sum fun d hd => Nat.mul_le_mul_right _ (hc d hd)

/-- Number of senders into the largest prime factor `P` with `P - 1 = 2 ^ a · m`, `m` odd:
at most `m - 1`, since `Σ_{d ∣ m, d ≠ 1} φ(d) = m - 1`. -/
theorem card_senders_largest_le (h : OddPerfect N) {P a m : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * m) (hmo : Odd m) :
    ((N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p))).card ≤
      m - 1 := by
  obtain ⟨hK, -, hc⟩ := senders_classes h hP hmax hm hmo
  rw [Finset.card_eq_sum_card_fiberwise hK]
  have h1 : 1 ∈ m.divisors := Nat.mem_divisors.mpr ⟨one_dvd m, by
    rintro rfl; exact absurd hmo (by decide)⟩
  have hsum := Finset.add_sum_erase m.divisors Nat.totient h1
  rw [Nat.sum_totient, Nat.totient_one] at hsum
  refine (Finset.sum_le_sum hc).trans ?_
  omega

/-- Regression test, the case `m = 1`: the largest prime factor `P` of an odd perfect number
does not have `P - 1 = 2 ^ a`. The capacity sum is empty, so `e_P = 0`. -/
theorem largest_sub_one_odd_part_ne_one (h : OddPerfect N) {P : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (a : ℕ) :
    P - 1 ≠ 2 ^ a := by
  intro ha
  have := factorization_largest_le_sum_totient h hP hmax (m := 1) (a := a)
    (by rw [ha, mul_one]) odd_one
  rw [Nat.divisors_one, Finset.erase_singleton, Finset.sum_empty] at this
  have h0 : N.factorization P ≠ 0 := Finsupp.mem_support_iff.mp hP
  omega

/-- Regression test, the case `m = 3`: if `P - 1 = 2 ^ a · 3` for the largest prime factor `P`,
then `e_P ≤ φ(3) (φ(3) - 1) = 2`. -/
theorem factorization_largest_le_two_of_odd_part_three (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (ha : P - 1 = 2 ^ a * 3) :
    N.factorization P ≤ 2 := by
  have := factorization_largest_le_sum_totient h hP hmax ha (by decide)
  have e : ∑ d ∈ (Nat.divisors 3).erase 1, d.totient * (d.totient - 1) = 2 := by decide
  omega

/-! ## Controls -/

/-- Weight two: `σ(3 ^ 4) = 11 ^ 2`. -/
example : 1 + 3 + 3 ^ 2 + 3 ^ 3 + 3 ^ 4 = 11 ^ 2 := by norm_num

/-- Lifting without `e_p + 1 < P`: `v_13(σ(3 ^ 38)) = 2` while `Φ_3(3) = 13`. -/
example : 13 ^ 2 ∣ (3 ^ 39 - 1) / 2 ∧ ¬ 13 ^ 3 ∣ (3 ^ 39 - 1) / 2 ∧ 3 ^ 2 + 3 + 1 = 13 := by
  norm_num

/-- Without `p < P` the signed map collides: modulo `7`, `-5 ≡ 23 ≡ 2`. -/
example : (7 - 5) % 7 = 23 % 7 := by norm_num

/-- `Φ_30(3) = 8401 > 3 ^ 8`, so the height bound needs `p + 1`. -/
example : (3 : ℕ) ^ 8 < 8401 ∧ 8401 < 4 ^ 8 := by norm_num

/-- A sender of order `2` into a prime that is not the largest: `σ(13) = 14 = 2 · 7`. -/
example : 7 ∣ 1 + 13 := by norm_num

end OddPerfect

#print axioms OddPerfect.cyclotomic_eval_int_pos_lt
#print axioms OddPerfect.padicValNat_pow_orderOf_sub_one_lt_totient
#print axioms OddPerfect.orderOf_neg_of_orderOf_eq_two_mul
#print axioms OddPerfect.sender_largest_data
#print axioms OddPerfect.factorization_largest_le_sum_totient
#print axioms OddPerfect.card_senders_largest_le
#print axioms OddPerfect.largest_sub_one_odd_part_ne_one
#print axioms OddPerfect.factorization_largest_le_two_of_odd_part_three
