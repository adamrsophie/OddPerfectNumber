import OddPerfect.Cyclotomic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# Primitive prime divisors

Bang's theorem (the case `b = 1` of Zsigmondy's theorem) for bases `a ≥ 3`: for every
`n ≥ 3` some prime `q` has `a` of multiplicative order exactly `n` modulo `q`.

The proof goes through the cyclotomic value `Φ_n(a)`. A prime factor `q` of `Φ_n(a)` not
dividing `n` is primitive. Otherwise every prime factor `q` of `Φ_n(a)` divides `n`, the order
of `a` modulo `q` is the part of `n` prime to `q` (so it divides `q - 1`), which forces a single
such prime; lifting the exponent shows it divides `Φ_n(a)` only once. Then `Φ_n(a) = q`,
contradicting `Φ_n(a) > (a - 1) ^ φ(n) ≥ 2 ^ (q - 1) ≥ q`.

As a consequence, each divisor `d ≥ 3` of `e + 1`, for the exact exponent `e` of a prime `p`
in an odd perfect number `N`, gives a prime factor of `N` congruent to one modulo `d`.
-/

namespace OddPerfect

open ArithmeticFunction Polynomial
open scoped ArithmeticFunction.sigma

/-- If a prime `q` divides the cyclotomic value `Φ_n(a)` with `n ≠ 0`, then the order of `a`
modulo `q` is the part of `n` prime to `q`, and it divides `q - 1`. -/
theorem orderOf_eq_ordCompl_of_dvd_cyclotomic_eval {a q n : ℕ} (hq : q.Prime) (hn : n ≠ 0)
    (hdiv : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    orderOf (a : ZMod q) = ordCompl[q] n ∧ ordCompl[q] n ∣ q - 1 := by
  have : Fact q.Prime := ⟨hq⟩
  set m := ordCompl[q] n with hm
  have hqm : ¬ q ∣ m := Nat.not_dvd_ordCompl hq hn
  have : NeZero (m : ZMod q) := NeZero.of_not_dvd (ZMod q) hqm
  have hroot : IsRoot (cyclotomic (q ^ n.factorization q * m) (ZMod q)) (a : ZMod q) := by
    rw [Nat.ordProj_mul_ordCompl_eq_self]
    rw [IsRoot.def, ← map_cyclotomic_int n (ZMod q), eval_map, ← Int.cast_natCast]
    change eval₂ _ (Int.castRingHom (ZMod q) (a : ℤ)) _ = 0
    rw [eval₂_hom, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdiv
  have hprim := isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hroot
  have hord : orderOf (a : ZMod q) = m := hprim.eq_orderOf.symm
  have hm0 : m ≠ 0 := fun h => hqm (h ▸ dvd_zero q)
  have ha0 : (a : ZMod q) ≠ 0 := by
    intro h
    rw [h, orderOf_eq_zero_iff'.mpr] at hord
    · exact hm0 hord.symm
    · intro k hk h0
      rw [zero_pow hk.ne'] at h0
      exact zero_ne_one h0
  exact ⟨hord, hord ▸ ZMod.orderOf_dvd_card_sub_one ha0⟩

/-- `Φ_n(a) * (a ^ d - 1) ∣ a ^ n - 1` for a proper divisor `d` of `n`, in `ℕ`. -/
private theorem natAbs_cyclotomic_mul_dvd {a d n : ℕ} (ha : 1 ≤ a) (h : d ∈ n.properDivisors) :
    ((cyclotomic n ℤ).eval (a : ℤ)).natAbs * (a ^ d - 1) ∣ a ^ n - 1 := by
  have h1 := map_dvd (evalRingHom (a : ℤ)) (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ h)
  simp only [coe_evalRingHom, eval_mul, eval_sub, eval_pow, eval_X, eval_one] at h1
  have h2 := Int.natAbs_dvd_natAbs.mpr h1
  rw [Int.natAbs_mul, mul_comm] at h2
  have e : ∀ k, ((a : ℤ) ^ k - 1).natAbs = a ^ k - 1 := fun k => by
    have : 1 ≤ a ^ k := Nat.one_le_pow _ _ ha
    have h3 : ((a : ℤ) ^ k - 1) = ((a ^ k - 1 : ℕ) : ℤ) := by push_cast [this]; ring
    rw [h3]; simp
  rwa [e, e] at h2

/-- A prime `q` dividing both `n ≥ 3` and `Φ_n(a)` divides `Φ_n(a)` exactly once. -/
private theorem not_sq_dvd_natAbs_cyclotomic_eval {a q n : ℕ} (ha : 2 ≤ a) (hn : 3 ≤ n)
    (hq : q.Prime) (hqn : q ∣ n) (hdiv : (q : ℤ) ∣ (cyclotomic n ℤ).eval (a : ℤ)) :
    ¬ q ^ 2 ∣ ((cyclotomic n ℤ).eval (a : ℤ)).natAbs := by
  have : Fact q.Prime := ⟨hq⟩
  have hn0 : n ≠ 0 := by omega
  have hq2 := hq.two_le
  obtain ⟨hord, hmq⟩ := orderOf_eq_ordCompl_of_dvd_cyclotomic_eval hq hn0 hdiv
  set F := ((cyclotomic n ℤ).eval (a : ℤ)).natAbs
  set m := ordCompl[q] n
  set k := n.factorization q
  have hk : 0 < k := hq.factorization_pos_of_dvd hn0 hqn
  have hnm : q ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n q
  -- the exponent `n / q`
  have hnq : n / q * q = n := Nat.div_mul_cancel hqn
  have hd1 : 1 ≤ n / q := Nat.div_pos (Nat.le_of_dvd (by omega) hqn) hq.pos
  have hprop : n / q ∈ n.properDivisors :=
    Nat.mem_properDivisors.mpr ⟨Nat.div_dvd_of_dvd hqn, Nat.div_lt_self (by omega) hq.one_lt⟩
  set x := a ^ (n / q) with hx
  have hx1 : 1 < x := Nat.one_lt_pow (by omega) (by omega)
  have hdvd : F * (x - 1) ∣ x ^ q - 1 := by
    have := natAbs_cyclotomic_mul_dvd (by omega : 1 ≤ a) hprop
    have e : a ^ n = x ^ q := by rw [hx, ← pow_mul, hnq]
    rwa [e] at this
  -- `m ∣ n / q`, hence `q ∣ x - 1`
  have hmd : m ∣ n / q := by
    apply Nat.dvd_div_of_mul_dvd
    rw [← hnm]
    exact mul_dvd_mul_right (dvd_pow_self q hk.ne') m
  have hqx : q ∣ x - 1 := by
    have h1 : (a : ZMod q) ^ (n / q) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hord]; exact hmd
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hx1.le, hx]
    push_cast
    rw [h1, sub_self]
  intro hsq
  rcases hq.eq_two_or_odd' with rfl | hodd
  · -- `q = 2`: then `n` is a power of two, at least four
    have hm1 : m = 1 := Nat.dvd_one.mp hmq
    rw [hm1, mul_one] at hnm
    have hk2 : 2 ≤ k := by
      by_contra h
      interval_cases k
      omega
    have h4 : 4 ∣ n := hnm ▸ (pow_dvd_pow 2 hk2)
    set y := a ^ (n / 4) with hy
    have hxy : x = y ^ 2 := by rw [hx, hy, ← pow_mul]; congr 1; omega
    have hxodd : ¬ 2 ∣ x := by omega
    have hyodd : Odd y := by
      rw [hxy] at hxodd
      rcases Nat.even_or_odd y with h | h
      · exact absurd (dvd_pow (even_iff_two_dvd.mp h) two_ne_zero) hxodd
      · exact h
    have hF : F ∣ x + 1 := by
      have e : x ^ 2 - 1 = (x + 1) * (x - 1) := by
        rw [← Nat.sq_sub_sq x 1]
      rw [e] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_right (by omega) hdvd
    have h4' : 4 ∣ y ^ 2 + 1 := hxy ▸ (hsq.trans hF)
    obtain ⟨t, ht⟩ := hyodd
    have : y ^ 2 + 1 = 4 * (t ^ 2 + t) + 2 := by rw [ht]; ring
    omega
  · have hqx' : ¬ q ∣ x := by
      intro h
      have := (Nat.dvd_sub_iff_right (Nat.sub_le x 1) h).mpr hqx
      rw [Nat.sub_sub_self hx1.le] at this
      exact hq.one_lt.ne' (Nat.dvd_one.mp this)
    have hlte := padicValNat.pow_sub_pow (p := q) (x := x) (y := 1) hodd hx1
      (by simpa using hqx) hqx' (n := q) hq.ne_zero
    rw [one_pow, padicValNat_self] at hlte
    have hne : x ^ q - 1 ≠ 0 := by
      have := Nat.one_lt_pow hq.ne_zero hx1; omega
    have h3 : q ^ (2 + padicValNat q (x - 1)) ∣ x ^ q - 1 := by
      rw [pow_add]
      exact (mul_dvd_mul hsq (by rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _)).trans
        hdvd
    have := (padicValNat_dvd_iff_le hne).mp h3
    simp only [Nat.padicValNat_def] at this hlte ⊢
    omega

/-- Bang's theorem for bases at least three: for `n ≥ 3` there is a prime `q` such that
`a` has multiplicative order exactly `n` modulo `q`. -/
theorem exists_prime_orderOf_eq {a n : ℕ} (ha : 3 ≤ a) (hn : 3 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ orderOf (a : ZMod q) = n := by
  by_contra hno
  push Not at hno
  have hn0 : n ≠ 0 := by omega
  set F := ((cyclotomic n ℤ).eval (a : ℤ)).natAbs with hFdef
  have hdivn : ∀ q, q.Prime → q ∣ F → q ∣ n := fun q hq h => by
    by_contra hqn
    exact hno q hq (orderOf_eq_of_dvd_cyclotomic_eval hq (Int.ofNat_dvd_left.mpr h) hqn).1
  have hbig : 2 ^ Nat.totient n < F :=
    lt_of_le_of_lt (Nat.pow_le_pow_left (by omega : 2 ≤ a - 1) _)
      (sub_one_pow_totient_lt_natAbs_cyclotomic_eval (by omega) (by omega))
  have hF1 : F ≠ 1 := by
    have : 0 < 2 ^ Nat.totient n := by positivity
    omega
  have hF0 : F ≠ 0 := Nat.ne_zero_of_lt hbig
  set q := F.minFac
  have hq : q.Prime := Nat.minFac_prime hF1
  have hqF : q ∣ F := Nat.minFac_dvd F
  have hqn := hdivn q hq hqF
  -- every prime factor of `F` is `q`
  have huniq : ∀ {r}, r.Prime → r ∣ F → r = q := by
    intro r hr hrF
    by_contra hrq
    have hrn := hdivn r hr hrF
    have key : ∀ s t, s.Prime → t.Prime → s ∣ F → t ∣ n → s ≠ t → t < s := by
      intro s t hs ht hsF htn hst
      have h1 := (orderOf_eq_ordCompl_of_dvd_cyclotomic_eval hs hn0
        (Int.ofNat_dvd_left.mpr hsF)).2
      have hts : ¬ s ∣ t := fun h => hst ((Nat.prime_dvd_prime_iff_eq hs ht).mp h)
      have h2 := (Nat.dvd_ordCompl_of_dvd_not_dvd htn hts).trans h1
      have := Nat.le_of_dvd (by have := hs.two_le; omega) h2
      have := hs.two_le
      omega
    have := key r q hr hq hrF hqn hrq
    have := key q r hq hr hqF hrn (Ne.symm hrq)
    omega
  have hFq := Nat.eq_prime_pow_of_unique_prime_dvd hF0 huniq
  have hsq := not_sq_dvd_natAbs_cyclotomic_eval (by omega) hn hq hqn (Int.ofNat_dvd_left.mpr hqF)
  have hFle : F ≤ q := by
    set e := F.primeFactorsList.length
    have he : e ≤ 1 := by
      by_contra h
      apply hsq
      change q ^ 2 ∣ F
      rw [hFq]
      exact pow_dvd_pow q (by omega)
    rw [hFq]
    calc q ^ e ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos he
      _ = q := pow_one q
  have htot : q - 1 ≤ Nat.totient n := by
    have h := Nat.totient_dvd_of_dvd hqn
    rw [Nat.totient_prime hq] at h
    exact Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) h
  have h1 : q - 1 < 2 ^ (q - 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (q - 1) ≤ 2 ^ Nat.totient n := Nat.pow_le_pow_right (by norm_num) htot
  omega

/-- A primitive prime factor of the component divisor sum. -/
theorem exists_prime_dvd_sigma_orderOf_eq {p e d : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hd3 : 3 ≤ d) (hd : d ∣ e + 1) :
    ∃ q : ℕ, q.Prime ∧ q ∣ σ 1 (p ^ e) ∧ orderOf (p : ZMod q) = d ∧ q % d = 1 := by
  obtain ⟨q, hq, ho⟩ := exists_prime_orderOf_eq hp3 hd3
  have : Fact q.Prime := ⟨hq⟩
  have hp0 : (p : ZMod q) ≠ 0 := by
    intro h
    rw [h, orderOf_eq_zero_iff'.mpr] at ho
    · omega
    · intro k hk h0
      rw [zero_pow hk.ne'] at h0
      exact zero_ne_one h0
  have hpq : p ≠ q := by
    rintro rfl
    exact hp0 (ZMod.natCast_self p)
  refine ⟨q, hq, dvd_sigma_prime_pow_of_orderOf_dvd hp hq hpq (by omega) (ho ▸ hd), ho, ?_⟩
  have hdq : d ∣ q - 1 := ho ▸ ZMod.orderOf_dvd_card_sub_one hp0
  have := (Nat.modEq_iff_dvd' hq.one_lt.le).mpr hdq
  rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < d)] at this
  exact this.symm

/-- In an odd perfect number, every divisor `d ≥ 3` of `e + 1`, for the exact exponent `e`
of a prime `p`, yields a prime factor of `N` congruent to one modulo `d`. -/
theorem exists_primeFactor_modEq_one {N p d : ℕ} (h : OddPerfect N)
    (hp : p ∈ N.primeFactors) (hd3 : 3 ≤ d) (hd : d ∣ N.factorization p + 1) :
    ∃ q ∈ N.primeFactors, orderOf (p : ZMod q) = d ∧ q % d = 1 := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨q, hq, hdiv, ho, hmod⟩ :=
    exists_prime_dvd_sigma_orderOf_eq hpp (by have := hpp.two_le; omega) hd3 hd
  have hq2 : q ≠ 2 := by
    rintro rfl
    rw [Nat.mod_eq_of_lt (by omega : 2 < d)] at hmod
    omega
  exact ⟨q, Nat.mem_primeFactors.mpr ⟨hq, OPNStarter.force_prime h.perfect hpp rfl hq hq2 hdiv,
    h.ne_zero⟩, ho, hmod⟩

end OddPerfect

#print axioms OddPerfect.orderOf_eq_ordCompl_of_dvd_cyclotomic_eval
#print axioms OddPerfect.exists_prime_orderOf_eq
#print axioms OddPerfect.exists_prime_dvd_sigma_orderOf_eq
#print axioms OddPerfect.exists_primeFactor_modEq_one
