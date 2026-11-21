import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# A square-ratio obstruction for the third cyclotomic polynomial

This elementary subcase is motivated by Question 10 of Ochem and Zelinsky,
arXiv:2607.19746v1. It excludes every positive even exponent difference `2*k` when `k` is at
most the smaller exponent. The polynomial arguments can be composite.
-/

namespace OPNGap

/-- If an odd prime power `q^k > 1` divides the polynomial value at `y ≥ 3`,
multiplication by its square cannot give another value of the polynomial. -/
theorem no_prime_power_square_ratio {x y q k : ℕ} (hy : 3 ≤ y)
    (hq : q.Prime) (hqodd : Odd q) (hk : 0 < k) (hd : q^k ∣ y^2 + y + 1) :
    x^2 + x + 1 ≠ (q^k)^2 * (y^2 + y + 1) := by
  intro h
  let p := q^k
  change x^2 + x + 1 = p^2 * (y^2+y+1) at h
  change p ∣ y^2+y+1 at hd
  have hqp : q ∣ p := dvd_pow_self q hk.ne'
  have ppos : 0 < p := pow_pos hq.pos _
  have hp2 : 2 ≤ p := le_trans hq.two_le (Nat.le_of_dvd ppos hqp)
  have hodd : Odd p := hqodd.pow
  let u := 2*x+1
  let v := 2*y+1
  have hv : 7 ≤ v := by dsimp [v]; omega
  have hs : u^2 + 3 = (p*v)^2 + 3*p^2 := by
    dsimp [u,v]
    nlinarith only [h]
  have hlt : p*v < u := by
    by_contra! hle
    have := Nat.pow_le_pow_left hle 2
    have hsq : 4 ≤ p^2 := Nat.pow_le_pow_left hp2 2
    omega
  obtain ⟨t, hut⟩ := Nat.exists_eq_add_of_le hlt.le
  have htpos : 0 < t := by omega
  have hteven : t % 2 = 0 := by
    have hu : u % 2 = 1 := by dsimp [u]; omega
    have hvmod : v % 2 = 1 := by dsimp [v]; omega
    have hpmod : p % 2 = 1 := by obtain ⟨k,hk⟩ := hodd; omega
    have heq := congrArg (· % 2) hut
    rw [hu, Nat.add_mod (p*v) t, Nat.mul_mod p v, hpmod, hvmod] at heq
    omega
  have ht2 : 2 ≤ t := by omega
  have hbalance : 2*p*v*t + t^2 + 3 = 3*p^2 := by
    rw [hut] at hs
    nlinarith only [hs]
  have hbasic : 2*v*t < 3*p := by
    apply (Nat.mul_lt_mul_left ppos).mp
    nlinarith only [hbalance, Nat.zero_le (t^2)]
  have hvsmall : 4*v < 3*p := by
    nlinarith only [hbasic, Nat.mul_le_mul_left (2*v) ht2]
  have htsmall : 4*t < p := by
    nlinarith only [hbasic, Nat.mul_le_mul_right t hv]
  have hpy := Nat.le_of_dvd (by positivity) hd
  have hsize : 4*p ≤ v^2+3 := by dsimp [v]; nlinarith only [hpy]
  have htv : t < v := by
    by_contra! hvt
    nlinarith only [hsize, hbasic, Nat.mul_le_mul_left v hvt, Nat.pow_le_pow_left hv 2]
  have hsum : v+t < p := by omega
  have hdivv : p ∣ v^2+3 := by
    have heq : v^2+3 = 4*(y^2+y+1) := by dsimp [v]; ring
    rw [heq]
    exact dvd_mul_of_dvd_right hd 4
  have hdivt : p ∣ t^2+3 := by
    have hdleft : p ∣ 2*p*v*t := by exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left p 2) v) t
    have hdright : p ∣ 3*p^2 := dvd_mul_of_dvd_right (dvd_pow_self p (by decide : 2 ≠ 0)) 3
    rw [← hbalance, Nat.add_assoc] at hdright
    exact (Nat.dvd_add_iff_right hdleft).mpr hdright
  have hdiff := Nat.dvd_sub hdivv hdivt
  have heq : (v^2+3) - (t^2+3) = (v-t)*(v+t) := by
    have hsq := Nat.pow_le_pow_left htv.le 2
    have hsqadd : t^2+3 ≤ v^2+3 := by omega
    zify [htv.le, hsqadd]
    ring
  rw [heq] at hdiff
  have hside : p ∣ v-t ∨ p ∣ v+t := by
    by_cases h1 : k = 1
    · have heqp : p = q := by simp [p,h1]
      rw [heqp] at hdiff ⊢
      exact hq.dvd_mul.mp hdiff
    have hd2 : q^2 ∣ p := pow_dvd_pow q (by omega)
    have hqv : ¬q ∣ v := by
      intro hqv
      have hv2 : q^2 ∣ v^2 := pow_dvd_pow_of_dvd hqv 2
      have h3dvd := (Nat.dvd_add_iff_right hv2).mpr (hd2.trans hdivv)
      have hle := Nat.le_of_dvd (by decide : 0 < 3) h3dvd
      have h4 : 4 ≤ q^2 := Nat.pow_le_pow_left hq.two_le 2
      omega
    by_cases hminus : q ∣ v-t
    · left
      have hplus : ¬q ∣ v+t := by
        intro hplus
        have htwo : q ∣ 2*v := by
          rw [show 2*v = (v-t)+(v+t) by omega]
          exact Nat.dvd_add hminus hplus
        rcases hq.dvd_mul.mp htwo with hq2 | hqv'
        · have hqeq : q = 2 := ((Nat.dvd_prime Nat.prime_two).mp hq2).resolve_left hq.ne_one
          rw [hqeq] at hqodd
          obtain ⟨i,hi⟩ := hqodd
          omega
        · exact hqv hqv'
      exact ((hq.coprime_iff_not_dvd.mpr hplus).pow_left k).dvd_mul_right.mp hdiff
    · exact Or.inr (((hq.coprime_iff_not_dvd.mpr hminus).pow_left k).dvd_mul_left.mp hdiff)
  rcases hside with hdminus | hdplus
  · have hle := Nat.le_of_dvd (by omega : 0 < v-t) hdminus
    omega
  · have hle := Nat.le_of_dvd (by omega : 0 < v+t) hdplus
    omega

/-- The gap-two specialization. -/
theorem no_prime_square_ratio {x y p : ℕ} (hy : 3 ≤ y)
    (hp : p.Prime) (hodd : Odd p) (hd : p ∣ y^2 + y + 1) :
    x^2 + x + 1 ≠ p^2 * (y^2 + y + 1) := by
  simpa using no_prime_power_square_ratio (x := x) (k := 1) hy hp hodd (by decide) (by simpa)

/-- The exponent-gap formulation. For a positive even gap `a-b = 2*k`,
any solution in the stated domain must have `k > b`, hence `a > 3*b`. -/
theorem no_even_gap_of_le {x y q r b k : ℕ} (hy : 3 ≤ y)
    (hq : q.Prime) (hodd : Odd q) (hk : 0 < k) (hkb : k ≤ b)
    (hx : x^2+x+1 = q^(b+2*k)*r) (hyval : y^2+y+1 = q^b*r) : False := by
  have hdk : q^k ∣ y^2+y+1 := hyval ▸ dvd_mul_of_dvd_left (pow_dvd_pow q hkb) r
  apply no_prime_power_square_ratio (x := x) hy hq hodd hk hdk
  rw [hx, hyval, pow_add, Nat.mul_comm 2 k, pow_mul]
  ring

end OPNGap

#print axioms OPNGap.no_even_gap_of_le

#print axioms OPNGap.no_prime_power_square_ratio

#print axioms OPNGap.no_prime_square_ratio
