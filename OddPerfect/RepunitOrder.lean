import Mathlib

/-!
# The order of the base of a geometric sum that is almost a prime power

Let `p` be an odd prime and `1 + w + ... + w ^ (m - 1) = k * p ^ s` with `w ≥ 2`, `m ≥ 1`,
`s ≥ 1` and `k < p`. Then `w` has order exactly `m` modulo `p`; in particular `p` does not
divide `w - 1` and `m` divides `p - 1`.

This is Lemma 2.1 of J. Zhao and Y. Chen (Front. Math. 20 (2025), no. 4, 795 to 827), stated
there with `m ≥ 2` and for the quotient `(w ^ m - 1) / (w - 1)`. Known mathematics. With
`w` a prime `q` and `m = e + 1` the sum is the divisor sum of `q ^ e`, so the lemma describes
the components `σ(q ^ e)` that are a small multiple of a prime power.

Proof: let `d` be the order of `w` modulo `p` and `n = m / d`. The sum factors as the sum of
length `d` times `F = 1 + v + ... + v ^ (n - 1)` with `v = w ^ d ≡ 1 (mod p)`, so `v > p`.
Suppose `n ≥ 2`. The part `c` of `F` prime to `p` divides `k`, so `c < p`, and lifting the
exponent gives `v_p(F) = v_p(n)`. If `p` does not divide `n` then `F = c < p`, against
`F ≥ v`. If `p` divides `n` then `F ≤ n * c ≤ p * (n - 1) < v * (n - 1) ≤ F`.
-/

namespace OddPerfect

open scoped BigOperators

/-- The sum of the first `n` powers of `w`, starting at exponent zero. -/
private def geomSum (w n : ℕ) : ℕ := ∑ i ∈ Finset.range n, w ^ i

/-- Each term of a natural geometric sum is at most the sum. -/
private theorem pow_le_geomSum {w i n : ℕ} (hi : i < n) : w ^ i ≤ geomSum w n := by
  unfold geomSum
  exact Finset.single_le_sum (f := fun j : ℕ => w ^ j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hi)

/-- Multiplying the geometric sum by `w - 1` gives `w ^ n - 1`. -/
private theorem geomSum_mul_sub_one {w : ℕ} (hw : 1 ≤ w) (n : ℕ) :
    geomSum w n * (w - 1) = w ^ n - 1 :=
  geom_sum_mul_of_one_le hw n

/-- A geometric sum of length `d * n` factors into sums of lengths `n` and `d`. -/
private theorem geomSum_mul_length {w : ℕ} (hw : 1 < w) (d n : ℕ) :
    geomSum w (d * n) = geomSum (w ^ d) n * geomSum w d := by
  have hv : 1 ≤ w ^ d := Nat.one_le_pow d w (by omega)
  apply Nat.mul_right_cancel (by omega : 0 < w - 1)
  calc
    geomSum w (d * n) * (w - 1) = (w ^ d) ^ n - 1 := by
      rw [geomSum_mul_sub_one hw.le, pow_mul]
    _ = (geomSum (w ^ d) n * geomSum w d) * (w - 1) := by
      rw [mul_assoc, geomSum_mul_sub_one hw.le, geomSum_mul_sub_one hv]

/-- A positive natural number represents one modulo `p` exactly when `p` divides its predecessor. -/
private theorem natCast_eq_one_iff_dvd_sub_one {p a : ℕ} (ha : 1 ≤ a) :
    (a : ZMod p) = 1 ↔ p ∣ a - 1 := by
  rw [← Nat.cast_one (R := ZMod p)]
  exact eq_comm.trans ((ZMod.natCast_eq_natCast_iff 1 a p).trans (Nat.modEq_iff_dvd' ha))

/-- If a geometric sum is a multiple of a positive power of `p`, then `p` divides the sum. -/
private theorem dvd_geomSum_of_eq_mul_prime_pow {w m p k s : ℕ} (hs : 1 ≤ s)
    (h : geomSum w m = k * p ^ s) : p ∣ geomSum w m := by
  rw [h]
  exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega : s ≠ 0)) k

/-- A positive power of `p` dividing the geometric sum forces `w ^ m` to be one modulo `p`. -/
private theorem pow_eq_one_of_geomSum_eq_mul_prime_pow {w m p k s : ℕ} (hw : 2 ≤ w)
    (hs : 1 ≤ s) (h : geomSum w m = k * p ^ s) : (w : ZMod p) ^ m = 1 := by
  have hdvd : p ∣ w ^ m - 1 := by
    rw [← geomSum_mul_sub_one (by omega : 1 ≤ w)]
    exact dvd_mul_of_dvd_left (dvd_geomSum_of_eq_mul_prime_pow hs h) (w - 1)
  rw [← Nat.cast_pow]
  exact (natCast_eq_one_iff_dvd_sub_one (Nat.one_le_pow m w (by omega))).2 hdvd

/-- A geometric sum of length at least two in a base above one congruent to one modulo an odd
prime `p` cannot divide `k * p ^ s` when `0 < k < p`. -/
private theorem geomSum_succ_not_dvd_mul_prime_pow {p v n k s : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hv : 1 < v) (hvp : p ∣ v - 1) (hn : 0 < n) (hk0 : 0 < k) (hk : k < p) :
    ¬ geomSum v (n + 1) ∣ k * p ^ s := by
  intro hdiv
  have : Fact p.Prime := ⟨hp⟩
  have hvsub : 0 < v - 1 := by omega
  have hpv : p < v := by
    have := Nat.le_of_dvd hvsub hvp
    omega
  have hvnd : ¬ p ∣ v := by
    intro hd
    exact hp.not_dvd_one ((Nat.dvd_sub_iff_right hv.le hd).1 hvp)
  let sum := geomSum v (n + 1)
  let j := padicValNat p (n + 1)
  let c := Nat.divMaxPow sum p
  have hlower : v * n ≤ sum :=
    (Nat.mul_le_pow (by omega : v ≠ 1) n).trans (pow_le_geomSum (Nat.lt_succ_self n))
  have hsum0 : sum ≠ 0 := by
    have hpos : 0 < v * n := Nat.mul_pos (by omega) hn
    omega
  have hval : padicValNat p sum = j := by
    have hlte :
        padicValNat p (v ^ (n + 1) - 1) = padicValNat p (v - 1) + j := by
      simpa only [one_pow] using
        padicValNat.pow_sub_pow (hp.odd_of_ne_two hp2) hv hvp hvnd (Nat.succ_ne_zero n)
    rw [← geomSum_mul_sub_one hv.le,
      padicValNat.mul hsum0 (Nat.ne_of_gt hvsub)] at hlte
    change padicValNat p sum + padicValNat p (v - 1) = padicValNat p (v - 1) + j at hlte
    omega
  have hsum : sum = p ^ j * c := by
    have hfactor := (Nat.pow_padicValNat_mul_divMaxPow p sum).symm
    rw [hval] at hfactor
    exact hfactor
  have hcsum : c ∣ sum := by
    rw [hsum]
    exact dvd_mul_left c (p ^ j)
  have hcop : c.Coprime (p ^ s) := hp.coprime_pow_of_not_dvd (Nat.not_dvd_divMaxPow hp.one_lt hsum0)
  have hck : c ∣ k := hcop.dvd_of_dvd_mul_right (hcsum.trans hdiv)
  have hcp : c < p := (Nat.le_of_dvd hk0 hck).trans_lt hk
  by_cases hj : j = 0
  · have hvc : v ≤ c := calc
      v = v * 1 := (mul_one v).symm
      _ ≤ v * n := Nat.mul_le_mul_left v hn
      _ ≤ sum := hlower
      _ = c := by rw [hsum, hj, pow_zero, one_mul]
    omega
  · have hjdvd : p ^ j ∣ n + 1 := pow_padicValNat_dvd (p := p) (n := n + 1)
    have hjle : p ^ j ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) hjdvd
    have hpn : p ≤ n + 1 := (Nat.le_of_dvd (pow_pos hp.pos j) (dvd_pow_self p hj)).trans hjle
    have hcn : c ≤ n := by omega
    have hsmall : sum < v * n := calc
      sum = p ^ j * c := hsum
      _ ≤ (n + 1) * c := Nat.mul_le_mul_right c hjle
      _ = c * n + c := by rw [add_mul, one_mul, mul_comm n c]
      _ ≤ c * n + n := Nat.add_le_add_left hcn _
      _ = (c + 1) * n := by rw [add_mul, one_mul]
      _ ≤ p * n := Nat.mul_le_mul_right n (by omega)
      _ < v * n := Nat.mul_lt_mul_of_pos_right hpv hn
    exact (not_lt_of_ge hlower) hsmall

/-- If `1 + w + ... + w^(m-1) = k * p^s` with `p` an odd prime, `s ≥ 1` and `k < p`, then `w`
has order exactly `m` modulo `p`. -/
theorem orderOf_eq_of_geom_sum_eq_mul_prime_pow {w m p k s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hw : 2 ≤ w) (hm : m ≠ 0) (hs : 1 ≤ s) (hk : k < p)
    (h : ∑ i ∈ Finset.range m, w ^ i = k * p ^ s) :
    orderOf (w : ZMod p) = m := by
  change geomSum w m = k * p ^ s at h
  have hpow := pow_eq_one_of_geomSum_eq_mul_prime_pow hw hs h
  have hk0 : 0 < k := by
    have hone : 1 ≤ geomSum w m := by
      simpa only [pow_zero] using (pow_le_geomSum (w := w) (i := 0) (Nat.pos_of_ne_zero hm))
    by_contra hnonpos
    have hkzero : k = 0 := by omega
    rw [h, hkzero, zero_mul] at hone
    omega
  let d := orderOf (w : ZMod p)
  obtain ⟨n, hn⟩ : d ∣ m := orderOf_dvd_of_pow_eq_one hpow
  have hd0 : d ≠ 0 := by
    intro hzero
    apply hm
    rw [hn, hzero, zero_mul]
  have hn0 : n ≠ 0 := by
    intro hzero
    apply hm
    rw [hn, hzero, mul_zero]
  have hn1 : n = 1 := by
    by_contra hne
    have hv : 1 < w ^ d := by
      have hle : w ^ 1 ≤ w ^ d := Nat.pow_le_pow_right (by omega) (by omega)
      rw [pow_one] at hle
      omega
    have hv1 : ((w ^ d : ℕ) : ZMod p) = 1 := by
      rw [Nat.cast_pow]
      exact pow_orderOf_eq_one (w : ZMod p)
    have hvp : p ∣ w ^ d - 1 := (natCast_eq_one_iff_dvd_sub_one hv.le).1 hv1
    have hdiv : geomSum (w ^ d) n ∣ k * p ^ s := by
      rw [← h, hn, geomSum_mul_length (by omega : 1 < w)]
      exact dvd_mul_right _ _
    have hr : n = (n - 1) + 1 := by omega
    have hpos : 0 < n - 1 := by omega
    rw [hr] at hdiv
    exact geomSum_succ_not_dvd_mul_prime_pow hp hp2 hv hvp hpos hk0 hk hdiv
  change d = m
  rw [hn, hn1, mul_one]

/-- Under the geometric sum hypothesis, `p` does not divide `w - 1`. -/
theorem not_dvd_sub_one_of_geom_sum_eq_mul_prime_pow {w m p k s : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hw : 2 ≤ w) (hm : m ≠ 0) (hs : 1 ≤ s) (hk : k < p)
    (h : ∑ i ∈ Finset.range m, w ^ i = k * p ^ s) : ¬ p ∣ w - 1 := by
  intro hdvd
  have hw1 : (w : ZMod p) = 1 := (natCast_eq_one_iff_dvd_sub_one (by omega : 1 ≤ w)).2 hdvd
  have hord := orderOf_eq_of_geom_sum_eq_mul_prime_pow hp hp2 hw hm hs hk h
  rw [hw1, orderOf_one] at hord
  change geomSum w m = k * p ^ s at h
  have hsum := dvd_geomSum_of_eq_mul_prime_pow hs h
  rw [← hord] at hsum
  exact hp.not_dvd_one (by simpa only [geomSum, Finset.sum_range_one, pow_zero] using hsum)

/-- Under the geometric sum hypothesis, its length `m` divides `p - 1`. -/
theorem dvd_sub_one_of_geom_sum_eq_mul_prime_pow {w m p k s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hw : 2 ≤ w) (hm : m ≠ 0) (hs : 1 ≤ s) (hk : k < p)
    (h : ∑ i ∈ Finset.range m, w ^ i = k * p ^ s) : m ∣ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hord := orderOf_eq_of_geom_sum_eq_mul_prime_pow hp hp2 hw hm hs hk h
  change geomSum w m = k * p ^ s at h
  have hpow := pow_eq_one_of_geomSum_eq_mul_prime_pow hw hs h
  have hw0 : (w : ZMod p) ≠ 0 := by
    intro hz
    rw [hz, zero_pow hm] at hpow
    exact zero_ne_one hpow
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one hw0

#print axioms orderOf_eq_of_geom_sum_eq_mul_prime_pow
#print axioms not_dvd_sub_one_of_geom_sum_eq_mul_prime_pow
#print axioms dvd_sub_one_of_geom_sum_eq_mul_prime_pow

end OddPerfect
