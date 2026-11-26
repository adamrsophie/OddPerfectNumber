import Mathlib

/-!
# Roots of a prime length geometric sum modulo a prime power

Write `R_l(x) = ∑ i < l, x ^ i` for a prime `l` and let `r ≠ l` be a prime.

* `card_filter_pow_dvd_geom_sum_le`: at most `l - 1` integers of an interval of length `r ^ k`
  satisfy `r ^ k ∣ R_l(x)`. Modulo `r` such an `x` is an `l`th root of unity other than `1`
  (at most `l - 1` residues), and two such integers congruent modulo `r` are congruent modulo
  `r ^ k`.
* `pow_lt_of_geom_sum_eq_prime_pow`: if `R_l(p₁)` and `R_l(p₂)` are powers of `r` for primes
  `p₁ < p₂`, then `p₁ ^ (l - 1) < p₂`. The powers `p₁ ^ i`, `i < l`, are all the `l`th roots of
  unity modulo `r`, so `p₂` is congruent to one of them modulo `R_l(p₁)`, and it is not equal
  to it.

Restricted result; no published source was checked; novelty not verified.
-/

open Finset

namespace OddPerfect

/-- If `n ∣ R_l(x)` then `x ^ l = 1` in `ZMod n`. -/
private theorem crc_pow_eq_one {n l x : ℕ} (h : n ∣ ∑ i ∈ range l, x ^ i) :
    (x : ZMod n) ^ l = 1 := by
  have h0 : ((∑ i ∈ range l, x ^ i : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at h0
  have h1 := geom_sum_mul (x : ZMod n) l
  rw [h0, zero_mul] at h1
  exact (sub_eq_zero.mp h1.symm)

/-- If `n ∣ R_l(x)` then `x ^ l ≡ 1 (mod n)`. -/
private theorem crc_pow_modEq_one {n l x : ℕ} (h : n ∣ ∑ i ∈ range l, x ^ i) :
    x ^ l ≡ 1 [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact crc_pow_eq_one h

/-- If the prime `r` divides `R_l(x)` with `0 < l`, then `r ∤ x`. -/
private theorem crc_not_dvd {r l x : ℕ} (hr : r.Prime) (hl : 0 < l)
    (h : r ∣ ∑ i ∈ range l, x ^ i) : ¬ r ∣ x := by
  intro hx
  have h0 : ((∑ i ∈ range l, x ^ i : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  have hx0 : (x : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hx
  push_cast at h0
  have : Fact r.Prime := ⟨hr⟩
  rw [hx0, ← Nat.succ_pred_eq_of_pos hl, sum_range_succ'] at h0
  simp at h0

/-- If the prime `r ≠ l` divides `R_l(x)` for a prime `l`, then `x ≠ 1` in `ZMod r`. -/
private theorem crc_ne_one {r l x : ℕ} (hl : l.Prime) (hr : r.Prime) (hrl : r ≠ l)
    (h : r ∣ ∑ i ∈ range l, x ^ i) : (x : ZMod r) ≠ 1 := by
  intro hx
  have h0 : ((∑ i ∈ range l, x ^ i : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at h0
  rw [hx] at h0
  simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h0
  have hdvd : r ∣ l := (ZMod.natCast_eq_zero_iff _ _).mp h0
  exact hrl ((Nat.prime_dvd_prime_iff_eq hr hl).mp hdvd)

/-- Lifting. Let `P` be prime with `P ∤ d` and `P ∤ X`, `X ≡ Y (mod P)` and
`X ^ d ≡ Y ^ d (mod P ^ j)`. Then `X ≡ Y (mod P ^ j)`. -/
private theorem crc_modEq_of_pow_modEq {P d j X Y : ℕ} (hP : P.Prime) (hPd : ¬ P ∣ d)
    (hPX : ¬ P ∣ X) (hXY : X ≡ Y [MOD P]) (hpow : X ^ d ≡ Y ^ d [MOD P ^ j]) :
    X ≡ Y [MOD P ^ j] := by
  have : Fact P.Prime := ⟨hP⟩
  rw [Nat.modEq_iff_dvd] at hpow ⊢
  have hfac := geom_sum₂_mul (Y : ℤ) (X : ℤ) d
  set S : ℤ := ∑ i ∈ range d, (Y : ℤ) ^ i * (X : ℤ) ^ (d - 1 - i) with hSdef
  have hS : ¬ (P : ℤ) ∣ S := by
    intro h
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd S P).mpr h
    have hxy : (Y : ZMod P) = (X : ZMod P) :=
      ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hXY).symm
    rw [hSdef] at h0
    push_cast at h0
    rw [hxy] at h0
    have hsum : ∑ i ∈ range d, (X : ZMod P) ^ i * (X : ZMod P) ^ (d - 1 - i) =
        (d : ZMod P) * (X : ZMod P) ^ (d - 1) := by
      rw [Finset.sum_congr rfl (g := fun _ => (X : ZMod P) ^ (d - 1)), sum_const, card_range,
        nsmul_eq_mul]
      intro i hi
      rw [← pow_add]
      congr 1
      have := mem_range.mp hi
      omega
    rw [hsum] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hPd ((ZMod.natCast_eq_zero_iff _ _).mp h1)
    · exact hPX ((ZMod.natCast_eq_zero_iff _ _).mp (by
        by_contra hx0
        exact pow_ne_zero _ hx0 h1))
  have hPj : IsCoprime ((P : ℤ) ^ j) S :=
    (((Nat.prime_iff_prime_int.mp hP).coprime_iff_not_dvd).mpr hS).pow_left
  push_cast at hpow ⊢
  rw [← hfac] at hpow
  exact hPj.dvd_of_dvd_mul_left hpow

/-- Two roots of `R_l` modulo `r ^ k` that are congruent modulo `r` are congruent modulo
`r ^ k`. -/
private theorem crc_lift {l r k x y : ℕ} (hl : l.Prime) (hr : r.Prime) (hrl : r ≠ l)
    (hk : 0 < k) (hx : r ^ k ∣ ∑ i ∈ range l, x ^ i) (hy : r ^ k ∣ ∑ i ∈ range l, y ^ i)
    (hxy : x ≡ y [MOD r]) : x ≡ y [MOD r ^ k] := by
  have hrx : r ∣ ∑ i ∈ range l, x ^ i := (dvd_pow_self r hk.ne').trans hx
  refine crc_modEq_of_pow_modEq hr ?_ (crc_not_dvd hr hl.pos hrx) hxy
    ((crc_pow_modEq_one hx).trans (crc_pow_modEq_one hy).symm)
  intro h
  exact hrl ((Nat.prime_dvd_prime_iff_eq hr hl).mp h)

/-- At most `l - 1` integers of an interval of length `r ^ k` have `r ^ k ∣ R_l(x)`. -/
theorem card_filter_pow_dvd_geom_sum_le {l r k a : ℕ} (hl : l.Prime) (hr : r.Prime)
    (hrl : r ≠ l) (hk : 0 < k) :
    ((Finset.Ioc a (a + r ^ k)).filter
      (fun x => r ^ k ∣ ∑ i ∈ Finset.range l, x ^ i)).card ≤ l - 1 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  set T : Finset (ZMod r) := (Polynomial.nthRoots l (1 : ZMod r)).toFinset.erase 1 with hT
  have hTcard : T.card ≤ l - 1 := by
    have h1 : (1 : ZMod r) ∈ (Polynomial.nthRoots l (1 : ZMod r)).toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hl.pos, one_pow]
    rw [hT, card_erase_of_mem h1]
    have := (Multiset.toFinset_card_le (Polynomial.nthRoots l (1 : ZMod r))).trans
      (Polynomial.card_nthRoots l (1 : ZMod r))
    omega
  refine le_trans (card_le_card_of_injOn (fun x : ℕ => (x : ZMod r)) ?_ ?_) hTcard
  · intro x hx
    have hx' := (mem_filter.mp (Finset.mem_coe.mp hx)).2
    have hrx : r ∣ ∑ i ∈ range l, x ^ i := (dvd_pow_self r hk.ne').trans hx'
    simp only [hT, Finset.mem_coe, mem_erase, Multiset.mem_toFinset,
      Polynomial.mem_nthRoots hl.pos]
    exact ⟨crc_ne_one hl hr hrl hrx, crc_pow_eq_one hrx⟩
  · intro x hx y hy hxy
    have hx' := mem_filter.mp (Finset.mem_coe.mp hx)
    have hy' := mem_filter.mp (Finset.mem_coe.mp hy)
    have hmod : x ≡ y [MOD r] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hxy
    have hk' := crc_lift hl hr hrl hk hx'.2 hy'.2 hmod
    have hxI := mem_Ioc.mp hx'.1
    have hyI := mem_Ioc.mp hy'.1
    rcases le_total x y with hle | hle
    · have hd := (Nat.modEq_iff_dvd' hle).mp hk'
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
    · have hd := (Nat.modEq_iff_dvd' hle).mp hk'.symm
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega

/-- In an integral domain, a list of `n` distinct `n`th roots of unity contains every `n`th
root of unity. -/
private theorem mem_of_pow_eq_one_of_nodup' {K : Type*} [CommRing K] [IsDomain K] {n : ℕ}
    (hn : 0 < n) {L : List K} (hL : L.Nodup) (hlen : L.length = n)
    (hroot : ∀ x ∈ L, x ^ n = 1) {y : K} (hy : y ^ n = 1) : y ∈ L := by
  by_contra hyL
  have hnd : (y :: L).Nodup := List.nodup_cons.mpr ⟨hyL, hL⟩
  have hle : ((y :: L : List K) : Multiset K) ≤ Polynomial.nthRoots n (1 : K) := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr hnd)]
    intro x hx
    rw [Polynomial.mem_nthRoots hn]
    rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx
    · exact hy
    · exact hroot x hx
  have h1 := Multiset.card_le_card hle
  have h2 := Polynomial.card_nthRoots n (1 : K)
  rw [Multiset.coe_card, List.length_cons, hlen] at h1
  omega

/-- `R_l` is strictly increasing for `2 ≤ l`. -/
private theorem crc_geom_lt {l x y : ℕ} (hl : 2 ≤ l) (hxy : x < y) :
    ∑ i ∈ range l, x ^ i < ∑ i ∈ range l, y ^ i := by
  refine sum_lt_sum (fun i _ => Nat.pow_le_pow_left hxy.le i) ⟨1, mem_range.mpr hl, ?_⟩
  simpa using hxy

/-- Two primes whose rows of length `l` are powers of the same prime: the larger exceeds the
`(l - 1)`st power of the smaller. -/
theorem pow_lt_of_geom_sum_eq_prime_pow {l r p₁ p₂ b₁ b₂ : ℕ} (hl : l.Prime) (hr : r.Prime)
    (hrl : r ≠ l) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (h12 : p₁ < p₂)
    (h₁ : ∑ i ∈ Finset.range l, p₁ ^ i = r ^ b₁)
    (h₂ : ∑ i ∈ Finset.range l, p₂ ^ i = r ^ b₂) : p₁ ^ (l - 1) < p₂ := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact l.Prime := ⟨hl⟩
  have hl2 := hl.two_le
  have hr1 := hr.one_lt
  -- `p₁ ^ (l - 1) < R_l(p₁) = r ^ b₁`
  have hbig : p₁ ^ (l - 1) < r ^ b₁ := by
    rw [← h₁]
    have hl' : l = (l - 1) + 1 := by omega
    have hsplit := sum_range_succ (fun i => p₁ ^ i) (l - 1)
    rw [← hl'] at hsplit
    rw [hsplit]
    have : 0 < ∑ i ∈ range (l - 1), p₁ ^ i :=
      sum_pos (fun i _ => pow_pos hp₁.pos i) ⟨0, mem_range.mpr (by omega)⟩
    omega
  have hb1 : 0 < b₁ := by
    rcases Nat.eq_zero_or_pos b₁ with h0 | h0
    · rw [h0, pow_zero] at hbig
      exact absurd hbig (by have := Nat.one_le_pow (l - 1) p₁ hp₁.pos; omega)
    · exact h0
  -- `r ^ b₁ ∣ R_l(p₂)`
  have hb12 : b₁ < b₂ := by
    have := crc_geom_lt hl2 h12
    rw [h₁, h₂] at this
    exact (pow_lt_pow_iff_right₀ hr1).mp this
  have hd₁ : r ^ b₁ ∣ ∑ i ∈ range l, p₁ ^ i := h₁ ▸ dvd_rfl
  have hd₂ : r ^ b₁ ∣ ∑ i ∈ range l, p₂ ^ i := h₂ ▸ pow_dvd_pow r hb12.le
  have hr₁ : r ∣ ∑ i ∈ range l, p₁ ^ i := (dvd_pow_self r hb1.ne').trans hd₁
  have hr₂ : r ∣ ∑ i ∈ range l, p₂ ^ i := (dvd_pow_self r hb1.ne').trans hd₂
  -- the powers of `p₁` are all the `l`th roots of unity modulo `r`
  have hord : orderOf (p₁ : ZMod r) = l :=
    orderOf_eq_prime (crc_pow_eq_one hr₁) (crc_ne_one hl hr hrl hr₁)
  set L : List (ZMod r) := (List.range l).map (fun i => (p₁ : ZMod r) ^ i) with hL
  have hLnd : L.Nodup := by
    refine List.Nodup.map_on ?_ (List.nodup_range)
    intro i hi j hj hij
    have hi' : i ∈ Set.Iio (orderOf (p₁ : ZMod r)) := by
      rw [hord]; exact List.mem_range.mp hi
    have hj' : j ∈ Set.Iio (orderOf (p₁ : ZMod r)) := by
      rw [hord]; exact List.mem_range.mp hj
    exact pow_injOn_Iio_orderOf hi' hj' hij
  have hLlen : L.length = l := by simp [hL]
  have hLroot : ∀ z ∈ L, z ^ l = 1 := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
    rw [← pow_mul, mul_comm, pow_mul, crc_pow_eq_one hr₁, one_pow]
  have hmem := mem_of_pow_eq_one_of_nodup' hl.pos hLnd hLlen hLroot (crc_pow_eq_one hr₂)
  obtain ⟨i, hi, hieq⟩ := List.mem_map.mp hmem
  have hi' : i < l := List.mem_range.mp hi
  -- lift the congruence `p₁ ^ i ≡ p₂` to modulus `r ^ b₁`
  have hmodr : p₁ ^ i ≡ p₂ [MOD r] := by
    rw [← ZMod.natCast_eq_natCast_iff]; push_cast; exact hieq
  have hrl' : ¬ r ∣ l := fun h => hrl ((Nat.prime_dvd_prime_iff_eq hr hl).mp h)
  have hrp : ¬ r ∣ p₁ ^ i := fun h => crc_not_dvd hr hl.pos hr₁ (hr.dvd_of_dvd_pow h)
  have hpow : (p₁ ^ i) ^ l ≡ p₂ ^ l [MOD r ^ b₁] := by
    have e1 : (p₁ ^ i) ^ l ≡ 1 [MOD r ^ b₁] := by
      rw [← pow_mul, mul_comm, pow_mul]
      simpa using (crc_pow_modEq_one hd₁).pow i
    exact e1.trans (crc_pow_modEq_one hd₂).symm
  have hlift := crc_modEq_of_pow_modEq hr hrl' hrp hmodr hpow
  have hpi : p₁ ^ i ≤ p₁ ^ (l - 1) := Nat.pow_le_pow_right hp₁.pos (by omega)
  have hmod2 : p₂ % r ^ b₁ = p₁ ^ i := by
    rw [← hlift, Nat.mod_eq_of_lt (by omega)]
  have hdiv := Nat.div_add_mod p₂ (r ^ b₁)
  rw [hmod2] at hdiv
  rcases Nat.eq_zero_or_pos (p₂ / r ^ b₁) with h0 | h0
  · exfalso
    rw [h0, mul_zero, zero_add] at hdiv
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · rw [hi0, pow_zero] at hdiv
      exact hp₂.one_lt.ne hdiv
    · have hdvd : p₁ ∣ p₂ := hdiv ▸ dvd_pow_self p₁ hi0.ne'
      exact h12.ne ((Nat.prime_dvd_prime_iff_eq hp₁ hp₂).mp hdvd)
  · have : r ^ b₁ ≤ r ^ b₁ * (p₂ / r ^ b₁) := Nat.le_mul_of_pos_right _ h0
    omega

end OddPerfect

#print axioms OddPerfect.card_filter_pow_dvd_geom_sum_le
#print axioms OddPerfect.pow_lt_of_geom_sum_eq_prime_pow
