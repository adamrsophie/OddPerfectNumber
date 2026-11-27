import OddPerfect.CycloRootCount

/-!
# Two primes whose rows share a large power of one prime

Write `R(x) = ∑ i < l, x ^ i` for a prime `l` and let `d ≠ l` be a prime.

* `PrimeMonomial.card_root_le`: at most `l` integers `z` with `0 < z ≤ d ^ k`, `k ≥ 1`, satisfy
  `z ^ l = 1` modulo `d ^ k`. Such a `z` has `d ^ k ∣ (z - 1) R(z)`, and `d` cannot divide both
  factors, so `z = 1` or `d ^ k ∣ R(z)` (at most `l - 1` integers, by
  `card_filter_pow_dvd_geom_sum_le`).
* `pow_lt_of_common_receiver_power`: let `p < p'` be primes with `d ^ x ∣ R(p)`,
  `d ^ x' ∣ R(p')` and `p ^ A < d ^ x`, `p ^ A < d ^ x'`. If the number of pairs `(i, j)` with
  `i + G j ≤ A` exceeds `l`, then `p ^ G < p'`. Otherwise the pairwise distinct integers
  `p ^ i * p' ^ j`, `i + G j ≤ A`, are all below `d ^ min x x'` and are all `l`th roots of unity
  modulo that power.

No odd perfect number appears in this module. Published method, see below.

Method. The counting argument of `pow_lt_of_common_receiver_power` is that of Lemma 3.1 of
T. Yamada, On finiteness of odd superperfect numbers (arXiv 0803.0437v7); the statement here
uses the region `i + G j ≤ A` in place of the triangle used there.
-/

open Finset

namespace OddPerfect.PrimeMonomial

/-- If `n ∣ R(x)` then `x ^ l = 1` in `ZMod n`. -/
theorem pow_eq_one_of_dvd {n l x : ℕ} (h : n ∣ ∑ i ∈ range l, x ^ i) :
    (x : ZMod n) ^ l = 1 := by
  have h0 : ((∑ i ∈ range l, x ^ i : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at h0
  have h1 := geom_sum_mul (x : ZMod n) l
  rw [h0, zero_mul] at h1
  exact (sub_eq_zero.mp h1.symm)

/-- If the prime `r ≠ l` divides `R(x)` for a prime `l`, then `x ≠ 1` in `ZMod r`. -/
theorem ne_one_of_dvd {r l x : ℕ} (hl : l.Prime) (hr : r.Prime) (hrl : r ≠ l)
    (h : r ∣ ∑ i ∈ range l, x ^ i) : (x : ZMod r) ≠ 1 := by
  intro hx
  have h0 : ((∑ i ∈ range l, x ^ i : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at h0
  rw [hx] at h0
  simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h0
  have hdvd : r ∣ l := (ZMod.natCast_eq_zero_iff _ _).mp h0
  exact hrl ((Nat.prime_dvd_prime_iff_eq hr hl).mp hdvd)

/-- The exponent of `p` in `p ^ i * p' ^ j` for distinct primes `p` and `p'`. -/
theorem factorization_mul_pow {p p' i j : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p') :
    (p ^ i * p' ^ j).factorization p = i := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp'.ne_zero),
    hp.factorization_pow, hp'.factorization_pow]
  simp [Ne.symm hne]

/-- At most `l` integers `z` with `0 < z ≤ d ^ k` satisfy `z ^ l = 1` modulo `d ^ k`. -/
theorem card_root_le {l d k : ℕ} (hl : l.Prime) (hd : d.Prime) (hdl : d ≠ l) (hk : 0 < k) :
    ((Ioc 0 (d ^ k)).filter (fun z : ℕ => (z : ZMod (d ^ k)) ^ l = 1)).card ≤ l := by
  classical
  have hsub : (Ioc 0 (d ^ k)).filter (fun z : ℕ => (z : ZMod (d ^ k)) ^ l = 1) ⊆
      insert 1 ((Ioc 0 (0 + d ^ k)).filter
        (fun z : ℕ => d ^ k ∣ ∑ i ∈ range l, z ^ i)) := by
    intro z hz
    obtain ⟨hzI, hzl⟩ := mem_filter.mp hz
    obtain ⟨hz1, hzk⟩ := mem_Ioc.mp hzI
    have h1 := geom_sum_mul (z : ZMod (d ^ k)) l
    rw [hzl, sub_self] at h1
    have h2 : (((∑ i ∈ range l, z ^ i) * (z - 1) : ℕ) : ZMod (d ^ k)) = 0 := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]
      push_cast
      exact h1
    have h3 : d ^ k ∣ (∑ i ∈ range l, z ^ i) * (z - 1) := (ZMod.natCast_eq_zero_iff _ _).mp h2
    by_cases hdz : d ∣ z - 1
    · have hR : ¬ d ∣ ∑ i ∈ range l, z ^ i := by
        intro hR
        refine ne_one_of_dvd hl hd hdl hR ?_
        have hm : 1 ≡ z [MOD d] := (Nat.modEq_iff_dvd' (by omega)).mpr hdz
        have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
        rw [Nat.cast_one] at this
        exact this.symm
      have hc : Nat.Coprime (d ^ k) (∑ i ∈ range l, z ^ i) :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hd).mpr hR)
      have h4 : d ^ k ∣ z - 1 := hc.dvd_of_dvd_mul_left h3
      have h5 : z - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h4 (by omega)
      rw [show z = 1 by omega]
      exact mem_insert_self _ _
    · have hc : Nat.Coprime (d ^ k) (z - 1) :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hd).mpr hdz)
      rw [mul_comm] at h3
      have h4 : d ^ k ∣ ∑ i ∈ range l, z ^ i := hc.dvd_of_dvd_mul_left h3
      refine mem_insert_of_mem (mem_filter.mpr ⟨?_, h4⟩)
      rw [zero_add]
      exact hzI
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_insert_le _ _
    _ ≤ (l - 1) + 1 := Nat.add_le_add_right (card_filter_pow_dvd_geom_sum_le hl hd hdl hk) 1
    _ = l := Nat.sub_add_cancel hl.one_lt.le

end OddPerfect.PrimeMonomial

namespace OddPerfect

open OddPerfect.PrimeMonomial

/-- Gap between two primes whose rows share a large power of one receiver. Let `l` and `d ≠ l`
be primes and `p < p'` primes with `d ^ x ∣ R(p)`, `d ^ x' ∣ R(p')`, where
`R(y) = ∑ i < l, y ^ i`, and `p ^ A` below both powers. If the number of pairs `(i, j)` with
`i + G j ≤ A` exceeds `l`, then `p ^ G < p'`. Published method, see the module header. -/
theorem pow_lt_of_common_receiver_power {l d x x' p p' A G : ℕ} (hl : l.Prime) (hd : d.Prime)
    (hdl : d ≠ l) (hp : p.Prime) (hp' : p'.Prime) (hlt : p < p')
    (h : d ^ x ∣ ∑ i ∈ Finset.range l, p ^ i) (h' : d ^ x' ∣ ∑ i ∈ Finset.range l, p' ^ i)
    (hx : p ^ A < d ^ x) (hx' : p ^ A < d ^ x')
    (hcount : l < ∑ j ∈ Finset.range (A / G + 1), (A - G * j + 1)) : p ^ G < p' := by
  classical
  by_contra hle
  push Not at hle
  have hpk : p ^ A < d ^ min x x' := by
    rcases le_total x x' with h1 | h1
    · rw [min_eq_left h1]; exact hx
    · rw [min_eq_right h1]; exact hx'
  have hk : 0 < min x x' := by
    rcases Nat.eq_zero_or_pos (min x x') with h0 | h0
    · rw [h0, pow_zero] at hpk
      exact absurd hpk (not_lt.mpr (Nat.one_le_pow _ _ hp.pos))
    · exact h0
  have hM : d ^ min x x' ∣ ∑ i ∈ range l, p ^ i := (pow_dvd_pow d (min_le_left x x')).trans h
  have hM' : d ^ min x x' ∣ ∑ i ∈ range l, p' ^ i :=
    (pow_dvd_pow d (min_le_right x x')).trans h'
  have e1 := pow_eq_one_of_dvd hM
  have e2 := pow_eq_one_of_dvd hM'
  have hSc : ((range (A / G + 1)).sigma (fun j => range (A - G * j + 1))).card =
      ∑ j ∈ range (A / G + 1), (A - G * j + 1) := by
    simp [card_sigma]
  have hinj : Set.InjOn (fun t : (Σ _ : ℕ, ℕ) => p ^ t.2 * p' ^ t.1)
      ((range (A / G + 1)).sigma (fun j => range (A - G * j + 1)) : Set (Σ _ : ℕ, ℕ)) := by
    rintro ⟨j, i⟩ _ ⟨j', i'⟩ _ hf
    have hf' : p ^ i * p' ^ j = p ^ i' * p' ^ j' := hf
    have hne : p ≠ p' := hlt.ne
    have h1 : (p ^ i * p' ^ j).factorization p = (p ^ i' * p' ^ j').factorization p := by
      rw [hf']
    have h2 : (p' ^ j * p ^ i).factorization p' = (p' ^ j' * p ^ i').factorization p' := by
      rw [mul_comm, hf', mul_comm]
    rw [factorization_mul_pow hp hp' hne, factorization_mul_pow hp hp' hne] at h1
    rw [factorization_mul_pow hp' hp hne.symm, factorization_mul_pow hp' hp hne.symm] at h2
    subst h1
    subst h2
    rfl
  have hmaps : Set.MapsTo (fun t : (Σ _ : ℕ, ℕ) => p ^ t.2 * p' ^ t.1)
      ((range (A / G + 1)).sigma (fun j => range (A - G * j + 1)) : Set (Σ _ : ℕ, ℕ))
      ((Ioc 0 (d ^ min x x')).filter (fun z : ℕ => (z : ZMod (d ^ min x x')) ^ l = 1) :
        Set ℕ) := by
    rintro ⟨j, i⟩ ht
    have ht' : j < A / G + 1 ∧ i < A - G * j + 1 := by
      have := mem_sigma.mp (Finset.mem_coe.mp ht)
      exact ⟨mem_range.mp this.1, mem_range.mp this.2⟩
    have hGj : G * j ≤ A :=
      calc G * j ≤ G * (A / G) := Nat.mul_le_mul_left G (by omega)
        _ ≤ A := Nat.mul_div_le A G
    have hz : p ^ i * p' ^ j ≤ p ^ A :=
      calc p ^ i * p' ^ j ≤ p ^ i * (p ^ G) ^ j :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle j)
        _ = p ^ (i + G * j) := by rw [← pow_mul, ← pow_add]
        _ ≤ p ^ A := Nat.pow_le_pow_right hp.pos (by omega)
    refine Finset.mem_coe.mpr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, ?_⟩)
    · exact Nat.mul_pos (pow_pos hp.pos _) (pow_pos hp'.pos _)
    · show p ^ i * p' ^ j ≤ d ^ min x x'
      omega
    show ((p ^ i * p' ^ j : ℕ) : ZMod (d ^ min x x')) ^ l = 1
    push_cast
    have hr : ((p : ZMod (d ^ min x x')) ^ i * (p' : ZMod (d ^ min x x')) ^ j) ^ l =
        ((p : ZMod (d ^ min x x')) ^ l) ^ i * ((p' : ZMod (d ^ min x x')) ^ l) ^ j := by
      ring
    rw [hr, e1, e2, one_pow, one_pow, one_mul]
  have hcard := card_le_card_of_injOn _ hmaps hinj
  have hroot := card_root_le hl hd hdl hk
  omega

end OddPerfect

#print axioms OddPerfect.PrimeMonomial.card_root_le
#print axioms OddPerfect.pow_lt_of_common_receiver_power
