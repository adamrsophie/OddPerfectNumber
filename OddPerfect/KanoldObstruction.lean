import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Kanold's obstruction for a pair of prime power equations

Let `G p X = 1 + X + ... + X ^ (p - 1)`; for prime `p` this is the `p`-th cyclotomic
polynomial evaluated at `X`. We prove that for an odd prime `p`, primes `r` and `s`, and
positive exponents `a` and `b`, the system

* `G p (r ^ p ^ u) = p * s ^ a`,
* `G p (s ^ p ^ v) = p * r ^ b`

has no solution. This is known mathematics: it is a special case of a theorem of H.-J. Kanold,
*Über ein spezielles System von zwei diophantischen Gleichungen*, J. reine angew. Math. 189,
pages 243 to 245, restricted to odd `p` and to arguments that are `p`-power powers.

The proof is elementary. Both equations force `r ≡ s ≡ 1 (mod p)`, `r ≡ 1 (mod p ^ (v + 1))`,
`s ≡ 1 (mod p ^ (u + 1))`, and `p ^ (p * p ^ u) ≡ 1` modulo `s ^ min a (p ^ v)`.

* If `a ≤ p ^ v` (or symmetrically `b ≤ p ^ u`), size comparison forces `v = 0` and `a = 1`;
  then `s` divides `(p ^ p ^ u) ^ p - 1`, and both possible factors lead to `s < r ^ p ^ u`,
  which contradicts `p * s = G p (r ^ p ^ u) > (r ^ p ^ u) ^ 2`.
* Otherwise `u = v`, and assuming `r < s`, the residue `R = b % (p * p ^ u)` is pinned down
  to `(p - 1) * p ^ u - 1`, which forces `u = 0`, `a = 2` and `p * (s - 1) = s ^ 2 - r ^ 2`,
  impossible since `p ∣ s - r`.

Main result: `OddPerfect.kanold_obstruction`.
-/

namespace OddPerfect

open Finset

/-- The geometric sum `∑ i ∈ range p, X ^ i`, that is `1 + X + ... + X ^ (p - 1)`. For prime
`p` it equals the `p`-th cyclotomic polynomial evaluated at `X`. -/
def kanoldG (p X : ℕ) : ℕ := ∑ i ∈ range p, X ^ i

/-- Splitting the geometric sum after `n` terms. -/
theorem kanoldG_add (n m X : ℕ) :
    kanoldG (n + m) X = kanoldG n X + X ^ n * kanoldG m X := by
  unfold kanoldG
  rw [Finset.sum_range_add, Finset.mul_sum]
  simp_rw [pow_add]

/-- The cast of `kanoldG` into a commutative semiring is the geometric sum there. -/
theorem kanoldG_cast {R : Type*} [CommSemiring R] (p X : ℕ) :
    ((kanoldG p X : ℕ) : R) = ∑ i ∈ range p, (X : R) ^ i := by
  simp [kanoldG]

/-- `G p X ≡ 1` modulo any divisor of `X`, for `p ≥ 1`. -/
theorem kanoldG_modEq_one {p X d : ℕ} (hp : 1 ≤ p) (hd : d ∣ X) :
    kanoldG p X ≡ 1 [MOD d] := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 1 + m := ⟨p - 1, by omega⟩
  rw [kanoldG_add]
  have h1 : kanoldG 1 X = 1 := by simp [kanoldG]
  rw [h1]
  have hdv : d ∣ X ^ 1 * kanoldG m X := by
    rw [pow_one]; exact dvd_mul_of_dvd_left hd _
  exact ((Nat.modEq_iff_dvd' (Nat.le_add_right 1 _)).mpr (by simpa using hdv)).symm

/-- `X ^ p ≡ 1` modulo any divisor of `G p X`. -/
theorem pow_modEq_one_of_dvd_kanoldG {p X n : ℕ} (h : n ∣ kanoldG p X) :
    X ^ p ≡ 1 [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  have h0 : ((kanoldG p X : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [kanoldG_cast] at h0
  have e := mul_geom_sum (X : ZMod n) p
  rw [h0, mul_zero] at e
  push_cast
  linear_combination -e

/-- Size bounds: `X ^ (p - 1) < G p X < p * X ^ (p - 1)` for `p ≥ 2` and `X ≥ 2`. -/
theorem kanoldG_bounds {p X : ℕ} (hp : 2 ≤ p) (hX : 2 ≤ X) :
    X ^ (p - 1) < kanoldG p X ∧ kanoldG p X < p * X ^ (p - 1) := by
  constructor
  · obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    unfold kanoldG
    rw [Finset.sum_range_succ, Nat.add_sub_cancel]
    have : 0 < ∑ i ∈ range m, X ^ i :=
      Finset.sum_pos (fun i _ => by positivity) ⟨0, Finset.mem_range.mpr (by omega)⟩
    omega
  · unfold kanoldG
    calc ∑ i ∈ range p, X ^ i < ∑ _i ∈ range p, X ^ (p - 1) := by
          apply Finset.sum_lt_sum
          · intro i hi
            exact Nat.pow_le_pow_right (by omega) (by rw [Finset.mem_range] at hi; omega)
          · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
            rw [pow_zero]
            exact Nat.one_lt_pow (by omega) (by omega)
      _ = p * X ^ (p - 1) := by simp

/-- `G p` is strictly increasing for `p ≥ 2`. -/
theorem kanoldG_lt_kanoldG {p Z X : ℕ} (hp : 2 ≤ p) (hZX : Z < X) :
    kanoldG p Z < kanoldG p X := by
  unfold kanoldG
  apply Finset.sum_lt_sum
  · intro i _; exact Nat.pow_le_pow_left hZX.le i
  · exact ⟨1, Finset.mem_range.mpr (by omega), by simpa using hZX⟩

/-- `X - Z` divides `G p X - G p Z` in `ℤ`. -/
theorem sub_dvd_kanoldG_sub (p X Z : ℕ) :
    ((X : ℤ) - Z) ∣ (kanoldG p X : ℤ) - kanoldG p Z := by
  rw [kanoldG_cast, kanoldG_cast, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i _ => sub_dvd_pow_sub_pow _ _ _

/-- If the prime `p` divides `G p (y ^ p ^ k)`, then `y ≡ 1 (mod p)`. -/
theorem cast_eq_one_of_dvd_kanoldG {p y k : ℕ} (hp : p.Prime)
    (h : p ∣ kanoldG p (y ^ p ^ k)) : (y : ZMod p) = 1 := by
  have := Fact.mk hp
  have h0 : ((kanoldG p (y ^ p ^ k) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [kanoldG_cast] at h0
  have e := mul_geom_sum ((y ^ p ^ k : ℕ) : ZMod p) p
  rw [h0, mul_zero] at e
  push_cast at e
  rw [ZMod.pow_card_pow, ZMod.pow_card] at e
  linear_combination -e

/-- If a prime `t ≠ p` divides `G p (y ^ p ^ k)` (with `p` prime), then
`t ≡ 1 (mod p ^ (k + 1))`. -/
theorem pow_succ_dvd_sub_one_of_dvd_kanoldG {p t y k : ℕ} (hp : p.Prime) (ht : t.Prime)
    (htp : t ≠ p) (h : t ∣ kanoldG p (y ^ p ^ k)) : p ^ (k + 1) ∣ t - 1 := by
  have := Fact.mk hp
  have := Fact.mk ht
  have h0 : ((kanoldG p (y ^ p ^ k) : ℕ) : ZMod t) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [kanoldG_cast] at h0
  push_cast at h0
  have hm := mul_geom_sum ((y : ZMod t) ^ p ^ k) p
  rw [h0, mul_zero, ← pow_mul, ← pow_succ] at hm
  have hfin : (y : ZMod t) ^ p ^ (k + 1) = 1 := by linear_combination -hm
  have hnot : ¬ (y : ZMod t) ^ p ^ k = 1 := by
    intro h1
    rw [h1] at h0
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h0
    have : t ∣ p := (ZMod.natCast_eq_zero_iff _ _).mp h0
    exact htp ((Nat.prime_dvd_prime_iff_eq ht hp).mp this)
  have hord := orderOf_eq_prime_pow hnot hfin
  have hne : (y : ZMod t) ≠ 0 := by
    intro hy
    rw [hy, zero_pow (pow_pos hp.pos _).ne'] at hfin
    exact zero_ne_one hfin
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one hne

/-- A number `n ≥ 2` with `n ≡ 1 (mod p)` exceeds `p`. -/
theorem lt_of_natCast_eq_one {p n : ℕ} (hp : 1 < p) (hn : 2 ≤ n) (h : (n : ZMod p) = 1) :
    p < n := by
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp] at h
  by_contra hlt
  push Not at hlt
  rcases hlt.lt_or_eq with hlt | rfl
  · rw [Nat.mod_eq_of_lt hlt] at h; omega
  · rw [Nat.mod_self] at h; omega

/-- A prime `p` is not a power of a different prime `r`. -/
theorem prime_ne_pow_of_ne {p r c : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p) :
    p ≠ r ^ c := by
  intro h
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [pow_zero] at h; exact hp.one_lt.ne' h
  · have : r ∣ p := by rw [h]; exact dvd_pow_self r hc.ne'
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp this)

/-- Step (3): from the pair of equations, `p ^ (p * A) ≡ 1` modulo `s ^ m` for every
`m ≤ min a A'`. -/
theorem pow_modEq_one_of_kanoldG_pair {p r s A A' a b m : ℕ}
    (h1 : kanoldG p (r ^ A) = p * s ^ a) (h2 : kanoldG p (s ^ A') = p * r ^ b)
    (hp : 1 ≤ p) (hma : m ≤ a) (hmA : m ≤ A') :
    p ^ (p * A) ≡ 1 [MOD s ^ m] := by
  have H1 : (r ^ A) ^ p ≡ 1 [MOD s ^ m] :=
    (pow_modEq_one_of_dvd_kanoldG (by rw [h1]; exact dvd_mul_left _ _)).of_dvd
      (pow_dvd_pow s hma)
  have H2 : p * r ^ b ≡ 1 [MOD s ^ m] := by
    have := kanoldG_modEq_one (p := p) hp (dvd_refl (s ^ A'))
    rw [h2] at this
    exact this.of_dvd (pow_dvd_pow s hmA)
  calc p ^ (p * A) = p ^ (p * A) * 1 ^ b := by simp
    _ ≡ p ^ (p * A) * ((r ^ A) ^ p) ^ b [MOD s ^ m] := (H1.symm.pow b).mul_left _
    _ = (p * r ^ b) ^ (p * A) := by ring
    _ ≡ 1 ^ (p * A) [MOD s ^ m] := H2.pow _
    _ = 1 := one_pow _

/-- Case B of Kanold's argument: the system has no solution when `a ≤ p ^ v`. -/
theorem kanold_obstruction_of_le {p r s u v a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : r.Prime) (hs : s.Prime) (hb : 0 < b)
    (h1 : kanoldG p (r ^ p ^ u) = p * s ^ a)
    (h2 : kanoldG p (s ^ p ^ v) = p * r ^ b) (hav : a ≤ p ^ v) : False := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hrp1 : (r : ZMod p) = 1 :=
    cast_eq_one_of_dvd_kanoldG hp (by rw [h1]; exact dvd_mul_right _ _)
  have hsp1 : (s : ZMod p) = 1 :=
    cast_eq_one_of_dvd_kanoldG hp (by rw [h2]; exact dvd_mul_right _ _)
  have hpr : p < r := lt_of_natCast_eq_one hp.one_lt hr.two_le hrp1
  have hps : p < s := lt_of_natCast_eq_one hp.one_lt hs.two_le hsp1
  have hr4 : p ^ (v + 1) ∣ r - 1 :=
    pow_succ_dvd_sub_one_of_dvd_kanoldG hp hr hpr.ne'
      (by rw [h2]; exact dvd_mul_of_dvd_right (dvd_pow_self r hb.ne') _)
  have hr4' : p ^ (v + 1) < r := by
    have := Nat.le_of_dvd (by have := hr.two_le; omega) hr4
    omega
  generalize hA : p ^ u = A at h1
  have hA0 : 0 < A := hA ▸ pow_pos hp.pos u
  have h3 : p ^ (p * A) ≡ 1 [MOD s ^ a] :=
    pow_modEq_one_of_kanoldG_pair h1 h2 hp.one_lt.le le_rfl hav
  have hpA1 : 1 ≤ p ^ (p * A) := Nat.one_le_pow _ _ hp.pos
  have hpA3 : p ≤ p ^ (p * A) := Nat.le_self_pow (Nat.mul_pos hp.pos hA0).ne' p
  have hsa_dvd : s ^ a ∣ p ^ (p * A) - 1 := (Nat.modEq_iff_dvd' hpA1).mp h3.symm
  have hsa_lt : s ^ a < p ^ (p * A) := by
    have := Nat.le_of_dvd (by omega) hsa_dvd
    omega
  have hrA : r ≤ r ^ A := Nat.le_self_pow hA0.ne' r
  have hX2 : 2 ≤ r ^ A := le_trans hr.two_le hrA
  obtain ⟨hlow, hup⟩ := kanoldG_bounds hp.two_le hX2
  rw [h1] at hlow hup
  have hv : v = 0 := by
    have hne : A * (p - 1) ≠ 0 := Nat.mul_ne_zero hA0.ne' (by omega)
    have c1 : (p ^ (v + 1)) ^ (A * (p - 1)) < (r ^ A) ^ (p - 1) := by
      rw [← pow_mul r]; exact Nat.pow_lt_pow_left hr4' hne
    have c2 : p * s ^ a < p ^ (p * A + 1) := by
      rw [pow_succ, mul_comm _ p]; exact Nat.mul_lt_mul_of_pos_left hsa_lt hp.pos
    have c3 := lt_trans (lt_trans c1 hlow) c2
    rw [← pow_mul, Nat.pow_lt_pow_iff_right hp.one_lt] at c3
    by_contra hv0
    have hw : A * (p - 1) + A = p * A := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp.one_lt.le, mul_comm]
    have hw2 : 2 * A ≤ A * (p - 1) := by
      rw [mul_comm 2 A]; exact Nat.mul_le_mul_left A (by omega)
    have hv1 : 1 ≤ v := Nat.one_le_iff_ne_zero.mpr hv0
    nlinarith
  subst hv
  have ha1 : a = 1 := by
    have : 0 < a := by
      by_contra h0
      have : a = 0 := by omega
      subst this
      rw [pow_zero, mul_one] at hlow
      have := Nat.le_self_pow (show p - 1 ≠ 0 by omega) (r ^ A)
      omega
    rw [pow_zero] at hav; omega
  subst ha1
  rw [pow_one] at hsa_dvd hlow h1
  -- `Z = p ^ A` and `s ∣ Z ^ p - 1`
  have hZX : p ^ A < r ^ A := Nat.pow_lt_pow_left hpr hA0.ne'
  have hZ3 : p ≤ p ^ A := Nat.le_self_pow hA0.ne' p
  have hsZ : (p ^ A) ^ p ≡ 1 [MOD s] := by
    have hd : s ∣ (p ^ A) ^ p - 1 := by rwa [← pow_mul, mul_comm]
    exact ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (pow_pos hp.pos _))).mpr hd).symm
  have := Fact.mk hs
  have hcases : ((p ^ A : ℕ) : ZMod s) = 1 ∨ ((kanoldG p (p ^ A) : ℕ) : ZMod s) = 0 := by
    have e := mul_geom_sum ((p ^ A : ℕ) : ZMod s) p
    rw [← kanoldG_cast] at e
    have hz : (((p ^ A) ^ p : ℕ) : ZMod s) = 1 := by
      rw [← Nat.cast_one]; exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hsZ
    rw [← Nat.cast_pow, hz, sub_self] at e
    rcases mul_eq_zero.mp e with e | e
    · left; exact sub_eq_zero.mp e
    · right; exact e
  have hsX : s < r ^ A := by
    rcases hcases with hc | hc
    · have hm : p ^ A ≡ 1 [MOD s] := by
        rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]; exact hc
      have hd := (Nat.modEq_iff_dvd' (by omega)).mp hm.symm
      have := Nat.le_of_dvd (by omega) hd
      omega
    · obtain ⟨f, hf⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hc
      have hGZp : kanoldG p (p ^ A) ≡ 1 [MOD p] :=
        kanoldG_modEq_one hp.one_lt.le (dvd_pow_self p hA0.ne')
      have hf1 : (f : ZMod p) = 1 := by
        have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hGZp
        rw [hf] at this
        push_cast at this
        rw [hsp1, one_mul] at this
        exact this
      have hflt : f < p := by
        have := kanoldG_lt_kanoldG hp.two_le hZX
        rw [hf, h1, mul_comm p s] at this
        exact Nat.lt_of_mul_lt_mul_left this
      have hf_eq : f = 1 := by
        have := (ZMod.natCast_eq_natCast_iff' f 1 p).mp (by rw [Nat.cast_one]; exact hf1)
        rwa [Nat.mod_eq_of_lt hflt, Nat.mod_eq_of_lt hp.one_lt] at this
      subst hf_eq
      rw [mul_one] at hf
      have hdiff := sub_dvd_kanoldG_sub p (r ^ A) (p ^ A)
      rw [h1, hf] at hdiff
      have hdvdN : r ^ A - p ^ A ∣ (p - 1) * s := by
        rw [← Int.natCast_dvd_natCast, Nat.cast_sub hZX.le, Nat.cast_mul,
          Nat.cast_sub hp.one_lt.le]
        convert hdiff using 1
        push_cast; ring
      -- `r ^ A - p ^ A ≡ 1 (mod p)` and `r ^ A - p ^ A ≥ 2`
      have hd1 : ((r ^ A - p ^ A : ℕ) : ZMod p) = 1 := by
        rw [Nat.cast_sub hZX.le]
        push_cast
        rw [hrp1, ZMod.natCast_self, one_pow, zero_pow hA0.ne', sub_zero]
      have hd2 : 2 ≤ r ^ A - p ^ A := by
        have hro : Odd (r ^ A) := (hr.odd_of_ne_two (by omega)).pow
        have hpo : Odd (p ^ A) := (hp.odd_of_ne_two hp2).pow
        rw [Nat.odd_iff] at hro hpo
        omega
      have hd3 := lt_of_natCast_eq_one hp.one_lt hd2 hd1
      by_cases hsd : s ∣ r ^ A - p ^ A
      · have := Nat.le_of_dvd (by omega) hsd
        omega
      · have hcop : Nat.Coprime (r ^ A - p ^ A) s :=
          ((Nat.Prime.coprime_iff_not_dvd hs).mpr hsd).symm
        have := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_right hdvdN)
        omega
  -- contradiction with `p * s = G p (r ^ A) > (r ^ A) ^ 2`
  have hsq : (r ^ A) ^ 2 ≤ (r ^ A) ^ (p - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have : p * s < r ^ A * r ^ A := Nat.mul_lt_mul'' (by omega) hsX
  rw [← pow_two] at this
  omega

/-- From the pair of equations, `p ^ v < a` forces `v ≤ u`. -/
theorem le_of_kanoldG_pair {p r s u v a b : ℕ} (hp : p.Prime) (hs : s.Prime)
    (h1 : kanoldG p (r ^ p ^ u) = p * s ^ a)
    (h2 : kanoldG p (s ^ p ^ v) = p * r ^ b) (hva : p ^ v < a) : v ≤ u := by
  have hsp1 : (s : ZMod p) = 1 :=
    cast_eq_one_of_dvd_kanoldG hp (by rw [h2]; exact dvd_mul_right _ _)
  have hps : p < s := lt_of_natCast_eq_one hp.one_lt hs.two_le hsp1
  have h3 : p ^ (p * p ^ u) ≡ 1 [MOD s ^ p ^ v] :=
    pow_modEq_one_of_kanoldG_pair h1 h2 hp.one_lt.le hva.le le_rfl
  have hd := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp h3.symm
  have hlt : s ^ p ^ v < p ^ (p * p ^ u) := by
    have h2' : 1 < p ^ (p * p ^ u) :=
      Nat.one_lt_pow (Nat.mul_pos hp.pos (pow_pos hp.pos _)).ne' hp.one_lt
    have := Nat.le_of_dvd (by omega) hd
    omega
  have := lt_trans (Nat.pow_lt_pow_left hps (pow_pos hp.pos v).ne') hlt
  rw [Nat.pow_lt_pow_iff_right hp.one_lt, ← pow_succ', Nat.pow_lt_pow_iff_right hp.one_lt] at this
  omega

/-- The two primes in a solution are distinct: `G p (r ^ p ^ u) = p * r ^ a` is impossible. -/
theorem kanoldG_ne_mul_self_pow {p r u a : ℕ} (hp : 1 ≤ p) (hr : r.Prime) (ha : 0 < a)
    (hpu : 0 < p ^ u) (h1 : kanoldG p (r ^ p ^ u) = p * r ^ a) : False := by
  have h := kanoldG_modEq_one (X := r ^ p ^ u) hp (dvd_pow_self r hpu.ne')
  rw [h1] at h
  have h0 : p * r ^ a ≡ 0 [MOD r] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right (dvd_pow_self r ha.ne') _)
  have h01 := (Nat.modEq_iff_dvd' (Nat.zero_le 1)).mp (h0.symm.trans h)
  rw [Nat.sub_zero, Nat.dvd_one] at h01
  exact hr.ne_one h01

/-- Case C of Kanold's argument: with equal exponents `u = v`, `p ^ u < a`, `p ^ u < b`, and
`r < s`, the system has no solution. -/
theorem kanold_obstruction_of_lt {p r s u a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : r.Prime) (hs : s.Prime) (hrs : r < s)
    (h1 : kanoldG p (r ^ p ^ u) = p * s ^ a)
    (h2 : kanoldG p (s ^ p ^ u) = p * r ^ b) (hua : p ^ u < a) (hub : p ^ u < b) : False := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hrp1 : (r : ZMod p) = 1 :=
    cast_eq_one_of_dvd_kanoldG hp (by rw [h1]; exact dvd_mul_right _ _)
  have hsp1 : (s : ZMod p) = 1 :=
    cast_eq_one_of_dvd_kanoldG hp (by rw [h2]; exact dvd_mul_right _ _)
  have hpr : p < r := lt_of_natCast_eq_one hp.one_lt hr.two_le hrp1
  have hps : p < s := lt_of_natCast_eq_one hp.one_lt hs.two_le hsp1
  have hr4 : p ^ (u + 1) < r := by
    have hd : p ^ (u + 1) ∣ r - 1 :=
      pow_succ_dvd_sub_one_of_dvd_kanoldG hp hr hpr.ne'
        (by rw [h2]; exact dvd_mul_of_dvd_right (dvd_pow_self r (by omega)) _)
    have := Nat.le_of_dvd (by have := hr.two_le; omega) hd
    omega
  generalize hA : p ^ u = A at h1 h2 hua hub
  have hA0 : 0 < A := hA ▸ pow_pos hp.pos u
  have hX2 : 2 ≤ r ^ A := le_trans hr.two_le (Nat.le_self_pow hA0.ne' r)
  have hrA : r ^ A < s ^ A := Nat.pow_lt_pow_left hrs hA0.ne'
  have hpA0 : 0 < p * A := Nat.mul_pos hp.pos hA0
  -- congruences
  have H1 : r ^ (p * A) ≡ 1 [MOD s ^ a] := by
    have := pow_modEq_one_of_dvd_kanoldG (p := p) (X := r ^ A) (n := s ^ a)
      (by rw [h1]; exact dvd_mul_left _ _)
    rwa [← pow_mul, mul_comm] at this
  have H1Y : r ^ (p * A) ≡ 1 [MOD s ^ A] := H1.of_dvd (pow_dvd_pow s hua.le)
  have H2 : p * r ^ b ≡ 1 [MOD s ^ A] := by
    have := kanoldG_modEq_one (p := p) hp.one_lt.le (dvd_refl (s ^ A))
    rwa [h2] at this
  -- if `p * A ∣ b + c` then `s ^ A ≤ r ^ c`
  have Kc : ∀ c q, b + c = p * A * q → s ^ A ≤ r ^ c := by
    intro c q hbc
    by_contra hlt
    push Not at hlt
    have hmod : p ≡ r ^ c [MOD s ^ A] := calc
      p = p * 1 ^ q := by simp
      _ ≡ p * (r ^ (p * A)) ^ q [MOD s ^ A] := (H1Y.symm.pow q).mul_left p
      _ = (p * r ^ b) * r ^ c := by rw [← pow_mul, ← hbc, pow_add]; ring
      _ ≡ 1 * r ^ c [MOD s ^ A] := H2.mul_right _
      _ = r ^ c := one_mul _
    have hpY : p < s ^ A := lt_of_lt_of_le hps (Nat.le_self_pow hA0.ne' s)
    exact prime_ne_pow_of_ne hp hr hpr.ne' (hmod.eq_of_lt_of_lt hpY hlt)
  -- the residue `R = b % (p * A)`
  have hbR : p * A * (b / (p * A)) + b % (p * A) = b := Nat.div_add_mod b (p * A)
  have hRlt : b % (p * A) < p * A := Nat.mod_lt _ hpA0
  generalize hq : b / (p * A) = q at hbR
  generalize hRdef : b % (p * A) = R at hbR hRlt
  have hR0 : R ≠ 0 := by
    intro h0
    have := Kc 0 q (by omega)
    rw [pow_zero] at this
    have := Nat.one_lt_pow hA0.ne' hs.one_lt
    omega
  have hRA : R + A < p * A := by
    have := Kc (p * A - R) (q + 1) (by rw [mul_add, mul_one]; omega)
    have : r ^ A < r ^ (p * A - R) := lt_of_lt_of_le hrA this
    rw [Nat.pow_lt_pow_iff_right hr.one_lt] at this
    omega
  -- (18): `p * r ^ R ≡ G p (s ^ A) (mod s ^ a)`
  have H18 : p * r ^ R ≡ kanoldG p (s ^ A) [MOD s ^ a] := by
    rw [h2]
    have : r ^ b = (r ^ (p * A)) ^ q * r ^ R := by rw [← pow_mul, ← pow_add, hbR]
    rw [this]
    calc p * r ^ R = p * (1 ^ q * r ^ R) := by simp
      _ ≡ p * ((r ^ (p * A)) ^ q * r ^ R) [MOD s ^ a] :=
          ((H1.symm.pow _).mul_right _).mul_left _
  -- size bounds from `G p (r ^ A) = p * s ^ a`
  obtain ⟨hXlow, hXup⟩ := kanoldG_bounds hp.two_le hX2
  rw [h1] at hXlow hXup
  have hne : A * (p - 1) ≠ 0 := Nat.mul_ne_zero hA0.ne' (by omega)
  have ha_lt : a < A * (p - 1) := by
    have h' : s ^ a < (r ^ A) ^ (p - 1) := Nat.lt_of_mul_lt_mul_left hXup
    rw [← pow_mul] at h'
    have := lt_trans h' (Nat.pow_lt_pow_left hrs hne)
    rwa [Nat.pow_lt_pow_iff_right hs.one_lt] at this
  -- (19): `A * z < a ≤ A * (z + 1)` with `1 ≤ z` and `z + 1 < p`
  have hz1 : A * ((a - 1) / A) + (a - 1) % A = a - 1 := Nat.div_add_mod (a - 1) A
  have hz2 : (a - 1) % A < A := Nat.mod_lt _ hA0
  generalize hzdef : (a - 1) / A = z at hz1
  generalize hwdef : (a - 1) % A = w at hz1 hz2
  have hzA : A * z < a := by omega
  have hzA' : a ≤ A * (z + 1) := by rw [mul_add, mul_one]; omega
  have hz_pos : 1 ≤ z := by
    by_contra h0
    have : z = 0 := by omega
    rw [this, mul_zero] at hz1
    omega
  have hzp : z + 1 < p := by
    have := Nat.lt_of_mul_lt_mul_left (lt_trans hzA ha_lt)
    omega
  -- (20): `T = G (z + 1) (s ^ A)`
  have hTmod : kanoldG p (s ^ A) ≡ kanoldG (z + 1) (s ^ A) [MOD s ^ a] := by
    have hsplit := kanoldG_add (z + 1) (p - (z + 1)) (s ^ A)
    rw [Nat.add_sub_cancel' hzp.le] at hsplit
    rw [hsplit]
    have hdv : s ^ a ∣ (s ^ A) ^ (z + 1) * kanoldG (p - (z + 1)) (s ^ A) :=
      dvd_mul_of_dvd_left (by rw [← pow_mul]; exact pow_dvd_pow s hzA') _
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mpr (by simpa using hdv)).symm
  have hTle : kanoldG (z + 1) (s ^ A) ≤ (z + 1) * (s ^ A) ^ z := by
    unfold kanoldG
    calc ∑ i ∈ range (z + 1), (s ^ A) ^ i ≤ ∑ _i ∈ range (z + 1), (s ^ A) ^ z :=
          Finset.sum_le_sum fun i hi =>
            Nat.pow_le_pow_right (pow_pos hs.pos _) (by rw [Finset.mem_range] at hi; omega)
      _ = (z + 1) * (s ^ A) ^ z := by simp
  have hTlt : kanoldG (z + 1) (s ^ A) < s ^ a := by
    calc _ ≤ (z + 1) * (s ^ A) ^ z := hTle
      _ < s * (s ^ A) ^ z := Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (pow_pos hs.pos _) _)
      _ = s ^ (A * z + 1) := by rw [← pow_mul, pow_succ, mul_comm]
      _ ≤ s ^ a := Nat.pow_le_pow_right hs.pos (by omega)
  have hTp : ¬ p ∣ kanoldG (z + 1) (s ^ A) := by
    intro hd
    have h0 : ((kanoldG (z + 1) (s ^ A) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [kanoldG_cast] at h0
    push_cast at h0
    rw [hsp1] at h0
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h0
    have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ _).mp h0)
    omega
  -- `s ^ a ≤ p * r ^ R`
  have HT : p * r ^ R ≡ kanoldG (z + 1) (s ^ A) [MOD s ^ a] := H18.trans hTmod
  have hge : s ^ a ≤ p * r ^ R := by
    by_contra hlt
    push Not at hlt
    exact hTp ⟨r ^ R, (HT.eq_of_lt_of_lt hlt hTlt).symm⟩
  -- `R + 1 = (p - 1) * A`
  have hrE : r ^ (A * (p - 1)) < p * s ^ a := by rw [pow_mul]; exact hXlow
  have hw : A * (p - 1) + A = p * A := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp.one_lt.le, mul_comm]
  have hR1 : A * (p - 1) ≤ R + 1 := by
    by_contra hcon
    push Not at hcon
    have h1' : r ^ (R + 2) ≤ r ^ (A * (p - 1)) := Nat.pow_le_pow_right hr.pos hcon
    have h2' : p * p < r * r := Nat.mul_self_lt_mul_self hpr
    have h3' : p * s ^ a ≤ p * (p * r ^ R) := Nat.mul_le_mul_left _ hge
    rw [pow_add, pow_two] at h1'
    have hrR : 0 < r ^ R := pow_pos hr.pos _
    have h4' : r ^ R * (p * p) < r ^ R * (r * r) := Nat.mul_lt_mul_of_pos_left h2' hrR
    have e : p * (p * r ^ R) = r ^ R * (p * p) := by ring
    omega
  have hReq : R + 1 = A * (p - 1) := by omega
  -- `r < p ^ 2`, hence `u = 0`
  have hr_lt : r < p * p := by
    have h3' : p * s ^ a ≤ p * (p * r ^ R) := Nat.mul_le_mul_left _ hge
    rw [← hReq, pow_succ] at hrE
    by_contra hc
    push Not at hc
    have h4' := Nat.mul_le_mul_left (r ^ R) hc
    have e : p * (p * r ^ R) = r ^ R * (p * p) := by ring
    omega
  have hu : u = 0 := by
    have : p ^ (u + 1) < p ^ 2 := by rw [pow_two]; omega
    rw [Nat.pow_lt_pow_iff_right hp.one_lt] at this
    omega
  subst hu
  rw [pow_zero] at hA
  subst hA
  have ha' : a = z + 1 := by omega
  have hRp : p = R + 2 := by omega
  -- (27): `s ^ a ∣ p * (s - 1) + r ^ 2`
  have hdiv : s ^ a ∣ p * (s - 1) + r ^ 2 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have e1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr HT
    have e2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr H1
    rw [kanoldG_cast] at e1
    push_cast at e1 e2
    simp only [pow_one, mul_one] at e1 e2
    rw [hRp] at e2
    have hs0 : (s : ZMod (s ^ a)) ^ (z + 1) = 0 := by
      rw [← ha', ← Nat.cast_pow, ZMod.natCast_self]
    have hg := geom_sum_mul (s : ZMod (s ^ a)) (z + 1)
    rw [hs0] at hg
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hs.one_lt.le, Nat.cast_pow, Nat.cast_one]
    linear_combination (-(p : ZMod (s ^ a)) * ((s : ZMod (s ^ a)) - 1)) * e2
      + (r : ZMod (s ^ a)) ^ 2 * ((s : ZMod (s ^ a)) - 1) * e1 + (r : ZMod (s ^ a)) ^ 2 * hg
  -- final size argument
  have hN_pos : 0 < p * (s - 1) + r ^ 2 := by have := pow_pos hr.pos 2; omega
  have hN1 : p * (s - 1) < s * s := Nat.mul_lt_mul'' hps (by omega)
  have hN2 : r ^ 2 < s ^ 2 := Nat.pow_lt_pow_left hrs (by norm_num)
  have hss : s ^ 2 = s * s := pow_two s
  have hN_lt : p * (s - 1) + r ^ 2 < 2 * s ^ 2 := by omega
  have ha2 : a = 2 := by
    have hle := Nat.le_of_dvd hN_pos hdiv
    have h23 : 2 * s ^ 2 ≤ s ^ 3 := by
      rw [pow_succ s 2, mul_comm]; exact Nat.mul_le_mul_left _ hs.two_le
    have : s ^ a < s ^ 3 := by omega
    rw [Nat.pow_lt_pow_iff_right hs.one_lt] at this
    omega
  rw [ha2] at hdiv
  obtain ⟨k, hk⟩ := hdiv
  have hk1 : k = 1 := by
    have hk0 : k ≠ 0 := by rintro rfl; omega
    have hk2 : k < 2 := by
      by_contra hk2
      push Not at hk2
      have := Nat.mul_le_mul_left (s ^ 2) hk2
      omega
    omega
  subst hk1
  rw [mul_one] at hk
  have hsr : p ∣ s - r := by
    have hm : r ≡ s [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff, hrp1, hsp1]
    exact (Nat.modEq_iff_dvd' hrs.le).mp hm
  obtain ⟨j, hj⟩ := hsr
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, mul_zero] at hj; omega
    · exact h0
  have hs_eq : s = r + p * j := by omega
  -- `s * s = r * s + p * j * s ≥ r * r + p * s > r ^ 2 + p * (s - 1) = s ^ 2`
  have e1 : s * s = r * s + p * j * s := by
    calc s * s = (r + p * j) * s := by rw [← hs_eq]
      _ = r * s + p * j * s := by ring
  have e2 : r * r ≤ r * s := Nat.mul_le_mul_left r hrs.le
  have e3 : p * s ≤ p * j * s := by
    calc p * s = p * s * 1 := (mul_one _).symm
      _ ≤ p * s * j := Nat.mul_le_mul_left _ hj1
      _ = p * j * s := by ring
  have e4 : p * (s - 1) < p * s := Nat.mul_lt_mul_of_pos_left (by omega) hp.pos
  have hrr : r ^ 2 = r * r := pow_two r
  omega

/-- **Kanold's obstruction.** For an odd prime `p`, primes `r` and `s`, and positive exponents
`a` and `b`, the equations `G p (r ^ p ^ u) = p * s ^ a` and `G p (s ^ p ^ v) = p * r ^ b`, with
`G p X = ∑ i ∈ range p, X ^ i`, have no common solution. This is a special case of a theorem of
H.-J. Kanold (J. reine angew. Math. 189, pages 243 to 245). -/
theorem kanold_obstruction {p r s u v a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : r.Prime) (hs : s.Prime) (ha : 0 < a) (hb : 0 < b)
    (h1 : ∑ i ∈ Finset.range p, (r ^ p ^ u) ^ i = p * s ^ a)
    (h2 : ∑ i ∈ Finset.range p, (s ^ p ^ v) ^ i = p * r ^ b) : False := by
  change kanoldG p (r ^ p ^ u) = p * s ^ a at h1
  change kanoldG p (s ^ p ^ v) = p * r ^ b at h2
  by_cases hav : a ≤ p ^ v
  · exact kanold_obstruction_of_le hp hp2 hr hs hb h1 h2 hav
  by_cases hbu : b ≤ p ^ u
  · exact kanold_obstruction_of_le hp hp2 hs hr ha h2 h1 hbu
  push Not at hav hbu
  have hvu : v ≤ u := le_of_kanoldG_pair hp hs h1 h2 hav
  have huv : u ≤ v := le_of_kanoldG_pair hp hr h2 h1 hbu
  obtain rfl : u = v := le_antisymm huv hvu
  rcases lt_trichotomy r s with hrs | rfl | hsr
  · exact kanold_obstruction_of_lt hp hp2 hr hs hrs h1 h2 hav hbu
  · exact kanoldG_ne_mul_self_pow hp.one_lt.le hr ha (pow_pos hp.pos _) h1
  · exact kanold_obstruction_of_lt hp hp2 hs hr hsr h2 h1 hbu hav

end OddPerfect

#print axioms OddPerfect.kanoldG_add
#print axioms OddPerfect.kanoldG_cast
#print axioms OddPerfect.kanoldG_modEq_one
#print axioms OddPerfect.pow_modEq_one_of_dvd_kanoldG
#print axioms OddPerfect.kanoldG_bounds
#print axioms OddPerfect.kanoldG_lt_kanoldG
#print axioms OddPerfect.sub_dvd_kanoldG_sub
#print axioms OddPerfect.cast_eq_one_of_dvd_kanoldG
#print axioms OddPerfect.pow_succ_dvd_sub_one_of_dvd_kanoldG
#print axioms OddPerfect.lt_of_natCast_eq_one
#print axioms OddPerfect.prime_ne_pow_of_ne
#print axioms OddPerfect.pow_modEq_one_of_kanoldG_pair
#print axioms OddPerfect.kanold_obstruction_of_le
#print axioms OddPerfect.le_of_kanoldG_pair
#print axioms OddPerfect.kanoldG_ne_mul_self_pow
#print axioms OddPerfect.kanold_obstruction_of_lt
#print axioms OddPerfect.kanold_obstruction
