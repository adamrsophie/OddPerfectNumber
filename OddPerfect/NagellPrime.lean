import OddPerfect.EscapeRowUnique
import OddPerfect.NagellReduction

/-!
# Nagell's theorem for prime `x` and a prime power on the right

We prove: if `x` and `q` are primes and `x ^ 2 + x + 1 = q ^ j` with `j ≥ 1`, then `j = 1`. This
is the classical theorem of Nagell (1921) for prime `x` and a prime power on the right; it is
known mathematics, proved here by an elementary argument in the Eisenstein integers
`Eis = QuadraticAlgebra ℤ (-1) (-1)`. In particular the hypothesis `NagellPrimePower` used
elsewhere in the library is proved (`nagellPrimePower`). The example `Φ₃(18) = 7 ^ 3` shows that
the primality of `x` is needed for the cube case.

* `not_phi3_eq_prime_pow_of_dvd`: if `phi3 x = q ^ j` with `j ≥ 1`, then `j` has no factor
  `n ≥ 2` prime to `6`. The row factors as `x - ω = ρ ^ j * θ` with `nrm ρ = q` and `θ` a unit;
  absorbing `θ` gives `β ^ n = x - ω` with `nrm β = q ^ (j / n)`. Then `(β ^ n).im = -1`, and a
  congruence argument (first and second order in `β.re`, and a comparison of powers of `2` in
  the binomial expansion) forces `nrm β = 1` or `nrm β = 3`, which is impossible.
* `phi3_eq_prime_pow_exponent`: the exponents `2` and `3` are handled by `not_isSquare_phi3` and
  `phi3_ne_cube_of_prime`.

Nothing here decides the odd perfect number conjecture.
-/

open Finset QuadraticAlgebra

namespace OddPerfect

namespace NagellPrime

open Eis

private lemma nrm_pow' (z : Eis) (k : ℕ) : nrm (z ^ k) = nrm z ^ k := by
  induction k with
  | zero => simp [nrm_one]
  | succ k ih => rw [pow_succ, nrm_mul, ih, pow_succ]

/-- Lemma U: a unit has order dividing `6`. -/
private lemma pow_six_of_nrm_one {θ : Eis} (h : nrm θ = 1) : θ ^ 6 = 1 := by
  rcases eq_of_nrm_eq_one h with rfl | rfl | rfl | rfl | rfl | rfl <;> ext <;> norm_num [pow_succ]

private lemma pow_mod_six {δ : Eis} (h : δ ^ 6 = 1) (n : ℕ) : δ ^ n = δ ^ (n % 6) := by
  conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul, h, one_pow, one_mul]

private lemma im_sum (s : Finset ℕ) (f : ℕ → Eis) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, im_add, ih]

/-- Binomial expansion of the `ω` coordinate of `(A + δ) ^ n`. -/
private lemma expand (A : ℤ) (δ : Eis) (n : ℕ) :
    (((A : Eis) + δ) ^ n).im =
      ∑ i ∈ range (n + 1), (n.choose i : ℤ) * A ^ i * (δ ^ (n - i)).im := by
  rw [add_pow, im_sum]
  refine sum_congr rfl fun i _ => ?_
  have e : (A : Eis) ^ i * δ ^ (n - i) * (n.choose i : Eis) =
      (((n.choose i : ℤ) * A ^ i : ℤ) : Eis) * δ ^ (n - i) := by push_cast; ring
  rw [e, im_mul, re_intCast, im_intCast]; push_cast; ring

/-- The expansion with its first three terms split off. -/
private lemma expand3 (A : ℤ) (δ : Eis) (m : ℕ) :
    (((A : Eis) + δ) ^ (m + 3)).im = (δ ^ (m + 3)).im + ((m : ℤ) + 3) * A * (δ ^ (m + 2)).im +
      ((m + 3).choose 2 : ℤ) * A ^ 2 * (δ ^ (m + 1)).im +
      ∑ i ∈ range (m + 1), ((m + 3).choose (3 + i) : ℤ) * A ^ (3 + i) * (δ ^ (m - i)).im := by
  have h3 : ∑ i ∈ range 3, ((m + 3).choose i : ℤ) * A ^ i * (δ ^ (m + 3 - i)).im =
      (δ ^ (m + 3)).im + ((m : ℤ) + 3) * A * (δ ^ (m + 2)).im +
        ((m + 3).choose 2 : ℤ) * A ^ 2 * (δ ^ (m + 1)).im := by
    simp only [sum_range_succ, sum_range_zero, zero_add, Nat.choose_zero_right,
      Nat.choose_one_right, pow_zero, pow_one, Nat.sub_zero, Nat.cast_one, one_mul]
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    push_cast; ring
  have hs : ∀ i ∈ range (m + 1),
      ((m + 3).choose (3 + i) : ℤ) * A ^ (3 + i) * (δ ^ (m + 3 - (3 + i))).im =
        ((m + 3).choose (3 + i) : ℤ) * A ^ (3 + i) * (δ ^ (m - i)).im := by
    intro i _
    rw [show m + 3 - (3 + i) = m - i by omega]
  rw [expand, show m + 3 + 1 = 3 + (m + 1) by ring, sum_range_add, h3, sum_congr rfl hs]

/-- Cancelling the part of `F` prime to `2`. -/
private lemma two_pow_dvd_of_mul {F : ℕ} (hF : F ≠ 0) {e : ℕ} (hk : ∀ k, 2 ^ k ∣ F → k ≤ e)
    {w : ℕ} {X : ℤ} (h : (2 : ℤ) ^ (w + e) ∣ (F : ℤ) * X) : (2 : ℤ) ^ w ∣ X := by
  obtain ⟨s, t, ht, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hF 2 (by norm_num)
  have hs := hk s (dvd_mul_right _ _)
  have hcop : IsCoprime ((2 : ℤ) ^ (w + e)) (t : ℤ) := by
    have : Nat.Coprime (2 ^ (w + e)) t :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ht)
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  have h1 : (2 : ℤ) ^ (w + e) ∣ (2 : ℤ) ^ s * X := by
    refine hcop.dvd_of_dvd_mul_left ?_
    have : ((2 ^ s * t : ℕ) : ℤ) * X = (t : ℤ) * ((2 : ℤ) ^ s * X) := by push_cast; ring
    rwa [this] at h
  have h2 : (2 : ℤ) ^ s * 2 ^ (w + e - s) ∣ (2 : ℤ) ^ s * X := by
    rwa [← pow_add, show s + (w + e - s) = w + e by omega]
  have h3 := (mul_dvd_mul_iff_left (pow_ne_zero s (two_ne_zero : (2 : ℤ) ≠ 0))).1 h2
  exact (pow_dvd_pow 2 (by omega)).trans h3

/-- The power of `2` in `(i + 3) * (i + 2)` is at most `i + 1`. -/
private lemma two_pow_dvd_bound (i k : ℕ) (h : 2 ^ k ∣ (3 + i) * (2 + i)) : k ≤ i + 1 := by
  have hle : 2 ^ k ≤ i + 3 := by
    rcases Nat.even_or_odd i with ⟨r, hr⟩ | ⟨r, hr⟩
    · have hc : Nat.Coprime (2 ^ k) (3 + i) :=
        Nat.Coprime.pow_left _ (by rw [Nat.coprime_two_left]; exact ⟨r + 1, by omega⟩)
      have := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left h)
      omega
    · have hc : Nat.Coprime (2 ^ k) (2 + i) :=
        Nat.Coprime.pow_left _ (by rw [Nat.coprime_two_left]; exact ⟨r + 1, by omega⟩)
      have := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right h)
      omega
  by_contra hc
  have h1 : 2 ^ (i + 2) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : i < 2 ^ i := Nat.lt_two_pow_self
  have h3 : 2 ^ (i + 2) = 4 * 2 ^ i := by ring
  omega

private lemma choose_id (m i : ℕ) :
    ((3 + i) * (2 + i) : ℤ) * ((m + 3).choose (3 + i) : ℤ) =
      2 * ((m + 3).choose 2 : ℤ) * ((m + 1).choose (1 + i) : ℤ) := by
  have h1 : (m + 3) * (m + 2).choose (2 + i) = (m + 3).choose (3 + i) * (3 + i) := by
    have := Nat.add_one_mul_choose_eq (m + 2) (2 + i)
    rwa [show m + 2 + 1 = m + 3 by ring, show 2 + i + 1 = 3 + i by ring] at this
  have h2 : (m + 2) * (m + 1).choose (1 + i) = (m + 2).choose (2 + i) * (2 + i) := by
    have := Nat.add_one_mul_choose_eq (m + 1) (1 + i)
    rwa [show m + 1 + 1 = m + 2 by ring, show 1 + i + 1 = 2 + i by ring] at this
  have h0 : (m + 3) * (m + 2) = (m + 3).choose 2 * 2 := by
    have := Nat.add_one_mul_choose_eq (m + 2) 1
    rwa [show m + 2 + 1 = m + 3 by ring, Nat.choose_one_right] at this
  have h1' : ((m : ℤ) + 3) * ((m + 2).choose (2 + i) : ℤ) =
      ((m + 3).choose (3 + i) : ℤ) * (3 + i) := by exact_mod_cast h1
  have h2' : ((m : ℤ) + 2) * ((m + 1).choose (1 + i) : ℤ) =
      ((m + 2).choose (2 + i) : ℤ) * (2 + i) := by exact_mod_cast h2
  have h0' : ((m : ℤ) + 3) * ((m : ℤ) + 2) = ((m + 3).choose 2 : ℤ) * 2 := by exact_mod_cast h0
  linear_combination ((m + 1).choose (1 + i) : ℤ) * h0' - ((m : ℤ) + 3) * h2' - (2 + (i : ℤ)) * h1'

/-- The comparison of powers of `2` in the case `n ≡ 1 (mod 6)`, `β = A - ω`. -/
private lemma two_adic {A : ℤ} (hA : Even A) (hA0 : A ≠ 0) (m : ℕ) (e : ℕ → ℤ)
    (h : ((m + 3).choose 2 : ℤ) * A ^ 2 +
      ∑ i ∈ range (m + 1), ((m + 3).choose (3 + i) : ℤ) * A ^ (3 + i) * e i = 0) : False := by
  obtain ⟨T, hT⟩ : ∃ T, T = ((m + 3).choose 2 : ℤ) * A ^ 2 := ⟨_, rfl⟩
  rw [← hT] at h
  have hT0 : T ≠ 0 := by
    rw [hT]
    exact mul_ne_zero (by exact_mod_cast (Nat.choose_pos (by omega)).ne') (pow_ne_zero 2 hA0)
  obtain ⟨v, t, ht, hvt⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hT0) 2 (by norm_num)
  have hv : (2 : ℤ) ^ v ∣ T := by
    have : ((2 ^ v : ℕ) : ℤ) ∣ T := Int.ofNat_dvd_left.2 ⟨t, hvt⟩
    exact_mod_cast this
  have hnv : ¬ (2 : ℤ) ^ (v + 1) ∣ T := by
    intro hd
    have : 2 ^ (v + 1) ∣ T.natAbs := Int.ofNat_dvd_left.1 (by exact_mod_cast hd)
    rw [hvt, pow_succ] at this
    exact ht ((mul_dvd_mul_iff_left (by positivity : (2 : ℕ) ^ v ≠ 0)).1 this)
  have h2A : (2 : ℤ) ∣ A := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨a, by rw [ha]; ring⟩
  apply hnv
  have hS : (2 : ℤ) ^ (v + 1) ∣
      ∑ i ∈ range (m + 1), ((m + 3).choose (3 + i) : ℤ) * A ^ (3 + i) * e i := by
    apply dvd_sum
    intro i _
    refine two_pow_dvd_of_mul (F := (3 + i) * (2 + i)) (by positivity) (e := i + 1)
      (fun k hk => two_pow_dvd_bound i k hk) ?_
    have hid := choose_id m i
    have e1 : (((3 + i) * (2 + i) : ℕ) : ℤ) * (((m + 3).choose (3 + i) : ℤ) * A ^ (3 + i) * e i) =
        T * (2 * A ^ (1 + i) * (((m + 1).choose (1 + i) : ℤ) * e i)) := by
      rw [hT]; push_cast
      linear_combination (A ^ (3 + i) * e i) * hid
    rw [e1, show v + 1 + (i + 1) = v + (i + 2) by ring, pow_add]
    refine mul_dvd_mul hv (Dvd.dvd.mul_right ?_ _)
    have h4 : (2 : ℤ) ^ (1 + i) ∣ A ^ (1 + i) := pow_dvd_pow_of_dvd h2A _
    rw [show (2 : ℤ) ^ (i + 2) = 2 * 2 ^ (1 + i) by ring]
    exact mul_dvd_mul_left 2 h4
  rw [eq_neg_of_add_eq_zero_left h]
  exact (dvd_neg).2 hS

/-- Lemma P for `β = A + B ω` with `A` even, `B = ± 1` and `n = m + 3`. -/
private lemma lemP_even {A B : ℤ} (hB : B = 1 ∨ B = -1) (hA : Even A) {m : ℕ}
    (h6 : (m + 3) % 6 = 1 ∨ (m + 3) % 6 = 5) (h : ((⟨A, B⟩ : Eis) ^ (m + 3)).im = -1) :
    nrm ⟨A, B⟩ = 1 ∨ nrm ⟨A, B⟩ = 3 := by
  by_cases hA0 : A = 0
  · left
    rw [nrm_mk, hA0]
    rcases hB with rfl | rfl <;> norm_num
  have hβ : (⟨A, B⟩ : Eis) = (A : Eis) + ⟨0, B⟩ := by ext <;> simp
  have hx := expand3 A ⟨0, B⟩ m
  rw [← hβ, h] at hx
  have hsec : A ^ 2 ∣ -1 - ((⟨0, B⟩ : Eis) ^ (m + 3)).im -
      ((m : ℤ) + 3) * A * ((⟨0, B⟩ : Eis) ^ (m + 2)).im := by
    have e : -1 - ((⟨0, B⟩ : Eis) ^ (m + 3)).im -
        ((m : ℤ) + 3) * A * ((⟨0, B⟩ : Eis) ^ (m + 2)).im =
        A ^ 2 * (((m + 3).choose 2 : ℤ) * ((⟨0, B⟩ : Eis) ^ (m + 1)).im) +
        ∑ i ∈ range (m + 1),
          ((m + 3).choose (3 + i) : ℤ) * A ^ (3 + i) * (((⟨0, B⟩ : Eis) ^ (m - i)).im) := by
      linear_combination hx
    rw [e]
    refine dvd_add (dvd_mul_right _ _) (dvd_sum fun i _ => ?_)
    exact ⟨((m + 3).choose (3 + i) : ℤ) * A ^ (1 + i) * (((⟨0, B⟩ : Eis) ^ (m - i)).im),
      by ring⟩
  have hfirst : A ∣ -1 - ((⟨0, B⟩ : Eis) ^ (m + 3)).im := by
    have h1 := (dvd_pow_self A two_ne_zero).trans hsec
    have h2 : A ∣ ((m : ℤ) + 3) * A * ((⟨0, B⟩ : Eis) ^ (m + 2)).im :=
      ⟨((m : ℤ) + 3) * ((⟨0, B⟩ : Eis) ^ (m + 2)).im, by ring⟩
    have := dvd_add h1 h2
    rwa [sub_add_cancel] at this
  rcases hB with rfl | rfl
  · have h6' : (⟨0, 1⟩ : Eis) ^ 6 = 1 := pow_six_of_nrm_one (by rw [nrm_mk]; norm_num)
    have hd : ∀ r, ((⟨0, 1⟩ : Eis) ^ r).im = ((⟨0, 1⟩ : Eis) ^ (r % 6)).im :=
      fun r => by rw [← pow_mod_six h6' r]
    rcases h6 with h1 | h5
    · have e1 : ((⟨0, 1⟩ : Eis) ^ (m + 3)).im = 1 := by rw [hd, h1]; norm_num
      have e2 : ((⟨0, 1⟩ : Eis) ^ (m + 2)).im = 0 := by
        rw [hd, show (m + 2) % 6 = 0 by omega]; norm_num
      rw [e1, e2, show (-1 : ℤ) - 1 - ((m : ℤ) + 3) * A * 0 = -2 by ring] at hsec
      obtain ⟨r, hr⟩ := hA
      have h4 : (4 : ℤ) ∣ -2 := dvd_trans (show (4 : ℤ) ∣ A ^ 2 from ⟨r ^ 2, by rw [hr]; ring⟩) hsec
      omega
    · have e1 : ((⟨0, 1⟩ : Eis) ^ (m + 3)).im = -1 := by rw [hd, h5]; norm_num [pow_succ]
      have e2 : ((⟨0, 1⟩ : Eis) ^ (m + 2)).im = 1 := by
        rw [hd, show (m + 2) % 6 = 4 by omega]; norm_num [pow_succ]
      rw [e1, e2] at hsec
      have h3 : A * A ∣ A * ((m : ℤ) + 3) := by
        have e : A * ((m : ℤ) + 3) = -(-1 - -1 - ((m : ℤ) + 3) * A * 1) := by ring
        rw [e, ← sq]
        exact (dvd_neg).2 hsec
      obtain ⟨c, hc⟩ := (mul_dvd_mul_iff_left hA0).1 h3
      obtain ⟨r, hr⟩ := hA
      have : (m : ℤ) + 3 = 2 * (r * c) := by rw [hc, hr]; ring
      omega
  · have h6' : (⟨0, -1⟩ : Eis) ^ 6 = 1 := pow_six_of_nrm_one (by rw [nrm_mk]; norm_num)
    have hd : ∀ r, ((⟨0, -1⟩ : Eis) ^ r).im = ((⟨0, -1⟩ : Eis) ^ (r % 6)).im :=
      fun r => by rw [← pow_mod_six h6' r]
    rcases h6 with h1 | h5
    · have e1 : ((⟨0, -1⟩ : Eis) ^ (m + 3)).im = -1 := by rw [hd, h1]; norm_num
      have e2 : ((⟨0, -1⟩ : Eis) ^ (m + 2)).im = 0 := by
        rw [hd, show (m + 2) % 6 = 0 by omega]; norm_num
      have e3 : ((⟨0, -1⟩ : Eis) ^ (m + 1)).im = 1 := by
        rw [hd, show (m + 1) % 6 = 5 by omega]; norm_num [pow_succ]
      rw [e1, e2, e3] at hx
      exact (two_adic hA hA0 m (fun i => ((⟨0, -1⟩ : Eis) ^ (m - i)).im)
        (by linear_combination -hx)).elim
    · have e1 : ((⟨0, -1⟩ : Eis) ^ (m + 3)).im = 1 := by rw [hd, h5]; norm_num [pow_succ]
      rw [e1] at hfirst
      have hγ6 : (⟨-1, -1⟩ : Eis) ^ 6 = 1 := pow_six_of_nrm_one (by rw [nrm_mk]; norm_num)
      have hγ : ((⟨-1, -1⟩ : Eis) ^ (m + 3)).im = 1 := by
        rw [pow_mod_six hγ6, h5]; norm_num [pow_succ]
      have hg := (Commute.all (⟨A, -1⟩ : Eis) ⟨-1, -1⟩).sub_dvd_pow_sub_pow (m + 3)
      rw [show (⟨A, -1⟩ : Eis) - ⟨-1, -1⟩ = ((A + 1 : ℤ) : Eis) by ext <;> simp,
        intCast_dvd_iff] at hg
      have hg2 := hg.2
      rw [im_sub, h, hγ] at hg2
      have hA2 : A ∣ 2 := by
        have : A ∣ -(-1 - 1) := (dvd_neg).2 hfirst
        norm_num at this
        exact this
      have hle1 := Int.le_of_dvd (by norm_num) hA2
      have hle2 := Int.le_of_dvd (by norm_num) ((neg_dvd).2 hA2)
      obtain ⟨r, hr⟩ := hA
      rcases (show A = 2 ∨ A = -2 by omega) with rfl | rfl
      · norm_num at hg2
      · right
        rw [nrm_mk]; norm_num

/-- Lemma P: if `n ≥ 2`, `n ≡ ± 1 (mod 6)` and `(β ^ n).im = -1`, then `nrm β` is `1` or `3`. -/
private lemma lemP {β : Eis} {n : ℕ} (hn : 2 ≤ n) (h6 : n % 6 = 1 ∨ n % 6 = 5)
    (h : (β ^ n).im = -1) : nrm β = 1 ∨ nrm β = 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hB : β.im = 1 ∨ β.im = -1 := by
    have hd := eis_im_dvd_im_pow β (m + 3)
    rw [h] at hd
    exact Int.isUnit_iff.mp (isUnit_of_dvd_one (dvd_neg.mp hd))
  rcases Int.even_or_odd β.re with he | ho
  · exact lemP_even hB he h6 h
  · have hodd : Odd (m + 3) := by
      rcases h6 with h6 | h6 <;> exact Nat.odd_iff.2 (by omega)
    have e : (⟨β.im - β.re, β.im⟩ : Eis) = -star β := by
      ext <;> simp; ring
    have h' : ((⟨β.im - β.re, β.im⟩ : Eis) ^ (m + 3)).im = -1 := by
      rw [e, hodd.neg_pow, ← star_pow, im_neg, im_star, neg_neg, h]
    have hn' : nrm (⟨β.im - β.re, β.im⟩ : Eis) = nrm β := by
      rw [nrm_mk]; simp only [nrm]; ring
    have heven : Even (β.im - β.re) := by
      refine ⟨(β.im - β.re) / 2, ?_⟩
      obtain ⟨k, hk⟩ := ho
      rcases hB with hb | hb <;> omega
    have := lemP_even hB heven h6 h'
    rwa [hn'] at this

end NagellPrime

open NagellPrime Eis in
/-- If `phi3 x = q ^ j` with `q` prime and `j ≥ 1`, then `j` has no factor `n ≥ 2` with `2 ∤ n`
and `3 ∤ n`. Elementary, in the Eisenstein integers; no classical hypothesis. -/
theorem not_phi3_eq_prime_pow_of_dvd {q x j n j' : ℕ} (hq : q.Prime) (hj : 1 ≤ j)
    (h : phi3 x = q ^ j) (hjn : j = n * j') (hn : 2 ≤ n) (hn2 : ¬ 2 ∣ n) (hn3 : ¬ 3 ∣ n) :
    False := by
  subst hjn
  have hj' : 1 ≤ j' := by
    rcases Nat.eq_zero_or_pos j' with h0 | h0
    · rw [h0, mul_zero] at hj; omega
    · exact h0
  have hq3 : q ≠ 3 := by
    rintro rfl
    apply not_nine_dvd_phi3 x
    rw [h]
    have : 3 ^ 2 ∣ 3 ^ (n * j') := pow_dvd_pow 3 (by nlinarith)
    simpa using this
  have hrow : Eis.nrm ⟨(x : ℤ), -1⟩ = 1 * (q : ℤ) ^ (n * j') := by
    have : ((phi3 x : ℕ) : ℤ) = ((q ^ (n * j') : ℕ) : ℤ) := by rw [h]
    push_cast [phi3] at this
    rw [nrm_mk]
    linear_combination this
  obtain ⟨ρ, θ, hρ, hθ, hx⟩ := exists_root_pow_mul_of_row hq hq3 x (n * j') (by nlinarith) 1 hrow
  have h6 := pow_six_of_nrm_one hθ
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (θ ^ k) ^ n = θ := by
    rcases (show n % 6 = 1 ∨ n % 6 = 5 by omega) with h1 | h5
    · exact ⟨1, by rw [pow_one, pow_mod_six h6, h1, pow_one]⟩
    · exact ⟨5, by rw [← pow_mul, pow_mod_six h6, show 5 * n % 6 = 1 by omega, pow_one]⟩
  have hβ : (θ ^ k * ρ ^ j') ^ n = ⟨(x : ℤ), -1⟩ := by
    rw [mul_pow, hk, ← pow_mul, mul_comm j' n, hx, mul_comm]
  have hnβ : nrm (θ ^ k * ρ ^ j') = (q : ℤ) ^ j' := by
    rw [nrm_mul, nrm_pow', nrm_pow', hθ, hρ, one_pow, one_mul]
  have hqj : 1 < q ^ j' := Nat.one_lt_pow (by omega) hq.one_lt
  rcases lemP (β := θ ^ k * ρ ^ j') hn (by omega) (by rw [hβ]) with h1 | h3
  · rw [hnβ] at h1
    have : q ^ j' = 1 := by exact_mod_cast h1
    omega
  · rw [hnβ] at h3
    have h3' : q ^ j' = 3 := by exact_mod_cast h3
    have hd : q ∣ 3 := h3' ▸ dvd_pow_self q (by omega)
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 hd)

/-- Nagell's theorem (1921) for prime `x` and a prime power on the right: if `x` and `q` are
primes and `phi3 x = q ^ j` with `j ≥ 1`, then `j = 1`. Known mathematics, proved here by an
elementary argument in the Eisenstein integers. The primality of `x` is needed for the cube
case: `phi3 18 = 7 ^ 3`. -/
theorem phi3_eq_prime_pow_exponent {q x j : ℕ} (hq : q.Prime) (hx : x.Prime) (hj : 1 ≤ j)
    (h : phi3 x = q ^ j) : j = 1 := by
  by_contra hj1
  obtain ⟨ℓ, hℓ, j', hj'⟩ := Nat.exists_prime_and_dvd hj1
  by_cases h2 : ℓ = 2
  · subst h2
    exact not_isSquare_phi3 hx.one_lt.le ⟨q ^ j', by rw [h, hj', mul_comm, pow_mul, sq]⟩
  · by_cases h3 : ℓ = 3
    · subst h3
      exact phi3_ne_cube_of_prime hx (q ^ j') (by rw [h, hj', pow_mul'])
    · exact not_phi3_eq_prime_pow_of_dvd hq hj h hj' hℓ.two_le
        (fun hd => h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 hd).symm)
        (fun hd => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 hd).symm)

/-- The hypothesis `NagellPrimePower` used elsewhere in the library holds: this is Nagell's
classical theorem for prime `x` and a prime power on the right, proved here elementarily. It is
known mathematics; nothing here decides the odd perfect number conjecture. -/
theorem nagellPrimePower : NagellPrimePower := by
  intro p r a hp hr ha h
  exact phi3_eq_prime_pow_exponent hr hp ha h

/-- Controls. `18` is not prime: the cube case needs a prime input. `22` and `313` show that
the equation with the factor `3` behaves differently. -/
example : 18 ^ 2 + 18 + 1 = 7 ^ 3 ∧ 3 ^ 2 + 3 + 1 = 13 ∧ 22 ^ 2 + 22 + 1 = 3 * 13 ^ 2 ∧
    313 ^ 2 + 313 + 1 = 3 * 181 ^ 2 := by norm_num

end OddPerfect

#print axioms OddPerfect.not_phi3_eq_prime_pow_of_dvd
#print axioms OddPerfect.phi3_eq_prime_pow_exponent
#print axioms OddPerfect.nagellPrimePower
