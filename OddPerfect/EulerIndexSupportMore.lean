import OddPerfect.EulerIndexSupport

/-!
# More half sums that are not squares, and the Euler index

Let `N = q ^ k * m ^ 2` be an odd perfect number in Euler's form, with `q` the special prime
and `q ∤ m`, and let `J = eulerIndex q k m`. This module extends `OddPerfect.EulerIndexSupport`
by three more elementary restricted results.

* For `U > 1` with `U ≡ 1 (mod 4)`, none of `(U ^ 7 + 1) / 2`, `(U ^ 11 + 1) / 2` and
  `(U ^ 13 + 1) / 2` is a square.
* Hence two distinct primes have odd valuation in `J`, and `J` has at least two distinct prime
  factors, when `k ≡ 13 (mod 28)`, `k ≡ 21 (mod 44)` or `k ≡ 25 (mod 52)`.

Method, for `p = 7, 11, 13`, `U = 4 a + 1` and `F = (U ^ p + 1) / (U + 1)`: the half sum is
`(2 a + 1) * F` and `F ≡ p (mod 2 a + 1)`, so a square half sum makes `F` a square or `p` times
a square. The second is ruled out modulo `8`. The first is ruled out by an odd `P` with
`(P - 1) ^ 2 < T ^ 2 * F < (P + 1) ^ 2` for an even `T`, valid for large `a`, and by exhibited
integer square roots for the finitely many small `a`.

These are elementary restricted results. The general statement for every exponent is the
proposition `HalfPowerNotSquare`, proved in `OddPerfect.EulerIndexSupportAll`. All of this is
known mathematics or elementary; novelty not verified.
-/

namespace OddPerfect

variable {N q k m : ℕ}

/-! ## Private helpers -/

/-- The special prime is `1 (mod 4)` and so is its exponent. -/
private lemma eism_special_facts (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ k * m ^ 2)
    (hqm : ¬ q ∣ m) : q % 4 = 1 ∧ k % 4 = 1 := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hfac : N.factorization q = k := by
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
      Finsupp.smul_apply, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  have hk : Odd k := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  have h4 := special_mod_four h hq (hfac ▸ hk)
  rwa [hfac] at h4

/-- A coprime factor of a square is a square. -/
private lemma eism_isSquare_left_of_coprime {a b c : ℕ} (hab : Nat.Coprime a b)
    (h : a * b = c ^ 2) : IsSquare a := by
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hab) h
  exact ⟨d, by rw [hd, sq]⟩

/-- If `A F = t ^ 2` and `gcd(A, F) ∣ p` for a prime `p`, then `F` is a square or `p` times a
square. -/
private lemma eism_sq_or_mul_sq {A F t p : ℕ} (hp : p.Prime) (hg : Nat.gcd A F ∣ p)
    (h : A * F = t ^ 2) : IsSquare F ∨ ∃ s, F = p * s ^ 2 := by
  rcases (Nat.dvd_prime hp).mp hg with h1 | h1
  · left
    exact eism_isSquare_left_of_coprime (Nat.Coprime.symm h1) (by rw [mul_comm]; exact h)
  · right
    obtain ⟨A', hA⟩ : p ∣ A := h1 ▸ Nat.gcd_dvd_left A F
    obtain ⟨F', hF⟩ : p ∣ F := h1 ▸ Nat.gcd_dvd_right A F
    have hc : Nat.Coprime A' F' := by
      have h2 : p * Nat.gcd A' F' = p * 1 := by
        rw [← Nat.gcd_mul_left, ← hA, ← hF, h1, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hp.pos h2
    have hpt : p ∣ t := hp.dvd_of_dvd_pow ⟨p * A' * F', by rw [← h, hA, hF]; ring⟩
    obtain ⟨s, rfl⟩ := hpt
    have hAF : A' * F' = s ^ 2 := by
      have h3 : p ^ 2 * (A' * F') = p ^ 2 * s ^ 2 := by rw [← mul_pow, ← h, hA, hF]; ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h3
    obtain ⟨d, hd⟩ := eism_isSquare_left_of_coprime hc.symm (by rw [mul_comm]; exact hAF)
    exact ⟨d, by rw [hF, hd, sq]⟩

/-- Two distinct primes of odd valuation give two distinct prime factors. -/
private lemma eism_two_le_card_of_odd {n p₁ p₂ : ℕ} (hne : p₁ ≠ p₂)
    (h₁ : Odd (n.factorization p₁)) (h₂ : Odd (n.factorization p₂)) :
    2 ≤ n.primeFactors.card := by
  have hm : ∀ p, Odd (n.factorization p) → p ∈ n.primeFactors := by
    intro p hp
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    intro h0
    rw [h0] at hp
    exact Nat.not_odd_zero hp
  exact Finset.one_lt_card.mpr ⟨p₁, hm _ h₁, p₂, hm _ h₂, hne⟩

/-- The shared reduction: if `(4 a + 1) ^ n + 1 = 2 (2 a + 1) F`, `F ≡ p (mod 2 a + 1)` for a
prime `p`, and `F` is neither a square nor `p` times a square, then the half sum is not a
square. -/
private lemma eism_combine {a n p F : ℕ} (hp : p.Prime)
    (hfac : (4 * a + 1) ^ n + 1 = 2 * ((2 * a + 1) * F))
    (hG : ∃ G : ℤ, (F : ℤ) = (2 * a + 1) * G + p) (h1 : ∀ s, F ≠ s ^ 2)
    (h2 : ∀ s, F ≠ p * s ^ 2) : ¬ IsSquare (((4 * a + 1) ^ n + 1) / 2) := by
  rintro ⟨t, ht⟩
  rw [hfac, Nat.mul_div_cancel_left _ two_pos] at ht
  have hg : Nat.gcd (2 * a + 1) F ∣ p := by
    obtain ⟨G, hG⟩ := hG
    have hl : ((Nat.gcd (2 * a + 1) F : ℕ) : ℤ) ∣ ((2 * a + 1 : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
    have hr : ((Nat.gcd (2 * a + 1) F : ℕ) : ℤ) ∣ (F : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
    push_cast at hl
    have h3 := dvd_sub hr (dvd_mul_of_dvd_left hl G)
    rw [hG, add_sub_cancel_left] at h3
    exact Int.natCast_dvd_natCast.mp h3
  rcases eism_sq_or_mul_sq hp hg (by rw [ht, sq]) with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact h1 s (by rw [hs, sq])
  · exact h2 s hs

/-- If `X ^ 2 < z ^ 2 < (X + 2) ^ 2`, then `z = X + 1`. -/
private lemma eism_between {X Y R1 R2 z : ℕ} (hlo : X * X + R1 = Y)
    (hhi : Y + R2 = (X + 2) * (X + 2)) (h1 : 0 < R1) (h2 : 0 < R2) (hY : Y = z * z) :
    z = X + 1 := by
  subst hY
  rcases le_or_gt z X with h | h
  · have := Nat.mul_le_mul h h
    omega
  · rcases le_or_gt (X + 2) z with h' | h'
    · have := Nat.mul_le_mul h' h'
      omega
    · omega

/-! ## Three half sums that are not squares -/

/-- The cofactor `F = (U ^ 7 + 1) / (U + 1)` at `U = 4 a + 1`. -/
private def eism_F7 (a : ℕ) : ℕ := 4096 * a ^ 6 + 5120 * a ^ 5 + 2816 * a ^ 4 + 832 * a ^ 3
    + 144 * a ^ 2 + 12 * a + 1

private lemma eism_F7_fac (a : ℕ) :
    (4 * a + 1) ^ 7 + 1 = 2 * ((2 * a + 1) * eism_F7 a) := by
  unfold eism_F7; ring

private lemma eism_F7_rem (a : ℕ) :
    ∃ G : ℤ, (eism_F7 a : ℤ) = (2 * a + 1) * G + 7 :=
  ⟨2048 * (a : ℤ) ^ 5 + 1536 * (a : ℤ) ^ 4 + 640 * (a : ℤ) ^ 3 + 96 * (a : ℤ) ^ 2 + 24 * (a : ℤ)
    - 6, by unfold eism_F7; push_cast; ring⟩

/-- `F` is never `7` times a square: compare both sides modulo `8`. -/
private lemma eism_F7_ne_mul_sq (a s : ℕ) : eism_F7 a ≠ 7 * s ^ 2 := by
  intro hs
  obtain ⟨b, e, he, rfl⟩ : ∃ b e, e < 2 ∧ a = 2 * b + e :=
    ⟨a / 2, a % 2, Nat.mod_lt _ (by norm_num), by omega⟩
  obtain ⟨w, d, hd, rfl⟩ : ∃ w d, d < 4 ∧ s = 4 * w + d :=
    ⟨s / 4, s % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  unfold eism_F7 at hs
  interval_cases e <;> interval_cases d <;> ring_nf at hs <;> omega

/-- `F` is not a square for `a ≥ 1`: `16 * s` would lie strictly between `P - 1`
and `P + 1` for an odd `P`. -/
private lemma eism_F7_ne_sq_large (c s : ℕ) : eism_F7 (c + 1) ≠ s ^ 2 := by
  intro hs
  have h := eism_between (z := 16 * s)
    (X := 1024 * c ^ 3 + 3712 * c ^ 2 + 4504 * c + 1824)
    (Y := 16 ^ 2 * eism_F7 (c + 1))
    (R1 := 2048 * c ^ 3 + 9664 * c ^ 2 + 13824 * c + 6400)
    (R2 := 2048 * c ^ 3 + 5184 * c ^ 2 + 4192 * c + 900)
    (by unfold eism_F7; ring) (by unfold eism_F7; ring) (by positivity) (by positivity)
    (by rw [hs]; ring)
  omega

private lemma eism_F7_ne_sq {a : ℕ} (ha : 1 ≤ a) (s : ℕ) : eism_F7 a ≠ s ^ 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  exact eism_F7_ne_sq_large c s

/-- For `U > 1` with `U ≡ 1 (mod 4)`, `(U ^ 7 + 1) / 2` is not a square. Known mathematics or
elementary; novelty not verified. -/
theorem not_isSquare_half_seventh_succ {U : ℕ} (hU : 1 < U) (h4 : U % 4 = 1) :
    ¬ IsSquare ((U ^ 7 + 1) / 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, U = 4 * a + 1 := ⟨U / 4, by omega⟩
  exact eism_combine (by norm_num) (eism_F7_fac a) (eism_F7_rem a)
    (eism_F7_ne_sq (by omega)) (eism_F7_ne_mul_sq a)

/-- The cofactor `F = (U ^ 11 + 1) / (U + 1)` at `U = 4 a + 1`. -/
private def eism_F11 (a : ℕ) : ℕ := 1048576 * a ^ 10 + 2359296 * a ^ 9 + 2424832 * a ^ 8
    + 1490944 * a ^ 7 + 606208 * a ^ 6 + 169984 * a ^ 5 + 33280 * a ^ 4 + 4480 * a ^ 3
    + 400 * a ^ 2 + 20 * a + 1

private lemma eism_F11_fac (a : ℕ) :
    (4 * a + 1) ^ 11 + 1 = 2 * ((2 * a + 1) * eism_F11 a) := by
  unfold eism_F11; ring

private lemma eism_F11_rem (a : ℕ) :
    ∃ G : ℤ, (eism_F11 a : ℤ) = (2 * a + 1) * G + 11 :=
  ⟨524288 * (a : ℤ) ^ 9 + 917504 * (a : ℤ) ^ 8 + 753664 * (a : ℤ) ^ 7 + 368640 * (a : ℤ) ^ 6
    + 118784 * (a : ℤ) ^ 5 + 25600 * (a : ℤ) ^ 4 + 3840 * (a : ℤ) ^ 3 + 320 * (a : ℤ) ^ 2
    + 40 * (a : ℤ) - 10, by unfold eism_F11; push_cast; ring⟩

/-- `F` is never `11` times a square: compare both sides modulo `8`. -/
private lemma eism_F11_ne_mul_sq (a s : ℕ) : eism_F11 a ≠ 11 * s ^ 2 := by
  intro hs
  obtain ⟨b, e, he, rfl⟩ : ∃ b e, e < 2 ∧ a = 2 * b + e :=
    ⟨a / 2, a % 2, Nat.mod_lt _ (by norm_num), by omega⟩
  obtain ⟨w, d, hd, rfl⟩ : ∃ w d, d < 4 ∧ s = 4 * w + d :=
    ⟨s / 4, s % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  unfold eism_F11 at hs
  interval_cases e <;> interval_cases d <;> ring_nf at hs <;> omega

/-- `F` is not a square for `a ≥ 14`: `256 * s` would lie strictly between `P - 1`
and `P + 1` for an odd `P`. -/
private lemma eism_F11_ne_sq_large (c s : ℕ) : eism_F11 (c + 14) ≠ s ^ 2 := by
  intro hs
  have h := eism_between (z := 256 * s)
    (X := 262144 * c ^ 5 + 18644992 * c ^ 4 + 530454528 * c ^ 3 + 7545842944 * c ^ 2
      + 53671156504 * c + 152699520998)
    (Y := 256 ^ 2 * eism_F11 (c + 14))
    (R1 := 524288 * c ^ 5 + 44859392 * c ^ 4 + 1489661952 * c ^ 3 + 24199303616 * c ^ 2
      + 193330872544 * c + 609857412444)
    (R2 := 524288 * c ^ 5 + 29720576 * c ^ 4 + 632156160 * c ^ 3 + 5984068160 * c ^ 2
      + 21353753472 * c + 940671552)
    (by unfold eism_F11; ring) (by unfold eism_F11; ring) (by positivity) (by positivity)
    (by rw [hs]; ring)
  omega

/-- Integer square roots of `eism_F11 a` for `a < 14` (entry `0` unused). -/
private def eism_R11 : List ℕ := [0, 2852, 56018, 357786, 1379852, 3990201, 9575983, 20166399,
    38555577, 68425453, 114468651, 182511363, 279636229, 414305217]

private lemma eism_F11_small : ∀ a, a < 14 → 1 ≤ a →
    (eism_R11.getD a 0) ^ 2 < eism_F11 a ∧ eism_F11 a < (eism_R11.getD a 0 + 1) ^ 2 := by
  decide +kernel

private lemma eism_F11_ne_sq {a : ℕ} (ha : 1 ≤ a) (s : ℕ) : eism_F11 a ≠ s ^ 2 := by
  intro hs
  rcases lt_or_ge a 14 with h | h
  · obtain ⟨h1, h2⟩ := eism_F11_small a h ha
    rw [hs] at h1 h2
    have := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h1
    have := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h2
    omega
  · obtain ⟨c, rfl⟩ : ∃ c, a = c + 14 := ⟨a - 14, by omega⟩
    exact eism_F11_ne_sq_large c s hs

/-- For `U > 1` with `U ≡ 1 (mod 4)`, `(U ^ 11 + 1) / 2` is not a square. Known mathematics or
elementary; novelty not verified. -/
theorem not_isSquare_half_eleventh_succ {U : ℕ} (hU : 1 < U) (h4 : U % 4 = 1) :
    ¬ IsSquare ((U ^ 11 + 1) / 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, U = 4 * a + 1 := ⟨U / 4, by omega⟩
  exact eism_combine (by norm_num) (eism_F11_fac a) (eism_F11_rem a)
    (eism_F11_ne_sq (by omega)) (eism_F11_ne_mul_sq a)

/-- The cofactor `F = (U ^ 13 + 1) / (U + 1)` at `U = 4 a + 1`. -/
private def eism_F13 (a : ℕ) : ℕ := 16777216 * a ^ 12 + 46137344 * a ^ 11 + 58720256 * a ^ 10
    + 45613056 * a ^ 9 + 24051712 * a ^ 8 + 9060352 * a ^ 7 + 2498560 * a ^ 6 + 507904 * a ^ 5
    + 75520 * a ^ 4 + 8000 * a ^ 3 + 576 * a ^ 2 + 24 * a + 1

private lemma eism_F13_fac (a : ℕ) :
    (4 * a + 1) ^ 13 + 1 = 2 * ((2 * a + 1) * eism_F13 a) := by
  unfold eism_F13; ring

private lemma eism_F13_rem (a : ℕ) :
    ∃ G : ℤ, (eism_F13 a : ℤ) = (2 * a + 1) * G + 13 :=
  ⟨8388608 * (a : ℤ) ^ 11 + 18874368 * (a : ℤ) ^ 10 + 19922944 * (a : ℤ) ^ 9
    + 12845056 * (a : ℤ) ^ 8 + 5603328 * (a : ℤ) ^ 7 + 1728512 * (a : ℤ) ^ 6 + 385024 * (a : ℤ) ^ 5
    + 61440 * (a : ℤ) ^ 4 + 7040 * (a : ℤ) ^ 3 + 480 * (a : ℤ) ^ 2 + 48 * (a : ℤ) - 12,
    by unfold eism_F13; push_cast; ring⟩

/-- `F` is never `13` times a square: compare both sides modulo `8`. -/
private lemma eism_F13_ne_mul_sq (a s : ℕ) : eism_F13 a ≠ 13 * s ^ 2 := by
  intro hs
  obtain ⟨b, e, he, rfl⟩ : ∃ b e, e < 2 ∧ a = 2 * b + e :=
    ⟨a / 2, a % 2, Nat.mod_lt _ (by norm_num), by omega⟩
  obtain ⟨w, d, hd, rfl⟩ : ∃ w d, d < 4 ∧ s = 4 * w + d :=
    ⟨s / 4, s % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  unfold eism_F13 at hs
  interval_cases e <;> interval_cases d <;> ring_nf at hs <;> omega

/-- `F` is not a square for `a ≥ 54`: `1024 * s` would lie strictly between `P - 1`
and `P + 1` for an odd `P`. -/
private lemma eism_F13_ne_sq_large (c s : ℕ) : eism_F13 (c + 54) ≠ s ^ 2 := by
  intro hs
  have h := eism_between (z := 1024 * s)
    (X := 4194304 * c ^ 6 + 1364721664 * c ^ 5 + 185019367424 * c ^ 4 + 13377938403328 * c ^ 3
      + 544106463184256 * c ^ 2 + 11802594073728976 * c + 106674343762289442)
    (Y := 1024 ^ 2 * eism_F13 (c + 54))
    (R1 := 8388608 * c ^ 6 + 2279604224 * c ^ 5 + 248181538816 * c ^ 4 + 13551862632448 * c ^ 3
      + 372841452765440 * c ^ 2 + 4226334387195072 * c + 3365092448579452)
    (R2 := 8388608 * c ^ 6 + 3179282432 * c ^ 5 + 491895930880 * c ^ 4 + 39959890980864 * c ^ 3
      + 1803584399971584 * c ^ 2 + 42984041907720832 * c + 423332282600578320)
    (by unfold eism_F13; ring) (by unfold eism_F13; ring) (by positivity) (by positivity)
    (by rw [hs]; ring)
  omega

/-- Integer square roots of `eism_F13 a` for `a < 54` (entry `0` unused). -/
private def eism_R13 : List ℕ := [0, 14263, 504169, 4651229, 23457500, 83794222, 239399579,
    584825578, 1272334052, 2531741777, 4693214712, 8213011363, 13702175256, 21958176544,
    33999502722, 51103198471, 74845354616, 107144546202, 150308219704, 207082029336, 280702122499,
    374950374337, 494212571418, 643539544533, 828711250619, 1056303803796, 1333759455528,
    1669459523902, 2072800272031, 2554271735571, 3125539499361, 3799529423187, 4590515316655,
    5514209563198, 6587856693191, 7830329906196, 9262230542315, 10905990502676, 12785977619033,
    14928603972480, 17362437161298, 20118314517911, 23229460274967, 26731605680537,
    30663112062438, 35065096841670, 39981562494977, 45459528466526, 51549166028710,
    58303936092065, 65780729964310, 74040013058511, 83145971550354, 93166661984552]

private lemma eism_F13_small : ∀ a, a < 54 → 1 ≤ a →
    (eism_R13.getD a 0) ^ 2 < eism_F13 a ∧ eism_F13 a < (eism_R13.getD a 0 + 1) ^ 2 := by
  decide +kernel

private lemma eism_F13_ne_sq {a : ℕ} (ha : 1 ≤ a) (s : ℕ) : eism_F13 a ≠ s ^ 2 := by
  intro hs
  rcases lt_or_ge a 54 with h | h
  · obtain ⟨h1, h2⟩ := eism_F13_small a h ha
    rw [hs] at h1 h2
    have := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h1
    have := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h2
    omega
  · obtain ⟨c, rfl⟩ : ∃ c, a = c + 54 := ⟨a - 54, by omega⟩
    exact eism_F13_ne_sq_large c s hs

/-- For `U > 1` with `U ≡ 1 (mod 4)`, `(U ^ 13 + 1) / 2` is not a square. Known mathematics or
elementary; novelty not verified. -/
theorem not_isSquare_half_thirteenth_succ {U : ℕ} (hU : 1 < U) (h4 : U % 4 = 1) :
    ¬ IsSquare ((U ^ 13 + 1) / 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, U = 4 * a + 1 := ⟨U / 4, by omega⟩
  exact eism_combine (by norm_num) (eism_F13_fac a) (eism_F13_rem a)
    (eism_F13_ne_sq (by omega)) (eism_F13_ne_mul_sq a)

/-! ## Consequences for the Euler index -/

/-- `q ^ n ≡ 1 (mod 4)` and `q ^ n > 1` for `q ≡ 1 (mod 4)` prime and `n > 0`. -/
private lemma eism_pow_facts (hq : q.Prime) (hq4 : q % 4 = 1) {n : ℕ} (hn : n ≠ 0) :
    1 < q ^ n ∧ q ^ n % 4 = 1 := by
  refine ⟨Nat.one_lt_pow hn hq.one_lt, ?_⟩
  simp [Nat.pow_mod, hq4]

/-- The pair statement together with the count of prime factors. -/
private lemma eism_odd_and_card (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k ≠ 1)
    (hS : ¬ IsSquare ((q ^ ((k + 1) / 2) + 1) / 2)) :
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      Odd ((eulerIndex q k m).factorization p₁) ∧
      Odd ((eulerIndex q k m).factorization p₂)) ∧
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  obtain ⟨p₁, p₂, hp₁, hp₂, hne, h₁, h₂⟩ :=
    exists_two_odd_valuation_of_half_not_square h hq hN hqm hk hS
  exact ⟨⟨p₁, p₂, hp₁, hp₂, hne, h₁, h₂⟩, eism_two_le_card_of_odd hne h₁ h₂⟩

/-- For an odd perfect number `q ^ k * m ^ 2` with special prime `q`, `q ∤ m` and
`k ≡ 13 (mod 28)`, two distinct primes have odd valuation in the Euler index, which therefore
has at least two distinct prime factors. Known mathematics or elementary; novelty not
verified. -/
theorem exists_two_odd_valuation_of_exponent_mod_twentyeight (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k % 28 = 13) :
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      Odd ((eulerIndex q k m).factorization p₁) ∧
      Odd ((eulerIndex q k m).factorization p₂)) ∧
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  have hq4 := (eism_special_facts h hq hN hqm).1
  refine eism_odd_and_card h hq hN hqm (by omega) ?_
  obtain ⟨hU, hU4⟩ := eism_pow_facts hq hq4 (n := 2 * (k / 28) + 1) (by omega)
  rw [show (k + 1) / 2 = (2 * (k / 28) + 1) * 7 by omega, pow_mul]
  exact not_isSquare_half_seventh_succ hU hU4

/-- For an odd perfect number `q ^ k * m ^ 2` with special prime `q`, `q ∤ m` and
`k ≡ 21 (mod 44)`, two distinct primes have odd valuation in the Euler index, which therefore
has at least two distinct prime factors. Known mathematics or elementary; novelty not
verified. -/
theorem exists_two_odd_valuation_of_exponent_mod_fortyfour (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k % 44 = 21) :
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      Odd ((eulerIndex q k m).factorization p₁) ∧
      Odd ((eulerIndex q k m).factorization p₂)) ∧
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  have hq4 := (eism_special_facts h hq hN hqm).1
  refine eism_odd_and_card h hq hN hqm (by omega) ?_
  obtain ⟨hU, hU4⟩ := eism_pow_facts hq hq4 (n := 2 * (k / 44) + 1) (by omega)
  rw [show (k + 1) / 2 = (2 * (k / 44) + 1) * 11 by omega, pow_mul]
  exact not_isSquare_half_eleventh_succ hU hU4

/-- For an odd perfect number `q ^ k * m ^ 2` with special prime `q`, `q ∤ m` and
`k ≡ 25 (mod 52)`, two distinct primes have odd valuation in the Euler index, which therefore
has at least two distinct prime factors. Known mathematics or elementary; novelty not
verified. -/
theorem exists_two_odd_valuation_of_exponent_mod_fiftytwo (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k % 52 = 25) :
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      Odd ((eulerIndex q k m).factorization p₁) ∧
      Odd ((eulerIndex q k m).factorization p₂)) ∧
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  have hq4 := (eism_special_facts h hq hN hqm).1
  refine eism_odd_and_card h hq hN hqm (by omega) ?_
  obtain ⟨hU, hU4⟩ := eism_pow_facts hq hq4 (n := 2 * (k / 52) + 1) (by omega)
  rw [show (k + 1) / 2 = (2 * (k / 52) + 1) * 13 by omega, pow_mul]
  exact not_isSquare_half_thirteenth_succ hU hU4

/-- For an odd perfect number `q ^ k * m ^ 2` with special prime `q` and `q ∤ m`, the Euler
index has at least two distinct prime factors when `k = 1`, `q ≡ 5 (mod 8)`, `k ≡ 5 (mod 12)`,
`k ≡ 9 (mod 20)`, `k ≡ 13 (mod 28)`, `k ≡ 21 (mod 44)` or `k ≡ 25 (mod 52)`. Known
mathematics or elementary; novelty not verified. -/
theorem two_le_card_primeFactors_eulerIndex_of_cases_more (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m)
    (hc : k = 1 ∨ q % 8 = 5 ∨ k % 12 = 5 ∨ k % 20 = 9 ∨ k % 28 = 13 ∨ k % 44 = 21 ∨
      k % 52 = 25) :
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  rcases hc with hc | hc | hc | hc | hc | hc | hc
  · exact two_le_card_primeFactors_eulerIndex_of_cases h hq hN hqm (Or.inl hc)
  · exact two_le_card_primeFactors_eulerIndex_of_cases h hq hN hqm (Or.inr (Or.inl hc))
  · exact two_le_card_primeFactors_eulerIndex_of_cases h hq hN hqm
      (Or.inr (Or.inr (Or.inl hc)))
  · exact two_le_card_primeFactors_eulerIndex_of_cases h hq hN hqm
      (Or.inr (Or.inr (Or.inr hc)))
  · exact (exists_two_odd_valuation_of_exponent_mod_twentyeight h hq hN hqm hc).2
  · exact (exists_two_odd_valuation_of_exponent_mod_fortyfour h hq hN hqm hc).2
  · exact (exists_two_odd_valuation_of_exponent_mod_fiftytwo h hq hN hqm hc).2

end OddPerfect

#print axioms OddPerfect.not_isSquare_half_seventh_succ
#print axioms OddPerfect.not_isSquare_half_eleventh_succ
#print axioms OddPerfect.not_isSquare_half_thirteenth_succ
#print axioms OddPerfect.exists_two_odd_valuation_of_exponent_mod_twentyeight
#print axioms OddPerfect.exists_two_odd_valuation_of_exponent_mod_fortyfour
#print axioms OddPerfect.exists_two_odd_valuation_of_exponent_mod_fiftytwo
#print axioms OddPerfect.two_le_card_primeFactors_eulerIndex_of_cases_more
