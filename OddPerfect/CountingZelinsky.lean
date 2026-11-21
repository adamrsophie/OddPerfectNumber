import OddPerfect.Counting

/-!
# Zelinsky's counting bounds for odd perfect numbers

Following J. Zelinsky, arXiv 1706.07009, for an odd perfect number `N`:

* if `3 ∤ N` then `8 ω(N) ≤ 3 Ω(N) + 7`;
* if `3 ∣ N` then `21 ω(N) ≤ 8 Ω(N) + 39`.

Write `S₂`, `S₁` for the exponent 2 primes that are `2`, resp. `1 (mod 3)`. The new ingredient
over `OddPerfect.Counting` is injectivity: for `p ∈ S₂` such that `σ(p ^ 2)` has at most two
prime factors, the largest prime factor `P` of `σ(p ^ 2)` (characterized by `σ(p ^ 2) ≤ P ^ 2`)
determines `p`, because a prime shared by `σ(a ^ 2)` and `σ(b ^ 2)` with `b < a` is at most `a`
(Zelinsky's Lemma 2). Likewise the 3-free part of `σ(p ^ 2)`, when prime, determines `p`;
this uses Ochem and Rao's Lemma 3, proved here by an elementary argument:
`3 (x ^ 2 + x + 1) = y ^ 2 + y + 1` forces `y = 3a + 1` and `x (x + 1) = 3 a (a + 1)`, which
has no solution with `x` an odd prime. The quantity `f₃` in the paper is `v_3(N)`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

/-- Ochem and Rao, Lemma 3: if `x` is an odd prime then `3 (x ^ 2 + x + 1)` is never of the
form `y ^ 2 + y + 1`. -/
theorem three_mul_phi3_ne_phi3 {x y : ℕ} (hx : x.Prime) (hx2 : x ≠ 2) :
    3 * (1 + x + x ^ 2) ≠ 1 + y + y ^ 2 := by
  intro h
  have hy : y % 3 = 1 := by
    have h0 : (1 + y + y ^ 2) % 3 = 0 := by omega
    rcases (by omega : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2) with h1 | h1 | h1 <;>
      simp [Nat.add_mod, Nat.pow_mod, h1] at h0 ⊢
  obtain ⟨a, rfl⟩ : ∃ a, y = 3 * a + 1 := ⟨y / 3, by omega⟩
  have key : x * (x + 1) = 3 * (a * (a + 1)) := by nlinarith
  have hx3 := hx.two_le
  have hx3' : 3 ≤ x := by omega
  rcases (Nat.Prime.dvd_mul hx).mp (key ▸ dvd_mul_right x (x + 1) :
      x ∣ 3 * (a * (a + 1))) with h3 | h3
  · have : x = 3 := (Nat.prime_dvd_prime_iff_eq hx Nat.prime_three).mp h3
    subst this
    have : a ≤ 2 := by nlinarith
    interval_cases a <;> omega
  · rcases (Nat.Prime.dvd_mul hx).mp h3 with h4 | h4
    · obtain ⟨c, rfl⟩ := h4
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · simp at key; omega
      · have hxc : x ≤ x * c := Nat.le_mul_of_pos_right x hc
        have hle : x * (x + 1) ≤ x * c * (x * c + 1) := Nat.mul_le_mul hxc (by omega)
        have hpos : 0 < x * (x + 1) := by positivity
        omega
    · obtain ⟨c, hc⟩ := h4
      rcases Nat.eq_zero_or_pos c with rfl | hc0
      · omega
      · have hxa : x ≤ a + 1 := by nlinarith
        nlinarith

/-- Zelinsky's Lemma 2, in the form used: if `b < a` are both `2 (mod 3)` and a prime
`P ≡ 1 (mod 3)` divides both `a ^ 2 + a + 1` and `b ^ 2 + b + 1`, then `P ≤ a`. -/
theorem shared_prime_le {a b P : ℕ} (ha : a % 3 = 2) (hb : b % 3 = 2) (hba : b < a)
    (hP : P.Prime) (hP3 : P % 3 = 1) (hPa : P ∣ 1 + a + a ^ 2) (hPb : P ∣ 1 + b + b ^ 2) :
    P ≤ a := by
  have hdiff : 1 + a + a ^ 2 = (1 + b + b ^ 2) + (a - b) * (a + b + 1) := by
    obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
    rw [Nat.add_sub_cancel_left]
    ring
  have hprod : P ∣ (a - b) * (a + b + 1) := by
    rw [hdiff] at hPa
    exact (Nat.dvd_add_right hPb).mp hPa
  rcases (Nat.Prime.dvd_mul hP).mp hprod with h1 | h1
  · have := Nat.le_of_dvd (by omega) h1
    omega
  · obtain ⟨k, hk⟩ := h1
    rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk2
    · omega
    · omega
    · nlinarith

/-- A number `n ≥ 2` with at most two prime factors (with multiplicity) has a prime factor
`P` with `n ≤ P ^ 2`. -/
theorem exists_prime_dvd_le_sq_of_cardFactors_le_two {n : ℕ} (hn : 2 ≤ n) (hΩ : Ω n ≤ 2) :
    ∃ P, P.Prime ∧ P ∣ n ∧ n ≤ P ^ 2 := by
  have hm : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨k, hk⟩ := Nat.minFac_dvd n
  have hk0 : k ≠ 0 := by rintro rfl; omega
  rcases (by omega : k = 1 ∨ 2 ≤ k) with rfl | hk2
  · refine ⟨n.minFac, hm, Nat.minFac_dvd n, ?_⟩
    rw [mul_one] at hk
    nlinarith [hm.two_le]
  · have hΩk : Ω k ≤ 1 := by
      rw [hk, cardFactors_mul hm.ne_zero hk0, cardFactors_apply_prime hm] at hΩ
      omega
    have hk1 : Ω k ≠ 0 := by
      rw [Ne, cardFactors_eq_zero_iff_eq_zero_or_one]
      omega
    have hkp : k.Prime := cardFactors_eq_one_iff_prime.mp (by omega)
    have hkn : k ∣ n := Dvd.intro_left n.minFac hk.symm
    refine ⟨k, hkp, hkn, ?_⟩
    have : n.minFac ≤ k := Nat.minFac_le_of_dvd hkp.two_le hkn
    calc n = n.minFac * k := hk
      _ ≤ k ^ 2 := by nlinarith

/-- The part of `p ^ 2 + p + 1` prime to 3: for `p ≡ 1 (mod 3)` the number `p ^ 2 + p + 1`
is `3` times a number prime to 3, and otherwise it is already prime to 3. -/
def phiCore (p : ℕ) : ℕ := if p % 3 = 1 then (1 + p + p ^ 2) / 3 else 1 + p + p ^ 2

private theorem phiCore_spec {p : ℕ} (hp : 2 ≤ p) (h0 : p % 3 ≠ 0) :
    ¬ 3 ∣ phiCore p ∧ phiCore p ∣ 1 + p + p ^ 2 ∧ 2 ≤ phiCore p ∧
      (p % 3 = 1 → 1 + p + p ^ 2 = 3 * phiCore p) ∧
      (p % 3 ≠ 1 → phiCore p = 1 + p + p ^ 2) := by
  unfold phiCore
  by_cases h1 : p % 3 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, p = 3 * k + 1 := ⟨p / 3, by omega⟩
    have hA : 1 + (3 * k + 1) + (3 * k + 1) ^ 2 = 3 * (3 * (k * k + k) + 1) := by ring
    rw [if_pos h1, hA, Nat.mul_div_cancel_left _ (by norm_num)]
    have hk : 1 ≤ k := by omega
    refine ⟨by omega, dvd_mul_left _ _, by nlinarith, fun _ => rfl, fun h => absurd h1 h⟩
  · rw [if_neg h1]
    refine ⟨?_, dvd_rfl, by nlinarith, fun h => absurd h h1, fun _ => rfl⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    rcases (by omega : p % 3 = 2) with h2
    simp [Nat.add_mod, Nat.pow_mod, h2]

private theorem sigma_sq' {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]

private theorem phi3_inj {a b : ℕ} (h : 1 + a + a ^ 2 = 1 + b + b ^ 2) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · nlinarith
  · exact hab
  · nlinarith

/-- The Zelinsky ledger. With `S₂` the exponent 2 primes that are `2 (mod 3)` (`a` of them),
`S₁` those that are `1 (mod 3)` (`b` of them), `R` the remaining prime factors other than 3
(`ρ` of them, total exponent `F`), `W` the number of prime factors with multiplicity of the
3-free parts of `σ(p ^ 2)` over `p ∈ S₁ ∪ S₂`, `X` the primes of `S₂` whose `σ(p ^ 2)` has at
most two prime factors, and `Y` the primes of `S₁ ∪ S₂` whose 3-free part of `σ(p ^ 2)` is
prime, the listed linear relations hold. The bounds `x ≤ ρ` and `y ≤ ρ` are the two
injectivity statements (largest prime factor, and the 3-free part itself). -/
theorem zelinsky_ledger {N : ℕ} (h : OddPerfect N) :
    ∃ a b x y W ρ F : ℕ,
      (∑ p ∈ N.primeFactors, N.factorization p) = 2 * a + F + N.factorization 3 ∧
      N.primeFactors.card = a + ρ + (if 3 ∣ N then 1 else 0) ∧
      4 * ρ ≤ F + 3 + 2 * b ∧ W ≤ F ∧ 3 * a + 2 * b ≤ W + x + y ∧
      x ≤ a ∧ y ≤ x + b ∧ x ≤ ρ ∧ y ≤ ρ ∧ b ≤ N.factorization 3 ∧
      (3 ∣ N → 2 ≤ N.factorization 3) := by
  classical
  obtain ⟨q, hq, hqN, hq4, he4, hev⟩ := exists_special_prime h
  have hN0 := h.ne_zero
  have hodd : ∀ p ∈ N.primeFactors, p % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  set P := N.primeFactors with hPdef
  set S := {p ∈ P | N.factorization p = 2 ∧ p % 3 ≠ 0} with hSdef
  set S2 := {p ∈ S | p % 3 = 2} with hS2def
  set S1 := {p ∈ S | p % 3 = 1} with hS1def
  set R := (P \ S2).erase 3 with hRdef
  set X := {p ∈ S | p % 3 = 2 ∧ Ω (phiCore p) ≤ 2} with hXdef
  set Y := {p ∈ S | Ω (phiCore p) = 1} with hYdef
  set W := ∑ p ∈ S, Ω (phiCore p) with hWdef
  set F := ∑ r ∈ R, N.factorization r with hFdef
  have hS2P : S2 ⊆ P := fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have memS : ∀ {p}, p ∈ S → p ∈ P ∧ p.Prime ∧ N.factorization p = 2 ∧ p % 3 ≠ 0 ∧
      2 ≤ p := by
    intro p hp
    obtain ⟨hpP, hf, h0⟩ := Finset.mem_filter.mp hp
    exact ⟨hpP, Nat.prime_of_mem_primeFactors hpP, hf, h0,
      (Nat.prime_of_mem_primeFactors hpP).two_le⟩
  -- every prime factor of a 3-free part lands in `R`, and is `1 (mod 3)`
  have hR : ∀ p ∈ S, ∀ r, r.Prime → r ∣ phiCore p → r ∈ R ∧ r % 3 = 1 := by
    intro p hp r hr hrc
    obtain ⟨hpP, hpp, hf, h0, hp2⟩ := memS hp
    obtain ⟨hc3, hcd, -, -, -⟩ := phiCore_spec hp2 h0
    have hrA : r ∣ 1 + p + p ^ 2 := hrc.trans hcd
    have hr2 : r ≠ 2 := by
      rintro rfl
      have := hodd p hpP
      have : (1 + p + p ^ 2) % 2 = 1 := by simp [Nat.add_mod, Nat.pow_mod, this]
      omega
    have hr3 : r ≠ 3 := by rintro rfl; exact hc3 hrc
    have hrN : r ∣ N := OPNStarter.force_prime h.perfect hpp hf hr hr2 (by rwa [sigma_sq' hpp])
    have hr1 : r % 3 = 1 := OPNThreeFree.target_mod_three hr hr3 hrA
    refine ⟨Finset.mem_erase.mpr ⟨hr3, Finset.mem_sdiff.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hr, hrN, hN0⟩, fun h2 => ?_⟩⟩, hr1⟩
    have := (Finset.mem_filter.mp h2).2
    omega
  -- (1) exponent sum
  have h3S2 : (3 : ℕ) ∉ S2 := fun h3 => by
    have := (Finset.mem_filter.mp h3).2
    omega
  have hfac3 : ¬ 3 ∣ N → N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd
  have h3P : 3 ∈ P ↔ 3 ∣ N := by
    rw [hPdef, Nat.mem_primeFactors]
    exact ⟨fun h => h.2.1, fun h3 => ⟨Nat.prime_three, h3, hN0⟩⟩
  have hsumS2 : ∑ p ∈ S2, N.factorization p = 2 * S2.card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp => by
      simp [(memS (Finset.mem_filter.mp hp).1).2.2.1]
  have hsplit : ∑ t ∈ P \ S2, N.factorization t + ∑ p ∈ S2, N.factorization p =
      ∑ p ∈ P, N.factorization p := Finset.sum_sdiff hS2P
  have hcsplit : (P \ S2).card + S2.card = P.card := Finset.card_sdiff_add_card_eq_card hS2P
  have hone : (∑ p ∈ P, N.factorization p) = 2 * S2.card + F + N.factorization 3 ∧
      P.card = S2.card + R.card + (if 3 ∣ N then 1 else 0) := by
    by_cases h3 : 3 ∣ N
    · have hm : 3 ∈ P \ S2 := Finset.mem_sdiff.mpr ⟨h3P.mpr h3, h3S2⟩
      have := Finset.add_sum_erase (P \ S2) (fun t => N.factorization t) hm
      have hc := Finset.card_erase_of_mem hm
      have hpos : 0 < (P \ S2).card := Finset.card_pos.mpr ⟨3, hm⟩
      rw [← hRdef] at this hc
      rw [if_pos h3]
      constructor <;> omega
    · have hm : 3 ∉ P \ S2 := fun hm => h3 (h3P.mp (Finset.mem_sdiff.mp hm).1)
      have hRe : R = P \ S2 := Finset.erase_eq_of_notMem hm
      have hF' : F = ∑ t ∈ P \ S2, N.factorization t := by rw [hFdef, hRe]
      have hc : R.card = (P \ S2).card := by rw [hRe]
      rw [if_neg h3, hfac3 h3]
      constructor <;> omega
  -- (3) every prime of `R` has exponent at least 4, except `q` and the primes of `S₁`
  have hfour : 4 * R.card ≤ F + 3 + 2 * S1.card := by
    have key : ∀ r ∈ R, 4 ≤ N.factorization r + 3 * (if r = q then 1 else 0) +
        2 * (if r ∈ S1 then 1 else 0) := by
      intro r hr
      obtain ⟨hr3, hrPS⟩ := Finset.mem_erase.mp hr
      obtain ⟨hrP, hrS2⟩ := Finset.mem_sdiff.mp hrPS
      have hrp := Nat.prime_of_mem_primeFactors hrP
      have h1 := hrp.factorization_pos_of_dvd hN0 (Nat.dvd_of_mem_primeFactors hrP)
      by_cases hrq : r = q
      · rw [if_pos hrq]; omega
      · rw [if_neg hrq]
        obtain ⟨j, hj⟩ := hev r hrp hrq
        by_cases hr2 : N.factorization r = 2
        · have h0 : r % 3 ≠ 0 := fun h0 =>
            hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hrp).mp
              (Nat.dvd_of_mod_eq_zero h0)).symm
          have hrS : r ∈ S := Finset.mem_filter.mpr ⟨hrP, hr2, h0⟩
          have hr1 : r % 3 = 1 := by
            by_contra hne
            exact hrS2 (Finset.mem_filter.mpr ⟨hrS, by omega⟩)
          rw [if_pos (Finset.mem_filter.mpr ⟨hrS, hr1⟩)]
          omega
        · split_ifs <;> omega
    have hs := Finset.sum_le_sum key
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_ite_eq' R q (fun _ => 1), ← Finset.card_filter] at hs
    simp only [Finset.sum_const, smul_eq_mul] at hs
    have hsub : (R.filter (· ∈ S1)).card ≤ S1.card :=
      Finset.card_le_card fun x hx => (Finset.mem_filter.mp hx).2
    have hq1 : (if q ∈ R then 1 else 0) ≤ 1 := by split_ifs <;> omega
    rw [← hFdef] at hs
    omega
  -- (4) conservation of the 3-free parts
  have hWF : W ≤ F := by
    have hp : ∀ p ∈ S, Ω (phiCore p) ≤ ∑ r ∈ R, sigmaWeight N p r := by
      intro p hp
      obtain ⟨hpP, hpp, hf, h0, hp2⟩ := memS hp
      obtain ⟨-, hcd, hc2, -, -⟩ := phiCore_spec hp2 h0
      rw [cardFactors_eq_sum_primeFactors]
      calc ∑ r ∈ (phiCore p).primeFactors, (phiCore p).factorization r
          ≤ ∑ r ∈ R, (phiCore p).factorization r := by
            refine Finset.sum_le_sum_of_subset fun r hr => ?_
            obtain ⟨hr, hrd, -⟩ := Nat.mem_primeFactors.mp hr
            exact (hR p hp r hr hrd).1
        _ ≤ ∑ r ∈ R, sigmaWeight N p r := by
            refine Finset.sum_le_sum fun r _ => ?_
            unfold sigmaWeight
            rw [hf, sigma_sq' hpp]
            exact (Nat.factorization_le_iff_dvd (by omega) (by positivity)).mpr hcd r
    calc W ≤ ∑ p ∈ S, ∑ r ∈ R, sigmaWeight N p r := Finset.sum_le_sum hp
      _ = ∑ r ∈ R, ∑ p ∈ S, sigmaWeight N p r := Finset.sum_comm
      _ ≤ ∑ r ∈ R, ∑ p ∈ P, sigmaWeight N p r :=
          Finset.sum_le_sum fun _ _ => Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = F := by
          refine Finset.sum_congr rfl fun r hr => ?_
          have hrP := (Finset.mem_sdiff.mp (Finset.mem_erase.mp hr).2).1
          have := hodd r hrP
          exact sigmaWeight_sum_eq h.perfect (Nat.prime_of_mem_primeFactors hrP) (by omega)
  -- (5) pointwise lower bound for the multiplicities
  have hW : 3 * S2.card + 2 * S1.card ≤ W + X.card + Y.card := by
    have key : ∀ p ∈ S, 3 * (if p % 3 = 2 then 1 else 0) + 2 * (if p % 3 = 1 then 1 else 0) ≤
        Ω (phiCore p) + (if p % 3 = 2 ∧ Ω (phiCore p) ≤ 2 then 1 else 0) +
          (if Ω (phiCore p) = 1 then 1 else 0) := by
      intro p hp
      obtain ⟨-, -, -, h0, hp2⟩ := memS hp
      obtain ⟨-, -, hc2, -, -⟩ := phiCore_spec hp2 h0
      have hΩ : Ω (phiCore p) ≠ 0 := by
        rw [Ne, cardFactors_eq_zero_iff_eq_zero_or_one]
        omega
      split_ifs <;> omega
    have hs := Finset.sum_le_sum key
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.card_filter, ← Finset.card_filter,
      ← Finset.card_filter, ← Finset.card_filter] at hs
    exact hs
  -- (6), (7) set inclusions
  have hXa : X.card ≤ S2.card := Finset.card_le_card fun p hp => by
    obtain ⟨hpS, h2, -⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpS, h2⟩
  have hYX : Y.card ≤ X.card + S1.card := by
    refine (Finset.card_le_card fun p hp => ?_).trans (Finset.card_union_le X S1)
    obtain ⟨hpS, h1⟩ := Finset.mem_filter.mp hp
    have h0 := (memS hpS).2.2.2.1
    rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h3 | h3
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpS, h3⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpS, h3, by omega⟩)
  -- (8) the largest prime factor is injective on `X`
  have hXR : X.card ≤ R.card := by
    have hbig : ∀ p ∈ X, ∃ t, t.Prime ∧ t ∣ phiCore p ∧ phiCore p ≤ t ^ 2 := by
      intro p hp
      obtain ⟨hpS, -, hΩ⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, -, -, h0, hp2⟩ := memS hpS
      exact exists_prime_dvd_le_sq_of_cardFactors_le_two (phiCore_spec hp2 h0).2.2.1 hΩ
    choose! f hf1 hf2 hf3 using hbig
    refine Finset.card_le_card_of_injOn f (fun p hp => (hR p (Finset.mem_filter.mp hp).1 _
      (hf1 p hp) (hf2 p hp)).1) ?_
    have hA : ∀ p ∈ X, p % 3 = 2 ∧ phiCore p = 1 + p + p ^ 2 ∧ f p % 3 = 1 := by
      intro p hp
      obtain ⟨hpS, h2, -⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, -, -, h0, hp2⟩ := memS hpS
      exact ⟨h2, (phiCore_spec hp2 h0).2.2.2.2 (by omega),
        (hR p hpS _ (hf1 p hp) (hf2 p hp)).2⟩
    have main : ∀ a ∈ X, ∀ b ∈ X, b < a → f a ≠ f b := by
      intro a ha b hb hba hfab
      obtain ⟨ha2, hca, hfa⟩ := hA a ha
      obtain ⟨hb2, hcb, -⟩ := hA b hb
      have hle := shared_prime_le ha2 hb2 hba (hf1 a ha) hfa (hca ▸ hf2 a ha)
        (hfab ▸ hcb ▸ hf2 b hb)
      have h3 := hf3 a ha
      rw [hca] at h3
      nlinarith
    intro a ha b hb hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact absurd hab.symm (main b hb a ha hlt)
    · exact heq
    · exact absurd hab (main a ha b hb hgt)
  -- (9) the 3-free part itself is injective on `Y`
  have hYR : Y.card ≤ R.card := by
    refine Finset.card_le_card_of_injOn phiCore (fun p hp => ?_) ?_
    · obtain ⟨hpS, h1⟩ := Finset.mem_filter.mp hp
      have hpr : (phiCore p).Prime := cardFactors_eq_one_iff_prime.mp h1
      exact (hR p hpS _ hpr dvd_rfl).1
    · have hA : ∀ p ∈ Y, p.Prime ∧ p ≠ 2 ∧
          ((p % 3 = 1 ∧ 1 + p + p ^ 2 = 3 * phiCore p) ∨
            (p % 3 = 2 ∧ phiCore p = 1 + p + p ^ 2)) := by
        intro p hp
        obtain ⟨hpS, -⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpP, hpp, -, h0, hp2⟩ := memS hpS
        have := hodd p hpP
        obtain ⟨-, -, -, h1, h2⟩ := phiCore_spec hp2 h0
        refine ⟨hpp, by omega, ?_⟩
        rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h3 | h3
        · exact Or.inl ⟨h3, h1 h3⟩
        · exact Or.inr ⟨h3, h2 (by omega)⟩
      intro a ha b hb hab
      obtain ⟨hap, ha2, ha | ha⟩ := hA a ha <;> obtain ⟨hbp, hb2, hb | hb⟩ := hA b hb
      · exact phi3_inj (by rw [ha.2, hb.2, hab])
      · exact absurd (show 3 * (1 + b + b ^ 2) = 1 + a + a ^ 2 by rw [← hb.2, ← hab, ha.2])
          (three_mul_phi3_ne_phi3 hbp hb2)
      · exact absurd (show 3 * (1 + a + a ^ 2) = 1 + b + b ^ 2 by rw [← ha.2, hab, hb.2])
          (three_mul_phi3_ne_phi3 hap ha2)
      · exact phi3_inj (by rw [← ha.2, ← hb.2, hab])
  -- (10), (11) the 3-adic ledger
  have hS1 : S1.card ≤ N.factorization 3 := by
    refine le_trans (Finset.card_le_card fun p hp => ?_) (card_sq_mod_three_eq_one_le h)
    obtain ⟨hpS, h1⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpP, -, hf, -, -⟩ := memS hpS
    exact Finset.mem_filter.mpr ⟨hpP, hf, h1⟩
  have h32 : 3 ∣ N → 2 ≤ N.factorization 3 := by
    intro h3
    have hq3 : (3 : ℕ) ≠ q := by rintro rfl; omega
    obtain ⟨j, hj⟩ := hev 3 Nat.prime_three hq3
    have := Nat.prime_three.factorization_pos_of_dvd hN0 h3
    omega
  exact ⟨S2.card, S1.card, X.card, Y.card, W, R.card, F, hone.1, hone.2, hfour, hWF, hW, hXa,
    hYX, hXR, hYR, hS1, h32⟩

/-- Zelinsky (arXiv 1706.07009), 3-free case: if `3 ∤ N` then `8 ω ≤ 3 Ω + 7`, that is
`Ω ≥ (8 ω - 7) / 3`. This strengthens `twelve_mul_card_le_of_not_three_dvd`. -/
theorem eight_mul_card_le_of_not_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    8 * N.primeFactors.card ≤ 3 * (∑ p ∈ N.primeFactors, N.factorization p) + 7 := by
  obtain ⟨a, b, x, y, W, ρ, F, hΩ, hω, h4, hWF, hW, hxa, hyx, hxρ, hyρ, hb, -⟩ :=
    zelinsky_ledger h
  rw [if_neg h3] at hω
  rw [Nat.factorization_eq_zero_of_not_dvd h3] at hΩ hb
  omega

/-- Zelinsky (arXiv 1706.07009), case `3 ∣ N`: `21 ω ≤ 8 Ω + 39`, that is
`Ω ≥ (21 ω - 39) / 8`. -/
theorem twentyone_mul_card_le_of_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) :
    21 * N.primeFactors.card ≤ 8 * (∑ p ∈ N.primeFactors, N.factorization p) + 39 := by
  obtain ⟨a, b, x, y, W, ρ, F, hΩ, hω, h4, hWF, hW, hxa, hyx, hxρ, hyρ, hb, h32⟩ :=
    zelinsky_ledger h
  rw [if_pos h3] at hω
  have := h32 h3
  omega

/-- Both cases at once: `21 ω ≤ 8 Ω + 39` for every odd perfect number. In the 3-free case
this follows from `8 ω ≤ 3 Ω + 7` and the Euler bound `2 ω ≤ Ω + 1`. -/
theorem twentyone_mul_card_le {N : ℕ} (h : OddPerfect N) :
    21 * N.primeFactors.card ≤ 8 * (∑ p ∈ N.primeFactors, N.factorization p) + 39 := by
  by_cases h3 : 3 ∣ N
  · exact twentyone_mul_card_le_of_three_dvd h h3
  · have h1 := eight_mul_card_le_of_not_three_dvd h h3
    have h2 := two_mul_card_le_sum_factorization_add_one h
    omega

/-- `8 ω(N) ≤ 3 Ω(N) + 7` when `3 ∤ N`, in terms of `Ω` and `ω`. -/
theorem eight_mul_omega_le_of_not_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    8 * ω N ≤ 3 * Ω N + 7 := by
  rw [cardFactors_eq_sum_primeFactors, cardDistinctFactors_eq_card_primeFactors]
  exact eight_mul_card_le_of_not_three_dvd h h3

/-- `21 ω(N) ≤ 8 Ω(N) + 39` when `3 ∣ N`, in terms of `Ω` and `ω`. -/
theorem twentyone_mul_omega_le_of_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) :
    21 * ω N ≤ 8 * Ω N + 39 := by
  rw [cardFactors_eq_sum_primeFactors, cardDistinctFactors_eq_card_primeFactors]
  exact twentyone_mul_card_le_of_three_dvd h h3

/-- `21 ω(N) ≤ 8 Ω(N) + 39` for every odd perfect number, in terms of `Ω` and `ω`. -/
theorem twentyone_mul_omega_le {N : ℕ} (h : OddPerfect N) : 21 * ω N ≤ 8 * Ω N + 39 := by
  rw [cardFactors_eq_sum_primeFactors, cardDistinctFactors_eq_card_primeFactors]
  exact twentyone_mul_card_le h

end OddPerfect

#print axioms OddPerfect.three_mul_phi3_ne_phi3
#print axioms OddPerfect.shared_prime_le
#print axioms OddPerfect.exists_prime_dvd_le_sq_of_cardFactors_le_two
#print axioms OddPerfect.zelinsky_ledger
#print axioms OddPerfect.eight_mul_card_le_of_not_three_dvd
#print axioms OddPerfect.twentyone_mul_card_le_of_three_dvd
#print axioms OddPerfect.twentyone_mul_card_le
#print axioms OddPerfect.eight_mul_omega_le_of_not_three_dvd
#print axioms OddPerfect.twentyone_mul_omega_le_of_three_dvd
#print axioms OddPerfect.twentyone_mul_omega_le
