import OddPerfect.LargestPrimeCapacity
import OddPerfect.SignedRepunit
import OddPerfect.Reciprocity

/-!
# Largest prime factor of the form `2 R + 1` with `R` prime: exact rows

Let `N` be an odd perfect number whose largest prime factor is `P = 2 R + 1` with `R` an odd
prime. A *sender* is a prime factor `u ≠ P` with `P ∣ σ(u ^ e_u)`, where `e_u = v_u(N)`.

* `largest_safe_factorization_even`: `P ≡ 3 (mod 4)`, so `P` is not the special prime and
  `v_P(N)` is even (a direct consequence of `special_mod_four`).
* `largest_safe_sender_row`: every sender `u` has `e_u = R - 1` and order `R` modulo `P`, and
  its whole row is a power of `P`: `σ(u ^ e_u) = 1 + u + ⋯ + u ^ (R - 1) = P ^ j` with
  `j = v_P(σ(u ^ e_u)) ≥ 1`.
* `largest_safe_special_not_sender`: the special prime is never a sender.
* `largest_safe_sender_parity`: if `u ≠ 3` then `u ≡ 1 (mod 4)` and `j` is odd; if `u = 3`
  then `j` is even.
* `largest_safe_size`: `(3 ^ R - 1) / 2 ≤ P ^ v_P(N)`.
* `largest_safe_card_senders`: if `3` is not a sender, the number of senders is even and at
  least `2`.

Proof sketch. The order `t` of a sender modulo `P` divides `P - 1 = 2 R` and is at least `3`
(`sender_largest_data`), so `R ∣ t ∣ e_u + 1`. The landed bound `2 e_u + 3 ≤ P`
(`two_mul_factorization_add_three_le`) gives `e_u + 1 ≤ R`, hence `e_u + 1 = R` and `t = R`.
So the row is `F = ∑ i < R, u ^ i`, and `F ∣ 2 N`. A prime `r ∣ F` has `u ^ R ≡ 1 (mod r)`.
If `u ≡ 1 (mod r)` then `F ≡ R`, so `r = R` and `u ≡ 1 (mod R)` with `1 < u < 2 R + 1` forces
`u = R + 1`, which is even. Otherwise `u` has order `R` modulo the odd prime `r`, so
`2 R ∣ r - 1` and `r ≥ P`; as `r ∣ N`, `r = P`. Parity: for `u ≥ 5` the row is not a square
(`geom_sum_prime_pow_ne_sq`), so `j` is odd; the Legendre symbol `(P / u)` is `1` on
`σ(u ^ e_u) = P ^ j` (`legendreSym_sigma_prime_pow`) and is `-1` when `u ≡ 3 (mod 4)`
(`legendreSym_receiver_of_dvd_sigma_even`, since `P ≡ 3 (mod 4)`), which forces `j` even.
Control: `R = 5`, `P = 11`, `u = 3`: `1 + 3 + 9 + 27 + 81 = 11 ^ 2`.

Scope: these are necessary conditions in the case that the largest prime factor is `2 R + 1`
with `R` prime; the case itself is not excluded here. Novelty is not verified. Known context,
not used or proved here: the equations `(x ^ n - 1) / (x - 1) = y ^ j` (Nagell, Ljunggren).
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N P R : ℕ}

private theorem lps_odd_of_mem (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) :
    p % 2 = 1 :=
  Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))

/-- A root `x ≠ 1` of `1 + x + ⋯ + x ^ (R - 1)` modulo an odd prime `r` has order `R`, so
`2 R + 1 ≤ r`. -/
private theorem lps_zmod_row {r : ℕ} (hr : r.Prime) (hR : R.Prime) (hR2 : R ≠ 2)
    {x : ZMod r} (h0 : ∑ i ∈ Finset.range R, x ^ i = 0) (hx : x ≠ 1) (hr2 : r ≠ 2) :
    2 * R + 1 ≤ r := by
  have : Fact r.Prime := ⟨hr⟩
  have hxR : x ^ R = 1 := by
    have := geom_sum_mul x R
    rw [h0, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hR.ne_zero] at hxR
    exact zero_ne_one hxR
  have hord : orderOf x = R := by
    rcases (Nat.dvd_prime hR).mp (orderOf_dvd_of_pow_eq_one hxR) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx
    · exact h1
  have hdvd := ZMod.orderOf_dvd_card_sub_one hx0
  rw [hord] at hdvd
  have hro := Nat.odd_iff.mp (hr.odd_of_ne_two hr2)
  have h2 : 2 ∣ r - 1 := by omega
  have hcop : Nat.Coprime 2 R := (Nat.coprime_two_left).mpr (hR.odd_of_ne_two hR2)
  have := Nat.le_of_dvd (by have := hr.two_le; omega) (hcop.mul_dvd_of_dvd_of_dvd h2 hdvd)
  omega

/-- The root `x = 1`: then `R ≡ 0 (mod r)`, so `r = R`. -/
private theorem lps_zmod_row_one {r : ℕ} (hr : r.Prime) (hR : R.Prime)
    (h0 : ∑ i ∈ Finset.range R, (1 : ZMod r) ^ i = 0) : r = R := by
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h0
  exact (Nat.prime_dvd_prime_iff_eq hr hR).mp ((ZMod.natCast_eq_zero_iff R r).mp h0)

/-- `P = 2 R + 1` with `R` an odd prime is not the special prime of an odd perfect number:
`v_P(N)` is even, since `P ≡ 3 (mod 4)`. -/
theorem largest_safe_factorization_even (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hR : R.Prime) (hR2 : R ≠ 2) (hPR : P = 2 * R + 1) : Even (N.factorization P) := by
  have hRo := Nat.odd_iff.mp (hR.odd_of_ne_two hR2)
  rcases Nat.even_or_odd (N.factorization P) with he | ho
  · exact he
  · have := (special_mod_four h (Nat.prime_of_mem_primeFactors hP) ho).1
    omega

/-- Exact rows. Let the largest prime factor of an odd perfect number `N` be `P = 2 R + 1`
with `R` an odd prime, and let `u ≠ P` be a prime factor with `P ∣ σ(u ^ e_u)`. Then
`e_u = R - 1`, the order of `u` modulo `P` is `R`, and
`1 + u + ⋯ + u ^ (R - 1) = P ^ j` with `j = v_P(σ(u ^ e_u)) ≥ 1`. -/
theorem largest_safe_sender_row (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) (hR2 : R ≠ 2) (hPR : P = 2 * R + 1)
    {u : ℕ} (hu : u ∈ N.primeFactors) (huP : u ≠ P) (hd : P ∣ σ 1 (u ^ N.factorization u)) :
    N.factorization u = R - 1 ∧ orderOf (u : ZMod P) = R ∧
      ∑ i ∈ Finset.range R, u ^ i = P ^ padicValNat P (σ 1 (u ^ N.factorization u)) ∧
      1 ≤ padicValNat P (σ 1 (u ^ N.factorization u)) := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have : Fact P.Prime := ⟨hPp⟩
  have hup := Nat.prime_of_mem_primeFactors hu
  have hu2' := hup.two_le
  have hRo := Nat.odd_iff.mp (hR.odd_of_ne_two hR2)
  have hR3 : 3 ≤ R := by have := hR.two_le; omega
  obtain ⟨hlt, hu2, ht3, -, -⟩ := sender_largest_data h hP hmax hu huP hd
  have he := two_mul_factorization_add_three_le h hu hmax
  set e := N.factorization u with hedef
  set t := orderOf (u : ZMod P) with htdef
  have hte : t ∣ e + 1 := by
    have hdd := (dvd_sigma_prime_pow_iff hup hPp huP).mp hd
    rwa [← htdef, if_neg (by omega)] at hdd
  have hu0 : (u : ZMod P) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hh
    have := Nat.le_of_dvd hup.pos hh
    omega
  have htP : t ∣ 2 * R := by
    have := ZMod.orderOf_dvd_card_sub_one hu0
    rwa [show P - 1 = 2 * R by omega] at this
  have hRt : R ∣ t := by
    obtain ⟨d1, d2, h1, h2, hdt⟩ := Nat.dvd_mul.mp htP
    rcases (Nat.dvd_prime hR).mp h2 with rfl | rfl
    · have := Nat.le_of_dvd two_pos h1
      omega
    · rw [← hdt]
      exact dvd_mul_left _ _
  have heR : e + 1 = R :=
    le_antisymm (by omega) (Nat.le_of_dvd (by omega) (hRt.trans hte))
  have htR : t = R := by
    have htR' : t ∣ R := by rw [← heR]; exact hte
    rcases (Nat.dvd_prime hR).mp htR' with h1 | h1
    · omega
    · exact h1
  have hσ : σ 1 (u ^ e) = ∑ i ∈ Finset.range R, u ^ i := by
    rw [sigma_one_apply_prime_pow hup, heR]
  have hF2N : ∑ i ∈ Finset.range R, u ^ i ∣ 2 * N := by
    rw [← hσ]
    exact OPNStarter.component_sigma_dvd h.perfect hup hedef.symm
  have hF0 : ∑ i ∈ Finset.range R, u ^ i ≠ 0 := by
    have : 0 < ∑ i ∈ Finset.range R, u ^ i :=
      Finset.sum_pos (fun i _ => pow_pos hup.pos i) ⟨0, Finset.mem_range.mpr (by omega)⟩
    omega
  have hprime : ∀ {r : ℕ}, r.Prime → r ∣ ∑ i ∈ Finset.range R, u ^ i → r = P := by
    intro r hr hrF
    have : Fact r.Prime := ⟨hr⟩
    have h0 : ∑ i ∈ Finset.range R, ((u : ℕ) : ZMod r) ^ i = 0 := by
      have := (ZMod.natCast_eq_zero_iff _ r).mpr hrF
      push_cast at this
      exact this
    by_cases hx : (u : ZMod r) = 1
    · exfalso
      rw [hx] at h0
      have hrR := lps_zmod_row_one hr hR h0
      have hmod : u % r = 1 := by
        have := (ZMod.natCast_eq_natCast_iff' u 1 r).mp (by rw [Nat.cast_one]; exact hx)
        rwa [Nat.mod_eq_of_lt hr.one_lt] at this
      rw [hrR] at hmod
      have hk := Nat.div_add_mod u R
      obtain ⟨k, hk'⟩ : ∃ k, k = u / R := ⟨_, rfl⟩
      rw [← hk'] at hk
      have hk2 : k < 3 := by
        by_contra hc
        have := Nat.mul_le_mul_left R (show 3 ≤ k by omega)
        omega
      interval_cases k <;> omega
    · have hr2 : r ≠ 2 := by
        rintro rfl
        apply hx
        rw [← ZMod.natCast_mod, hu2, Nat.cast_one]
      have h1 := lps_zmod_row hr hR hR2 h0 hx hr2
      have hrN : r ∣ N :=
        Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
          (hrF.trans hF2N)
      have := hmax r (Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩)
      omega
  obtain ⟨k, hk⟩ : ∃ k, ∑ i ∈ Finset.range R, u ^ i = P ^ k :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hF0 hprime⟩
  have hj : padicValNat P (σ 1 (u ^ e)) = k := by
    rw [hσ, hk, Nat.padicValNat_def, padicValNat.prime_pow]
  refine ⟨by omega, htR, by rw [hj]; exact hk, ?_⟩
  rw [hj]
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · rw [hσ, hk, h0, pow_zero] at hd
    have := Nat.le_of_dvd one_pos hd
    omega
  · omega

/-- The special prime is not a sender into `P = 2 R + 1` (with `R` an odd prime the largest
prime factor): a sender has even exponent `R - 1`. -/
theorem largest_safe_special_not_sender (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) (hR2 : R ≠ 2) (hPR : P = 2 * R + 1)
    {q : ℕ} (hq : q ∈ N.primeFactors) (hqP : q ≠ P) (hodd : Odd (N.factorization q)) :
    ¬ P ∣ σ 1 (q ^ N.factorization q) := by
  intro hd
  have he := (largest_safe_sender_row h hP hmax hR hR2 hPR hq hqP hd).1
  have hRo := Nat.odd_iff.mp (hR.odd_of_ne_two hR2)
  have := Nat.odd_iff.mp hodd
  have := hR.two_le
  omega

/-- Parity of the row exponent. With `P = 2 R + 1` (`R` an odd prime) the largest prime factor
and `u` a sender with `j = v_P(σ(u ^ e_u))`: if `u ≠ 3` then `u ≡ 1 (mod 4)` and `j` is odd;
if `u = 3` then `j` is even. -/
theorem largest_safe_sender_parity (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) (hR2 : R ≠ 2) (hPR : P = 2 * R + 1)
    {u : ℕ} (hu : u ∈ N.primeFactors) (huP : u ≠ P) (hd : P ∣ σ 1 (u ^ N.factorization u)) :
    (u ≠ 3 → u % 4 = 1 ∧ Odd (padicValNat P (σ 1 (u ^ N.factorization u)))) ∧
      (u = 3 → Even (padicValNat P (σ 1 (u ^ N.factorization u)))) := by
  obtain ⟨he, -, hrow, -⟩ := largest_safe_sender_row h hP hmax hR hR2 hPR hu huP hd
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hup := Nat.prime_of_mem_primeFactors hu
  have : Fact P.Prime := ⟨hPp⟩
  have : Fact u.Prime := ⟨hup⟩
  have hRo := Nat.odd_iff.mp (hR.odd_of_ne_two hR2)
  have hR3 : 3 ≤ R := by have := hR.two_le; omega
  have hu2 := lps_odd_of_mem h hu
  have hu2' := hup.two_le
  have hP4 : P % 4 = 3 := by omega
  have hev : Even (N.factorization u) := by rw [he]; exact ⟨(R - 1) / 2, by omega⟩
  set j := padicValNat P (σ 1 (u ^ N.factorization u)) with hjdef
  have hσ : σ 1 (u ^ N.factorization u) = P ^ j := by
    rw [sigma_one_apply_prime_pow hup, he, Nat.sub_add_cancel hR.one_le]
    exact hrow
  have hL := legendreSym_receiver_of_dvd_sigma_even (p := u) (r := P) (by omega) (by omega)
    hev hd
  have hpow : legendreSym u P ^ j = 1 := by
    have h1 := legendreSym_sigma_prime_pow u (N.factorization u)
    rw [hσ] at h1
    have key : ∀ n : ℕ, legendreSym u ((P : ℤ) ^ n) = legendreSym u P ^ n := by
      intro n
      induction n with
      | zero => simp [legendreSym.at_one]
      | succ n ih => rw [pow_succ, legendreSym.mul, ih, pow_succ]
    rw [← key]
    exact_mod_cast h1
  have h3even : u % 4 = 3 → Even j := by
    intro h3
    rw [hL, if_pos ⟨h3, hP4⟩] at hpow
    exact (neg_one_pow_eq_one_iff_even (by decide)).mp hpow
  refine ⟨fun hu3 => ?_, fun hu3 => h3even (by omega)⟩
  have hjodd : Odd j := by
    rcases Nat.even_or_odd j with ⟨m, hm⟩ | ho
    · exfalso
      have hne := geom_sum_prime_pow_ne_sq (h := 1) (y := P ^ m) hup (by omega) odd_one
        (hR.odd_of_ne_two hR2) hR3
      simp only [pow_one] at hne
      apply hne
      rw [hrow, hm, pow_add, sq]
    · exact ho
  refine ⟨?_, hjodd⟩
  rcases Nat.even_or_odd j with hj | hj
  · exact absurd hj (Nat.not_even_iff_odd.mpr hjodd)
  · by_contra hc
    exact absurd (h3even (by omega)) (Nat.not_even_iff_odd.mpr hjodd)

/-- Size. If the largest prime factor of an odd perfect number `N` is `P = 2 R + 1` with `R`
an odd prime, then `(3 ^ R - 1) / 2 ≤ P ^ v_P(N)`: some sender `u ≥ 3` has the row
`1 + u + ⋯ + u ^ (R - 1) = P ^ j`, and `P ^ j ∣ N`. -/
theorem largest_safe_size (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) (hR2 : R ≠ 2) (hPR : P = 2 * R + 1) :
    (3 ^ R - 1) / 2 ≤ P ^ N.factorization P := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hRo := Nat.odd_iff.mp (hR.odd_of_ne_two hR2)
  obtain ⟨u, huP, hu, -, hd⟩ := exists_sigmaEdge_into h.perfect hP (by omega)
  obtain ⟨he, -, hrow, -⟩ := largest_safe_sender_row h hP hmax hR hR2 hPR hu huP hd
  have hup := Nat.prime_of_mem_primeFactors hu
  have hu3 : 3 ≤ u := by have := hup.two_le; have := lps_odd_of_mem h hu; omega
  set j := padicValNat P (σ 1 (u ^ N.factorization u)) with hjdef
  have hσ : σ 1 (u ^ N.factorization u) = P ^ j := by
    rw [sigma_one_apply_prime_pow hup, he, Nat.sub_add_cancel hR.one_le]
    exact hrow
  have h3 : (3 ^ R - 1) / 2 ≤ P ^ j := by
    have hg : ∑ i ∈ Finset.range R, 3 ^ i = (3 ^ R - 1) / 2 := Nat.geomSum_eq (by norm_num) R
    rw [← hrow, ← hg]
    exact Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left hu3 i
  have hdvd : P ^ j ∣ N := by
    have h2N := OPNStarter.component_sigma_dvd h.perfect hup rfl
    rw [hσ] at h2N
    exact Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_left j ((Nat.coprime_primes hPp Nat.prime_two).mpr (by omega))) h2N
  have hjle := (hPp.pow_dvd_iff_le_factorization h.ne_zero).mp hdvd
  exact h3.trans (Nat.pow_le_pow_right hPp.pos hjle)

/-- The senders into `P` and the ledger `v_P(N) = Σ_senders v_P(σ(u ^ e_u))` (a copy of a
private lemma of `OddPerfect/LargestPrimeCapacity.lean`). -/
private theorem lps_sum_senders (h : OddPerfect N) (hP : P ∈ N.primeFactors) :
    N.factorization P = ∑ p ∈ (N.primeFactors.erase P).filter
      (fun p => P ∣ σ 1 (p ^ N.factorization p)), padicValNat P (σ 1 (p ^ N.factorization p)) := by
  have hP2 : P ≠ 2 := by have := lps_odd_of_mem h hP; omega
  rw [factorization_eq_sum_erase h.perfect (Nat.prime_of_mem_primeFactors hP) hP2,
    Finset.sum_filter_of_ne]
  intro p _ hne
  by_contra hd
  exact hne (by rw [Nat.padicValNat_def]; exact padicValNat.eq_zero_of_not_dvd hd)

/-- Number of senders. If the largest prime factor of an odd perfect number `N` is
`P = 2 R + 1` with `R` an odd prime, and `3` is not a sender (for example `3 ∤ N`), then the
number of senders into `P` is even and at least `2`: every row exponent is odd and they add
up to the even, positive `v_P(N)`. -/
theorem largest_safe_card_senders (h : OddPerfect N) (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hR : R.Prime) (hR2 : R ≠ 2) (hPR : P = 2 * R + 1)
    (h3 : ¬ P ∣ σ 1 (3 ^ N.factorization 3)) :
    Even ((N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p))).card ∧
      2 ≤ ((N.primeFactors.erase P).filter
        (fun p => P ∣ σ 1 (p ^ N.factorization p))).card := by
  set S := (N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p))
    with hSdef
  have hsum := lps_sum_senders h hP
  rw [← hSdef] at hsum
  have hodd : ∀ p ∈ S, padicValNat P (σ 1 (p ^ N.factorization p)) % 2 = 1 := by
    intro p hp
    rw [hSdef, Finset.mem_filter, Finset.mem_erase] at hp
    obtain ⟨⟨hpP, hpN⟩, hd⟩ := hp
    have hp3 : p ≠ 3 := by rintro rfl; exact h3 hd
    exact Nat.odd_iff.mp
      ((largest_safe_sender_parity h hP hmax hR hR2 hPR hpN hpP hd).1 hp3).2
  have hmod : N.factorization P % 2 = S.card % 2 := by
    rw [hsum, Finset.sum_nat_mod, Finset.sum_congr rfl hodd, Finset.card_eq_sum_ones]
  have hev := largest_safe_factorization_even h hP hR hR2 hPR
  have hpos : N.factorization P ≠ 0 := Finsupp.mem_support_iff.mp hP
  have hne : S.card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero.mp h0, Finset.sum_empty] at hsum
    exact hpos hsum
  obtain ⟨m, hm⟩ := hev
  refine ⟨⟨S.card / 2, by omega⟩, by omega⟩

/-! ## Controls -/

/-- The case `R = 5`, `P = 11`, `u = 3`: `σ(3 ^ 4) = 11 ^ 2`, an even row exponent at `u = 3`. -/
example : 1 + 3 + 3 ^ 2 + 3 ^ 3 + 3 ^ 4 = 11 ^ 2 := by norm_num

end OddPerfect

#print axioms OddPerfect.largest_safe_factorization_even
#print axioms OddPerfect.largest_safe_sender_row
#print axioms OddPerfect.largest_safe_special_not_sender
#print axioms OddPerfect.largest_safe_sender_parity
#print axioms OddPerfect.largest_safe_size
#print axioms OddPerfect.largest_safe_card_senders
