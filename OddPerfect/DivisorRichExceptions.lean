import OddPerfect.KanoldSquare
import OddPerfect.EqualExponents

/-!
# Exceptions to a common index divisor with many divisors

Let `N` be an odd perfect number, `l` an odd prime, `D` a number, and `E` a set of at most `s`
exceptional primes such that `D ∣ v_p(N) + 1` for every prime factor `p` of `N` outside `E`,
with at least one such `p`. Write `F` for the divisors of `D` divisible by `l`.

* `padicValNat_mul_card_sub_le_factorization`: `v_l(D) (|F| - s) ≤ v_l(N)`.
* `dvd_of_divisor_rich`: if `l ∣ D` and `s < |F|`, then `l ∣ N`.
* `dvd_of_two_mul_lt_card_divisors`: if `l ∣ D` and `2 s < τ(D)`, then `l ∣ N`.
* `mul_sub_le_factorization_of_pow_dvd`: for `D = l ^ b`, `b (b - s) ≤ v_l(N)`.
* `dvd_of_exceptions_of_pow_dvd`: for `D = l ^ b` and `s < b`, `l ∣ N`.

There is no size condition on `l` (the landed `dvd_of_exceptions_of_sixteen_pow_lt` needs
`16 ^ s < l`). What these statements do not give: nothing once `s` reaches `|F|`; for `D = l`
only `s = 0` is covered, and there the landed `pow_four_dvd_of_dvd_succ` is stronger, so this
file is not a generalization of it.

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.
-/

namespace OddPerfect

/-- **Exceptions against a divisor rich common index divisor.** Let `N` be an odd perfect
number, `l` an odd prime, and `E` a set of at most `s` primes such that
`D ∣ v_p(N) + 1` for every prime factor `p ∉ E` of `N`, with at least one such `p`. With `F`
the divisors of `D` divisible by `l`, `v_l(D) (|F| - s) ≤ v_l(N)`. Gives nothing once
`s ≥ |F|`. Restricted result; no published source was checked; novelty not verified. -/
theorem padicValNat_mul_card_sub_le_factorization {N l D s : ℕ} (h : OddPerfect N)
    (hl : l.Prime) (hl2 : l ≠ 2) (E : Finset ℕ) (hE : E.card ≤ s)
    (hex : ∃ p ∈ N.primeFactors, p ∉ E)
    (hcomp : ∀ p ∈ N.primeFactors, p ∉ E → D ∣ N.factorization p + 1) :
    padicValNat l D * ((D.divisors.filter fun d => l ∣ d).card - s) ≤ N.factorization l := by
  have hD : D ≠ 0 := by
    obtain ⟨p, hpN, hpE⟩ := hex
    intro h0
    have h1 := hcomp p hpN hpE
    rw [h0, zero_dvd_iff] at h1
    omega
  obtain ⟨p, hpN, hpE⟩ := hex
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  set F := D.divisors.filter fun d => l ∣ d with hF
  set W := (N.primeFactors.filter fun r => r % l = 1).erase p with hW
  have hFW : F.card ≤ W.card := by
    refine card_le_card_erase_of_dvd_succ h hl.two_le hpN F ?_ ?_ ?_
    · intro d hd
      obtain ⟨hdD, hld⟩ := Finset.mem_filter.mp hd
      exact hl3.trans (Nat.le_of_dvd
        (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hdD) (Nat.pos_of_ne_zero hD)) hld)
    · intro d hd
      exact (Finset.mem_filter.mp hd).2
    · intro d hd
      exact (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1).trans (hcomp p hpN hpE)
  set b := padicValNat l D with hb
  have hbD : l ^ b ∣ D := by
    rw [hb, Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _
  have hval : ∀ r ∈ W \ E, b ≤ padicValNat l (N.factorization r + 1) := by
    intro r hr
    obtain ⟨hrW, hrE⟩ := Finset.mem_sdiff.mp hr
    have hrN : r ∈ N.primeFactors := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hrW)).1
    rw [Nat.padicValNat_def]
    exact (Nat.pow_dvd_iff_le_multiplicity hl.ne_one (Nat.succ_ne_zero _)).mp
      (hbD.trans (hcomp r hrN hrE))
  have hsum : (W \ E).card * b ≤ N.factorization l := by
    calc (W \ E).card * b = (W \ E).card • b := (smul_eq_mul _ _).symm
      _ ≤ ∑ r ∈ W \ E, padicValNat l (N.factorization r + 1) :=
          Finset.card_nsmul_le_sum _ _ _ hval
      _ ≤ ∑ r ∈ N.primeFactors.filter (fun r => r % l = 1),
            padicValNat l (N.factorization r + 1) :=
          Finset.sum_le_sum_of_subset
            (fun r hr => Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hr).1)
      _ ≤ N.factorization l := sum_padicValNat_succ_le h.2 hl hl2
  have hcard : F.card - s ≤ (W \ E).card := by
    have := Finset.le_card_sdiff E W
    omega
  calc b * (F.card - s) ≤ b * (W \ E).card := Nat.mul_le_mul_left _ hcard
    _ = (W \ E).card * b := Nat.mul_comm _ _
    _ ≤ N.factorization l := hsum

/-- If `l ∣ D` and the exceptions number fewer than the divisors of `D` divisible by `l`, then
`l ∣ N`, with no size condition on `l`. Restricted result; no published source was checked;
novelty not verified. -/
theorem dvd_of_divisor_rich {N l D s : ℕ} (h : OddPerfect N) (hl : l.Prime) (hl2 : l ≠ 2)
    (E : Finset ℕ) (hE : E.card ≤ s) (hex : ∃ p ∈ N.primeFactors, p ∉ E)
    (hcomp : ∀ p ∈ N.primeFactors, p ∉ E → D ∣ N.factorization p + 1) (hlD : l ∣ D)
    (hcard : s < (D.divisors.filter fun d => l ∣ d).card) : l ∣ N := by
  have hD : D ≠ 0 := by
    obtain ⟨p, hpN, hpE⟩ := hex
    intro h0
    have h1 := hcomp p hpN hpE
    rw [h0, zero_dvd_iff] at h1
    omega
  have hb : 1 ≤ padicValNat l D := by
    rw [Nat.padicValNat_def]
    exact (Nat.pow_dvd_iff_le_multiplicity hl.ne_one hD).mp (by simpa using hlD)
  have key := padicValNat_mul_card_sub_le_factorization h hl hl2 E hE hex hcomp
  apply Nat.dvd_of_factorization_pos
  have h1 : 1 ≤ (D.divisors.filter fun d => l ∣ d).card - s := by omega
  have := Nat.mul_le_mul hb h1
  omega

/-- If `l ∣ D` and `2 s < τ(D)`, then `l ∣ N`: multiplication by `l` maps the divisors of `D`
not divisible by `l` injectively into those divisible by `l`. Restricted result; no published
source was checked; novelty not verified. -/
theorem dvd_of_two_mul_lt_card_divisors {N l D s : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hl2 : l ≠ 2) (E : Finset ℕ) (hE : E.card ≤ s)
    (hex : ∃ p ∈ N.primeFactors, p ∉ E)
    (hcomp : ∀ p ∈ N.primeFactors, p ∉ E → D ∣ N.factorization p + 1) (hlD : l ∣ D)
    (hcard : 2 * s < D.divisors.card) : l ∣ N := by
  have hD : D ≠ 0 := by
    obtain ⟨p, hpN, hpE⟩ := hex
    intro h0
    have h1 := hcomp p hpN hpE
    rw [h0, zero_dvd_iff] at h1
    omega
  apply dvd_of_divisor_rich h hl hl2 E hE hex hcomp hlD
  have hsplit := Finset.card_filter_add_card_filter_not (s := D.divisors) (fun d => l ∣ d)
  have hinj : (D.divisors.filter fun d => ¬ l ∣ d).card ≤
      (D.divisors.filter fun d => l ∣ d).card := by
    refine Finset.card_le_card_of_injOn (fun d => l * d) ?_ ?_
    · intro d hd
      obtain ⟨hdD, hnd⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hd)
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hD⟩,
        dvd_mul_right l d⟩)
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.Prime.coprime_iff_not_dvd hl).mpr hnd) hlD
        (Nat.dvd_of_mem_divisors hdD)
    · intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left hl.pos hxy
  omega

/-- For the common index divisor `l ^ b`: `b (b - s) ≤ v_l(N)`. Restricted result; no
published source was checked; novelty not verified. -/
theorem mul_sub_le_factorization_of_pow_dvd {N l b s : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hl2 : l ≠ 2) (E : Finset ℕ) (hE : E.card ≤ s) (hex : ∃ p ∈ N.primeFactors, p ∉ E)
    (hcomp : ∀ p ∈ N.primeFactors, p ∉ E → l ^ b ∣ N.factorization p + 1) :
    b * (b - s) ≤ N.factorization l := by
  have : Fact l.Prime := ⟨hl⟩
  have hD : l ^ b ≠ 0 := pow_ne_zero _ hl.ne_zero
  have key := padicValNat_mul_card_sub_le_factorization h hl hl2 E hE hex hcomp
  have hv : padicValNat l (l ^ b) = b := by
    rw [Nat.padicValNat_def]; exact Nat.multiplicity_prime_pow b
  have hF : b ≤ ((l ^ b).divisors.filter fun d => l ∣ d).card := by
    have himg : (Finset.Icc 1 b).image (fun k => l ^ k) ⊆
        (l ^ b).divisors.filter fun d => l ∣ d := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hk1, hkb⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨pow_dvd_pow l hkb, hD⟩,
        dvd_pow_self l (by omega)⟩
    have := Finset.card_le_card himg
    rwa [Finset.card_image_of_injective _ (Nat.pow_right_injective hl.two_le), Nat.card_Icc,
      Nat.add_sub_cancel] at this
  rw [hv] at key
  calc b * (b - s) ≤ b * (((l ^ b).divisors.filter fun d => l ∣ d).card - s) :=
        Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hF s)
    _ ≤ N.factorization l := key

/-- For the common index divisor `l ^ b` with fewer than `b` exceptions, `l ∣ N`, with no size
condition on `l`. Restricted result; no published source was checked; novelty not verified. -/
theorem dvd_of_exceptions_of_pow_dvd {N l b s : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hl2 : l ≠ 2) (E : Finset ℕ) (hE : E.card ≤ s) (hex : ∃ p ∈ N.primeFactors, p ∉ E)
    (hcomp : ∀ p ∈ N.primeFactors, p ∉ E → l ^ b ∣ N.factorization p + 1) (hsb : s < b) :
    l ∣ N := by
  have key := mul_sub_le_factorization_of_pow_dvd h hl hl2 E hE hex hcomp
  apply Nat.dvd_of_factorization_pos
  have : 1 ≤ b * (b - s) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  omega

end OddPerfect

#print axioms OddPerfect.padicValNat_mul_card_sub_le_factorization
#print axioms OddPerfect.dvd_of_divisor_rich
#print axioms OddPerfect.dvd_of_two_mul_lt_card_divisors
#print axioms OddPerfect.mul_sub_le_factorization_of_pow_dvd
#print axioms OddPerfect.dvd_of_exceptions_of_pow_dvd
