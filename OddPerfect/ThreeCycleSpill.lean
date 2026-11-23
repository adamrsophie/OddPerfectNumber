import OddPerfect.SevenModTwelve
import OddPerfect.Seed.Starter

/-!
# A 3-cycle of square rows on primes that are 7 modulo 12

Write `phi3 x = x ^ 2 + x + 1`. Let `N` be an odd perfect number and `r, s, t` three distinct
prime factors of `N`, all `7` modulo `12`, with `s ∣ phi3 r`, `t ∣ phi3 s` and `r ∣ phi3 t`.
The main result `three_cycle_excess_or_outside` says that one of the three exponents is at
least `4`, or some prime other than `3, r, s, t` divides one of the three rows.

Such cycles exist among integers: `phi3 43 = 3 * 631`, `phi3 631 = 3 * 307 * 433` and
`phi3 307 = 3 * 43 * 733`, with `43, 631, 307` all `7` modulo `12` (checked at the end of the
module). So no acyclicity statement holds, only the disjunction.

The disjunction does not bound anything alone: different cycles may spill into the same
outside prime, so it is a rule for a later counting argument or checker.

Proof idea. A prime that is `3` modulo `4` is not the special prime, so its exponent is even
and positive. If all three exponents are `2`, then `phi3 r = σ(r ^ 2)` divides `N`. If moreover
no outside prime occurs, the prime factors of `phi3 r` lie in `{3, s}`: `r` is coprime to its
row, and `t ∣ phi3 r` together with `r ∣ phi3 t` is ruled out by quadratic reciprocity. So
`phi3 r = 3 * s ^ k` with `1 ≤ k ≤ 2`; modulo `4` the row is `1`, which forces `k = 1`, hence
`3 * s = r ^ 2 + r + 1` and `r < s`. Going round the cycle gives `r < s < t < r`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace ThreeCycleSpill

/-- One row of the cycle. Let `r, s, t` be prime factors of an odd perfect number `N`, all `7`
modulo `12`, with `r ≠ t`, `s ∣ phi3 r` and `r ∣ phi3 t`. If `v_r(N) < 4`, `v_s(N) < 4` and
every prime factor of `phi3 r` is one of `3, r, s, t`, then `r < s` (the proof shows
`phi3 r = 3 * s`). -/
theorem row_lt {N r s t : ℕ} (h : OddPerfect N)
    (hr : r ∈ N.primeFactors) (hs : s ∈ N.primeFactors) (htp : t.Prime) (htr : t ≠ r)
    (hr12 : r % 12 = 7) (hs12 : s % 12 = 7) (ht12 : t % 12 = 7)
    (h1 : s ∣ phi3 r) (h3 : r ∣ phi3 t)
    (hvr : N.factorization r < 4) (hvs : N.factorization s < 4)
    (hno : ∀ u, u.Prime → u ∣ phi3 r → u = 3 ∨ u = r ∨ u = s ∨ u = t) :
    r < s := by
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hsp := Nat.prime_of_mem_primeFactors hs
  have hN0 := h.ne_zero
  -- the exponent of `r` is `2`
  have hvr2 : N.factorization r = 2 := by
    have h1le := (hrp.dvd_iff_one_le_factorization hN0).mp (Nat.dvd_of_mem_primeFactors hr)
    rcases Nat.even_or_odd (N.factorization r) with ⟨j, hj⟩ | hodd
    · omega
    · have := (special_mod_four h hrp hodd).1
      omega
  -- the row divides `N`
  have hrowN : phi3 r ∣ N := by
    have hd := OPNStarter.component_sigma_dvd h.perfect hrp hvr2
    rw [sigma_prime_sq hrp] at hd
    have hc : Nat.Coprime (phi3 r) 2 :=
      (Nat.prime_two.coprime_iff_not_dvd.2 (phi3_odd r).not_two_dvd_nat).symm
    exact hc.dvd_of_dvd_mul_left hd
  -- split off the single factor `3`
  have h3d : 3 ∣ phi3 r := (three_dvd_phi3_iff r).2 (by omega)
  obtain ⟨m, hm⟩ := h3d
  have hm3 : ¬ 3 ∣ m := fun hd => not_nine_dvd_phi3 r (hm ▸ mul_dvd_mul_left 3 hd)
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp [phi3] at hm
  -- every prime factor of `m` is `s`
  have huniq : ∀ {d : ℕ}, d.Prime → d ∣ m → d = s := by
    intro d hd hdm
    have hdr : d ∣ phi3 r := hm ▸ dvd_mul_of_dvd_right hdm 3
    rcases hno d hd hdr with h | h | h | h
    · exact absurd (h ▸ hdm) hm3
    · subst h
      have hc : Nat.Coprime d d := (phi3_coprime_self d).coprime_dvd_left hdr
      exact absurd (Nat.coprime_self d |>.1 hc) hd.one_lt.ne'
    · exact h
    · subst h
      exact (not_mutual_phi3_of_three_mod_four htp hrp htr (by omega) (by omega) h3 hdr).elim
  obtain ⟨k, hms⟩ : ∃ k, m = s ^ k := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hm0 huniq⟩
  -- bounds on `k`
  have hk1 : 1 ≤ k := by
    have hsm : s ∣ m := by
      rw [hm] at h1
      exact (Nat.Coprime.dvd_of_dvd_mul_left
        ((Nat.coprime_primes hsp Nat.prime_three).2 (by omega)) h1)
    by_contra hk0
    rw [show k = 0 by omega, pow_zero] at hms
    rw [hms] at hsm
    exact hsp.one_lt.ne' (Nat.dvd_one.1 hsm)
  have hk2 : k ≤ 2 := by
    have hskN : s ^ k ∣ N := by
      rw [← hms]
      exact (Dvd.intro_left 3 hm.symm).trans hrowN
    have hle := (hsp.pow_dvd_iff_le_factorization hN0).mp hskN
    rcases Nat.even_or_odd (N.factorization s) with ⟨j, hj⟩ | hodd
    · omega
    · have := (special_mod_four h hsp hodd).1
      omega
  -- modulo `4`
  have hrow4 : phi3 r % 4 = 1 := by
    obtain ⟨a, rfl⟩ : ∃ a, r = 4 * a + 3 := ⟨r / 4, by omega⟩
    have he : phi3 (4 * a + 3) = 4 * (4 * a ^ 2 + 7 * a + 3) + 1 := by
      unfold phi3; ring
    rw [he, Nat.mul_add_mod]
  have hk_eq : k = 1 := by
    by_contra hne
    have hk2' : k = 2 := by omega
    rw [hm, hms, hk2', Nat.mul_mod, Nat.pow_mod] at hrow4
    have : s % 4 = 3 := by omega
    rw [this] at hrow4
    norm_num at hrow4
  rw [hms, hk_eq, pow_one] at hm
  unfold phi3 at hm
  have hr2 := hrp.two_le
  nlinarith

end ThreeCycleSpill

open ThreeCycleSpill

/-- Let `N` be an odd perfect number and `r, s, t` three distinct prime factors of `N`, all `7`
modulo `12`, forming a cycle of square rows: `s ∣ phi3 r`, `t ∣ phi3 s`, `r ∣ phi3 t`. Then one
of `v_r(N), v_s(N), v_t(N)` is at least `4`, or some prime other than `3, r, s, t` divides one
of `phi3 r, phi3 s, phi3 t`.

This disjunction does not bound anything alone: different cycles may spill into the same
outside prime. -/
theorem three_cycle_excess_or_outside {N r s t : ℕ} (h : OddPerfect N)
    (hr : r ∈ N.primeFactors) (hs : s ∈ N.primeFactors) (ht : t ∈ N.primeFactors)
    (hrs : r ≠ s) (hst : s ≠ t) (htr : t ≠ r)
    (hr12 : r % 12 = 7) (hs12 : s % 12 = 7) (ht12 : t % 12 = 7)
    (h1 : s ∣ phi3 r) (h2 : t ∣ phi3 s) (h3 : r ∣ phi3 t) :
    (4 ≤ N.factorization r ∨ 4 ≤ N.factorization s ∨ 4 ≤ N.factorization t) ∨
      ∃ u, u.Prime ∧ u ≠ 3 ∧ u ≠ r ∧ u ≠ s ∧ u ≠ t ∧ (u ∣ phi3 r ∨ u ∣ phi3 s ∨ u ∣ phi3 t) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨hvr, hvs, hvt⟩, hno⟩ := hc
  have hno' : ∀ x, (x = r ∨ x = s ∨ x = t) →
      ∀ u, u.Prime → u ∣ phi3 x → u = 3 ∨ u = r ∨ u = s ∨ u = t := by
    intro x hx u hu hd
    by_contra hne
    push Not at hne
    obtain ⟨a, b, c, d⟩ := hne
    have := hno u hu a b c d
    rcases hx with rfl | rfl | rfl
    · exact this.1 hd
    · exact this.2.1 hd
    · exact this.2.2 hd
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hsp := Nat.prime_of_mem_primeFactors hs
  have htp := Nat.prime_of_mem_primeFactors ht
  have e1 : r < s := row_lt h hr hs htp htr hr12 hs12 ht12 h1 h3 hvr hvs
    (hno' r (Or.inl rfl))
  have e2 : s < t := row_lt h hs ht hrp hrs hs12 ht12 hr12 h2 h1 hvs hvt
    (fun u hu hd => by
      rcases hno' s (Or.inr (Or.inl rfl)) u hu hd with h | h | h | h <;> simp [h])
  have e3 : t < r := row_lt h ht hr hsp hst ht12 hr12 hs12 h3 h2 hvt hvr
    (fun u hu hd => by
      rcases hno' t (Or.inr (Or.inr rfl)) u hu hd with h | h | h | h <;> simp [h])
  omega

/-! ## Control: a cycle among integers -/

/-- `phi3 43 = 3 * 631`. -/
theorem phi3_43 : phi3 43 = 3 * 631 := by norm_num [phi3]

/-- `phi3 631 = 3 * 307 * 433`. -/
theorem phi3_631 : phi3 631 = 3 * 307 * 433 := by norm_num [phi3]

/-- `phi3 307 = 3 * 43 * 733`. -/
theorem phi3_307 : phi3 307 = 3 * 43 * 733 := by norm_num [phi3]

/-- The primes of the control cycle. -/
theorem control_primes :
    Nat.Prime 43 ∧ Nat.Prime 631 ∧ Nat.Prime 307 ∧ Nat.Prime 433 ∧ Nat.Prime 733 := by
  norm_num

/-- The three cycle primes are `7` modulo `12`. -/
theorem control_mod_twelve : 43 % 12 = 7 ∧ 631 % 12 = 7 ∧ 307 % 12 = 7 := by decide

end OddPerfect

#print axioms OddPerfect.ThreeCycleSpill.row_lt
#print axioms OddPerfect.three_cycle_excess_or_outside
#print axioms OddPerfect.phi3_43
#print axioms OddPerfect.phi3_631
#print axioms OddPerfect.phi3_307
#print axioms OddPerfect.control_primes
#print axioms OddPerfect.control_mod_twelve
