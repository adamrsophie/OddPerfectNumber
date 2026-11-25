import OddPerfect.MixedPaletteEdges

/-!
# The special exponent in the palette of exponents 2 and 4 without the primes 3 and 5

Restricted family result; the family is not excluded, and whether the result is in the
literature was not verified.

Let `N` be an odd perfect number with special prime `q` and special exponent `a = v_q(N)`, let
every other prime factor have exponent `2` or `4`, and let exactly one prime factor `P` exceed
`q`. The landed `special_exponent_eq_one_nine_or_thirteen_of_not_three_dvd` gives
`a ∈ {1, 9, 13}` when `3 ∤ N`. Under the explicit hypotheses `3 ∤ N` and `5 ∤ N`, the value
`a = 9` is impossible and `a = 13` forces `q ≡ 1 (mod 60)`
(`special_exponent_eq_one_or_thirteen_of_not_three_five_dvd`). By the Main Theorem of
Fletcher, Nielsen and Ochem (Math. Comp. 81 (2012)) the least prime factor exceeds `10 ^ 8` when
every prime factor other than the special prime has exponent `2` or `4`, so `3 ∤ N` and `5 ∤ N`
hold in this family; that theorem is not formalized here, and the two conditions are explicit
hypotheses.

Proof outline for `a ∈ {9, 13}`, with `c = (a + 1) / 2`. If `q ≡ 1 (mod 5)` and `a = 9`, then
`5 ∣ σ(q ^ 9) ∣ 2 N`. If `q ≢ 1 (mod 5)`, no row `σ(p ^ 4)` is divisible by `q`, the rows of the
primes below `q` carry at most `1` at `q`, so `P` has exponent `2` and
`q ^ (a - 1) ∣ σ(P ^ 2) < (P + 1) ^ 2`, whence `q ^ (c - 1) ≤ P`. The rows of the primes below
`q` are below `q ^ 4 ≤ P`, so `P ^ 2 ∣ σ(q ^ a) = A (q ^ c + 1)` with
`A = 1 + q + ... + q ^ (c - 1)`. Since `A q + 1 = A + q ^ c`, a common prime divisor of `A` and
`q ^ c + 1` divides `2`, so `P ^ 2` divides one factor; both are at most
`q ^ c + 1 < q ^ (a - 1) ≤ P ^ 2`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem rtpf_geom_mul_add (q c : ℕ) :
    (∑ i ∈ Finset.range c, q ^ i) * q + 1 = (∑ i ∈ Finset.range c, q ^ i) + q ^ c := by
  induction c with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ, add_mul]
    omega

private theorem rtpf_geom_double (q c : ℕ) :
    ∑ i ∈ Finset.range (2 * c), q ^ i =
      (∑ i ∈ Finset.range c, q ^ i) * (q ^ c + 1) := by
  rw [two_mul, Finset.sum_range_add]
  have h : ∑ x ∈ Finset.range c, q ^ (c + x) = q ^ c * ∑ x ∈ Finset.range c, q ^ x := by
    rw [Finset.mul_sum]
    simp only [pow_add]
  rw [h]
  ring

private theorem rtpf_pow_gap {q c d : ℕ} (hq : 2 ≤ q) (hc : 1 ≤ c) (hcd : c < d) :
    q ^ c + 1 < q ^ d := by
  have h1 : q ^ (c + 1) ≤ q ^ d := Nat.pow_le_pow_right (by omega) hcd
  have h2 : q ≤ q ^ c := Nat.le_self_pow (by omega) q
  have h3 : q ^ (c + 1) = q ^ c * q := pow_succ q c
  have h4 : q ^ c * 2 ≤ q ^ c * q := Nat.mul_le_mul_left _ hq
  omega

/-- The square of an odd prime `P` with `q ^ c + 1 < P ^ 2` does not divide
`σ(q ^ a) = 1 + q + ... + q ^ a` when `a + 1 = 2 c`. -/
private theorem rtpf_core {q P a c : ℕ} (hq : 2 ≤ q) (hc : 1 ≤ c) (hP : P.Prime) (hP2 : P ≠ 2)
    (hac : a + 1 = 2 * c) (hbig : q ^ c + 1 < P ^ 2)
    (hd : P ^ 2 ∣ ∑ i ∈ Finset.range (a + 1), q ^ i) : False := by
  have hgm := rtpf_geom_mul_add q c
  have hA1 : 1 ≤ ∑ i ∈ Finset.range c, q ^ i := by
    have := Finset.single_le_sum (f := fun i => q ^ i) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (show 0 < c by omega))
    simpa using this
  rw [hac, rtpf_geom_double] at hd
  generalize ∑ i ∈ Finset.range c, q ^ i = A at hgm hA1 hd
  have h2A : A * 2 ≤ A * q := Nat.mul_le_mul_left _ hq
  have hAle : A ≤ q ^ c := by omega
  have hpos : 0 < q ^ c + 1 := by omega
  have hPd : ¬ (P ∣ A ∧ P ∣ q ^ c + 1) := by
    rintro ⟨h1, h2⟩
    have h3 : P ∣ A + (q ^ c + 1) := dvd_add h1 h2
    rw [show A + (q ^ c + 1) = A * q + 2 by omega] at h3
    have h4 : P ∣ 2 := (Nat.dvd_add_right (dvd_mul_of_dvd_left h1 q)).mp h3
    exact hP2 ((Nat.prime_dvd_prime_iff_eq hP Nat.prime_two).mp h4)
  by_cases hPA : P ∣ A
  · have hcop : Nat.Coprime (P ^ 2) (q ^ c + 1) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hP).mpr fun h2 => hPd ⟨hPA, h2⟩)
    have := Nat.le_of_dvd (by omega) (hcop.dvd_of_dvd_mul_right hd)
    omega
  · have hcop : Nat.Coprime (P ^ 2) A :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hP).mpr hPA)
    have := Nat.le_of_dvd hpos (hcop.dvd_of_dvd_mul_left hd)
    omega

/-- Modulo `m`, a geometric sum of `l` terms with ratio `1 (mod m)` is `l`. -/
private theorem rtpf_cast_geom_sum {l m p : ℕ} (hp : p % m = 1) :
    ((∑ i ∈ Finset.range l, p ^ i : ℕ) : ZMod m) = l := by
  push_cast
  rw [show (p : ZMod m) = 1 by rw [← ZMod.natCast_mod, hp, Nat.cast_one]]
  simp

/-- An odd prime dividing the divisor sum of a prime power component is a prime factor. -/
private theorem rtpf_mem_of_dvd_sigma {N p r : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors)
    (hr : r.Prime) (hr2 : r ≠ 2) (hd : r ∣ σ 1 (p ^ N.factorization p)) :
    r ∈ N.primeFactors := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have h0 : σ 1 (p ^ N.factorization p) ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
  have hw : 1 ≤ sigmaWeight N p r := hr.factorization_pos_of_dvd h0 hd
  exact mem_primeFactors_of_sigmaWeight_ne_zero h.perfect hp hr2 (by omega)

/-- Palette with one prime above the special prime, without the primes `3` and `5`. Let `N` be
an odd perfect number with special prime `q`, let every other prime factor have exponent `2` or
`4`, and let `q` be the second largest prime factor (some prime factor `P > q`, every prime
factor other than `P` at most `q`). Under the explicit hypotheses `3 ∤ N` and `5 ∤ N`,
`v_q(N) = 1`, or `v_q(N) = 13` and `q ≡ 1 (mod 60)`. Restricted family result: the family is not
excluded. The Main Theorem of Fletcher, Nielsen and Ochem (Math. Comp. 81 (2012)) gives `3 ∤ N`
and `5 ∤ N` in this family; it is not formalized here. Novelty not verified. -/
theorem special_exponent_eq_one_or_thirteen_of_not_three_five_dvd {N q P : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) :
    N.factorization q = 1 ∨ (N.factorization q = 13 ∧ q % 60 = 1) := by
  classical
  rcases special_exponent_eq_one_nine_or_thirteen_of_not_three_dvd h hq hodd hP hqP hsecond
    hexp h3 with h1 | h913
  · exact Or.inl h1
  right
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hPq : P ≠ q := by omega
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨j, hj⟩ := hodd; omega)
  have hP2 : P ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hP)
  have hq2 : q ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hqmem)
  have hq12 := special_mod_twelve h h3 hq hodd
  have hq5 : q ≠ 5 := fun h' => h5 (h' ▸ Nat.dvd_of_mem_primeFactors hqmem)
  have hqge : 2 ≤ q := hq.two_le
  have hq51 : q % 5 = 1 := by
    by_contra hne
    -- no quartic row reaches `q`, so `P` has exponent `2`
    have hvP : sigmaWeight N P q = 0 ∨ N.factorization P = 2 := by
      rcases hexp P hP hPq with he | he
      · exact Or.inr he
      · left
        unfold sigmaWeight
        rw [he, sigma_one_apply_prime_pow hPp]
        exact Nat.factorization_eq_zero_of_not_dvd
          (not_dvd_geom_sum_of_not_dvd_sub_one hq Nat.prime_five hq5 (by omega) P)
    -- the ledgers at `q` and at `P`
    have hrest : N.primeFactors.filter (fun p => ¬ p < q) = {q, P} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hp, hpq⟩
        by_cases hpP : p = P
        · exact Or.inr hpP
        · have := hsecond p hp hpP
          exact Or.inl (by omega)
      · rintro (rfl | rfl)
        · exact ⟨hqmem, lt_irrefl _⟩
        · exact ⟨hP, by omega⟩
    have hledq := sigmaWeight_sum_eq h.2 hq hq2
    rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (· < q), hrest,
      Finset.sum_pair hPq.symm, sigmaWeight_self hq] at hledq
    have hledP := sigmaWeight_sum_eq h.2 hPp hP2
    rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (· < q), hrest,
      Finset.sum_pair hPq.symm, sigmaWeight_self hPp] at hledP
    have hlow := mixed_sum_sigmaWeight_below_special_le_mod_of_not_three_dvd h hq hexp h3
    have hlow1 : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ 1 := by
      split_ifs at hlow <;> omega
    have he2 : N.factorization P = 2 := by
      rcases hvP with h0 | h2
      · omega
      · exact h2
    -- `q ^ (a - 1)` divides `σ(P ^ 2)`, so `q ^ ((a - 1) / 2) ≤ P`
    have hqw : q ^ sigmaWeight N P q ∣ σ 1 (P ^ N.factorization P) := Nat.ordProj_dvd _ _
    rw [he2] at hqw
    have hσ0 : 0 < σ 1 (P ^ 2) := sigma_pos 1 _ (pow_ne_zero _ hPp.ne_zero)
    have hlt := sigma_prime_pow_lt_succ_pow hPp (k := 2) (by norm_num)
    have hle := Nat.le_of_dvd hσ0 hqw
    have hpow : q ^ (N.factorization q - 1) ≤ q ^ sigmaWeight N P q :=
      Nat.pow_le_pow_right hq.pos (by omega)
    obtain ⟨k, hk⟩ : ∃ k, N.factorization q - 1 = 2 * k :=
      ⟨(N.factorization q - 1) / 2, by omega⟩
    have hk2 : q ^ (N.factorization q - 1) = (q ^ k) ^ 2 := by rw [hk, pow_mul']
    have hqk : q ^ k ≤ P := by
      by_contra hc
      push Not at hc
      have : (P + 1) ^ 2 ≤ (q ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.succ_le_of_lt hc) 2
      omega
    have hPbig : q ^ (N.factorization q - 1) ≤ P ^ 2 := by
      rw [hk2]
      exact Nat.pow_le_pow_left hqk 2
    have hq4 : q ^ 4 ≤ P := le_trans (Nat.pow_le_pow_right hq.pos (by omega)) hqk
    -- no row of a prime below `q` is divisible by `P`
    have hlowP : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p P = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hp'
      have hk24 := hexp p hp' (by omega)
      have hs0 : 0 < σ 1 (p ^ N.factorization p) := sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)
      have h1 := sigma_prime_pow_lt_succ_pow hpp (k := N.factorization p) (by omega)
      have h2 : (p + 1) ^ N.factorization p ≤ q ^ N.factorization p :=
        Nat.pow_le_pow_left (by omega) _
      have h3 : q ^ N.factorization p ≤ q ^ 4 := Nat.pow_le_pow_right hq.pos (by omega)
      unfold sigmaWeight
      refine Nat.factorization_eq_zero_of_not_dvd fun hd => ?_
      have := Nat.le_of_dvd hs0 hd
      omega
    have hvq : sigmaWeight N q P = 2 := by omega
    have hPv : P ^ sigmaWeight N q P ∣ σ 1 (q ^ N.factorization q) := Nat.ordProj_dvd _ _
    rw [hvq, sigma_one_apply_prime_pow hq] at hPv
    rcases h913 with h9 | h13
    · exact rtpf_core hqge (c := 5) (by norm_num) hPp hP2 (by omega)
        (lt_of_lt_of_le (rtpf_pow_gap hqge (by norm_num)
          (show 5 < N.factorization q - 1 by omega)) hPbig) hPv
    · exact rtpf_core hqge (c := 7) (by norm_num) hPp hP2 (by omega)
        (lt_of_lt_of_le (rtpf_pow_gap hqge (by norm_num)
          (show 7 < N.factorization q - 1 by omega)) hPbig) hPv
  rcases h913 with h9 | h13
  · exfalso
    apply h5
    have hd : 5 ∣ σ 1 (q ^ N.factorization q) := by
      rw [sigma_one_apply_prime_pow hq, h9]
      exact (ZMod.natCast_eq_zero_iff _ _).mp (by rw [rtpf_cast_geom_sum hq51]; decide)
    exact Nat.dvd_of_mem_primeFactors
      (rtpf_mem_of_dvd_sigma h hqmem Nat.prime_five (by norm_num) hd)
  · exact ⟨h13, by omega⟩

end OddPerfect

#print axioms OddPerfect.special_exponent_eq_one_or_thirteen_of_not_three_five_dvd
