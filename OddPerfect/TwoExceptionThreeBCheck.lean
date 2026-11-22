import OddPerfect.TwoExceptionThreeACheck

/-!
# Checkers for branch B

Branch B of `two_exceptions_five_three_sq_branch_b` has special prime 5, `e₃ = 2`, the exceptions
13 and a prime `s ≡ 1 (mod 5)` with `Φ₅(s) ∣ N`, and every other prime factor squared. This file
states the forcing rules of that configuration as an abstract context `Ctx N s` and defines two
Boolean walks with soundness proofs:

* `fchk` derives forced primes from `Φ₅(s)` and from `t^2 + t + 1` of forced squares and stops at
  7 or at two distinct forced primes `≡ 1 (mod 3)` outside `{13, s}`;
* `scover` walks over `s ≡ 1 (mod 10)` below a bound, and `tcover` walks over the possible
  primes `t ≡ 1 (mod 3)` below a bound whose `t^2 + t + 1` is `3 · 13^a · s^b`.
-/

namespace OddPerfect.TwoExceptionThreeB

open OddPerfect.TwoExceptionThreeA

/-- The forcing rules of branch B for the prime `s`. -/
structure Ctx (N s : ℕ) : Prop where
  phi5 : ∀ w, w.Prime → w ≠ 2 → w ∣ phi5 s → w ∣ N
  sq : ∀ v w, v.Prime → v ∣ N → v ≠ 5 → v ≠ 13 → v ≠ s → w.Prime → w ≠ 2 → w ∣ phi3 v → w ∣ N
  two : ∀ a b, a.Prime → b.Prime → a ∣ N → b ∣ N → a ≠ b → a % 3 = 1 → b % 3 = 1 → a ≠ 13 →
    b ≠ 13 → a ≠ s → b ≠ s → False
  seven : ¬ 7 ∣ N

/-- Primality: membership in a certified list or trial division. -/
def primeOK (P : List ℕ) (w : ℕ) : Bool := P.contains w || sqrtPrime w

theorem primeOK_sound {P : List ℕ} (hP : ∀ p ∈ P, p.Prime) {w : ℕ} (h : primeOK P w = true) :
    w.Prime := by
  simp only [primeOK, Bool.or_eq_true] at h
  rcases h with h | h
  · exact hP w (List.contains_iff_mem.mp h)
  · exact sqrtPrime_sound h

/-- The forcing walk: each step `(w, v)` adds a prime `w` dividing `Φ₅(s)` (when `v = 0`) or
dividing `v^2 + v + 1` for an earlier forced prime `v ∉ {5, 13, s}`. At the end `a = 7` is
forced, or `a` and `b` are distinct forced primes `≡ 1 (mod 3)` outside `{13, s}`. -/
def fchk (P : List ℕ) (s : ℕ) : List ℕ → List (ℕ × ℕ) → ℕ → ℕ → Bool
  | known, [], a, b => known.contains a && (a == 7 || (known.contains b && a != b &&
      a % 3 == 1 && b % 3 == 1 && a != 13 && b != 13 && a != s && b != s))
  | known, (w, v) :: rest, a, b => w != 2 && primeOK P w &&
      ((v == 0 && phi5 s % w == 0) ||
        (known.contains v && v != 5 && v != 13 && v != s && phi3 v % w == 0)) &&
      fchk P s (w :: known) rest a b

theorem fchk_sound {P : List ℕ} (hP : ∀ p ∈ P, p.Prime) {N s : ℕ} (hc : Ctx N s) :
    ∀ (steps : List (ℕ × ℕ)) (known : List ℕ) (a b : ℕ),
      (∀ w ∈ known, w.Prime ∧ w ∣ N) → fchk P s known steps a b = true → False
  | [], known, a, b, hk, h => by
    simp only [fchk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      List.contains_iff_mem] at h
    obtain ⟨ha, h7 | ⟨⟨⟨⟨⟨⟨⟨⟨hb, hab⟩, ha3⟩, hb3⟩, ha13⟩, hb13⟩, has⟩, hbs⟩⟩⟩ := h
    · subst h7
      exact hc.seven (hk 7 ha).2
    · exact hc.two a b (hk a ha).1 (hk b hb).1 (hk a ha).2 (hk b hb).2 hab ha3 hb3 ha13 hb13
        has hbs
  | (w, v) :: rest, known, a, b, hk, h => by
    simp only [fchk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      List.contains_iff_mem] at h
    obtain ⟨⟨⟨hw2, hwp⟩, hsrc⟩, hrest⟩ := h
    have hw := primeOK_sound hP hwp
    have hwN : w ∣ N := by
      rcases hsrc with ⟨-, hd⟩ | ⟨⟨⟨⟨hv, hv5⟩, hv13⟩, hvs⟩, hd⟩
      · exact hc.phi5 w hw hw2 (Nat.dvd_of_mod_eq_zero hd)
      · exact hc.sq v w (hk v hv).1 (hk v hv).2 hv5 hv13 hvs hw hw2 (Nat.dvd_of_mod_eq_zero hd)
    refine fchk_sound hP hc rest (w :: known) a b (fun u hu => ?_) hrest
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨hw, hwN⟩
    · exact hk u hu

/-- One entry `(n, d, steps, a, b)` of the walk over `s`: `n` is composite with divisor `d`, or
`n = 61`, or the forcing walk closes `n`. -/
def sEntry (P : List ℕ) (n d : ℕ) (steps : List (ℕ × ℕ)) (a b : ℕ) : Bool :=
  (1 < d && d < n && n % d == 0) || n == 61 || fchk P n [] steps a b

/-- The walk over `n, n + 10, …`, ending exactly at `hi`. -/
def scover (P : List ℕ) : ℕ → List (ℕ × ℕ × List (ℕ × ℕ) × ℕ × ℕ) → ℕ → Bool
  | n, [], hi => n == hi
  | n, (m, d, steps, a, b) :: L, hi => m == n && sEntry P m d steps a b && scover P (n + 10) L hi

theorem scover_sound {P : List ℕ} (hP : ∀ p ∈ P, p.Prime) {hi : ℕ} :
    ∀ (L : List (ℕ × ℕ × List (ℕ × ℕ) × ℕ × ℕ)) (n : ℕ), scover P n L hi = true →
      ∀ x, n ≤ x → x < hi → x % 10 = n % 10 → x.Prime → x ≠ 61 → ∀ N, Ctx N x → False
  | [], n, h => by
    intro x h1 h2
    simp only [scover, beq_iff_eq] at h
    omega
  | (m, d, steps, a, b) :: L, n, h => by
    intro x h1 h2 h3 hx h61 N hc
    simp only [scover, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hok⟩, hrest⟩ := h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · simp only [sEntry, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
      rcases hok with (⟨⟨hd1, hd2⟩, hd3⟩ | h61') | hf
      · have := (Nat.prime_def_lt.mp hx).2 d hd2 (Nat.dvd_of_mod_eq_zero hd3)
        omega
      · exact h61 h61'
      · exact fchk_sound hP hc steps [] a b (by simp) hf
    · exact scover_sound hP L (m + 10) hrest x (by omega) h2 (by omega) hx h61 N hc

/-- A positive `m` whose prime factors all equal `s` is a power of `s`. -/
theorem eq_pow_of_primeFactors {m s : ℕ} (hm : m ≠ 0) (h : ∀ q, q.Prime → q ∣ m → q = s) :
    m = s ^ m.factorization s := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  rw [Finsupp.prod_of_support_subset _ (s := {s}) (by
    intro q hq
    rw [Nat.support_factorization] at hq
    simp only [Finset.mem_singleton]
    exact h q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq))
    _ (fun _ _ => pow_zero _), Finset.prod_singleton]

/-- One entry `(t, d, a, m, p, k, steps, u, v)` of the walk over `t`: `t` is composite with
divisor `d`; or `t^2 + t + 1 = 3 · 13^a · m` with `13 ∤ m` and `m` is not `s^b` for a prime
`s ≥ lo` (it is below `lo`, or splits into two coprime factors `d` and `m / d`), or `m = p^k`
for a certified prime `p` that is below `lo`, is not `1 (mod 5)`, or is closed by the forcing
walk started at `t`. -/
def tEntry (P : List ℕ) (lo t d a m p k : ℕ) (steps : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  (1 < d && d < t && t % d == 0) ||
  (phi3 t == 3 * 13 ^ a * m && m % 13 != 0 &&
    ((m != 1 && m < lo) || (1 < d && d < m && m % d == 0 && Nat.gcd d (m / d) == 1) ||
      (1 ≤ k && p ^ k == m && primeOK P p &&
        (p < lo || p % 5 != 1 || fchk P p [t] steps u v))))

/-- The walk over `t, t + 3, …`, ending exactly at `hi`. -/
def tcover (P : List ℕ) (lo : ℕ) :
    ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ) × ℕ × ℕ) → ℕ → Bool
  | n, [], hi => n == hi
  | n, (t, d, a, m, p, k, steps, u, v) :: L, hi =>
    t == n && tEntry P lo t d a m p k steps u v && tcover P lo (n + 3) L hi

/-- What the walk over `t` excludes. -/
def TGood (lo t : ℕ) : Prop :=
  ∀ N s, Ctx N s → s.Prime → lo ≤ s → s % 5 = 1 → t.Prime → t ∣ N →
    (∀ q, q.Prime → q ∣ phi3 t → q = 3 ∨ q = 13 ∨ q = s) → False

theorem tEntry_sound {P : List ℕ} (hP : ∀ p ∈ P, p.Prime) {lo t d a m p k : ℕ}
    {steps : List (ℕ × ℕ)} {u v : ℕ} (h : tEntry P lo t d a m p k steps u v = true) :
    TGood lo t := by
  intro N s hc hs hlo hs5 ht htN hsupp
  simp only [tEntry, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨hd1, hd2⟩, hd3⟩ | ⟨⟨heq, hm13⟩, hcase⟩
  · have := (Nat.prime_def_lt.mp ht).2 d hd2 (Nat.dvd_of_mod_eq_zero hd3)
    omega
  -- `m` is a power of `s`
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := phi3_odd t
    rw [heq] at this
    simp at this
  have hmd : m ∣ phi3 t := ⟨3 * 13 ^ a, by rw [heq]; ring⟩
  have hm3 : ¬ 3 ∣ m := fun h3 => not_nine_dvd_phi3 t (by
    rw [heq, show 3 * 13 ^ a * m = 13 ^ a * (3 * m) by ring]
    exact Dvd.dvd.mul_left (show 3 * 3 ∣ 3 * m from Nat.mul_dvd_mul_left 3 h3) _)
  have hpow : m = s ^ m.factorization s := eq_pow_of_primeFactors hm0 (fun q hq hqm => by
    rcases hsupp q hq (hqm.trans hmd) with h3 | h13 | hqs
    · subst h3; exact absurd hqm hm3
    · subst h13; exact absurd (Nat.mod_eq_zero_of_dvd hqm) hm13
    · exact hqs)
  set b := m.factorization s
  have hs2 := hs.two_le
  rcases hcase with (⟨hm1, hmlo⟩ | ⟨⟨⟨⟨hd1, hd2⟩, hd3⟩, hgcd⟩⟩) | ⟨⟨⟨⟨hk, hpk⟩, hpp⟩, hfin⟩⟩
  · -- `m = s^b` with `b ≥ 1` is at least `s`
    have hb : b ≠ 0 := by
      intro hb
      rw [hb, pow_zero] at hpow
      exact hm1 hpow
    have : s ≤ m := by
      rw [hpow]
      calc s = s ^ 1 := (pow_one s).symm
        _ ≤ s ^ b := Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hb)
    omega
  · -- a prime power has no split into two coprime factors above 1
    have hdm : d ∣ s ^ b := hpow ▸ Nat.dvd_of_mod_eq_zero hd3
    obtain ⟨i, hi, hdi⟩ := (Nat.dvd_prime_pow hs).mp hdm
    have hi0 : i ≠ 0 := by
      rintro rfl
      simp at hdi
      omega
    have hq : m / d = s ^ (b - i) := by
      rw [hdi]
      conv_lhs => rw [hpow]
      rw [Nat.pow_div hi hs.pos]
    have hbi : b - i ≠ 0 := by
      intro hbi
      rw [hbi, pow_zero] at hq
      have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd3)
      rw [hq, one_mul] at this
      omega
    have h1 : s ∣ d := hdi ▸ dvd_pow_self s hi0
    have h2 : s ∣ m / d := hq ▸ dvd_pow_self s hbi
    have := Nat.dvd_gcd h1 h2
    rw [hgcd] at this
    exact hs.one_lt.ne' (Nat.dvd_one.mp this)
  · -- `m = p^k`, so `s = p`
    have hp := primeOK_sound hP hpp
    have hsp : s = p := by
      have hb : b ≠ 0 := by
        intro hb
        rw [hb, pow_zero] at hpow
        rw [hpow] at hpk
        have := Nat.one_lt_pow (by omega : k ≠ 0) hp.one_lt
        omega
      have : s ∣ p ^ k := by rw [hpk, hpow]; exact dvd_pow_self s hb
      exact (Nat.prime_dvd_prime_iff_eq hs hp).mp (hs.dvd_of_dvd_pow this)
    subst hsp
    rcases hfin with (h1 | h2) | h3
    · omega
    · exact h2 hs5
    · exact fchk_sound hP hc steps [t] u v (fun w hw => by
        rcases List.mem_singleton.mp hw with rfl
        exact ⟨ht, htN⟩) h3

theorem tcover_sound {P : List ℕ} (hP : ∀ p ∈ P, p.Prime) {lo hi : ℕ} :
    ∀ (L : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ) × ℕ × ℕ)) (n : ℕ),
      tcover P lo n L hi = true → ∀ x, n ≤ x → x < hi → x % 3 = n % 3 → TGood lo x
  | [], n, h => by
    intro x h1 h2
    simp only [tcover, beq_iff_eq] at h
    omega
  | (t, d, a, m, p, k, steps, u, v) :: L, n, h => by
    intro x h1 h2 h3
    simp only [tcover, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hok⟩, hrest⟩ := h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact tEntry_sound hP hok
    · exact tcover_sound hP L (t + 3) hrest x (by omega) h2 (by omega)

end OddPerfect.TwoExceptionThreeB

#print axioms OddPerfect.TwoExceptionThreeB.primeOK_sound
#print axioms OddPerfect.TwoExceptionThreeB.fchk_sound
#print axioms OddPerfect.TwoExceptionThreeB.scover_sound
#print axioms OddPerfect.TwoExceptionThreeB.eq_pow_of_primeFactors
#print axioms OddPerfect.TwoExceptionThreeB.tEntry_sound
#print axioms OddPerfect.TwoExceptionThreeB.tcover_sound
