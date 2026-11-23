import OddPerfect.CountingZelinsky
import OddPerfect.Phi3Algebra

/-!
# Clayton and Hansen: `99 ω ≤ 37 Ω + 187` for odd perfect numbers

Following Clayton and Hansen (arXiv 2303.11974; INTEGERS 23 (2023), A79), we prove `(99/37) ω(N) - 187/37 ≤ Ω(N)`
for every odd perfect number `N`, and `(51/19) ω(N) - 46/19 ≤ Ω(N)` when `3 ∤ N`.

The primes of `S` (exponent exactly `2`, other than `3`) are sorted by `Ω(p ^ 2 + p + 1)` and
by `p mod 3`. Each inequality of the ledger `ch_ledger` is its own lemma, and the ledger is
closed by `omega`. The paper's rows (5.9) to (5.13) and (5.18), (5.19) are used in a merged
form that gives the same linear program optimum. The paper's Lemma "Semi-linked S22/S31"
is proved here through the direct lemmas `ch_sum_S22_S31` and `ch_small_S22_not_S31`, which do
not use the paper's Factorization2 lemma; the no triple threat proposition of Hansen and
Nielsen is proved here as `no_triple_threat` for odd primes by unique factorization in `ℤ[ω]`,
done by hand on integer pairs.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

/-- Multiplication of `m + n ω` (with `ω ^ 2 + ω + 1 = 0`) on integer pairs. -/
def eisMul (x y : ℤ × ℤ) : ℤ × ℤ := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

/-- The norm `m ^ 2 - m n + n ^ 2` of `m + n ω`. -/
def eisNorm (x : ℤ × ℤ) : ℤ := x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

/-- The norm `eisNorm` is multiplicative. -/
theorem eisNorm_mul (x y : ℤ × ℤ) : eisNorm (eisMul x y) = eisNorm x * eisNorm y := by
  simp only [eisNorm, eisMul]; ring

/-- Division by a prime of the form `c ^ 2 + c + 1`. -/
theorem eis_div {m n c : ℤ} (hq : Prime (c ^ 2 + c + 1)) (hd : c ^ 2 + c + 1 ∣ eisNorm (m, n)) :
    ∃ u : ℤ × ℤ, ((m, n) = eisMul u (c, -1) ∨ (m, n) = eisMul u (c + 1, 1)) ∧
      eisNorm u * (c ^ 2 + c + 1) = eisNorm (m, n) := by
  have key : (m + n * c) * (m - n * (1 + c)) = eisNorm (m, n) - n ^ 2 * (c ^ 2 + c + 1) := by
    simp only [eisNorm]; ring
  have hd' : c ^ 2 + c + 1 ∣ (m + n * c) * (m - n * (1 + c)) := by
    rw [key]; exact dvd_sub hd (dvd_mul_left _ _)
  rcases hq.dvd_or_dvd hd' with ⟨k, hk⟩ | ⟨k, hk⟩
  · have he : (m, n) = eisMul (k * (c + 1) - n, k) (c, -1) := by
      simp only [eisMul, Prod.mk.injEq]; exact ⟨by linear_combination hk, by ring⟩
    refine ⟨_, Or.inl he, ?_⟩
    rw [he, eisNorm_mul]; simp only [eisNorm]; ring
  · have he : (m, n) = eisMul (k * c + n, -k) (c + 1, 1) := by
      simp only [eisMul, Prod.mk.injEq]; exact ⟨by linear_combination hk, by ring⟩
    refine ⟨_, Or.inr he, ?_⟩
    rw [he, eisNorm_mul]; simp only [eisNorm]; ring

/-- The six elements of norm `1`. -/
theorem eis_unit {u : ℤ × ℤ} (h : eisNorm u = 1) :
    u = (1, 0) ∨ u = (-1, 0) ∨ u = (0, 1) ∨ u = (0, -1) ∨ u = (1, 1) ∨ u = (-1, -1) := by
  obtain ⟨s, t⟩ := u
  simp only [eisNorm] at h
  have ht : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * s - t)]
  have ht' : -1 ≤ t ∧ t ≤ 1 := by constructor <;> nlinarith
  have hs : -1 ≤ s ∧ s ≤ 1 := by
    have : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * t - s)]
    constructor <;> nlinarith
  obtain ⟨h1, h2⟩ := ht'
  obtain ⟨h3, h4⟩ := hs
  interval_cases s <;> interval_cases t <;> simp_all

/-- If `(x, -1) = ε · (U, V)` with `ε` a unit, then one of `V`, `U`, `U - V` is `±1`
(Hansen and Nielsen, Lemma 2.1, in the direction used). -/
theorem eis_unit_coeff {ε : ℤ × ℤ} {x U V : ℤ} (hε : eisNorm ε = 1)
    (h : (x, -1) = eisMul ε (U, V)) :
    V = 1 ∨ V = -1 ∨ U = 1 ∨ U = -1 ∨ U - V = 1 ∨ U - V = -1 := by
  rcases eis_unit hε with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eisMul, Prod.mk.injEq] at h <;> omega

private theorem no_sol_prime {x y z : ℕ} (hx : x.Prime) (hy : y.Prime) (hz : z.Prime)
    (h : (x : ℤ) * y = z * (x + y + 1)) : False := by
  have h' : x * y = z * (x + y + 1) := by exact_mod_cast h
  have hzd : z ∣ x * y := ⟨_, h'⟩
  rcases (Nat.Prime.dvd_mul hz).1 hzd with h1 | h1
  · have := (Nat.prime_dvd_prime_iff_eq hz hx).1 h1
    subst this
    have hx0 := hz.pos
    have : y = z + y + 1 := Nat.eq_of_mul_eq_mul_left hx0 h'
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hz hy).1 h1
    subst this
    have hx0 := hz.pos
    have : x = x + z + 1 := Nat.eq_of_mul_eq_mul_left hx0 (by rw [mul_comm, h'])
    omega

private theorem no_sol_mod3 {x y z : ℤ} (hx : x % 3 = 2) (hy : y % 3 = 2) (hz : z % 3 = 2)
    (h : x * y = z * (x + y + 1) + 2) : False := by
  have := congrArg (· % 3) h
  simp [Int.add_emod, Int.mul_emod, hx, hy, hz] at this

/-- No triple threat (Hansen and Nielsen, arXiv 2204.08971, Proposition 4.3, in the form
needed): for odd primes `a, b, c ≡ 2 (mod 3)` with `a ^ 2 + a + 1`, `b ^ 2 + b + 1`,
`c ^ 2 + c + 1` prime, no `x` satisfies
`x ^ 2 + x + 1 = (a ^ 2 + a + 1)(b ^ 2 + b + 1)(c ^ 2 + c + 1)`. Repetitions among `a, b, c`
are allowed. The prime `2` has to be excluded:
`18 ^ 2 + 18 + 1 = 343 = (2 ^ 2 + 2 + 1) ^ 3`. The proof is an explicit descent in `ℤ[ω]` written on integer pairs. -/
theorem no_triple_threat {x a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (ha2 : a ≠ 2) (hb2 : b ≠ 2) (hc2 : c ≠ 2)
    (ha3 : a % 3 = 2) (hb3 : b % 3 = 2) (hc3 : c % 3 = 2) (hA : (phi3 a).Prime)
    (hB : (phi3 b).Prime) (hC : (phi3 c).Prime) (h : phi3 x = phi3 a * phi3 b * phi3 c) :
    False := by
  have ha5 : (5 : ℤ) ≤ a := by
    have := ha.two_le
    exact_mod_cast (show 5 ≤ a by omega)
  have hb5 : (5 : ℤ) ≤ b := by
    have := hb.two_le
    exact_mod_cast (show 5 ≤ b by omega)
  have hc5 : (5 : ℤ) ≤ c := by
    have := hc.two_le
    exact_mod_cast (show 5 ≤ c by omega)
  have ha3' : (a : ℤ) % 3 = 2 := by exact_mod_cast ha3
  have hb3' : (b : ℤ) % 3 = 2 := by exact_mod_cast hb3
  have hc3' : (c : ℤ) % 3 = 2 := by exact_mod_cast hc3
  have cast : ∀ y : ℕ, ((phi3 y : ℕ) : ℤ) = (y : ℤ) ^ 2 + y + 1 := fun y => by
    unfold phi3; push_cast; ring
  have pA : Prime ((a : ℤ) ^ 2 + a + 1) := by rw [← cast]; exact Nat.prime_iff_prime_int.1 hA
  have pB : Prime ((b : ℤ) ^ 2 + b + 1) := by rw [← cast]; exact Nat.prime_iff_prime_int.1 hB
  have pC : Prime ((c : ℤ) ^ 2 + c + 1) := by rw [← cast]; exact Nat.prime_iff_prime_int.1 hC
  have h0 : eisNorm ((x : ℤ), -1) =
      ((a : ℤ) ^ 2 + a + 1) * ((b : ℤ) ^ 2 + b + 1) * ((c : ℤ) ^ 2 + c + 1) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [Nat.cast_mul, cast] at this
    rw [← this]; simp only [eisNorm]; ring
  obtain ⟨u1, hu1, hn1⟩ := eis_div pC ⟨((a : ℤ) ^ 2 + a + 1) * ((b : ℤ) ^ 2 + b + 1), by rw [h0]; ring⟩
  have hn1' : eisNorm u1 = ((a : ℤ) ^ 2 + a + 1) * ((b : ℤ) ^ 2 + b + 1) := by
    have := pC.ne_zero
    apply mul_right_cancel₀ this
    rw [hn1, h0]
  obtain ⟨s1, t1⟩ := u1
  obtain ⟨u2, hu2, hn2⟩ := eis_div pB ⟨(a : ℤ) ^ 2 + a + 1, by rw [hn1']; ring⟩
  have hn2' : eisNorm u2 = ((a : ℤ) ^ 2 + a + 1) := by
    have := pB.ne_zero
    apply mul_right_cancel₀ this
    rw [hn2, hn1', mul_comm]
  obtain ⟨s2, t2⟩ := u2
  obtain ⟨u3, hu3, hn3⟩ := eis_div pA ⟨1, by rw [hn2', mul_one]⟩
  have hn3' : eisNorm u3 = 1 := by
    have := pA.ne_zero
    apply mul_right_cancel₀ this
    rw [hn3, hn2', one_mul]
  have hassoc : ∀ e p q r : ℤ × ℤ,
      eisMul (eisMul (eisMul e p) q) r = eisMul e (eisMul (eisMul p q) r) := by
    intro e p q r; simp only [eisMul, Prod.mk.injEq]; constructor <;> ring
  have a0 : (0 : ℤ) ≤ a := by linarith
  have b0 : (0 : ℤ) ≤ b := by linarith
  have c0 : (0 : ℤ) ≤ c := by linarith
  have m1 := mul_le_mul_of_nonneg_left hb5 a0
  have m2 := mul_le_mul_of_nonneg_right ha5 b0
  have m3 := mul_le_mul_of_nonneg_left hc5 a0
  have m4 := mul_le_mul_of_nonneg_right ha5 c0
  have m5 := mul_le_mul_of_nonneg_left hc5 b0
  have m6 := mul_le_mul_of_nonneg_right hb5 c0
  have m7 := mul_le_mul_of_nonneg_left hc5 (mul_nonneg a0 b0)
  have m8 := mul_le_mul_of_nonneg_left hb5 (mul_nonneg a0 c0)
  have m9 := mul_le_mul_of_nonneg_left ha5 (mul_nonneg b0 c0)
  clear h0 hn1 hn1' hn2 hn2' hn3 pA pB pC cast h hA hB hC
  rcases hu3 with hu3 | hu3 <;> rcases hu2 with hu2 | hu2 <;> rcases hu1 with hu1 | hu1 <;>
  · rw [hu2, hu3, hassoc] at hu1
    have key := eis_unit_coeff hn3' hu1
    simp only [eisMul] at key
    rcases key with e | e | e | e | e | e <;>
    first
    | linarith
    | exact no_sol_prime ha hb hc (by linear_combination e)
    | exact no_sol_prime ha hb hc (by linear_combination -e)
    | exact no_sol_prime ha hc hb (by linear_combination e)
    | exact no_sol_prime ha hc hb (by linear_combination -e)
    | exact no_sol_prime hb hc ha (by linear_combination e)
    | exact no_sol_prime hb hc ha (by linear_combination -e)
    | exact no_sol_mod3 ha3' hb3' hc3' (by linear_combination e)
    | exact no_sol_mod3 ha3' hb3' hc3' (by linear_combination -e)
    | exact no_sol_mod3 ha3' hc3' hb3' (by linear_combination e)
    | exact no_sol_mod3 ha3' hc3' hb3' (by linear_combination -e)
    | exact no_sol_mod3 hb3' hc3' ha3' (by linear_combination e)
    | exact no_sol_mod3 hb3' hc3' ha3' (by linear_combination -e)



/-! ### Algebraic lemmas -/

/-- Clayton and Hansen, Corollary "Uniqueness" (arXiv 2303.11974): the prime `d` determines
`a` in a configuration `a ^ 2 + a + 1 = c d`, `b ^ 2 + b + 1 = 3 c`, `c > d > 3`, `c` prime,
`b ≥ 3`. Indeed `b ^ 2 + 7 = 5 b + 3 d` and `a + 3 = b + d`. -/
theorem ch_uniqueness {a₁ b₁ c₁ a₂ b₂ c₂ d : ℕ} (hc₁ : c₁.Prime) (hc₂ : c₂.Prime)
    (h₁ : phi3 a₁ = c₁ * d) (h₁' : phi3 b₁ = 3 * c₁) (h₂ : phi3 a₂ = c₂ * d)
    (h₂' : phi3 b₂ = 3 * c₂) (hd₁ : d < c₁) (hd₂ : d < c₂) (hd3 : 3 < d) (hb₁ : 3 ≤ b₁)
    (hb₂ : 3 ≤ b₂) : a₁ = a₂ := by
  obtain ⟨hs₁, hr₁⟩ := ch_factorization1 hc₁ h₁ (by rw [h₁', mul_comm]) hd₁ hd3
  obtain ⟨hs₂, hr₂⟩ := ch_factorization1 hc₂ h₂ (by rw [h₂', mul_comm]) hd₂ hd3
  have e₁ : b₁ ^ 2 + 7 = 5 * b₁ + 3 * d := by
    have := h₁'; rw [hs₁] at this; unfold phi3 at this; omega
  have e₂ : b₂ ^ 2 + 7 = 5 * b₂ + 3 * d := by
    have := h₂'; rw [hs₂] at this; unfold phi3 at this; omega
  have hb : b₁ = b₂ := by
    have f₁ : ((b₁ : ℤ)) ^ 2 + 7 = 5 * b₁ + 3 * d := by exact_mod_cast e₁
    have f₂ : ((b₂ : ℤ)) ^ 2 + 7 = 5 * b₂ + 3 * d := by exact_mod_cast e₂
    have hm : ((b₂ : ℤ) - b₁) * (b₂ + b₁ - 5) = 0 := by linear_combination f₂ - f₁
    rcases mul_eq_zero.mp hm with h | h
    · omega
    · omega
  omega

/-- Direct proof of Clayton and Hansen's Lemma "Semi-linked between S22 and S31"
(arXiv 2303.11974), which does not use the paper's Factorization2 lemma.
If `d` is prime, `a ^ 2 + a + 1 = 3 d e` with `e ≤ d`, `c ^ 2 + c + 1 = d g` with `g < d`, and
`a ≠ c` are odd, then `d = a + c + 1`. Two elements of `S_{3,1}` with largest prime `d`
therefore coincide when an element of `S_{2,2}` also has largest prime `d`. -/
theorem ch_sum_S22_S31 {a c d e g : ℕ} (hd : d.Prime) (hA : phi3 a = 3 * d * e)
    (hC : phi3 c = d * g) (hde : e ≤ d) (hgd : g < d) (ha : a % 2 = 1) (hc : c % 2 = 1)
    (hac : a ≠ c) : d = a + c + 1 := by
  have hd0 := hd.pos
  have hcd : c < d := by
    have : c ^ 2 < d ^ 2 := by
      calc c ^ 2 < phi3 c := sq_lt_phi3 c
        _ = d * g := hC
        _ < d * d := Nat.mul_lt_mul_of_pos_left hgd hd0
        _ = d ^ 2 := by ring
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have had : a < 2 * d := by
    have : a ^ 2 < (2 * d) ^ 2 := by
      have := sq_lt_phi3 a
      have : 3 * d * e ≤ 3 * d * d := Nat.mul_le_mul_left _ hde
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hd2 : d % 2 = 1 := by
    rcases hd.eq_two_or_odd with h2 | h2
    · subst h2
      have := (phi3_odd c); rw [hC, Nat.odd_mul] at this
      exact absurd this.1 (by decide)
    · exact h2
  rcases phi3_common_prime_cases hd ⟨3 * e, by rw [hA]; ring⟩ ⟨g, hC⟩ with h | h
  · rcases le_or_gt c a with hle | hlt
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).1 h.symm
      rcases k with _ | _ | k
      · omega
      · omega
      · have : d * (k + 1 + 1) = d * k + 2 * d := by ring
        omega
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).1 h
      rcases k with _ | k
      · omega
      · have : d * (k + 1) = d * k + d := by ring
        omega
  · obtain ⟨k, hk⟩ := h
    rcases k with _ | _ | _ | k
    · omega
    · omega
    · omega
    · have : d * (k + 1 + 1 + 1) = d * k + 3 * d := by ring
      omega

/-- Clayton and Hansen, Lemma "Small factor of S21-S22 pair not S31" (arXiv 2303.11974),
with the case `g = f` included (it occurs: `313 ^ 2 + 313 + 1 = 3 · 181 ^ 2`). Let
`d, f` be primes with `3 < f < d`, `a ^ 2 + a + 1 = d f`, `b ^ 2 + b + 1 = 3 d`, with `a, b`
odd and `a ≡ 2 (mod 3)`. Then no odd `c ≡ 1 (mod 3)` has
`c ^ 2 + c + 1 = 3 f g` with `g ≤ f`. -/
theorem ch_small_S22_not_S31 {a b c d f g : ℕ} (hd : d.Prime) (hf : f.Prime)
    (hA : phi3 a = d * f) (hB : phi3 b = 3 * d) (hC : phi3 c = 3 * f * g) (hfd : f < d)
    (hf3 : 3 < f) (hgf : g ≤ f) (ha2 : a % 2 = 1) (hb2 : b % 2 = 1) (hc2 : c % 2 = 1)
    (ha3 : a % 3 = 2) (hc3 : c % 3 = 1) : False := by
  obtain ⟨hs, hr⟩ := ch_factorization1 hd hA (by rw [hB, mul_comm]) hfd hf3
  have hbsq : b ^ 2 = 3 * a + 2 * b + 2 := by
    have := hB; rw [hs] at this; unfold phi3 at this; omega
  have haf : a < 2 * f := by
    have h1 : (b : ℤ) ^ 2 = 3 * a + 2 * b + 2 := by exact_mod_cast hbsq
    have h2 : (a : ℤ) + 3 = b + f := by exact_mod_cast hr
    have h4 : (b : ℤ) - 4 ≠ 0 := by omega
    have h5 : (0 : ℤ) < ((b : ℤ) - 4) ^ 2 := by positivity
    have : (a : ℤ) < 2 * f := by nlinarith
    exact_mod_cast this
  have hf0 := hf.pos
  have hcf : c < 2 * f := by
    have : c ^ 2 < (2 * f) ^ 2 := by
      have := sq_lt_phi3 c
      have : 3 * f * g ≤ 3 * f * f := Nat.mul_le_mul_left _ hgf
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hfA : f ∣ phi3 a := ⟨d, by rw [hA]; ring⟩
  have hf1 := prime_dvd_phi3_mod_three hf (by omega) hfA
  rcases phi3_common_prime_cases hf hfA ⟨3 * g, by rw [hC]; ring⟩ with h | h
  · rcases le_or_gt c a with hle | hlt
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).1 h.symm
      rcases k with _ | _ | k
      · omega
      · omega
      · have : f * (k + 1 + 1) = f * k + 2 * f := by ring
        omega
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hlt.le).1 h
      rcases k with _ | _ | k
      · omega
      · omega
      · have : f * (k + 1 + 1) = f * k + 2 * f := by ring
        omega
  · obtain ⟨k, hk⟩ := h
    rcases k with _ | _ | _ | _ | k
    · omega
    · omega
    · omega
    · omega
    · have : f * (k + 1 + 1 + 1 + 1) = f * k + 4 * f := by ring
      omega

/-- Two primes `a ≠ b` with `a ^ 2 + a + 1 = 3 d e`, `b ^ 2 + b + 1 = 3 d f`, `e, f ≤ d`,
`d` prime, satisfy `3 d = a + b + 1` (from Clayton and Hansen's Factorization3). -/
theorem ch_sum_S31_S31 {a b d e f : ℕ} (hd : d.Prime) (hA : phi3 a = 3 * d * e)
    (hB : phi3 b = 3 * d * f) (hde : e ≤ d) (hfd : f ≤ d) (hab : a ≠ b) :
    3 * d = a + b + 1 := by
  rcases lt_trichotomy f e with h | h | h
  · exact (ch_factorization3 hd hA hB hde h).1
  · subst h
    exact absurd (phi3_strictMono.injective (hA.trans hB.symm)) hab
  · have := (ch_factorization3 hd hB hA hfd h).1
    omega



/-! ### The classes of Clayton and Hansen -/

section Defs
variable (N : ℕ)

/-- `S`: the prime factors other than `3` with exponent exactly `2`. -/
def chS : Finset ℕ := {p ∈ N.primeFactors | p ≠ 3 ∧ N.factorization p = 2}

/-- `T ∪ {p₀}`: the prime factors other than `3` with exponent different from `2`. -/
def chT : Finset ℕ := {p ∈ N.primeFactors | p ≠ 3 ∧ N.factorization p ≠ 2}

/-- `S₁`: the elements `p` of `S` with `σ(p ^ 2)` prime. -/
def chS1 : Finset ℕ := {p ∈ chS N | Ω (phi3 p) = 1}

/-- `S_{m,1}`: the elements `p ≡ 1 (mod 3)` of `S` with `Ω(σ(p ^ 2)) = m`. -/
def chA (m : ℕ) : Finset ℕ := {p ∈ chS N | Ω (phi3 p) = m ∧ p % 3 = 1}

/-- `S_{m,2}`: the elements `p ≢ 1 (mod 3)` of `S` with `Ω(σ(p ^ 2)) = m`. -/
def chB (m : ℕ) : Finset ℕ := {p ∈ chS N | Ω (phi3 p) = m ∧ p % 3 ≠ 1}

/-- `S_{≥4,1}`. -/
def chA4 : Finset ℕ := {p ∈ chS N | 4 ≤ Ω (phi3 p) ∧ p % 3 = 1}

/-- `S_{≥4,2}`. -/
def chB4 : Finset ℕ := {p ∈ chS N | 4 ≤ Ω (phi3 p) ∧ p % 3 ≠ 1}

/-- The elements of `S` that are `1 (mod 3)`. -/
def chSone : Finset ℕ := {p ∈ chS N | p % 3 = 1}

/-- `f(S₁)`: the primes `σ(p ^ 2)` for `p ∈ S₁`. -/
def chF1 : Finset ℕ := (chS1 N).image phi3

/-- `S₁^S`. -/
def chS1S : Finset ℕ := {p ∈ chS1 N | phi3 p ∈ chS N}

/-- `S₁^T`: `σ(p ^ 2)` is a prime of exponent at least `4`. -/
def chS1T : Finset ℕ := {p ∈ chS1 N | phi3 p ∈ chT N ∧ 4 ≤ N.factorization (phi3 p)}

/-- The elements of `S₃` contributing a prime of `S` outside `f(S₁)`. -/
def chXS : Finset ℕ :=
  {p ∈ chS N | Ω (phi3 p) = 3 ∧ ∃ r ∈ (phi3 p).primeFactors, r ∈ chS N ∧ r ∉ chF1 N}

/-- The elements of `S₃` contributing a prime of `T ∪ {p₀}` outside `f(S₁)`. -/
def chXT : Finset ℕ :=
  {p ∈ chS N | Ω (phi3 p) = 3 ∧ ∃ r ∈ (phi3 p).primeFactors, r ∈ chT N ∧ r ∉ chF1 N}

/-- `g₄ + e₀`: the total exponent of the primes of `T ∪ {p₀}`. -/
def chG : ℕ := ∑ r ∈ chT N, N.factorization r

end Defs

/-- The largest prime factor (`0` for `n ≤ 1`). -/
def bigP (n : ℕ) : ℕ := n.primeFactors.sup id

/-- The linked prime `ℓ_p` of Clayton and Hansen: the largest prime factor of `σ(p ^ 2)`,
except for `p ∈ S_{2,2}` whose largest prime is also contributed by an element of `S_{2,1}`,
where it is the smaller prime factor. -/
def chLink (N p : ℕ) : ℕ :=
  if Ω (phi3 p) = 2 ∧ p % 3 ≠ 1 ∧ ∃ r ∈ chA N 2, phi3 r = 3 * bigP (phi3 p) then
    phi3 p / bigP (phi3 p) else bigP (phi3 p)

/-! ### Basic facts -/

/-- `bigP n` is the largest prime factor of `n`. -/
theorem bigP_eq {n m : ℕ} (hm : m ∈ n.primeFactors) (hle : ∀ r ∈ n.primeFactors, r ≤ m) :
    bigP n = m :=
  le_antisymm (Finset.sup_le hle) (Finset.le_sup (f := id) hm)

/-- Basic facts about a prime of `S`. -/
theorem chS_spec {N p : ℕ} (h : OddPerfect N) (hp : p ∈ chS N) :
    p ∈ N.primeFactors ∧ p.Prime ∧ p ≠ 3 ∧ N.factorization p = 2 ∧ p % 2 = 1 ∧
      p % 3 ≠ 0 ∧ 5 ≤ p := by
  obtain ⟨hpP, h3, h2⟩ := Finset.mem_filter.mp hp
  have hpp := Nat.prime_of_mem_primeFactors hpP
  have hodd : p % 2 = 1 :=
    Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hpP))
  have h0 : p % 3 ≠ 0 := fun h0 => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp
    (Nat.dvd_of_mod_eq_zero h0)).symm
  have := hpp.two_le
  exact ⟨hpP, hpp, h3, h2, hodd, h0, by omega⟩

/-- For `p ∈ S`, the weight of `p` at `r` is the exponent of `r` in `p ^ 2 + p + 1`. -/
theorem chS_sigmaWeight {N p : ℕ} (h : OddPerfect N) (hp : p ∈ chS N) (r : ℕ) :
    sigmaWeight N p r = (phi3 p).factorization r := by
  obtain ⟨-, hpp, -, h2, -⟩ := chS_spec h hp
  unfold sigmaWeight
  rw [h2, sigma_prime_sq hpp]

/-- A prime factor of `σ(p ^ 2)` for `p ∈ S` is an odd prime factor of `N`, and `1 (mod 3)`
unless it is `3`. -/
theorem chS_target {N p r : ℕ} (h : OddPerfect N) (hp : p ∈ chS N) (hr : r.Prime)
    (hd : r ∣ phi3 p) : r ∈ N.primeFactors ∧ r ≠ 2 ∧ (r ≠ 3 → r % 3 = 1) := by
  obtain ⟨-, hpp, -, h2, -⟩ := chS_spec h hp
  have hr2 : r ≠ 2 := by
    rintro rfl
    have := phi3_odd p
    rw [Nat.odd_iff] at this
    omega
  refine ⟨Nat.mem_primeFactors.mpr ⟨hr, OPNStarter.force_prime h.perfect hpp h2 hr hr2
    (by rwa [sigma_prime_sq hpp]), h.ne_zero⟩, hr2, fun h3 => prime_dvd_phi3_mod_three hr h3 hd⟩

/-- A prime factor of `N` other than `3` lies in `S` or in `T ∪ {p₀}`. -/
theorem mem_chS_or_chT {N r : ℕ} (hr : r ∈ N.primeFactors) (h3 : r ≠ 3) :
    r ∈ chS N ∨ r ∈ chT N := by
  by_cases h2 : N.factorization r = 2
  · exact Or.inl (Finset.mem_filter.mpr ⟨hr, h3, h2⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨hr, h3, h2⟩)

/-- For `p ∈ S`, `p ^ 2 + p + 1 ≥ 31`. -/
theorem two_le_phi3_of_chS {N p : ℕ} (h : OddPerfect N) (hp : p ∈ chS N) : 31 ≤ phi3 p := by
  have := (chS_spec h hp).2.2.2.2.2.2
  unfold phi3; nlinarith

/-- For `p ∈ S`, `p ^ 2 + p + 1` has at least one prime factor. -/
theorem cardFactors_phi3_ne_zero {N p : ℕ} (h : OddPerfect N) (hp : p ∈ chS N) :
    Ω (phi3 p) ≠ 0 := by
  have := two_le_phi3_of_chS h hp
  rw [Ne, cardFactors_eq_zero_iff_eq_zero_or_one]
  omega

/-- For `p ∈ S` with `p ≡ 1 (mod 3)`, `σ(p ^ 2)` is not prime. -/
theorem two_le_cardFactors_of_mod_one {N p : ℕ} (h : OddPerfect N) (hp : p ∈ chS N)
    (h1 : p % 3 = 1) : 2 ≤ Ω (phi3 p) := by
  have h0 := cardFactors_phi3_ne_zero h hp
  by_contra hlt
  have hpr : (phi3 p).Prime := cardFactors_eq_one_iff_prime.mp (by omega)
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).mp ((three_dvd_phi3_iff p).2 h1)
  have := two_le_phi3_of_chS h hp
  omega

/-- A number with `Ω = 2` is a product of two primes. -/
theorem exists_two_of_cardFactors {n : ℕ} (h : Ω n = 2) :
    ∃ x y, x.Prime ∧ y.Prime ∧ n = x * y := by
  rw [cardFactors_apply, List.length_eq_two] at h
  obtain ⟨x, y, hxy⟩ := h
  have hn : n ≠ 0 := by rintro rfl; simp at hxy
  have hp := Nat.prod_primeFactorsList hn
  rw [hxy] at hp
  refine ⟨x, y, Nat.prime_of_mem_primeFactorsList (by rw [hxy]; simp),
    Nat.prime_of_mem_primeFactorsList (by rw [hxy]; simp), ?_⟩
  simpa using hp.symm

/-- A number with `Ω = 3` is a product of three primes. -/
theorem exists_three_of_cardFactors {n : ℕ} (h : Ω n = 3) :
    ∃ x y z, x.Prime ∧ y.Prime ∧ z.Prime ∧ n = x * y * z := by
  rw [cardFactors_apply, List.length_eq_three] at h
  obtain ⟨x, y, z, hxy⟩ := h
  have hn : n ≠ 0 := by rintro rfl; simp at hxy
  have hp := Nat.prod_primeFactorsList hn
  rw [hxy] at hp
  refine ⟨x, y, z, Nat.prime_of_mem_primeFactorsList (by rw [hxy]; simp),
    Nat.prime_of_mem_primeFactorsList (by rw [hxy]; simp),
    Nat.prime_of_mem_primeFactorsList (by rw [hxy]; simp), ?_⟩
  simp at hp
  rw [← hp, mul_assoc]

/-- A prime dividing a product of two primes is one of them. -/
theorem prime_eq_of_dvd_mul_prime {x y r : ℕ} (hx : x.Prime) (hy : y.Prime) (hr : r.Prime)
    (hd : r ∣ x * y) : r = x ∨ r = y := by
  rcases (Nat.Prime.dvd_mul hr).1 hd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr hx).1 h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hy).1 h)

/-! ### Shapes of `σ(p ^ 2)` in each class -/

/-- The shape of an element of `S₁`. -/
theorem shape_S1 {N p : ℕ} (h : OddPerfect N) (hp : p ∈ chS1 N) :
    (phi3 p).Prime ∧ p % 3 = 2 ∧ bigP (phi3 p) = phi3 p := by
  obtain ⟨hpS, h1⟩ := Finset.mem_filter.mp hp
  have hpr : (phi3 p).Prime := cardFactors_eq_one_iff_prime.mp h1
  obtain ⟨-, -, -, -, -, h0, -⟩ := chS_spec h hpS
  have hn1 : p % 3 ≠ 1 := fun h' => by
    have := two_le_cardFactors_of_mod_one h hpS h'; omega
  refine ⟨hpr, by omega, bigP_eq (Nat.mem_primeFactors.mpr ⟨hpr, dvd_rfl, hpr.ne_zero⟩) ?_⟩
  intro r hr
  rw [Nat.Prime.primeFactors hpr, Finset.mem_singleton] at hr
  omega

/-- The shape of an element of `S_{2,1}`. -/
theorem shape_S21 {N p : ℕ} (hp : p ∈ chA N 2) :
    ∃ q, q.Prime ∧ 7 ≤ q ∧ phi3 p = 3 * q ∧ bigP (phi3 p) = q := by
  obtain ⟨hpS, h2, h1⟩ := Finset.mem_filter.mp hp
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_of_cardFactors h2
  have h3 : 3 ∣ x * y := hxy ▸ (three_dvd_phi3_iff p).2 h1
  have key : ∃ q, q.Prime ∧ phi3 p = 3 * q := by
    rcases prime_eq_of_dvd_mul_prime hx hy Nat.prime_three h3 with h | h
    · exact ⟨y, hy, by rw [hxy, ← h]⟩
    · exact ⟨x, hx, by rw [hxy, ← h, mul_comm]⟩
  obtain ⟨q, hq, hpq⟩ := key
  have hq3 : q ≠ 3 := by
    rintro rfl; exact not_nine_dvd_phi3 p ⟨1, by rw [hpq]⟩
  have hqd : q ∣ phi3 p := ⟨3, by rw [hpq, mul_comm]⟩
  have hq7 := seven_le_of_prime_dvd_phi3 hq hq3 hqd
  refine ⟨q, hq, hq7, hpq, bigP_eq (Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩) ?_⟩
  intro r hr
  obtain ⟨hr, hrd, -⟩ := Nat.mem_primeFactors.mp hr
  rw [hpq] at hrd
  rcases prime_eq_of_dvd_mul_prime Nat.prime_three hq hr hrd with h | h <;> omega

/-- The shape of an element of `S_{2,2}`. -/
theorem shape_S22 {N p : ℕ} (h : OddPerfect N) (hp : p ∈ chB N 2) :
    ∃ x y, x.Prime ∧ y.Prime ∧ 7 ≤ x ∧ x < y ∧ phi3 p = x * y ∧ bigP (phi3 p) = y ∧
      p % 3 = 2 := by
  obtain ⟨hpS, h2, h1⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, -, -, -, -, h0, h5⟩ := chS_spec h hpS
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_of_cardFactors h2
  have hn3 : ¬ 3 ∣ phi3 p := fun h3 => h1 ((three_dvd_phi3_iff p).1 h3)
  have hxd : x ∣ phi3 p := ⟨y, hxy⟩
  have hyd : y ∣ phi3 p := ⟨x, by rw [hxy, mul_comm]⟩
  have hx3 : x ≠ 3 := by rintro rfl; exact hn3 hxd
  have hy3 : y ≠ 3 := by rintro rfl; exact hn3 hyd
  have hx7 := seven_le_of_prime_dvd_phi3 hx hx3 hxd
  have hy7 := seven_le_of_prime_dvd_phi3 hy hy3 hyd
  have hne : x ≠ y := by
    rintro rfl
    exact not_isSquare_phi3 (show 1 ≤ p by omega) ⟨x, hxy⟩
  have hmem : ∀ r ∈ (phi3 p).primeFactors, r = x ∨ r = y := by
    intro r hr
    obtain ⟨hr, hrd, -⟩ := Nat.mem_primeFactors.mp hr
    rw [hxy] at hrd
    exact prime_eq_of_dvd_mul_prime hx hy hr hrd
  have hpos : phi3 p ≠ 0 := by unfold phi3; omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨x, y, hx, hy, hx7, hlt, hxy, bigP_eq (Nat.mem_primeFactors.mpr ⟨hy, hyd, hpos⟩)
      fun r hr => ?_, by omega⟩
    rcases hmem r hr with rfl | rfl <;> omega
  · refine ⟨y, x, hy, hx, hy7, hlt, by rw [hxy, mul_comm],
      bigP_eq (Nat.mem_primeFactors.mpr ⟨hx, hxd, hpos⟩) fun r hr => ?_, by omega⟩
    rcases hmem r hr with rfl | rfl <;> omega

/-- The shape of an element of `S_{3,1}`. -/
theorem shape_S31 {N p : ℕ} (hp : p ∈ chA N 3) :
    ∃ d e, d.Prime ∧ e.Prime ∧ 7 ≤ e ∧ e ≤ d ∧ phi3 p = 3 * d * e ∧ bigP (phi3 p) = d := by
  obtain ⟨hpS, h2, h1⟩ := Finset.mem_filter.mp hp
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := exists_three_of_cardFactors h2
  have h3 : 3 ∣ x * y * z := hxyz ▸ (three_dvd_phi3_iff p).2 h1
  have key : ∃ u v, u.Prime ∧ v.Prime ∧ phi3 p = 3 * u * v := by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
    · rcases prime_eq_of_dvd_mul_prime hx hy Nat.prime_three h with h | h
      · exact ⟨y, z, hy, hz, by rw [hxyz, ← h]⟩
      · exact ⟨x, z, hx, hz, by rw [hxyz, ← h]; ring⟩
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hz).1 h
      exact ⟨x, y, hx, hy, by rw [hxyz, ← this]; ring⟩
  obtain ⟨u, v, hu, hv, huv⟩ := key
  have hud : u ∣ phi3 p := ⟨3 * v, by rw [huv]; ring⟩
  have hvd : v ∣ phi3 p := ⟨3 * u, by rw [huv]; ring⟩
  have hu3 : u ≠ 3 := by rintro rfl; exact not_nine_dvd_phi3 p ⟨v, by omega⟩
  have hv3 : v ≠ 3 := by rintro rfl; exact not_nine_dvd_phi3 p ⟨u, by omega⟩
  have hu7 := seven_le_of_prime_dvd_phi3 hu hu3 hud
  have hv7 := seven_le_of_prime_dvd_phi3 hv hv3 hvd
  have hmem : ∀ r ∈ (phi3 p).primeFactors, r = 3 ∨ r = u ∨ r = v := by
    intro r hr
    obtain ⟨hr, hrd, -⟩ := Nat.mem_primeFactors.mp hr
    rw [huv] at hrd
    rcases (Nat.Prime.dvd_mul hr).1 hrd with h | h
    · rcases prime_eq_of_dvd_mul_prime Nat.prime_three hu hr h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr hv).1 h))
  have hpos : phi3 p ≠ 0 := by unfold phi3; omega
  rcases le_total v u with hle | hle
  · refine ⟨u, v, hu, hv, hv7, hle, huv, bigP_eq (Nat.mem_primeFactors.mpr ⟨hu, hud, hpos⟩)
      fun r hr => ?_⟩
    rcases hmem r hr with rfl | rfl | rfl <;> omega
  · refine ⟨v, u, hv, hu, hu7, hle, by rw [huv]; ring,
      bigP_eq (Nat.mem_primeFactors.mpr ⟨hv, hvd, hpos⟩) fun r hr => ?_⟩
    rcases hmem r hr with rfl | rfl | rfl <;> omega


/-! ### Rows of the ledger: bookkeeping -/

/-- `ω = |S| + |T ∪ {p₀}| + [3 ∣ N]` and `Ω = 2 |S| + (g₄ + e₀) + f₃` (Clayton and Hansen
(5.1), (5.2)). -/
theorem ch_omega_Omega {N : ℕ} (h : OddPerfect N) :
    N.primeFactors.card = (chS N).card + (chT N).card + (if 3 ∣ N then 1 else 0) ∧
      ∑ p ∈ N.primeFactors, N.factorization p =
        2 * (chS N).card + chG N + N.factorization 3 := by
  classical
  set P := N.primeFactors
  have eS : chS N = (P.erase 3).filter (fun p => N.factorization p = 2) := by
    ext p; simp [chS, P, Finset.mem_erase, and_assoc, and_comm, and_left_comm]
  have eT : chT N = (P.erase 3).filter (fun p => ¬ N.factorization p = 2) := by
    ext p; simp [chT, P, Finset.mem_erase, and_assoc, and_comm, and_left_comm]
  have hc := Finset.card_filter_add_card_filter_not
    (s := P.erase 3) (fun p => N.factorization p = 2)
  have hs := Finset.sum_filter_add_sum_filter_not (P.erase 3)
    (fun p => N.factorization p = 2) (fun p => N.factorization p)
  rw [← eS, ← eT] at hc hs
  have hS2 : ∑ p ∈ chS N, N.factorization p = 2 * (chS N).card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp => by simp [(Finset.mem_filter.mp hp).2.2]
  have h3P : 3 ∈ P ↔ 3 ∣ N := by
    simp only [P, Nat.mem_primeFactors]
    exact ⟨fun h => h.2.1, fun h3 => ⟨Nat.prime_three, h3, h.ne_zero⟩⟩
  unfold chG
  by_cases h3 : 3 ∣ N
  · have hm := h3P.mpr h3
    have e1 := Finset.card_erase_add_one hm
    have e2 := Finset.sum_erase_add P (fun p => N.factorization p) hm
    rw [if_pos h3]
    constructor <;> omega
  · have hm : 3 ∉ P := fun hm => h3 (h3P.mp hm)
    rw [Finset.erase_eq_of_notMem hm] at hc hs
    rw [if_neg h3, Nat.factorization_eq_zero_of_not_dvd h3]
    constructor <;> omega

/-- Clayton and Hansen (5.3) and (5.4): `4 |T| ≤ g₄` and `1 ≤ e₀`, combined as
`4 |T ∪ {p₀}| ≤ g₄ + e₀ + 3`. -/
theorem ch_four_mul_card_T {N : ℕ} (h : OddPerfect N) : 4 * (chT N).card ≤ chG N + 3 := by
  classical
  obtain ⟨q, hq, hqN, -, -, hev⟩ := exists_special_prime h
  have key : ∀ r ∈ chT N, 4 ≤ N.factorization r + 3 * (if r = q then 1 else 0) := by
    intro r hr
    obtain ⟨hrP, -, h2⟩ := Finset.mem_filter.mp hr
    have hrp := Nat.prime_of_mem_primeFactors hrP
    have h1 := hrp.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hrP)
    by_cases hrq : r = q
    · rw [if_pos hrq]; omega
    · rw [if_neg hrq]
      obtain ⟨j, hj⟩ := hev r hrp hrq
      omega
  have hs := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' (chT N) q (fun _ => 1)] at hs
  simp only [Finset.sum_const, smul_eq_mul] at hs
  unfold chG
  have : (if q ∈ chT N then 1 else 0) ≤ 1 := by split_ifs <;> omega
  omega

/-- Clayton and Hansen (5.5) to (5.8): the partition of `S` into the classes. -/
theorem ch_card_S {N : ℕ} (h : OddPerfect N) :
    (chS N).card = (chS1 N).card + (chA N 2).card + (chB N 2).card + (chA N 3).card +
      (chB N 3).card + (chA4 N).card + (chB4 N).card := by
  classical
  have key : ∀ p ∈ chS N, 1 = (if Ω (phi3 p) = 1 then 1 else 0) +
      (if Ω (phi3 p) = 2 ∧ p % 3 = 1 then 1 else 0) +
      (if Ω (phi3 p) = 2 ∧ p % 3 ≠ 1 then 1 else 0) +
      (if Ω (phi3 p) = 3 ∧ p % 3 = 1 then 1 else 0) +
      (if Ω (phi3 p) = 3 ∧ p % 3 ≠ 1 then 1 else 0) +
      (if 4 ≤ Ω (phi3 p) ∧ p % 3 = 1 then 1 else 0) +
      (if 4 ≤ Ω (phi3 p) ∧ p % 3 ≠ 1 then 1 else 0) := by
    intro p hp
    have := cardFactors_phi3_ne_zero h hp
    split_ifs <;> omega
  rw [Finset.card_eq_sum_ones, Finset.sum_congr rfl key]
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
  rfl

/-- The elements of `S` that are `1 (mod 3)` are exactly `S_{2,1} ∪ S_{3,1} ∪ S_{≥4,1}`. -/
theorem ch_card_Sone {N : ℕ} (h : OddPerfect N) :
    (chSone N).card = (chA N 2).card + (chA N 3).card + (chA4 N).card := by
  classical
  have key : ∀ p ∈ chSone N, 1 = (if Ω (phi3 p) = 2 then 1 else 0) +
      (if Ω (phi3 p) = 3 then 1 else 0) + (if 4 ≤ Ω (phi3 p) then 1 else 0) := by
    intro p hp
    obtain ⟨hpS, h1⟩ := Finset.mem_filter.mp hp
    have := two_le_cardFactors_of_mod_one h hpS h1
    split_ifs <;> omega
  rw [Finset.card_eq_sum_ones, Finset.sum_congr rfl key]
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
  have e : ∀ (P : ℕ → Prop) [DecidablePred P],
      ((chSone N).filter P).card = ((chS N).filter (fun p => P p ∧ p % 3 = 1)).card := by
    intro P _
    congr 1
    ext p; simp [chSone, and_comm, and_left_comm]
  rw [e, e, e]
  rfl

/-- Clayton and Hansen (5.14): each element of `S_{2,1} ∪ S_{3,1} ∪ S_{≥4,1}` contributes one
factor `3`. -/
theorem ch_card_Sone_le {N : ℕ} (h : OddPerfect N) :
    (chA N 2).card + (chA N 3).card + (chA4 N).card ≤ N.factorization 3 := by
  rw [← ch_card_Sone h]
  refine le_trans (Finset.card_le_card fun p hp => ?_) (card_sq_mod_three_eq_one_le h)
  obtain ⟨hpS, h1⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpP, -, h2⟩ := Finset.mem_filter.mp hpS
  exact Finset.mem_filter.mpr ⟨hpP, h2, h1⟩

/-- Conservation: senders in `A` deliver into the odd primes `R` at most their exponents. -/
theorem recv_le {N : ℕ} (h : OddPerfect N) (A R : Finset ℕ) (hA : A ⊆ N.primeFactors)
    (hR : ∀ r ∈ R, r.Prime ∧ r ≠ 2) :
    ∑ p ∈ A, ∑ r ∈ R, sigmaWeight N p r ≤ ∑ r ∈ R, N.factorization r := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun r hr => ?_
  rw [← sigmaWeight_sum_eq h.perfect (hR r hr).1 (hR r hr).2]
  exact Finset.sum_le_sum_of_subset hA

/-- `S` consists of prime factors of `N`. -/
theorem chS_sub {N : ℕ} : chS N ⊆ N.primeFactors := Finset.filter_subset _ _

/-- The primes of `T ∪ {p₀}` are odd primes. -/
theorem chT_odd {N : ℕ} (h : OddPerfect N) : ∀ r ∈ chT N, r.Prime ∧ r ≠ 2 := by
  intro r hr
  obtain ⟨hrP, -, -⟩ := Finset.mem_filter.mp hr
  refine ⟨Nat.prime_of_mem_primeFactors hrP, ?_⟩
  rintro rfl
  exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hrP)

/-- The primes of `S` are odd primes. -/
theorem chS_odd {N : ℕ} (h : OddPerfect N) : ∀ r ∈ chS N, r.Prime ∧ r ≠ 2 := by
  intro r hr
  obtain ⟨hrP, -, -⟩ := Finset.mem_filter.mp hr
  refine ⟨Nat.prime_of_mem_primeFactors hrP, ?_⟩
  rintro rfl
  exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hrP)

/-- Clayton and Hansen (5.15): counting the primes other than `3` contributed by `S`. -/
theorem ch_contributed_by_S {N : ℕ} (h : OddPerfect N) :
    (chS1 N).card + 2 * (chB N 2).card + 3 * (chB N 3).card + (chA4 N).card +
      4 * (chB4 N).card ≤ chG N + (chA N 2).card := by
  classical
  set R := chSone N ∪ chT N
  have hdisj : Disjoint (chSone N) (chT N) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2.2
  have hR : ∀ r ∈ R, r.Prime ∧ r ≠ 2 := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact chS_odd h r (Finset.mem_filter.mp hr).1
    · exact chT_odd h r hr
  have hcap : ∑ r ∈ R, N.factorization r = 2 * (chSone N).card + chG N := by
    rw [Finset.sum_union hdisj]
    unfold chG
    congr 1
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r hr => by
      simp [(Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.2]
  -- the primes other than `3` of `σ(p ^ 2)`, with multiplicity
  have hp : ∀ p ∈ chS N, Ω (phi3 p) ≤ (if p % 3 = 1 then 1 else 0) +
      ∑ r ∈ R, sigmaWeight N p r := by
    intro p hp
    have hpos : phi3 p ≠ 0 := by unfold phi3; omega
    rw [cardFactors_eq_sum_primeFactors]
    have h3 : (phi3 p).factorization 3 = if p % 3 = 1 then 1 else 0 := factorization_three_phi3 p
    have hsplit : ∑ r ∈ (phi3 p).primeFactors, (phi3 p).factorization r ≤
        (phi3 p).factorization 3 +
          ∑ r ∈ (phi3 p).primeFactors.erase 3, (phi3 p).factorization r := by
      by_cases h3m : 3 ∈ (phi3 p).primeFactors
      · rw [Finset.add_sum_erase _ _ h3m]
      · rw [Finset.erase_eq_of_notMem h3m]; omega
    have hsub : ∑ r ∈ (phi3 p).primeFactors.erase 3, (phi3 p).factorization r ≤
        ∑ r ∈ R, sigmaWeight N p r := by
      rw [Finset.sum_congr rfl fun r _ => chS_sigmaWeight h hp r]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => ?_) (fun _ _ _ => Nat.zero_le _)
      obtain ⟨hr3, hr⟩ := Finset.mem_erase.mp hr
      obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.mp hr
      obtain ⟨hrN, -, hr1⟩ := chS_target h hp hrp hrd
      rcases mem_chS_or_chT hrN hr3 with hS | hT
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS, hr1 hr3⟩)
      · exact Finset.mem_union_right _ hT
    omega
  have hsum := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at hsum
  have hrec := recv_le h (chS N) R chS_sub hR
  -- pointwise lower bounds
  have hlow : ∀ p ∈ chS N, (if Ω (phi3 p) = 1 then 1 else 0) +
      (if Ω (phi3 p) = 2 ∧ p % 3 = 1 then 1 else 0) +
      2 * (if Ω (phi3 p) = 2 ∧ p % 3 ≠ 1 then 1 else 0) +
      2 * (if Ω (phi3 p) = 3 ∧ p % 3 = 1 then 1 else 0) +
      3 * (if Ω (phi3 p) = 3 ∧ p % 3 ≠ 1 then 1 else 0) +
      3 * (if 4 ≤ Ω (phi3 p) ∧ p % 3 = 1 then 1 else 0) +
      4 * (if 4 ≤ Ω (phi3 p) ∧ p % 3 ≠ 1 then 1 else 0) + (if p % 3 = 1 then 1 else 0) ≤
      Ω (phi3 p) := by
    intro p hp
    have := cardFactors_phi3_ne_zero h hp
    have h1 : p % 3 = 1 → 2 ≤ Ω (phi3 p) := two_le_cardFactors_of_mod_one h hp
    split_ifs <;> omega
  have hl := Finset.sum_le_sum hlow
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id] at hl
  have hSone : ((chS N).filter (fun p => p % 3 = 1)).card = (chSone N).card := rfl
  have hc := ch_card_Sone h
  change (chS1 N).card + (chA N 2).card + 2 * (chB N 2).card + 2 * (chA N 3).card +
    3 * (chB N 3).card + 3 * (chA4 N).card + 4 * (chB4 N).card + (chSone N).card ≤ _ at hl
  rw [hSone] at hsum
  omega


/-! ### Rows of the ledger: the primes contributed by `S₁` and by `S₃` -/

/-- `phi3` is injective on every finite set. -/
theorem phi3_injOn (s : Finset ℕ) : Set.InjOn phi3 (s : Set ℕ) :=
  fun _ _ _ _ h => phi3_strictMono.injective h

/-- Clayton and Hansen (5.9) and (5.13): `|S₁| ≤ |S₁^S| + |S₁^T| + 1`, the `1` accounting for
at most one element of `S₁` contributing the special prime. -/
theorem ch_card_S1_le {N : ℕ} (h : OddPerfect N) :
    (chS1 N).card ≤ (chS1S N).card + (chS1T N).card + 1 := by
  classical
  obtain ⟨q, hq, hqN, -, -, hev⟩ := exists_special_prime h
  set Z := (chS1 N).filter (fun p => phi3 p = q)
  have hZ : Z.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    exact phi3_strictMono.injective ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have hsub : chS1 N ⊆ chS1S N ∪ chS1T N ∪ Z := by
    intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    obtain ⟨hpr, -, -⟩ := shape_S1 h hp
    obtain ⟨hN, -, -⟩ := chS_target h hpS hpr dvd_rfl
    have h3 : phi3 p ≠ 3 := by have := two_le_phi3_of_chS h hpS; omega
    rcases mem_chS_or_chT hN h3 with hS | hT
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hS⟩))
    · by_cases hpq : phi3 p = q
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hpq⟩)
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hp, hT, ?_⟩))
        obtain ⟨hTP, -, h2⟩ := Finset.mem_filter.mp hT
        obtain ⟨j, hj⟩ := hev _ hpr hpq
        have := hpr.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hTP)
        omega
  have c1 := Finset.card_le_card hsub
  have c2 := Finset.card_union_le (chS1S N ∪ chS1T N) Z
  have c3 := Finset.card_union_le (chS1S N) (chS1T N)
  omega

/-- `|S₁^S|` primes of `S` (all `1 (mod 3)`) lie in `f(S₁)`. -/
theorem card_S1S_le {N : ℕ} (h : OddPerfect N) :
    (chS1S N).card ≤ (chSone N ∩ chF1 N).card := by
  refine Finset.card_le_card_of_injOn phi3 (fun p hp => ?_) (phi3_injOn _)
  obtain ⟨hp1, hS⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, h2, -⟩ := shape_S1 h hp1
  refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hS, ?_⟩, Finset.mem_image_of_mem _ hp1⟩
  have := prime_dvd_phi3_mod_three (shape_S1 h hp1).1
    (by have := two_le_phi3_of_chS h (Finset.mem_filter.mp hp1).1; omega) (dvd_refl (phi3 p))
  exact this

/-- Clayton and Hansen (5.18), in merged form: the primes of `S` that are `1 (mod 3)` absorb
two units each; `f(S₁) ∩ S` uses `2 |S₁^S|` of them and each element of `X_S` needs one more. -/
theorem ch_contributed_to_S {N : ℕ} (h : OddPerfect N) :
    2 * (chS1S N).card + (chXS N).card ≤ 2 * (chSone N).card := by
  classical
  set R := chSone N \ chF1 N
  have hR : ∀ r ∈ R, r.Prime ∧ r ≠ 2 :=
    fun r hr => chS_odd h r (Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1).1
  have hone : ∀ p ∈ chXS N, 1 ≤ ∑ r ∈ R, sigmaWeight N p r := by
    intro p hp
    obtain ⟨hpS, -, r, hr, hrS, hrF⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.mp hr
    have hr3 : r ≠ 3 := (Finset.mem_filter.mp hrS).2.1
    have hr1 := (chS_target h hpS hrp hrd).2.2 hr3
    have hrR : r ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hrS, hr1⟩, hrF⟩
    have hw : 1 ≤ sigmaWeight N p r := by
      rw [chS_sigmaWeight h hpS]
      exact (hrp.dvd_iff_one_le_factorization (by unfold phi3; omega)).mp hrd
    exact hw.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hrR)
  have hXS : chXS N ⊆ N.primeFactors := fun p hp => chS_sub (Finset.mem_filter.mp hp).1
  have h1 : (chXS N).card ≤ ∑ r ∈ R, N.factorization r := by
    calc (chXS N).card = ∑ p ∈ chXS N, 1 := Finset.card_eq_sum_ones _
      _ ≤ ∑ p ∈ chXS N, ∑ r ∈ R, sigmaWeight N p r := Finset.sum_le_sum hone
      _ ≤ _ := recv_le h _ R hXS hR
  have h2 : ∑ r ∈ R, N.factorization r = 2 * R.card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r hr => by
      simp [(Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hr).1).1).2.2]
  have h3 : R.card + (chSone N ∩ chF1 N).card = (chSone N).card := by
    rw [Finset.card_sdiff_add_card_inter]
  have h4 := card_S1S_le h
  omega

/-- Clayton and Hansen (5.19), in merged form: `4 |S₁^T| + |X_T| ≤ g₄ + e₀`. -/
theorem ch_contributed_to_T {N : ℕ} (h : OddPerfect N) :
    4 * (chS1T N).card + (chXT N).card ≤ chG N := by
  classical
  set R := chT N \ chF1 N
  have hR : ∀ r ∈ R, r.Prime ∧ r ≠ 2 := fun r hr => chT_odd h r (Finset.mem_sdiff.mp hr).1
  have hone : ∀ p ∈ chXT N, 1 ≤ ∑ r ∈ R, sigmaWeight N p r := by
    intro p hp
    obtain ⟨hpS, -, r, hr, hrT, hrF⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.mp hr
    have hrR : r ∈ R := Finset.mem_sdiff.mpr ⟨hrT, hrF⟩
    have hw : 1 ≤ sigmaWeight N p r := by
      rw [chS_sigmaWeight h hpS]
      exact (hrp.dvd_iff_one_le_factorization (by unfold phi3; omega)).mp hrd
    exact hw.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hrR)
  have hXT : chXT N ⊆ N.primeFactors := fun p hp => chS_sub (Finset.mem_filter.mp hp).1
  have h1 : (chXT N).card ≤ ∑ r ∈ R, N.factorization r := by
    calc (chXT N).card = ∑ p ∈ chXT N, 1 := Finset.card_eq_sum_ones _
      _ ≤ ∑ p ∈ chXT N, ∑ r ∈ R, sigmaWeight N p r := Finset.sum_le_sum hone
      _ ≤ _ := recv_le h _ R hXT hR
  have h2 : 4 * (chS1T N).card ≤ ∑ r ∈ chT N ∩ chF1 N, N.factorization r := by
    have hc : (chS1T N).card ≤ ((chT N ∩ chF1 N).filter
        (fun r => 4 ≤ N.factorization r)).card := by
      refine Finset.card_le_card_of_injOn phi3 (fun p hp => ?_) (phi3_injOn _)
      obtain ⟨hp1, hT, h4⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hT, Finset.mem_image_of_mem _ hp1⟩, h4⟩
    have : 4 * ((chT N ∩ chF1 N).filter (fun r => 4 ≤ N.factorization r)).card ≤
        ∑ r ∈ chT N ∩ chF1 N, N.factorization r := by
      calc 4 * ((chT N ∩ chF1 N).filter (fun r => 4 ≤ N.factorization r)).card
          = ∑ r ∈ (chT N ∩ chF1 N).filter (fun r => 4 ≤ N.factorization r), 4 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ r ∈ (chT N ∩ chF1 N).filter (fun r => 4 ≤ N.factorization r),
            N.factorization r := Finset.sum_le_sum fun r hr => (Finset.mem_filter.mp hr).2
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    omega
  have h3 : ∑ r ∈ R, N.factorization r + ∑ r ∈ chT N ∩ chF1 N, N.factorization r = chG N := by
    unfold chG
    rw [add_comm, Finset.sum_inter_add_sum_sdiff]
  omega

/-- Every element of `S₃` contributes a prime other than `3` outside `f(S₁)`: for `S_{3,1}`
by Clayton and Hansen's Lemma "Unique between S1 and S31" applied to the largest prime,
for `S_{3,2}` by the no triple threat theorem. Hence `|S₃| ≤ |X_S| + |X_T|`, the merged form
of Clayton and Hansen (5.10) to (5.12). -/
theorem ch_card_S3_le {N : ℕ} (h : OddPerfect N) :
    (chA N 3).card + (chB N 3).card ≤ (chXS N).card + (chXT N).card := by
  classical
  have hfree : ∀ p ∈ chS N, Ω (phi3 p) = 3 →
      ∃ r ∈ (phi3 p).primeFactors, r ≠ 3 ∧ r ∉ chF1 N := by
    intro p hp hΩ
    obtain ⟨-, hpp, -, -, hp2, h0, hp5⟩ := chS_spec h hp
    have hpos : phi3 p ≠ 0 := by unfold phi3; omega
    by_cases h1 : p % 3 = 1
    · obtain ⟨d, e, hd, he, he7, hed, hde, -⟩ :=
        shape_S31 (Finset.mem_filter.mpr ⟨hp, hΩ, h1⟩)
      refine ⟨d, Nat.mem_primeFactors.mpr ⟨hd, ⟨3 * e, by rw [hde]; ring⟩, hpos⟩,
        by omega, fun hdF => ?_⟩
      obtain ⟨b, hb, hbd⟩ := Finset.mem_image.mp hdF
      exact ch_unique_S1_S31 hpp (chS_spec h (Finset.mem_filter.mp hb).1).2.1 hd
        (by omega) hde hbd hed
    · obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := exists_three_of_cardFactors hΩ
      have hn3 : ¬ 3 ∣ phi3 p := fun h3 => h1 ((three_dvd_phi3_iff p).1 h3)
      have hxd : x ∣ phi3 p := ⟨y * z, by rw [hxyz]; ring⟩
      have hyd : y ∣ phi3 p := ⟨x * z, by rw [hxyz]; ring⟩
      have hzd : z ∣ phi3 p := ⟨x * y, by rw [hxyz]; ring⟩
      have mem : ∀ {r}, r.Prime → r ∣ phi3 p → r ∈ (phi3 p).primeFactors :=
        fun hr hrd => Nat.mem_primeFactors.mpr ⟨hr, hrd, hpos⟩
      have n3 : ∀ {r}, r ∣ phi3 p → r ≠ 3 := fun hrd h3 => hn3 (h3 ▸ hrd)
      by_contra hall
      push Not at hall
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hall x (mem hx hxd) (n3 hxd))
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (hall y (mem hy hyd) (n3 hyd))
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (hall z (mem hz hzd) (n3 hzd))
      obtain ⟨-, ha2, -⟩ := shape_S1 h ha
      obtain ⟨-, hb2, -⟩ := shape_S1 h hb
      obtain ⟨-, hc2, -⟩ := shape_S1 h hc
      obtain ⟨-, hap, -, -, hao, -⟩ := chS_spec h (Finset.mem_filter.mp ha).1
      obtain ⟨-, hbp, -, -, hbo, -⟩ := chS_spec h (Finset.mem_filter.mp hb).1
      obtain ⟨-, hcp, -, -, hco, -⟩ := chS_spec h (Finset.mem_filter.mp hc).1
      exact no_triple_threat hap hbp hcp (by omega) (by omega) (by omega) ha2 hb2 hc2 hx hy hz
        hxyz
  have hsub : chA N 3 ∪ chB N 3 ⊆ chXS N ∪ chXT N := by
    intro p hp
    have hpS : p ∈ chS N ∧ Ω (phi3 p) = 3 := by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
      · exact ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
    obtain ⟨r, hr, hr3, hrF⟩ := hfree p hpS.1 hpS.2
    obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.mp hr
    obtain ⟨hrN, -, -⟩ := chS_target h hpS.1 hrp hrd
    rcases mem_chS_or_chT hrN hr3 with hS | hT
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpS.1, hpS.2, r, hr, hS, hrF⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpS.1, hpS.2, r, hr, hT, hrF⟩)
  have hdisj : Disjoint (chA N 3) (chB N 3) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    exact (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).2.2
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at this
  exact this.trans (Finset.card_union_le _ _)


/-! ### The linking map -/

/-- The value of the linking map on `S_{2,2}`. -/
theorem chLink_S22 {N p x y : ℕ} (hp : p ∈ chB N 2) (hxy : phi3 p = x * y)
    (hy0 : 0 < y) (hbig : bigP (phi3 p) = y) :
    chLink N p = if ∃ r ∈ chA N 2, phi3 r = 3 * y then x else y := by
  obtain ⟨-, h2, h1⟩ := Finset.mem_filter.mp hp
  unfold chLink
  rw [hbig, hxy, Nat.mul_div_cancel _ hy0]
  by_cases hE : ∃ r ∈ chA N 2, phi3 r = 3 * y
  · rw [if_pos ⟨by rw [← hxy]; exact h2, h1, hE⟩, if_pos hE]
  · rw [if_neg (fun h => hE h.2.2), if_neg hE]

/-- Outside `S_{2,2}` the linking map gives the largest prime. -/
theorem chLink_of_not_S22 {N p : ℕ} (hp : ¬ (Ω (phi3 p) = 2 ∧ p % 3 ≠ 1)) :
    chLink N p = bigP (phi3 p) := by
  unfold chLink
  rw [if_neg (fun h => hp ⟨h.1, h.2.1⟩)]

/-- The four shapes of an element of `S₁ ∪ S₂` together with its linked prime. -/
theorem link_view {N p : ℕ} (h : OddPerfect N) (hp : p ∈ chS1 N ∪ chA N 2 ∪ chB N 2) :
    ((phi3 p).Prime ∧ p % 3 = 2 ∧ chLink N p = phi3 p ∧ p ∈ chS1 N) ∨
    (∃ q, q.Prime ∧ 7 ≤ q ∧ phi3 p = 3 * q ∧ chLink N p = q ∧ p ∈ chA N 2) ∨
    (∃ x y, x.Prime ∧ y.Prime ∧ 7 ≤ x ∧ x < y ∧ phi3 p = x * y ∧ p % 3 = 2 ∧
      (¬ ∃ r ∈ chA N 2, phi3 r = 3 * y) ∧ chLink N p = y ∧ p ∈ chB N 2) ∨
    (∃ x y r, x.Prime ∧ y.Prime ∧ 7 ≤ x ∧ x < y ∧ phi3 p = x * y ∧ p % 3 = 2 ∧
      r ∈ chA N 2 ∧ phi3 r = 3 * y ∧ chLink N p = x ∧ p ∈ chB N 2) := by
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨hpr, h2, hb⟩ := shape_S1 h hp
      have h1 := (Finset.mem_filter.mp hp).2
      refine Or.inl ⟨hpr, h2, ?_, hp⟩
      rw [chLink_of_not_S22 (by omega), hb]
    · obtain ⟨q, hq, hq7, hpq, hb⟩ := shape_S21 hp
      have h1 := (Finset.mem_filter.mp hp).2.2
      refine Or.inr (Or.inl ⟨q, hq, hq7, hpq, ?_, hp⟩)
      rw [chLink_of_not_S22 (by omega), hb]
  · obtain ⟨x, y, hx, hy, hx7, hxy, hpxy, hb, h2⟩ := shape_S22 h hp
    have hl := chLink_S22 hp hpxy (by omega) hb
    by_cases hE : ∃ r ∈ chA N 2, phi3 r = 3 * y
    · obtain ⟨r, hr, hry⟩ := hE
      rw [if_pos ⟨r, hr, hry⟩] at hl
      exact Or.inr (Or.inr (Or.inr ⟨x, y, r, hx, hy, hx7, hxy, hpxy, h2, hr, hry, hl, hp⟩))
    · rw [if_neg hE] at hl
      exact Or.inr (Or.inr (Or.inl ⟨x, y, hx, hy, hx7, hxy, hpxy, h2, hE, hl, hp⟩))

/-- Clayton and Hansen, Lemma "LinkInjective" (arXiv 2303.11974): the linking map is injective
on `S₁ ∪ S₂`. -/
theorem chLink_injOn {N : ℕ} (h : OddPerfect N) :
    Set.InjOn (chLink N) ((chS1 N ∪ chA N 2 ∪ chB N 2 : Finset ℕ) : Set ℕ) := by
  have memS : ∀ {p}, p ∈ chS1 N ∪ chA N 2 ∪ chB N 2 → p ∈ chS N := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hp).1
  have memA : ∀ {r}, r ∈ chA N 2 → r.Prime ∧ r % 2 = 1 ∧ 5 ≤ r := by
    intro r hr
    obtain ⟨-, hrp, -, -, hro, -, hr5⟩ := chS_spec h (Finset.mem_filter.mp hr).1
    exact ⟨hrp, hro, hr5⟩
  -- the asymmetric core: `p₁` in a class not later than `p₂`
  have core : ∀ p₁ p₂, p₁ ∈ chS1 N ∪ chA N 2 ∪ chB N 2 → p₂ ∈ chS1 N ∪ chA N 2 ∪ chB N 2 →
      chLink N p₁ = chLink N p₂ →
      (p₁ ∈ chS1 N ∨ (p₁ ∈ chA N 2 ∧ p₂ ∉ chS1 N) ∨ (p₁ ∈ chB N 2 ∧ p₂ ∈ chB N 2)) →
      p₁ = p₂ := by
    intro p₁ p₂ hp₁ hp₂ hl hord
    obtain ⟨-, hp₁p, -, -, hp₁o, -, hp₁5⟩ := chS_spec h (memS hp₁)
    obtain ⟨-, hp₂p, -, -, hp₂o, -, hp₂5⟩ := chS_spec h (memS hp₂)
    have inj : phi3 p₁ = phi3 p₂ → p₁ = p₂ := fun e => phi3_strictMono.injective e
    have cS1 : ∀ {p}, p ∈ chS1 N → Ω (phi3 p) = 1 := fun h => (Finset.mem_filter.mp h).2
    have cA : ∀ {p}, p ∈ chA N 2 → Ω (phi3 p) = 2 ∧ p % 3 = 1 :=
      fun h => (Finset.mem_filter.mp h).2
    have cB : ∀ {p}, p ∈ chB N 2 → Ω (phi3 p) = 2 ∧ p % 3 ≠ 1 :=
      fun h => (Finset.mem_filter.mp h).2
    rcases link_view h hp₁ with ⟨hA1, hA2, hA3, hA4⟩ | ⟨q, hq, hq7, hpq, hl₁, hA⟩ |
        ⟨x, y, hx, hy, hx7, hxy, hpxy, h2, hE, hl₁, hm₁⟩ |
        ⟨x, y, r, hx, hy, hx7, hxy, hpxy, h2, hr, hry, hl₁, hm₁⟩ <;>
      rcases link_view h hp₂ with ⟨hB1, hB2, hB3, hB4⟩ | ⟨q', hq', hq7', hpq', hl₂, hB⟩ |
        ⟨x', y', hx', hy', hx7', hxy', hpxy', h2', hE', hl₂, hm₂⟩ |
        ⟨x', y', r', hx', hy', hx7', hxy', hpxy', h2', hr', hry', hl₂, hm₂⟩
    -- S₁, S₁
    · exact inj (by rw [← hA3, ← hB3, hl])
    -- S₁, S₂₁
    · exact absurd (by rw [hpq', ← hl₂, ← hl, hA3]) (no_phi3_eq_three_mul_phi3 hp₂p hA1)
    -- S₁, S₂₂ (largest)
    · exact absurd hp₂p (ch_zelProof1_not_prime hy' (by rw [hpxy', mul_comm])
        (by rw [← hA3, hl, hl₂]) hxy' (by omega))
    -- S₁, S₂₂ (smaller)
    · obtain ⟨hrp, hro, hr5⟩ := memA hr'
      exact (ch_unique_S1_S2 hp₂p hrp hy' hx' (by omega) (by omega) (by omega) hxy'
        (by rw [hpxy', mul_comm]) hry' hp₁p (by omega) (by rw [← hA3, hl, hl₂, mul_one])
        (by omega) (Or.inl rfl)).elim
    -- S₂₁, S₁ : excluded by the ordering
    · exfalso
      rcases hord with c | ⟨c, c'⟩ | ⟨c, c'⟩
      · have := cS1 c; have := cA hA; omega
      · exact c' hB4
      · have := cS1 hB4; have := cB c'; omega
    -- S₂₁, S₂₁
    · exact inj (by rw [hpq, hpq', ← hl₁, ← hl₂, hl])
    -- S₂₁, S₂₂ (largest): then `p₂` would be exceptional
    · exact absurd ⟨p₁, hA, by rw [hpq, ← hl₁, hl, hl₂]⟩ hE'
    -- S₂₁, S₂₂ (smaller)
    · obtain ⟨hrp, hro, hr5⟩ := memA hr'
      exact (ch_unique_S1_S2 hp₂p hrp hy' hx' (by omega) (by omega) (by omega) hxy'
        (by rw [hpxy', mul_comm]) hry' hp₁p (by omega)
        (by rw [hpq, ← hl₁, hl, hl₂, mul_comm]) (by omega)
        (Or.inr ⟨Nat.prime_three, by norm_num⟩)).elim
    -- S₂₂ (largest), S₁ : excluded
    · exfalso
      rcases hord with c | ⟨c, c'⟩ | ⟨c, c'⟩
      · have := cS1 c; have := cB hm₁; omega
      · exact c' hB4
      · have := cS1 hB4; have := cB c'; omega
    -- S₂₂ (largest), S₂₁ : excluded
    · exfalso
      have := cA hB; have := cB hm₁
      rcases hord with c | ⟨c, c'⟩ | ⟨c, c'⟩
      · have := cS1 c; omega
      · have := cA c; omega
      · have := cB c'; omega
    -- S₂₂ (largest), S₂₂ (largest)
    · have hyy : y = y' := by rw [← hl₁, ← hl₂, hl]
      subst hyy
      rcases lt_trichotomy x x' with hlt | heq | hgt
      · exact (ch_zelProof2 hp₂p hp₁p hy hx' hx (by omega) (by omega) (by omega) (by omega)
          (by omega) hxy' hlt ⟨hpxy'.trans (mul_comm _ _), hpxy.trans (mul_comm _ _)⟩).elim
      · exact inj (by rw [hpxy, hpxy', heq])
      · exact (ch_zelProof2 hp₁p hp₂p hy hx hx' (by omega) (by omega) (by omega) (by omega)
          (by omega) hxy hgt ⟨hpxy.trans (mul_comm _ _), hpxy'.trans (mul_comm _ _)⟩).elim
    -- S₂₂ (largest), S₂₂ (smaller)
    · obtain ⟨hrp, hro, hr5⟩ := memA hr'
      exact (ch_unique_S1_S2 hp₂p hrp hy' hx' (by omega) (by omega) (by omega) hxy'
        (by rw [hpxy', mul_comm]) hry' hp₁p (by omega)
        (by rw [hpxy, ← hl₁, hl, hl₂, mul_comm]) (by rw [← hl₂, ← hl, hl₁]; exact hxy)
        (Or.inr ⟨hx, by omega⟩)).elim
    -- S₂₂ (smaller), S₁ : excluded
    · exfalso
      rcases hord with c | ⟨c, c'⟩ | ⟨c, c'⟩
      · have := cS1 c; have := cB hm₁; omega
      · exact c' hB4
      · have := cS1 hB4; have := cB c'; omega
    -- S₂₂ (smaller), S₂₁ : excluded
    · exfalso
      have := cA hB; have := cB hm₁
      rcases hord with c | ⟨c, c'⟩ | ⟨c, c'⟩
      · have := cS1 c; omega
      · have := cA c; omega
      · have := cB c'; omega
    -- S₂₂ (smaller), S₂₂ (largest)
    · obtain ⟨hrp, hro, hr5⟩ := memA hr
      exact (ch_unique_S1_S2 hp₁p hrp hy hx (by omega) (by omega) (by omega) hxy
        (by rw [hpxy, mul_comm]) hry hp₂p (by omega)
        (by rw [hpxy', ← hl₂, ← hl, hl₁, mul_comm]) (by rw [← hl₁, hl, hl₂]; exact hxy')
        (Or.inr ⟨hx', by omega⟩)).elim
    -- S₂₂ (smaller), S₂₂ (smaller)
    · have hxx : x = x' := by rw [← hl₁, ← hl₂, hl]
      subst hxx
      obtain ⟨hrp, hro, hr5⟩ := memA hr
      obtain ⟨hrp', hro', hr5'⟩ := memA hr'
      exact ch_uniqueness hy hy' (by rw [hpxy, mul_comm]) hry (by rw [hpxy', mul_comm]) hry'
        hxy hxy' (by omega) (by omega) (by omega)
  intro p₁ hp₁ p₂ hp₂ hl
  have hp₁' : p₁ ∈ chS1 N ∪ chA N 2 ∪ chB N 2 := hp₁
  have hp₂' : p₂ ∈ chS1 N ∪ chA N 2 ∪ chB N 2 := hp₂
  have cls : ∀ {p}, p ∈ chS1 N ∪ chA N 2 ∪ chB N 2 →
      p ∈ chS1 N ∨ p ∈ chA N 2 ∨ p ∈ chB N 2 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr hp)
  have d12 : ∀ {p}, p ∈ chS1 N → p ∉ chA N 2 := fun h1 h2 => by
    have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2.1; omega
  have d13 : ∀ {p}, p ∈ chS1 N → p ∉ chB N 2 := fun h1 h2 => by
    have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2.1; omega
  rcases cls hp₁' with c₁ | c₁ | c₁ <;> rcases cls hp₂' with c₂ | c₂ | c₂
  · exact core p₁ p₂ hp₁' hp₂' hl (Or.inl c₁)
  · exact core p₁ p₂ hp₁' hp₂' hl (Or.inl c₁)
  · exact core p₁ p₂ hp₁' hp₂' hl (Or.inl c₁)
  · exact (core p₂ p₁ hp₂' hp₁' hl.symm (Or.inl c₂)).symm
  · exact core p₁ p₂ hp₁' hp₂' hl (Or.inr (Or.inl ⟨c₁, fun h => d12 h c₂⟩))
  · exact core p₁ p₂ hp₁' hp₂' hl (Or.inr (Or.inl ⟨c₁, fun h => d13 h c₂⟩))
  · exact (core p₂ p₁ hp₂' hp₁' hl.symm (Or.inl c₂)).symm
  · exact (core p₂ p₁ hp₂' hp₁' hl.symm (Or.inr (Or.inl ⟨c₂, fun h => d13 h c₁⟩))).symm
  · exact core p₁ p₂ hp₁' hp₂' hl (Or.inr (Or.inr ⟨c₁, c₂⟩))


/-! ### The linking map on `S_{3,1}` -/

/-- The shape of an element of `S_{3,1}` together with its linked prime. -/
theorem link_view_S31 {N p : ℕ} (hp : p ∈ chA N 3) :
    ∃ d e, d.Prime ∧ e.Prime ∧ 7 ≤ e ∧ e ≤ d ∧ phi3 p = 3 * d * e ∧ chLink N p = d := by
  obtain ⟨d, e, hd, he, he7, hed, hde, hb⟩ := shape_S31 hp
  have h1 := (Finset.mem_filter.mp hp).2.2
  exact ⟨d, e, hd, he, he7, hed, hde, by rw [chLink_of_not_S22 (by omega), hb]⟩

/-- Clayton and Hansen, Lemmas "Unique between S1 and S31" and "Unique between S21 and S31":
the linked prime of an element of `S_{3,1}` is not that of an element of `S₁ ∪ S_{2,1}`. -/
theorem chLink_ne_S31 {N a b : ℕ} (h : OddPerfect N) (ha : a ∈ chS1 N ∪ chA N 2)
    (hb : b ∈ chA N 3) : chLink N a ≠ chLink N b := by
  obtain ⟨d, e, hd, he, he7, hed, hde, hlb⟩ := link_view_S31 hb
  have hbp := (chS_spec h (Finset.mem_filter.mp hb).1).2.1
  intro hl
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨-, -, hb1⟩ := shape_S1 h ha
    have h1 := (Finset.mem_filter.mp ha).2
    rw [chLink_of_not_S22 (by omega), hb1] at hl
    exact ch_unique_S1_S31 hbp (chS_spec h (Finset.mem_filter.mp ha).1).2.1 hd (by omega) hde
      (by rw [hl, hlb]) hed
  · obtain ⟨q, -, -, hpq, hb1⟩ := shape_S21 ha
    have h1 := (Finset.mem_filter.mp ha).2.2
    rw [chLink_of_not_S22 (by omega), hb1] at hl
    exact ch_unique_S21_S31 hbp hd (by omega) hde (by rw [hpq, hl, hlb]) hed

/-- Clayton and Hansen, Lemma "LinkAlmostInjective" (arXiv 2303.11974), with the direct
lemmas `ch_sum_S22_S31` and `ch_small_S22_not_S31`: every fiber of the linking map on
`S_{2,2} ∪ S_{3,1}` has at most two elements. -/
theorem chLink_fiber_le_two {N : ℕ} (h : OddPerfect N) (x : ℕ) :
    ((chB N 2 ∪ chA N 3).filter (fun p => chLink N p = x)).card ≤ 2 := by
  classical
  set F22 := (chB N 2).filter (fun p => chLink N p = x)
  set F31 := (chA N 3).filter (fun p => chLink N p = x)
  have hF : (chB N 2 ∪ chA N 3).filter (fun p => chLink N p = x) = F22 ∪ F31 :=
    Finset.filter_union _ _ _
  have h22 : F22.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    obtain ⟨ha, hla⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hlb⟩ := Finset.mem_filter.mp hb
    exact chLink_injOn h (Finset.mem_union_right _ ha) (Finset.mem_union_right _ hb)
      (hla.trans hlb.symm)
  -- data of the elements of `F31`
  have v31 : ∀ a ∈ F31, ∃ e, e ≤ x ∧ 7 ≤ e ∧ x.Prime ∧ phi3 a = 3 * x * e ∧ a % 2 = 1 ∧
      a % 3 = 1 ∧ a ∈ chA N 3 := by
    intro a ha
    obtain ⟨ha, hla⟩ := Finset.mem_filter.mp ha
    obtain ⟨d, e, hd, he, he7, hed, hde, hl⟩ := link_view_S31 ha
    rw [hla] at hl
    subst hl
    exact ⟨e, hed, he7, hd, hde, (chS_spec h (Finset.mem_filter.mp ha).1).2.2.2.2.1,
      (Finset.mem_filter.mp ha).2.2, ha⟩
  have h31 : F31.card ≤ 2 := by
    by_contra hc
    push Not at hc
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hc
    obtain ⟨e₁, h₁, -, hx, ha', -⟩ := v31 a ha
    obtain ⟨e₂, h₂, -, -, hb', -⟩ := v31 b hb
    obtain ⟨e₃, h₃, -, -, hc', -⟩ := v31 c hc
    have := ch_sum_S31_S31 hx ha' hb' h₁ h₂ hab
    have := ch_sum_S31_S31 hx ha' hc' h₁ h₃ hac
    omega
  have hmix : F22.Nonempty → F31.card ≤ 1 := by
    rintro ⟨c, hc⟩
    obtain ⟨hcB, hlc⟩ := Finset.mem_filter.mp hc
    obtain ⟨-, hcp, -, -, hco, -, -⟩ := chS_spec h (Finset.mem_filter.mp hcB).1
    obtain ⟨u, y, hu, hy, hu7, huy, hcuy, hby, hc2⟩ := shape_S22 h hcB
    have hl := chLink_S22 hcB hcuy (by omega) hby
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    obtain ⟨e₁, h₁, he₁, hx, ha', hao, ha1, haA⟩ := v31 a ha
    obtain ⟨e₂, h₂, -, -, hb', hbo, hb1, -⟩ := v31 b hb
    have hca : ∀ {z}, z % 3 = 1 → z ≠ c := fun hz hzc => by omega
    by_cases hE : ∃ r ∈ chA N 2, phi3 r = 3 * y
    · rw [if_pos hE] at hl
      obtain ⟨r, hr, hry⟩ := hE
      obtain ⟨-, -, -, -, hro, -, hr5⟩ := chS_spec h (Finset.mem_filter.mp hr).1
      rw [hlc] at hl
      subst hl
      exact (ch_small_S22_not_S31 hy hx (by rw [hcuy, mul_comm]) hry ha' huy (by omega) h₁
        hco hro hao hc2 ha1).elim
    · rw [if_neg hE, hlc] at hl
      subst hl
      have s₁ := ch_sum_S22_S31 hx ha' (by rw [hcuy, mul_comm]) h₁ huy hao hco (hca ha1)
      have s₂ := ch_sum_S22_S31 hx hb' (by rw [hcuy, mul_comm]) h₂ huy hbo hco (hca hb1)
      omega
  rw [hF]
  refine (Finset.card_union_le _ _).trans ?_
  rcases F22.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.card_empty]; omega
  · have := hmix hne; omega

/-- The linked prime of an element of `S₁ ∪ S₂ ∪ S_{3,1}` is a prime of `S` that is
`1 (mod 3)` or a prime of `T ∪ {p₀}`. -/
theorem chLink_mem {N p : ℕ} (h : OddPerfect N)
    (hp : p ∈ chS1 N ∪ chA N 2 ∪ chB N 2 ∪ chA N 3) : chLink N p ∈ chSone N ∪ chT N := by
  have key : ∃ r, r.Prime ∧ r ∣ phi3 p ∧ 7 ≤ r ∧ chLink N p = r ∧ p ∈ chS N := by
    rcases Finset.mem_union.mp hp with hp | hp
    · have hpS : p ∈ chS N := by
        rcases Finset.mem_union.mp hp with hp | hp
        · rcases Finset.mem_union.mp hp with hp | hp
          · exact (Finset.mem_filter.mp hp).1
          · exact (Finset.mem_filter.mp hp).1
        · exact (Finset.mem_filter.mp hp).1
      rcases link_view h hp with ⟨hA1, -, hA3, -⟩ | ⟨q, hq, hq7, hpq, hl, -⟩ |
          ⟨x, y, hx, hy, hx7, hxy, hpxy, -, -, hl, -⟩ |
          ⟨x, y, r, hx, hy, hx7, hxy, hpxy, -, -, -, hl, -⟩
      · exact ⟨_, hA1, dvd_rfl, by have := two_le_phi3_of_chS h hpS; omega, hA3, hpS⟩
      · exact ⟨q, hq, ⟨3, by rw [hpq, mul_comm]⟩, hq7, hl, hpS⟩
      · exact ⟨y, hy, ⟨x, by rw [hpxy, mul_comm]⟩, by omega, hl, hpS⟩
      · exact ⟨x, hx, ⟨y, hpxy⟩, hx7, hl, hpS⟩
    · obtain ⟨d, e, hd, he, he7, hed, hde, hl⟩ := link_view_S31 hp
      exact ⟨d, hd, ⟨3 * e, by rw [hde]; ring⟩, by omega, hl, (Finset.mem_filter.mp hp).1⟩
  obtain ⟨r, hr, hrd, hr7, hl, hpS⟩ := key
  rw [hl]
  obtain ⟨hrN, -, hr1⟩ := chS_target h hpS hr hrd
  rcases mem_chS_or_chT hrN (by omega) with hS | hT
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS, hr1 (by omega)⟩)
  · exact Finset.mem_union_right _ hT

/-- `S₁` and `S_{2,1}` are disjoint. -/
theorem disjoint_chS1_chA2 (N : ℕ) : Disjoint (chS1 N) (chA N 2) := by
  rw [Finset.disjoint_left]; intro p h1 h2
  have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2.1; omega

/-- `S₁ ∪ S_{2,1}` and `S_{2,2}` are disjoint. -/
theorem disjoint_chS1A2_chB2 (N : ℕ) : Disjoint (chS1 N ∪ chA N 2) (chB N 2) := by
  rw [Finset.disjoint_left]; intro p h1 h2
  have := (Finset.mem_filter.mp h2).2
  rcases Finset.mem_union.mp h1 with h1 | h1
  · have := (Finset.mem_filter.mp h1).2; omega
  · have := (Finset.mem_filter.mp h1).2; omega

/-- `S_{2,2}` and `S_{3,1}` are disjoint. -/
theorem disjoint_chB2_chA3 (N : ℕ) : Disjoint (chB N 2) (chA N 3) := by
  rw [Finset.disjoint_left]; intro p h1 h2
  have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega

/-- Clayton and Hansen (5.16), from Lemma "LinkInjective":
`|S₁| + |S₂| ≤ |T| + 1 + |S_{2,1}| + |S_{3,1}| + |S_{≥4,1}|`. -/
theorem ch_link_injective_row {N : ℕ} (h : OddPerfect N) :
    (chS1 N).card + (chA N 2).card + (chB N 2).card ≤ (chSone N).card + (chT N).card := by
  have hc := Finset.card_le_card_of_injOn (chLink N)
    (s := chS1 N ∪ chA N 2 ∪ chB N 2) (t := chSone N ∪ chT N)
    (fun p hp => chLink_mem h (Finset.mem_union_left _ hp)) (chLink_injOn h)
  rw [Finset.card_union_of_disjoint (disjoint_chS1A2_chB2 N),
    Finset.card_union_of_disjoint (disjoint_chS1_chA2 N)] at hc
  exact hc.trans (Finset.card_union_le _ _)

/-- Clayton and Hansen (5.17), from Lemma "LinkAlmostInjective":
`|S₁| + |S_{2,1}| + (|S_{2,2}| + |S_{3,1}|) / 2 ≤ |T| + 1 + |S_{2,1}| + |S_{3,1}| + |S_{≥4,1}|`,
stated after multiplying by `2`. -/
theorem ch_link_almost_injective_row {N : ℕ} (h : OddPerfect N) :
    2 * ((chS1 N).card + (chA N 2).card) + (chB N 2).card + (chA N 3).card ≤
      2 * ((chSone N).card + (chT N).card) := by
  classical
  set A := chS1 N ∪ chA N 2
  set B := chB N 2 ∪ chA N 3
  have hA : (A.image (chLink N)).card = A.card :=
    Finset.card_image_of_injOn ((chLink_injOn h).mono (by
      intro p hp; exact Finset.mem_union_left _ hp))
  have hB : B.card ≤ 2 * (B.image (chLink N)).card :=
    Finset.card_le_mul_card_image B 2 fun x _ => chLink_fiber_le_two h x
  have hdisj : Disjoint (A.image (chLink N)) (B.image (chLink N)) := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzA
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hzB
    rcases Finset.mem_union.mp hb with hb | hb
    · have := chLink_injOn h (Finset.mem_union_right _ hb) (Finset.mem_union_left _ ha) hab
      subst this
      exact Finset.disjoint_left.mp (disjoint_chS1A2_chB2 N) ha hb
    · exact chLink_ne_S31 h ha hb hab.symm
  have hsub : A.image (chLink N) ∪ B.image (chLink N) ⊆ chSone N ∪ chT N := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact chLink_mem h (Finset.mem_union_left _ (Finset.mem_union_left _ ha))
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      rcases Finset.mem_union.mp hb with hb | hb
      · exact chLink_mem h (Finset.mem_union_left _ (Finset.mem_union_right _ hb))
      · exact chLink_mem h (Finset.mem_union_right _ hb)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 := Finset.card_union_le (chSone N) (chT N)
  have h3 : A.card = (chS1 N).card + (chA N 2).card :=
    Finset.card_union_of_disjoint (disjoint_chS1_chA2 N)
  have h4 : B.card = (chB N 2).card + (chA N 3).card :=
    Finset.card_union_of_disjoint (disjoint_chB2_chA3 N)
  omega


/-! ### The ledger and the main theorems -/

/-- The Clayton and Hansen ledger (arXiv 2303.11974, Section 5, in merged form). With
`s = |S|`, `t = |T ∪ {p₀}|`, `G = g₄ + e₀`, `f = v₃(N)`, `s1 = |S₁|`, `a2, a3, a4` the sizes of
`S_{2,1}, S_{3,1}, S_{≥4,1}`, `b2, b3, b4` those of `S_{2,2}, S_{3,2}, S_{≥4,2}`,
`sone = |S_{·,1}|`, `s1s = |S₁^S|`, `s1t = |S₁^T|`, `xs = |X_S|`, `xt = |X_T|`, the listed
linear relations hold. -/
theorem ch_ledger {N : ℕ} (h : OddPerfect N) :
    ∃ s t G f s1 a2 b2 a3 b3 a4 b4 s1s s1t xs xt sone : ℕ,
      N.primeFactors.card = s + t + (if 3 ∣ N then 1 else 0) ∧
      ∑ p ∈ N.primeFactors, N.factorization p = 2 * s + G + f ∧
      f = N.factorization 3 ∧ 4 * t ≤ G + 3 ∧
      s = s1 + a2 + b2 + a3 + b3 + a4 + b4 ∧ sone = a2 + a3 + a4 ∧
      s1 ≤ s1s + s1t + 1 ∧ a3 + b3 ≤ xs + xt ∧ sone ≤ f ∧
      s1 + 2 * b2 + 3 * b3 + a4 + 4 * b4 ≤ G + a2 ∧
      s1 + a2 + b2 ≤ sone + t ∧ 2 * (s1 + a2) + b2 + a3 ≤ 2 * (sone + t) ∧
      2 * s1s + xs ≤ 2 * sone ∧ 4 * s1t + xt ≤ G := by
  obtain ⟨h1, h2⟩ := ch_omega_Omega h
  have hsone := ch_card_Sone h
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, rfl, ch_four_mul_card_T h,
    ch_card_S h, hsone, ch_card_S1_le h, ch_card_S3_le h, hsone ▸ ch_card_Sone_le h,
    ch_contributed_by_S h, ch_link_injective_row h, ch_link_almost_injective_row h,
    ch_contributed_to_S h, ch_contributed_to_T h⟩

/-- Clayton and Hansen (arXiv 2303.11974), Theorem 1: for an odd perfect number,
`(99/37) ω - 187/37 ≤ Ω`, stated with `N.primeFactors.card` and the exponent sum. -/
theorem ninetynine_mul_card_le {N : ℕ} (h : OddPerfect N) :
    99 * N.primeFactors.card ≤ 37 * (∑ p ∈ N.primeFactors, N.factorization p) + 187 := by
  obtain ⟨s, t, G, f, s1, a2, b2, a3, b3, a4, b4, s1s, s1t, xs, xt, sone, hω, hΩ, -, h4,
    hS, hsone, h9, h12, h14, h15, h16, h17, h18, h19⟩ := ch_ledger h
  have : (if 3 ∣ N then 1 else 0) ≤ 1 := by split_ifs <;> omega
  omega

/-- Clayton and Hansen (arXiv 2303.11974), Theorem 2: for an odd perfect number with `3 ∤ N`,
`(51/19) ω - 46/19 ≤ Ω`, stated with `N.primeFactors.card` and the exponent sum. -/
theorem fiftyone_mul_card_le_of_not_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    51 * N.primeFactors.card ≤ 19 * (∑ p ∈ N.primeFactors, N.factorization p) + 46 := by
  obtain ⟨s, t, G, f, s1, a2, b2, a3, b3, a4, b4, s1s, s1t, xs, xt, sone, hω, hΩ, hf, h4,
    hS, hsone, h9, h12, h14, h15, h16, h17, h18, h19⟩ := ch_ledger h
  rw [if_neg h3] at hω
  rw [Nat.factorization_eq_zero_of_not_dvd h3] at hf
  omega

/-- Clayton and Hansen: `99 ω(N) ≤ 37 Ω(N) + 187` for every odd perfect number `N`. -/
theorem ninetynine_mul_omega_le {N : ℕ} (h : OddPerfect N) : 99 * ω N ≤ 37 * Ω N + 187 := by
  rw [cardFactors_eq_sum_primeFactors, cardDistinctFactors_eq_card_primeFactors]
  exact ninetynine_mul_card_le h

/-- Clayton and Hansen: `51 ω(N) ≤ 19 Ω(N) + 46` for every odd perfect number `N` with
`3 ∤ N`. -/
theorem fiftyone_mul_omega_le_of_not_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    51 * ω N ≤ 19 * Ω N + 46 := by
  rw [cardFactors_eq_sum_primeFactors, cardDistinctFactors_eq_card_primeFactors]
  exact fiftyone_mul_card_le_of_not_three_dvd h h3

end OddPerfect

#print axioms OddPerfect.eisNorm_mul
#print axioms OddPerfect.eis_div
#print axioms OddPerfect.eis_unit
#print axioms OddPerfect.eis_unit_coeff
#print axioms OddPerfect.no_triple_threat
#print axioms OddPerfect.ch_uniqueness
#print axioms OddPerfect.ch_sum_S22_S31
#print axioms OddPerfect.ch_small_S22_not_S31
#print axioms OddPerfect.ch_sum_S31_S31
#print axioms OddPerfect.bigP_eq
#print axioms OddPerfect.chS_spec
#print axioms OddPerfect.chS_sigmaWeight
#print axioms OddPerfect.chS_target
#print axioms OddPerfect.mem_chS_or_chT
#print axioms OddPerfect.two_le_phi3_of_chS
#print axioms OddPerfect.cardFactors_phi3_ne_zero
#print axioms OddPerfect.two_le_cardFactors_of_mod_one
#print axioms OddPerfect.exists_two_of_cardFactors
#print axioms OddPerfect.exists_three_of_cardFactors
#print axioms OddPerfect.prime_eq_of_dvd_mul_prime
#print axioms OddPerfect.shape_S1
#print axioms OddPerfect.shape_S21
#print axioms OddPerfect.shape_S22
#print axioms OddPerfect.shape_S31
#print axioms OddPerfect.ch_omega_Omega
#print axioms OddPerfect.ch_four_mul_card_T
#print axioms OddPerfect.ch_card_S
#print axioms OddPerfect.ch_card_Sone
#print axioms OddPerfect.ch_card_Sone_le
#print axioms OddPerfect.recv_le
#print axioms OddPerfect.chS_sub
#print axioms OddPerfect.chT_odd
#print axioms OddPerfect.chS_odd
#print axioms OddPerfect.ch_contributed_by_S
#print axioms OddPerfect.phi3_injOn
#print axioms OddPerfect.ch_card_S1_le
#print axioms OddPerfect.card_S1S_le
#print axioms OddPerfect.ch_contributed_to_S
#print axioms OddPerfect.ch_contributed_to_T
#print axioms OddPerfect.ch_card_S3_le
#print axioms OddPerfect.chLink_S22
#print axioms OddPerfect.chLink_of_not_S22
#print axioms OddPerfect.link_view
#print axioms OddPerfect.chLink_injOn
#print axioms OddPerfect.link_view_S31
#print axioms OddPerfect.chLink_ne_S31
#print axioms OddPerfect.chLink_fiber_le_two
#print axioms OddPerfect.chLink_mem
#print axioms OddPerfect.disjoint_chS1_chA2
#print axioms OddPerfect.disjoint_chS1A2_chB2
#print axioms OddPerfect.disjoint_chB2_chA3
#print axioms OddPerfect.ch_link_injective_row
#print axioms OddPerfect.ch_link_almost_injective_row
#print axioms OddPerfect.ch_ledger
#print axioms OddPerfect.ninetynine_mul_card_le
#print axioms OddPerfect.fiftyone_mul_card_le_of_not_three_dvd
#print axioms OddPerfect.ninetynine_mul_omega_le
#print axioms OddPerfect.fiftyone_mul_omega_le_of_not_three_dvd
