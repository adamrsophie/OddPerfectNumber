import OddPerfect.TwoExceptionFour
import OddPerfect.TwoExceptionThree

/-!
# Two exceptional exponents, exponent 4 at 3: the special prime is 1 modulo 12

Let `N` be an odd perfect number with special prime `q`, `e₃ = 4`, and every prime factor other
than `q`, `r₁` and `r₂` of exponent exactly 2. Then `q ≡ 1 (mod 12)`.

By `two_exceptions_five_three_ne_four` and `two_exceptions_three_pow_four` the exceptions are
`3` and `11` and the exponent `e` of 11 is even with `e ≥ 6`. Assume `q ≡ 2 (mod 3)`, so
`q ≡ 5 (mod 12)` and `q ≥ 17`. A prime `≡ 2 (mod 3)` divides no `σ(p^2)`, so the exact ledgers
give `v_q(N) = v_q(σ(11^e))` and `e = 2 + v_11(σ(q^α))`, using `σ(3^4) = 11^2`. Hence
`A · q^α = σ(11^e)` and `2 · 11^(e-2) · B = σ(q^α)`; abundancy bounds give `67 ≤ A·B ≤ 70`,
congruences modulo 3 give `3 ∣ B` and `A ≡ 2 (mod 3)`, so `A = 23` and `B = 3`, and the two
closed forms `10 · σ(11^e) + 1 = 11^(e+1)` and `(q - 1) · σ(q^α) + 1 = q^(α+1)` then have no
common solution.

The result holds only in this restricted family. The class `q ≡ 1 (mod 12)` is not reached,
because there ordinary square rows can feed `q`. Nothing about odd perfect numbers in general is
claimed. Whether these statements are new was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace TwoExceptionFourMod

/-- Closed form of the divisor sum of a prime power. -/
private theorem sigma_mul_add {p : ℕ} (hp : p.Prime) (a : ℕ) :
    σ 1 (p ^ a) * (p - 1) + 1 = p ^ (a + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  rw [sigma_one_apply_prime_pow hp, Nat.add_sub_cancel]
  exact geom_sum_mul_add m (a + 1)

private theorem pow_mod_three_of_even {x n : ℕ} (hx : x % 3 = 2) (hn : Even n) :
    x ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h2 : x ^ 2 % 3 = 1 := by rw [Nat.pow_mod]; simp [hx]
  rw [← two_mul, pow_mul, Nat.pow_mod, h2]
  simp

private theorem pow_mod_three_of_odd {x n : ℕ} (hx : x % 3 = 2) (hn : Odd n) :
    x ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, Nat.mul_mod, pow_mod_three_of_even hx ⟨k, by ring⟩, hx]

private theorem m_eq_sixteen {m : ℕ} (h1 : m < 28) (h2 : (m + 1) % 12 = 5)
    (h3 : 17 ≤ m + 1) : m = 16 := by
  omega

private theorem no_solution_sixteen {X : ℕ} (h : 49 * (X * 16) + 16 + 231 = 1331 * X) :
    False := by
  omega

/-- The arithmetic core: for `q ≡ 5 (mod 12)`, `q ≥ 17`, odd `α` and even `e'`, there are no
`A`, `B` with `σ(11^(e'+2)) = q^α · A` and `σ(q^α) = 2 · 11^e' · B`. -/
theorem no_quotients {q α e' A B : ℕ} (hq : q.Prime) (hq12 : q % 12 = 5) (hq17 : 17 ≤ q)
    (hα : Odd α) (he : Even e') (hA : σ 1 (11 ^ (e' + 2)) = q ^ α * A)
    (hB : σ 1 (q ^ α) = 2 * 11 ^ e' * B) : False := by
  have hS := sigma_mul_add (by norm_num : Nat.Prime 11) (e' + 2)
  have hT := sigma_mul_add hq α
  rw [show 11 ^ (e' + 2 + 1) = 1331 * 11 ^ e' by ring] at hS
  rw [pow_succ] at hT
  have hXm : 11 ^ e' % 3 = 1 := pow_mod_three_of_even (by norm_num) he
  have hQm : q ^ α % 3 = 2 := pow_mod_three_of_odd (by omega) hα
  have hXpos : 0 < 11 ^ e' := by positivity
  have hQ2 : 2 ≤ q ^ α := le_trans (by omega) (Nat.le_self_pow (by
    obtain ⟨k, rfl⟩ := hα; omega) q)
  generalize σ 1 (11 ^ (e' + 2)) = S at hS hA
  generalize σ 1 (q ^ α) = T at hT hB
  generalize 11 ^ e' = X at hS hB hXm hXpos
  generalize q ^ α = Q at hT hA hQm hQ2
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hT
  norm_num at hS
  -- hS : S * 10 + 1 = 1331 * X, hT : T * m + 1 = Q * (m + 1)
  have hS133 : 133 * X ≤ S := by omega
  have hS1331 : S * 10 < 1331 * X := by omega
  have hTQ : Q < T := by
    by_contra hc
    have : T * m ≤ Q * m := Nat.mul_le_mul_right m (by omega)
    linarith
  have hTlt : T * m < Q * (m + 1) := by omega
  have hST : S * T = 2 * (A * B) * (X * Q) := by rw [hA, hB]; ring
  have hXQ : 0 < X * Q := by positivity
  have hlow : 67 ≤ A * B := by
    have l1 : 133 * X * Q < S * T :=
      calc 133 * X * Q < 133 * X * T := Nat.mul_lt_mul_of_pos_left hTQ (by positivity)
        _ ≤ S * T := Nat.mul_le_mul_right _ hS133
    rw [hST] at l1
    have : 133 * (X * Q) < 2 * (A * B) * (X * Q) := by linarith
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  have hhigh : A * B ≤ 70 := by
    have u1 : S * 10 * (T * m) < 1331 * X * (Q * (m + 1)) :=
      Nat.mul_lt_mul'' hS1331 hTlt
    have u2 : (20 * m * (A * B)) * (X * Q) < (1331 * (m + 1)) * (X * Q) := by
      have : S * 10 * (T * m) = 20 * m * (A * B) * (X * Q) := by
        rw [show S * 10 * (T * m) = 10 * m * (S * T) by ring, hST]; ring
      rw [this] at u1
      linarith
    have u3 := Nat.lt_of_mul_lt_mul_right u2
    by_contra hc
    have : 20 * m * 71 ≤ 20 * m * (A * B) := Nat.mul_le_mul_left _ (by omega)
    linarith
  -- congruences modulo 3
  have hA3 : A % 3 = 2 := by
    have e1 : Q * A * 10 + 1 ≡ 2 * A * 10 + 1 [MOD 3] :=
      (((show Q ≡ 2 [MOD 3] from hQm).mul_right A).mul_right 10).add_right 1
    have e2 : 1331 * X ≡ 1331 * 1 [MOD 3] := (show X ≡ 1 [MOD 3] from hXm).mul_left 1331
    rw [← hA, hS] at e1
    have e3 := e1.symm.trans e2
    unfold Nat.ModEq at e3
    omega
  have hB3 : B % 3 = 0 := by
    have e1 : 2 * X * B * m + 1 ≡ 2 * 1 * B * 1 + 1 [MOD 3] :=
      ((((show X ≡ 1 [MOD 3] from hXm).mul_left 2).mul_right B).mul (show m ≡ 1 [MOD 3] by
        unfold Nat.ModEq; omega)).add_right 1
    have e2 : Q * (m + 1) ≡ 2 * 2 [MOD 3] :=
      (show Q ≡ 2 [MOD 3] from hQm).mul (show m + 1 ≡ 2 [MOD 3] by unfold Nat.ModEq; omega)
    rw [← hB] at e1
    rw [← hT] at e2
    have e3 := e1.symm.trans e2
    unfold Nat.ModEq at e3
    omega
  have h69 : A * B = 69 := by
    have : 3 ∣ A * B := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hB3) A
    omega
  obtain ⟨b, rfl⟩ : 3 ∣ B := Nat.dvd_of_mod_eq_zero hB3
  have hAb : A * b = 23 := by
    have : A * (3 * b) = 3 * (A * b) := by ring
    omega
  have hA23 : A ≤ 23 := Nat.le_of_dvd (by norm_num) ⟨b, hAb.symm⟩
  have hAB : A = 23 ∧ b = 1 := by
    interval_cases A <;> omega
  obtain ⟨rfl, rfl⟩ := hAB
  subst hA hB
  -- hS : Q * 23 * 10 + 1 = 1331 * X, hT : 2 * X * (3 * 1) * m + 1 = Q * (m + 1)
  have key : 49 * (X * m) + m + 231 = 1331 * X := by
    have e := congrArg (· * (m + 1)) hS
    linarith
  have hm : m < 28 := by
    by_contra hc
    have : X * 28 ≤ X * m := Nat.mul_le_mul_left X (by omega)
    linarith
  have h16 := m_eq_sixteen hm hq12 hq17
  subst h16
  exact no_solution_sixteen key

end TwoExceptionFourMod

open TwoExceptionFourMod

/-- A prime `r ≡ 2 (mod 3)` divides no `σ(p^2)` for a prime `p`: a prime factor of
`p^2 + p + 1` other than 3 is `1` modulo 3. -/
theorem not_dvd_sigma_sq_of_mod_three_two {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hr3 : r % 3 = 2) : ¬ r ∣ σ 1 (p ^ 2) := by
  rw [sigma_prime_sq hp]
  intro hd
  have := prime_dvd_phi3_mod_three hr (by omega) hd
  omega

private theorem sigma_three_pow_four : σ 1 (3 ^ 4) = 11 ^ 2 := by
  rw [sigma_one_apply_prime_pow Nat.prime_three]
  norm_num [Finset.sum_range_succ]

/-- Receipt at the special prime: let `N` be an odd perfect number with `e₃ = 4`, a prime
`q ≡ 2 (mod 3)`, `q ≠ 11`, and every prime factor other than `q`, `3` and `11` of exponent
exactly 2. Then `v_q(N) = v_q(σ(11^e))` for the exponent `e` of 11. -/
theorem factorization_special_eq_of_three_pow_four {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq2 : q ≠ 2) (hq3 : q % 3 = 2) (hq11 : q ≠ 11) (h34 : N.factorization 3 = 4)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → p ≠ 11 → N.factorization p = 2) :
    N.factorization q = padicValNat q (σ 1 (11 ^ N.factorization 11)) := by
  rw [factorization_eq_sum_erase h.perfect hq hq2]
  refine Finset.sum_eq_single 11 (fun p hp hp11 => ?_) (fun h11 => ?_)
  · obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    have hpP := Nat.prime_of_mem_primeFactors hpN
    apply padicValNat.eq_zero_of_not_dvd
    by_cases hp3 : p = 3
    · subst hp3
      rw [h34, sigma_three_pow_four]
      intro hd
      exact hq11 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hd))
    · rw [hsq p hpN hpq hp3 hp11]
      exact not_dvd_sigma_sq_of_mod_three_two hpP hq hq3
  · have : N.factorization 11 = 0 := by
      by_contra hc
      exact h11 (Finset.mem_erase.mpr ⟨Ne.symm hq11, Nat.mem_primeFactors.mpr
        ⟨by norm_num, Nat.dvd_of_factorization_pos hc, h.ne_zero⟩⟩)
    rw [this]
    simp

/-- Receipt at 11: under the hypotheses of `factorization_special_eq_of_three_pow_four`, the
exponent of 11 is `2 + v_11(σ(q^α))` for the exponent `α` of `q`. -/
theorem factorization_eleven_eq_of_three_pow_four {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hq3 : q % 3 = 2) (hq11 : q ≠ 11) (h34 : N.factorization 3 = 4)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → p ≠ 11 → N.factorization p = 2) :
    N.factorization 11 = 2 + padicValNat 11 (σ 1 (q ^ N.factorization q)) := by
  have p11 : Nat.Prime 11 := by norm_num
  have : Fact (Nat.Prime 11) := ⟨p11⟩
  have hq3' : q ≠ 3 := by omega
  have h0 : ∀ p ∈ N.primeFactors.erase 11, p ≠ 3 ∧ p ≠ q →
      padicValNat 11 (σ 1 (p ^ N.factorization p)) = 0 := by
    intro p hp hpn
    obtain ⟨hp11, hpN⟩ := Finset.mem_erase.mp hp
    apply padicValNat.eq_zero_of_not_dvd
    rw [hsq p hpN hpn.2 hpn.1 hp11]
    exact not_dvd_sigma_sq_of_mod_three_two (Nat.prime_of_mem_primeFactors hpN) p11
      (by norm_num)
  have ha : 3 ∉ N.primeFactors.erase 11 →
      padicValNat 11 (σ 1 (3 ^ N.factorization 3)) = 0 := fun h3 =>
    absurd (Finset.mem_erase.mpr ⟨by norm_num, Nat.mem_primeFactors.mpr
      ⟨Nat.prime_three, Nat.dvd_of_factorization_pos (by omega), h.ne_zero⟩⟩) h3
  have hb : q ∉ N.primeFactors.erase 11 →
      padicValNat 11 (σ 1 (q ^ N.factorization q)) = 0 := by
    intro hqn
    have : N.factorization q = 0 := by
      by_contra hc
      exact hqn (Finset.mem_erase.mpr ⟨hq11, Nat.mem_primeFactors.mpr
        ⟨hq, Nat.dvd_of_factorization_pos hc, h.ne_zero⟩⟩)
    rw [this]
    simp
  rw [factorization_eq_sum_erase h.perfect p11 (by norm_num),
    Finset.sum_eq_add (f := fun p => padicValNat 11 (σ 1 (p ^ N.factorization p))) 3 q
      (Ne.symm hq3') h0 ha hb]
  rw [h34, sigma_three_pow_four, padicValNat.prime_pow]

/-- Let `N` be an odd perfect number with special prime `q` and `e₃ = 4`, in which every prime
factor other than `q`, `r₁` and `r₂` has exponent exactly 2. Then `q ≡ 1 (mod 12)`. This holds
only in this restricted family; nothing about odd perfect numbers in general is claimed. Whether
this statement is new was not verified. -/
theorem two_exceptions_three_pow_four_special_mod_twelve
    {N q r₁ r₂ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (h34 : N.factorization 3 = 4)
    (hsq : ∀ p ∈ N.primeFactors,
      p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    q % 12 = 1 := by
  have hq5 : q ≠ 5 := by
    rintro rfl
    exact two_exceptions_five_three_ne_four h hodd hsq h34
  obtain ⟨hr, he, he6, -, -⟩ := two_exceptions_three_pow_four h hq hodd hq5 h34 hsq
  have hsq' : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → p ≠ 11 → N.factorization p = 2 := by
    intro p hp h1 h2 h3
    rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hsq p hp h1 h2 h3
    · exact hsq p hp h1 h3 h2
  obtain ⟨hq4, -⟩ := mod_four_special h hq hodd
  have hq3 : q % 3 ≠ 0 := by
    intro h0
    have h3 : q = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp (Nat.dvd_of_mod_eq_zero h0)).symm
    rw [h3, h34] at hodd
    exact absurd hodd (by decide)
  by_contra hne
  have hq32 : q % 3 = 2 := by omega
  have hq11 : q ≠ 11 := by omega
  have hq2 : q ≠ 2 := by omega
  have hα := factorization_special_eq_of_three_pow_four h hq hq2 hq32 hq11 h34 hsq'
  have he2 := factorization_eleven_eq_of_three_pow_four h hq hq32 hq11 h34 hsq'
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the quotient A
  have hdA : q ^ N.factorization q ∣ σ 1 (11 ^ N.factorization 11) := by
    have := pow_padicValNat_dvd (p := q) (n := σ 1 (11 ^ N.factorization 11))
    rwa [← hα] at this
  -- the quotient B
  set e' := padicValNat 11 (σ 1 (q ^ N.factorization q)) with he'
  have hd11 : 11 ^ e' ∣ σ 1 (q ^ N.factorization q) := pow_padicValNat_dvd
  have hd2 : 2 ∣ σ 1 (q ^ N.factorization q) := by
    apply dvd_of_one_le_padicValNat
    obtain ⟨t1, t2⟩ := padicValNat_two_special h hq hodd
    rw [padicValNat_two_sigma_prime_pow hq hq2,
      if_neg (Nat.not_even_iff_odd.mpr hodd), t1, t2]
  obtain ⟨B, hB⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd
    ((by norm_num : Nat.Coprime 2 11).pow_right e') hd2 hd11
  obtain ⟨A, hA⟩ := hdA
  rw [he2, add_comm] at hA
  have hev : Even e' := by
    rw [he2] at he
    obtain ⟨k, hk⟩ := he
    exact ⟨k - 1, by omega⟩
  exact no_quotients hq (by omega) (by omega) hodd hev hA hB

end OddPerfect

#print axioms OddPerfect.TwoExceptionFourMod.no_quotients
#print axioms OddPerfect.not_dvd_sigma_sq_of_mod_three_two
#print axioms OddPerfect.factorization_special_eq_of_three_pow_four
#print axioms OddPerfect.factorization_eleven_eq_of_three_pow_four
#print axioms OddPerfect.two_exceptions_three_pow_four_special_mod_twelve
