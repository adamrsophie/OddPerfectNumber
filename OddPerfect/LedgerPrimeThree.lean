import OddPerfect.LedgerPrimeTwo
import OddPerfect.LedgerOrdersTwo

/-!
# The forced collision of prime divisor sums: congruences, sizes and the Goormaghtigh equation

Let `N` be an odd perfect number with special prime `q`, and assume the case hypothesis that
the full divisor sum `σ(p ^ e_p)` of every ordinary component is prime. That hypothesis is not
known to hold for a hypothetical odd perfect number. `OddPerfect.LedgerPrimeTwo` then gives
ordinary primes `s`, `p ≠ r` with `σ(p ^ e) = σ(r ^ f) = s`, `e ≠ f`, `σ(s ^ g) = q`, and prime
indices `m = e + 1`, `n = f + 1`, `k = g + 1`.

* `prime_sigma_collision_structure`: with `e < f`, also `2 m n ∣ s - 1`, `2 k ∣ q - 1`,
  `q ≡ k (mod 2 m n)`, the residue disjunction `g ≡ 0 (mod 4)` or
  (`p ≡ r ≡ 1 (mod 4)` and `e ≡ f ≡ 2 (mod 4)`), `s ≥ 2 m n + 1`, `r < p`,
  `p ^ e < s < p ^ m`, `r ^ f < s < r ^ n`, `s ^ g < q < s ^ k`, and `p ≢ 1 (mod m)`,
  `r ≢ 1 (mod n)`, `s ≢ 1 (mod k)`. So the collision is a solution of the Goormaghtigh equation
  `(x ^ m - 1) / (x - 1) = (y ^ n - 1) / (y - 1)` with odd prime bases, odd prime exponents
  `m ≠ n` and a prime common value.
* `GoormaghtighOddPrime`, `GoormaghtighOddPrimeIndex`: the odd prime base case of the
  Goormaghtigh conjecture, and its restriction to the shape above. Both are open statements,
  used only as explicit hypotheses.
* `exists_not_prime_sigma_of_goormaghtighOddPrimeIndex`, `exists_not_prime_sigma_of_goormaghtigh`:
  conditional on these statements, some ordinary divisor sum `σ(p ^ e_p)` is not prime.
* `card_filter_dvd_succ_le_sum`, `card_sub_one_le_sum_of_forall_dvd`: a capacity bound for the
  prime factors whose index is divisible by a fixed `d ≥ 3`.

Whether these results are in the literature was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega

namespace OddPerfect

/-- If `σ(p ^ e) = s` for primes `p`, `s` and the index `e + 1` is prime, then
`e + 1 ∣ s - 1`: the order of `p` modulo `s` divides `e + 1` and is not `1`, since `p < s`. -/
theorem succ_dvd_sub_one_of_sigma_prime_pow_eq {p s e : ℕ} (hp : p.Prime) (hs : s.Prime)
    (he1 : (e + 1).Prime) (hps : σ 1 (p ^ e) = s) : e + 1 ∣ s - 1 := by
  have he : e ≠ 0 := by
    rintro rfl
    exact Nat.not_prime_one he1
  have hlt : p < s := hps ▸ lt_sigma_prime_pow hp he
  rcases (prime_dvd_sigma_prime_pow hp hs (by rw [hps])).2 with ⟨h1, -⟩ | ⟨h1, hd, hd'⟩
  · rw [Nat.mod_eq_of_lt hlt] at h1
    exact absurd h1 hp.one_lt.ne'
  · rcases (Nat.dvd_prime he1).mp hd with h | h
    · omega
    · rwa [h] at hd'

/-- For a prime `x` and `E ≥ 1`: `x ^ E < σ(x ^ E) < x ^ (E + 1)`. -/
theorem pow_lt_sigma_prime_pow_lt {x E : ℕ} (hx : x.Prime) (hE : E ≠ 0) :
    x ^ E < σ 1 (x ^ E) ∧ σ 1 (x ^ E) < x ^ (E + 1) := by
  constructor
  · rw [sigma_one_apply_prime_pow hx, Finset.sum_range_succ]
    have := Finset.single_le_sum (f := fun i => x ^ i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.pos_of_ne_zero hE))
    simp only [pow_zero] at this
    omega
  · have h1 := sigma_prime_pow_mul_pred hx E
    have h2 := Nat.le_mul_of_pos_right (σ 1 (x ^ E)) (show 0 < x - 1 by have := hx.two_le; omega)
    have h3 := Nat.one_le_pow (E + 1) x hx.pos
    omega

/-- For a prime `x ≡ 3 (mod 4)` and even `E`: `σ(x ^ E) ≡ 1 (mod 4)`. -/
theorem sigma_prime_pow_mod_four_of_three {x E : ℕ} (hx : x.Prime) (h3 : x % 4 = 3)
    (hE : Even E) : σ 1 (x ^ E) % 4 = 1 := by
  obtain ⟨j, rfl⟩ := hE
  rw [sigma_one_apply_prime_pow hx]
  have hx4 : (x : ZMod 4) = 3 := by
    rw [← ZMod.natCast_mod, h3]
    rfl
  have h9 : (3 : ZMod 4) ^ 2 = 1 := by decide
  have key : ∀ j : ℕ, (((∑ i ∈ Finset.range (j + j + 1), x ^ i : ℕ)) : ZMod 4) = 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show j + 1 + (j + 1) + 1 = (j + j + 1) + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
      push_cast at ih ⊢
      rw [ih, hx4, show j + j + 1 + 1 = 2 * (j + 1) by ring, show j + j + 1 = 2 * j + 1 by ring,
        pow_succ, pow_mul, pow_mul, h9, one_pow, one_pow]
      decide
  have := (ZMod.natCast_eq_natCast_iff' _ 1 4).mp (by exact_mod_cast key j)
  simpa using this

/-- Residues modulo `4` of `σ(x ^ E)` for an odd prime `x` and even `E`: either `x ≡ 3` and
`σ(x ^ E) ≡ 1`, or `x ≡ 1` and `σ(x ^ E) ≡ E + 1 (mod 4)`. -/
theorem sigma_prime_pow_even_mod_four {x E : ℕ} (hx : x.Prime) (hx2 : x ≠ 2) (hE : Even E) :
    (x % 4 = 3 ∧ σ 1 (x ^ E) % 4 = 1) ∨ (x % 4 = 1 ∧ σ 1 (x ^ E) % 4 = (E + 1) % 4) := by
  have ho := Nat.odd_iff.mp (hx.odd_of_ne_two hx2)
  rcases (by omega : x % 4 = 1 ∨ x % 4 = 3) with h1 | h3
  · exact Or.inr ⟨h1, sigma_prime_pow_modEq_succ hx (by unfold Nat.ModEq; omega) E⟩
  · exact Or.inl ⟨h3, sigma_prime_pow_mod_four_of_three hx h3 hE⟩

/-- If `σ(x ^ E) = y` for primes `x`, `y` with prime index `E + 1 < y`, then
`x ≢ 1 (mod E + 1)`: otherwise `y ≡ E + 1 ≡ 0 (mod E + 1)`. -/
theorem mod_succ_ne_one_of_sigma_prime_pow_eq {x y E : ℕ} (hx : x.Prime) (hy : y.Prime)
    (hE1 : (E + 1).Prime) (hxy : σ 1 (x ^ E) = y) (hlt : E + 1 < y) : x % (E + 1) ≠ 1 := by
  intro h1
  have hm := sigma_prime_pow_modEq_succ hx (show x ≡ 1 [MOD E + 1] by
    unfold Nat.ModEq
    rw [h1, Nat.mod_eq_of_lt hE1.one_lt]) E
  rw [hxy] at hm
  have hd : E + 1 ∣ y := Nat.dvd_of_mod_eq_zero (by rw [hm, Nat.mod_self])
  have := (Nat.prime_dvd_prime_iff_eq hE1 hy).mp hd
  omega

/-- The added facts for a fixed collision with `e < f`. -/
private theorem lp3_core {N q s p r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hsN : s ∈ N.primeFactors)
    (hσs : σ 1 (s ^ N.factorization s) = q) (hes : Even (N.factorization s))
    (hes2 : 2 ≤ N.factorization s) (hpN : p ∈ N.primeFactors) (hpq : p ≠ q)
    (hrN : r ∈ N.primeFactors) (hrq : r ≠ q)
    (hσp : σ 1 (p ^ N.factorization p) = s) (hσr : σ 1 (r ^ N.factorization r) = s)
    (hlt : N.factorization p < N.factorization r)
    (hk : (N.factorization s + 1).Prime) (hm : (N.factorization p + 1).Prime)
    (hn : (N.factorization r + 1).Prime) :
    Even (N.factorization p) ∧ Even (N.factorization r) ∧ 2 ≤ N.factorization p ∧
      2 * (N.factorization p + 1) * (N.factorization r + 1) ∣ s - 1 ∧
      2 * (N.factorization s + 1) ∣ q - 1 ∧
      q ≡ N.factorization s + 1 [MOD 2 * (N.factorization p + 1) * (N.factorization r + 1)] ∧
      (N.factorization s % 4 = 0 ∨ (p % 4 = 1 ∧ r % 4 = 1 ∧ N.factorization p % 4 = 2 ∧
        N.factorization r % 4 = 2)) ∧
      2 * (N.factorization p + 1) * (N.factorization r + 1) + 1 ≤ s ∧ r < p ∧
      p ^ N.factorization p < s ∧ s < p ^ (N.factorization p + 1) ∧
      r ^ N.factorization r < s ∧ s < r ^ (N.factorization r + 1) ∧
      s ^ N.factorization s < q ∧ q < s ^ (N.factorization s + 1) ∧
      p % (N.factorization p + 1) ≠ 1 ∧ r % (N.factorization r + 1) ≠ 1 ∧
      s % (N.factorization s + 1) ≠ 1 := by
  have hodd2 : ∀ x ∈ N.primeFactors, x ≠ 2 := fun x hx h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hx)
  have hs1 := Nat.prime_of_mem_primeFactors hsN
  have hp1 := Nat.prime_of_mem_primeFactors hpN
  have hr1 := Nat.prime_of_mem_primeFactors hrN
  have hs2 := hodd2 s hsN
  have hp2 := hodd2 p hpN
  have hr2 := hodd2 r hrN
  have hevp := even_factorization_of_ne h hq hodd hp1 hpq
  have hevr := even_factorization_of_ne h hq hodd hr1 hrq
  have hpe0 : N.factorization p ≠ 0 :=
    Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hpN)
  have hq4 := (special_mod_four h hq hodd).1
  set e := N.factorization p with he
  set f := N.factorization r with hf
  set g := N.factorization s with hg
  have he2 : 2 ≤ e := by obtain ⟨j, hj⟩ := hevp; omega
  have hmd := succ_dvd_sub_one_of_sigma_prime_pow_eq hp1 hs1 hm hσp
  have hnd := succ_dvd_sub_one_of_sigma_prime_pow_eq hr1 hs1 hn hσr
  have hkd := succ_dvd_sub_one_of_sigma_prime_pow_eq hs1 hq hk hσs
  have hm2 : e + 1 ≠ 2 := by omega
  have hn2 : f + 1 ≠ 2 := by omega
  have hk2 : g + 1 ≠ 2 := by omega
  have hcop : Nat.Coprime (e + 1) (f + 1) := (Nat.coprime_primes hm hn).mpr (by omega)
  have h2m : Nat.Coprime 2 (e + 1) := (Nat.coprime_primes Nat.prime_two hm).mpr (Ne.symm hm2)
  have h2n : Nat.Coprime 2 (f + 1) := (Nat.coprime_primes Nat.prime_two hn).mpr (Ne.symm hn2)
  have h2k : Nat.Coprime 2 (g + 1) := (Nat.coprime_primes Nat.prime_two hk).mpr (Ne.symm hk2)
  have hsodd : s % 2 = 1 := Nat.odd_iff.mp (hs1.odd_of_ne_two hs2)
  have hs3 : 3 ≤ s := by have := hs1.two_le; omega
  have hD : 2 * (e + 1) * (f + 1) ∣ s - 1 := by
    rw [mul_assoc]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.mul_right h2m h2n)
      (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hmd hnd)
  have hK : 2 * (g + 1) ∣ q - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd h2k (Nat.dvd_of_mod_eq_zero (by omega)) hkd
  have hsmod : s ≡ 1 [MOD 2 * (e + 1) * (f + 1)] :=
    ((Nat.modEq_iff_dvd' hs1.one_lt.le).mpr hD).symm
  have hqk := sigma_prime_pow_modEq_succ hs1 hsmod g
  rw [hσs] at hqk
  have hmod4 : g % 4 = 0 ∨ (p % 4 = 1 ∧ r % 4 = 1 ∧ e % 4 = 2 ∧ f % 4 = 2) := by
    rcases sigma_prime_pow_even_mod_four hs1 hs2 hes with ⟨hs4, -⟩ | ⟨-, hq'⟩
    · right
      rcases sigma_prime_pow_even_mod_four hp1 hp2 hevp with ⟨-, h1⟩ | ⟨hp4, h1⟩ <;>
      rcases sigma_prime_pow_even_mod_four hr1 hr2 hevr with ⟨-, h2⟩ | ⟨hr4, h2⟩ <;>
      rw [hσp] at h1 <;> rw [hσr] at h2 <;> omega
    · left
      rw [hσs] at hq'
      omega
  have hsize : 2 * (e + 1) * (f + 1) + 1 ≤ s := by
    have := Nat.le_of_dvd (by omega) hD
    omega
  obtain ⟨hp3, hp4⟩ := pow_lt_sigma_prime_pow_lt hp1 hpe0
  obtain ⟨hr3, hr4⟩ := pow_lt_sigma_prime_pow_lt hr1 (show f ≠ 0 by omega)
  obtain ⟨hs5, hs6⟩ := pow_lt_sigma_prime_pow_lt hs1 (show g ≠ 0 by omega)
  rw [hσp] at hp3 hp4
  rw [hσr] at hr3 hr4
  rw [hσs] at hs5 hs6
  have hrp : r < p := by
    by_contra hle
    push Not at hle
    have h1 := Nat.pow_le_pow_left hle (e + 1)
    have h2 := Nat.pow_le_pow_right hr1.pos (show e + 1 ≤ f by omega)
    omega
  have hmlt : e + 1 < s := by have := Nat.le_of_dvd (by omega) hmd; omega
  have hnlt : f + 1 < s := by have := Nat.le_of_dvd (by omega) hnd; omega
  have hklt : g + 1 < q := by
    have := hq.two_le
    have := Nat.le_of_dvd (by omega) hkd
    omega
  exact ⟨hevp, hevr, he2, hD, hK, hqk, hmod4, hsize, hrp, hp3, hp4, hr3, hr4, hs5, hs6,
    mod_succ_ne_one_of_sigma_prime_pow_eq hp1 hs1 hm hσp hmlt,
    mod_succ_ne_one_of_sigma_prime_pow_eq hr1 hs1 hn hσr hnlt,
    mod_succ_ne_one_of_sigma_prime_pow_eq hs1 hq hk hσs hklt⟩

/-- **Structure of the forced collision.** Let `N` be an odd perfect number and `q` its special
prime. If the full divisor sum `σ(p ^ e_p)` is prime for every prime factor `p ≠ q`, there are
ordinary primes `s`, `p ≠ r` with `σ(s ^ g) = q`, `s ∤ σ(q ^ a)`, `σ(p ^ e) = σ(r ^ f) = s`,
`e < f` (`e = e_p`, `f = e_r`, `g = e_s`, all even, `e, g ≥ 2`), prime indices `m = e + 1`,
`n = f + 1`, `k = g + 1`, and moreover: `2 m n ∣ s - 1`, `2 k ∣ q - 1`, `q ≡ k (mod 2 m n)`,
`g ≡ 0 (mod 4)` or (`p ≡ r ≡ 1 (mod 4)` and `e ≡ f ≡ 2 (mod 4)`), `s ≥ 2 m n + 1`, `r < p`,
`p ^ e < s < p ^ m`, `r ^ f < s < r ^ n`, `s ^ g < q < s ^ k`, and `p ≢ 1 (mod m)`,
`r ≢ 1 (mod n)`, `s ≢ 1 (mod k)`. The primality of all ordinary full divisor sums is a case
hypothesis, not known to hold for a hypothetical odd perfect number. Whether this result is in
the literature was not verified. -/
theorem prime_sigma_collision_structure {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hP : ∀ p ∈ N.primeFactors, p ≠ q → (σ 1 (p ^ N.factorization p)).Prime) :
    ∃ s p r : ℕ, s ∈ N.primeFactors ∧ s ≠ q ∧ σ 1 (s ^ N.factorization s) = q ∧
      ¬ s ∣ σ 1 (q ^ N.factorization q) ∧ Even (N.factorization s) ∧
      2 ≤ N.factorization s ∧
      p ∈ N.primeFactors ∧ p ≠ q ∧ r ∈ N.primeFactors ∧ r ≠ q ∧ p ≠ r ∧
      σ 1 (p ^ N.factorization p) = s ∧ σ 1 (r ^ N.factorization r) = s ∧
      N.factorization p < N.factorization r ∧
      (N.factorization s + 1).Prime ∧ (N.factorization p + 1).Prime ∧
      (N.factorization r + 1).Prime ∧
      Even (N.factorization p) ∧ Even (N.factorization r) ∧ 2 ≤ N.factorization p ∧
      2 * (N.factorization p + 1) * (N.factorization r + 1) ∣ s - 1 ∧
      2 * (N.factorization s + 1) ∣ q - 1 ∧
      q ≡ N.factorization s + 1 [MOD 2 * (N.factorization p + 1) * (N.factorization r + 1)] ∧
      (N.factorization s % 4 = 0 ∨ (p % 4 = 1 ∧ r % 4 = 1 ∧ N.factorization p % 4 = 2 ∧
        N.factorization r % 4 = 2)) ∧
      2 * (N.factorization p + 1) * (N.factorization r + 1) + 1 ≤ s ∧ r < p ∧
      p ^ N.factorization p < s ∧ s < p ^ (N.factorization p + 1) ∧
      r ^ N.factorization r < s ∧ s < r ^ (N.factorization r + 1) ∧
      s ^ N.factorization s < q ∧ q < s ^ (N.factorization s + 1) ∧
      p % (N.factorization p + 1) ≠ 1 ∧ r % (N.factorization r + 1) ≠ 1 ∧
      s % (N.factorization s + 1) ≠ 1 := by
  obtain ⟨s, p, r, hsN, hsq, hσs, hnd, hes, hes2, hpN, hpq, hrN, hrq, hpr, hσp, hσr, hne,
    hk, hm, hn⟩ := exists_prime_sigma_collision_prime_index h hq hodd hP
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨s, p, r, hsN, hsq, hσs, hnd, hes, hes2, hpN, hpq, hrN, hrq, hpr, hσp, hσr, hlt,
      hk, hm, hn, lp3_core h hq hodd hsN hσs hes hes2 hpN hpq hrN hrq hσp hσr hlt hk hm hn⟩
  · exact ⟨s, r, p, hsN, hsq, hσs, hnd, hes, hes2, hrN, hrq, hpN, hpq, Ne.symm hpr, hσr, hσp,
      hlt, hk, hn, hm, lp3_core h hq hodd hsN hσs hes hes2 hrN hrq hpN hpq hσr hσp hlt hk hn hm⟩

/-- The odd prime base case of the Goormaghtigh conjecture: for distinct odd primes `x`, `y`
and exponents `3 ≤ m ≠ n`, `(x ^ m - 1) / (x - 1) ≠ (y ^ n - 1) / (y - 1)`, written with
`σ(x ^ (m - 1)) = 1 + x + ... + x ^ (m - 1)`. This is an open statement, a definition only,
never assumed as an axiom. Remark on the literature, not a theorem: the two known solutions
`31` and `8191` of the full Goormaghtigh equation both have base `2`, so the odd prime base
case has no known solution. -/
def GoormaghtighOddPrime : Prop :=
  ∀ x y m n : ℕ, x.Prime → y.Prime → x ≠ 2 → y ≠ 2 → x ≠ y → 3 ≤ m → 3 ≤ n → m ≠ n →
    σ 1 (x ^ (m - 1)) ≠ σ 1 (y ^ (n - 1))

/-- The restriction of `GoormaghtighOddPrime` to the shape of the forced collision: prime
exponents `m`, `n` (so `m - 1`, `n - 1` are even and `gcd(m - 1, n - 1) ≥ 2`) and a prime
common value. An open statement, a definition only, never assumed as an axiom. -/
def GoormaghtighOddPrimeIndex : Prop :=
  ∀ x y m n : ℕ, x.Prime → y.Prime → x ≠ 2 → y ≠ 2 → x ≠ y → m.Prime → n.Prime → 3 ≤ m →
    3 ≤ n → m ≠ n → Even (m - 1) → Even (n - 1) → (σ 1 (x ^ (m - 1))).Prime →
      σ 1 (x ^ (m - 1)) ≠ σ 1 (y ^ (n - 1))

/-- `GoormaghtighOddPrime` implies its restriction `GoormaghtighOddPrimeIndex`. -/
theorem goormaghtighOddPrimeIndex_of_goormaghtighOddPrime (H : GoormaghtighOddPrime) :
    GoormaghtighOddPrimeIndex :=
  fun x y m n hx hy hx2 hy2 hxy _ _ hm hn hmn _ _ _ => H x y m n hx hy hx2 hy2 hxy hm hn hmn

/-- **Conditional corollary, restricted form.** This is a conditional statement: it assumes the
open statement `GoormaghtighOddPrimeIndex` as an explicit hypothesis. Under it, for an odd
perfect number `N` with special prime `q`, some ordinary prime factor `p` has `σ(p ^ e_p)` not
prime. Any future proof of the Goormaghtigh equation for odd prime bases, prime exponents
and a prime common value (here `gcd(m - 1, n - 1) ≥ 2`) can be plugged in. -/
theorem exists_not_prime_sigma_of_goormaghtighOddPrimeIndex (H : GoormaghtighOddPrimeIndex)
    {N q : ℕ} (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    ∃ p ∈ N.primeFactors, p ≠ q ∧ ¬ (σ 1 (p ^ N.factorization p)).Prime := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, p, r, hsN, hsq, -, -, -, -, hpN, -, hrN, -, hpr, hσp, hσr, hlt, -, hm, hn, hevp,
    hevr, he2, -⟩ := prime_sigma_collision_structure h hq hodd hcon
  have hodd2 : ∀ x ∈ N.primeFactors, x ≠ 2 := fun x hx h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hx)
  refine H p r (N.factorization p + 1) (N.factorization r + 1) (Nat.prime_of_mem_primeFactors hpN)
    (Nat.prime_of_mem_primeFactors hrN) (hodd2 p hpN) (hodd2 r hrN) hpr hm hn (by omega)
    (by omega) (by omega) (by simpa using hevp) (by simpa using hevr) ?_ ?_
  · simp only [Nat.add_sub_cancel]
    rw [hσp]
    exact Nat.prime_of_mem_primeFactors hsN
  · simp only [Nat.add_sub_cancel]
    rw [hσp, hσr]

/-- **Conditional corollary.** This is a conditional statement: it assumes the open statement
`GoormaghtighOddPrime` (the odd prime base case of the Goormaghtigh conjecture) as an explicit
hypothesis. Under it, for an odd perfect number `N` with special prime `q`, some ordinary prime
factor `p` has `σ(p ^ e_p)` not prime. -/
theorem exists_not_prime_sigma_of_goormaghtigh (H : GoormaghtighOddPrime) {N q : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    ∃ p ∈ N.primeFactors, p ≠ q ∧ ¬ (σ 1 (p ^ N.factorization p)).Prime :=
  exists_not_prime_sigma_of_goormaghtighOddPrimeIndex
    (goormaghtighOddPrimeIndex_of_goormaghtighOddPrime H) h hq hodd

/-- **Capacity for a common index divisor.** For an odd perfect number `N` and `d ≥ 3`, the
number of prime factors `p` of `N` with `d ∣ e_p + 1` is at most the sum of the exponents `e_t`
over the prime factors `t` of `N` with `d ∣ t - 1`. Whether this is in the literature was not
verified. -/
theorem card_filter_dvd_succ_le_sum {N : ℕ} (h : OddPerfect N) {d : ℕ} (hd : 3 ≤ d) :
    (N.primeFactors.filter (fun p => d ∣ N.factorization p + 1)).card ≤
      ∑ t ∈ N.primeFactors.filter (fun t => d ∣ t - 1), N.factorization t := by
  set A := N.primeFactors.filter (fun p => d ∣ N.factorization p + 1)
  have key := sum_card_le_sum_min_compatible h (A := A) (Finset.filter_subset _ _)
    (D := fun _ => {d}) (fun p hp d' hd' => by
      rw [Finset.mem_singleton] at hd'
      rw [hd']
      exact ⟨hd, (Finset.mem_filter.mp hp).2⟩)
  simp only [Finset.card_singleton, Finset.sum_const, smul_eq_mul, mul_one] at key
  refine key.trans ?_
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun t _ => ?_
  split_ifs with ht
  · exact min_le_left _ _
  · have : compatible A (fun _ => {d}) t = ∅ := by
      rw [compatible, Finset.filter_eq_empty_iff]
      rintro p - ⟨-, d', hd', hdt⟩
      rw [Finset.mem_singleton] at hd'
      exact ht (hd' ▸ hdt)
    simp [this]

/-- **Capacity for the common divisor family.** If `d ≥ 3` divides the index `e_p + 1` of every
prime factor `p ≠ q` of an odd perfect number `N`, then `ω N - 1` is at most the sum of the
exponents `e_t` over the prime factors `t` of `N` with `d ∣ t - 1`. Whether this is in the
literature was not verified. -/
theorem card_sub_one_le_sum_of_forall_dvd {N : ℕ} (h : OddPerfect N) {q d : ℕ} (hd : 3 ≤ d)
    (hall : ∀ p ∈ N.primeFactors, p ≠ q → d ∣ N.factorization p + 1) :
    ω N - 1 ≤ ∑ t ∈ N.primeFactors.filter (fun t => d ∣ t - 1), N.factorization t := by
  refine le_trans ?_ (card_filter_dvd_succ_le_sum h hd)
  rw [cardDistinctFactors_eq_card_primeFactors]
  have hsub : N.primeFactors.erase q ⊆
      N.primeFactors.filter (fun p => d ∣ N.factorization p + 1) := fun p hp => by
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    exact Finset.mem_filter.mpr ⟨hpN, hall p hpN hpq⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.pred_card_le_card_erase (s := N.primeFactors) (a := q)
  omega

end OddPerfect

#print axioms OddPerfect.succ_dvd_sub_one_of_sigma_prime_pow_eq
#print axioms OddPerfect.pow_lt_sigma_prime_pow_lt
#print axioms OddPerfect.sigma_prime_pow_mod_four_of_three
#print axioms OddPerfect.sigma_prime_pow_even_mod_four
#print axioms OddPerfect.mod_succ_ne_one_of_sigma_prime_pow_eq
#print axioms OddPerfect.prime_sigma_collision_structure
#print axioms OddPerfect.goormaghtighOddPrimeIndex_of_goormaghtighOddPrime
#print axioms OddPerfect.exists_not_prime_sigma_of_goormaghtighOddPrimeIndex
#print axioms OddPerfect.exists_not_prime_sigma_of_goormaghtigh
#print axioms OddPerfect.card_filter_dvd_succ_le_sum
#print axioms OddPerfect.card_sub_one_le_sum_of_forall_dvd
