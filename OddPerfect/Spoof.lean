import OddPerfect.Euler
import Mathlib.Tactic.NormNum.Prime
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Defs

/-!
# Spoof odd perfect numbers and local counterexamples

Kernel checked adversarial examples. A spoof factorization (`IsSpoofOddPerfect`) satisfies
the following conditions, with no primality requirement on the bases: bases odd, at least 3,
and pairwise coprime; exponents positive; formal divisor sum equal to twice the value; exactly
one odd exponent, at a base congruent to 1 mod 4, with exponent congruent to 1 mod 4. For
Descartes' spoof the file proves `IsSpoofOddPerfect`, Touchard's congruence, the congruence
`value ≡ 1 (mod 4)`, at least three bases, and formal valuation conservation at every `q`;
so these conditions are satisfiable. It is not a claim that the spoof meets every condition
known for odd perfect numbers. The integer `198585576189 = 3^2 7^2 11^2 13^2 22021` itself has
six distinct prime factors, since `22021 = 19^2 · 61` is composite, and it is not perfect; the
spoof presentation treats `22021` as if it were prime. The second part records small local phenomena that
defeat naive arguments. This file is a regression suite for future arguments.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.Spoof

/-- `geom b e = 1 + b + ... + b ^ e`, by recursion so that the kernel evaluates it. -/
def geom (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => geom b e + b ^ (e + 1)

/-- `geom` agrees with the geometric sum used by mathlib. -/
theorem geom_eq_sum (b e : ℕ) : geom b e = ∑ i ∈ Finset.range (e + 1), b ^ i := by
  induction e with
  | zero => simp [geom]
  | succ e ih => rw [geom, ih, Finset.sum_range_succ _ (e + 1)]

/-- For a prime `p`, the divisor sum of `p ^ e` is `geom p e`. -/
theorem sigma_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) : σ 1 (p ^ e) = geom p e := by
  rw [sigma_one_apply_prime_pow hp, geom_eq_sum]

/-- Formal value `∏ b ^ e` of a spoof factorization. -/
def value (l : List (ℕ × ℕ)) : ℕ := (l.map fun x => x.1 ^ x.2).prod

/-- Formal divisor sum `∏ (1 + b + ... + b ^ e)`, pretending every base is prime. -/
def formalSigma (l : List (ℕ × ℕ)) : ℕ := (l.map fun x => geom x.1 x.2).prod

/-- A selection of conditions on the shape of an odd perfect number, without primality of
the bases: bases odd, at least 3, pairwise coprime; exponents
positive; formal divisor sum equal to twice the value; exactly one odd exponent, at a base
congruent to 1 mod 4 with exponent congruent to 1 mod 4. "Exactly one" is expressed as: some
entry has odd exponent and every entry with odd exponent equals it (entries are distinct
because the bases are pairwise coprime and at least 3). -/
def IsSpoofOddPerfect (l : List (ℕ × ℕ)) : Prop :=
  (∀ x ∈ l, Odd x.1 ∧ 3 ≤ x.1 ∧ 0 < x.2) ∧
  l.Pairwise (fun x y => Nat.Coprime x.1 y.1) ∧
  formalSigma l = 2 * value l ∧
  ∃ x ∈ l, x.2 % 2 = 1 ∧ x.1 % 4 = 1 ∧ x.2 % 4 = 1 ∧ ∀ y ∈ l, y.2 % 2 = 1 → y = x

/-- `IsSpoofOddPerfect` is decidable, so concrete spoofs are checked by `decide`. -/
instance (l : List (ℕ × ℕ)) : Decidable (IsSpoofOddPerfect l) := by
  unfold IsSpoofOddPerfect; infer_instance

/-- Descartes' spoof `3^2 7^2 11^2 13^2 22021`, with `22021 = 19^2 * 61` treated as prime. -/
def descartes : List (ℕ × ℕ) := [(3, 2), (7, 2), (11, 2), (13, 2), (22021, 1)]

/-- The Descartes spoof satisfies `IsSpoofOddPerfect` (kernel checked by `decide`): bases odd,
at least 3, and pairwise coprime; exponents positive; formal divisor sum equal to twice the
value; exactly one odd exponent, at the base `22021 ≡ 1 (mod 4)` with exponent 1. Further facts
proved below are Touchard's congruence (`touchard_descartes`), `value ≡ 1 (mod 4)`
(`value_descartes_mod_four`), at least three bases (`three_le_length_descartes`), and formal
valuation conservation (`valuation_balance_descartes`). The positive integer
`198585576189 = value descartes` has six distinct prime factors, since `22021 = 19^2 · 61` is
composite (`eq_22021`), and it is not perfect (`not_perfect_value_descartes`); the spoof
presentation treats `22021` as if it were prime. -/
theorem isSpoofOddPerfect_descartes : IsSpoofOddPerfect descartes := by decide

/-- If every base is prime and the bases are pairwise distinct, the formal divisor sum is the
true divisor sum of the value. -/
theorem formalSigma_eq_sigma (l : List (ℕ × ℕ)) (hp : ∀ x ∈ l, x.1.Prime)
    (hd : (l.map Prod.fst).Nodup) : formalSigma l = σ 1 (value l) := by
  induction l with
  | nil => simp [formalSigma, value]
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hd
    have hx := hp x (by simp)
    have hcop : Nat.Coprime (x.1 ^ x.2) (value l) := by
      refine Nat.Coprime.pow_left _ (Nat.coprime_list_prod_right_iff.mpr ?_)
      simp only [List.mem_map]
      rintro _ ⟨y, hy, rfl⟩
      refine Nat.Coprime.pow_right _ ((Nat.coprime_primes hx (hp y (by simp [hy]))).mpr ?_)
      rintro h
      exact hd.1 ⟨y, hy, h.symm⟩
    rw [show formalSigma (x :: l) = geom x.1 x.2 * formalSigma l from rfl,
      show value (x :: l) = x.1 ^ x.2 * value l from rfl,
      isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime_pow hx,
      ih (fun y hy => hp y (by simp [hy])) hd.2]

/-- A spoof all of whose bases are prime is a genuine odd perfect number. -/
theorem oddPerfect_of_isSpoofOddPerfect {l : List (ℕ × ℕ)} (h : IsSpoofOddPerfect l)
    (hp : ∀ x ∈ l, x.1.Prime) : OddPerfect (value l) := by
  obtain ⟨hb, hc, hs, -⟩ := h
  have hd : (l.map Prod.fst).Nodup := by
    refine List.pairwise_map.mpr (hc.imp_of_mem fun hx _ hxy he => ?_)
    have := (Nat.coprime_self _).mp (he ▸ hxy)
    have := (hb _ hx).2.1
    omega
  have hodd : Odd (value l) := by
    refine Nat.coprime_two_left.mp (Nat.coprime_list_prod_right_iff.mpr ?_)
    simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_left.mpr (hb x hx).1)
  refine ⟨hodd, (Nat.perfect_iff_sum_divisors_eq_two_mul hodd.pos).mpr ?_⟩
  rw [← sigma_one_apply, ← formalSigma_eq_sigma l hp hd, hs]

/-- Conversely, every odd perfect number comes from a spoof with prime bases: its prime
factorization. -/
theorem exists_spoof_of_oddPerfect {N : ℕ} (h : OddPerfect N) :
    ∃ l, IsSpoofOddPerfect l ∧ (∀ x ∈ l, x.1.Prime) ∧ value l = N := by
  set l := N.primeFactors.toList.map fun p => (p, N.factorization p) with hl
  have hmem : ∀ x ∈ l, x.1 ∈ N.primeFactors ∧ x.2 = N.factorization x.1 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact ⟨Finset.mem_toList.mp hp, rfl⟩
  have hprime : ∀ x ∈ l, x.1.Prime := fun x hx => Nat.prime_of_mem_primeFactors (hmem x hx).1
  have hval : value l = N := by
    rw [value, hl, List.map_map, Finset.prod_map_toList]
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self h.ne_zero]
    rfl
  have hd : (l.map Prod.fst).Nodup := by
    rw [hl, List.map_map]
    simpa [Function.comp_def] using N.primeFactors.nodup_toList
  obtain ⟨q, hq, hqN, hq4, hk, hev⟩ := exists_special_prime h
  refine ⟨l, ⟨fun x hx => ?_, ?_, ?_, ⟨(q, N.factorization q), ?_, by omega, hq4, hk, ?_⟩⟩,
    hprime, hval⟩
  · obtain ⟨hx1, hx2⟩ := hmem x hx
    have hpp := Nat.prime_of_mem_primeFactors hx1
    have hpo : Odd x.1 := h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hx1)
    refine ⟨hpo, ?_, ?_⟩
    · have := hpp.two_le
      have : x.1 ≠ 2 := by rintro h2; rw [h2] at hpo; exact absurd hpo (by decide)
      omega
    · rw [hx2]; exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by simpa using hx1))
  · rw [hl]
    refine List.pairwise_map.mpr (N.primeFactors.nodup_toList.imp_of_mem fun ha hb hab => ?_)
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp ha))
      (Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hb))).mpr hab
  · rw [formalSigma_eq_sigma l hprime hd, hval, h.sigma_eq]
  · exact List.mem_map.mpr ⟨q, Finset.mem_toList.mpr
      (Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩), rfl⟩
  · intro y hy hyo
    obtain ⟨hy1, hy2⟩ := hmem y hy
    have hyq : y.1 = q := by
      by_contra hne
      have := hev _ (Nat.prime_of_mem_primeFactors hy1) hne
      rw [← hy2] at this
      exact absurd hyo (by rw [Nat.even_iff] at this; omega)
    exact Prod.ext hyq (by rw [hy2, hyq])

/-- The conditions of `IsSpoofOddPerfect` are satisfiable without primality of the bases, so
these conditions alone do not imply a contradiction. -/
theorem exists_spoof : ∃ l, IsSpoofOddPerfect l := ⟨descartes, isSpoofOddPerfect_descartes⟩

/-- The last Descartes base is not prime. -/
theorem not_prime_22021 : ¬ Nat.Prime 22021 := by norm_num

/-- The factorization of the last Descartes base. -/
theorem eq_22021 : 22021 = 19 ^ 2 * 61 := by norm_num

/-- The true prime factorization of the Descartes number. -/
def descartesTrue : List (ℕ × ℕ) := [(3, 2), (7, 2), (11, 2), (13, 2), (19, 2), (61, 1)]

/-- The Descartes number is not perfect: its true divisor sum, computed through multiplicativity
on `3^2 7^2 11^2 13^2 19^2 61`, is not twice the number. -/
theorem not_perfect_value_descartes : ¬ (value descartes).Perfect := by
  intro hP
  have hv : value descartes = value descartesTrue := by decide
  have hs := formalSigma_eq_sigma descartesTrue (by simp [descartesTrue]; norm_num) (by decide)
  have h2 := OPNStarter.sigma_eq_two_mul hP
  rw [hv, ← hs] at h2
  exact absurd h2 (by decide)

/-- The Descartes number satisfies Touchard's congruence (it is `≡ 9 (mod 36)`). -/
theorem touchard_descartes : value descartes % 12 = 1 ∨ value descartes % 36 = 9 := by decide

/-- The Descartes number is `≡ 1 (mod 4)`. -/
theorem value_descartes_mod_four : value descartes % 4 = 1 := by decide

/-- The Descartes spoof has at least three bases (it has five). -/
theorem three_le_length_descartes : 3 ≤ descartes.length := by decide

/-- The `q`-adic valuation of a product of nonzero naturals is the sum of the valuations. -/
theorem factorization_list_prod (L : List ℕ) (h : ∀ n ∈ L, n ≠ 0) (q : ℕ) :
    L.prod.factorization q = (L.map fun n => n.factorization q).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hL : ∀ n ∈ L, n ≠ 0 := fun n hn => h n (by simp [hn])
    rw [List.prod_cons, Nat.factorization_mul (h a (by simp))
      (List.prod_ne_zero fun h0 => hL 0 h0 rfl), Finsupp.add_apply, ih hL]
    simp

/-- `geom b e` is positive. -/
theorem geom_pos (b e : ℕ) : 0 < geom b e := by
  induction e with
  | zero => simp [geom]
  | succ e ih => simp only [geom]; omega

/-- Formal valuation conservation: for every spoof and every `q`, the analog of
`OPNStarter.valuation_balance` holds with component sums `geom b e`. It holds for every `q`,
in particular at every base that is actually prime, so this bookkeeping alone cannot rule out a
spoof. -/
theorem valuation_balance {l : List (ℕ × ℕ)} (h : IsSpoofOddPerfect l) (q : ℕ) :
    Nat.factorization 2 q + (value l).factorization q =
      (l.map fun x => (geom x.1 x.2).factorization q).sum := by
  have hv : value l ≠ 0 := List.prod_ne_zero fun h0 => by
    obtain ⟨x, hx, hx0⟩ := List.mem_map.mp h0
    have := (h.1 x hx).2.1
    exact pow_ne_zero _ (by omega : x.1 ≠ 0) hx0
  have hg : ∀ n ∈ l.map (fun x => geom x.1 x.2), n ≠ 0 := by
    simp only [List.mem_map]
    rintro _ ⟨x, -, rfl⟩
    exact (geom_pos _ _).ne'
  rw [← Finsupp.add_apply, ← Nat.factorization_mul two_ne_zero hv, ← h.2.2.1, formalSigma,
    factorization_list_prod _ hg, List.map_map]
  rfl

/-- The Descartes spoof satisfies formal valuation conservation at every `q`, in particular at
its genuinely prime bases `3, 7, 11, 13`. -/
theorem valuation_balance_descartes (q : ℕ) :
    Nat.factorization 2 q + (value descartes).factorization q =
      (descartes.map fun x => (geom x.1 x.2).factorization q).sum :=
  valuation_balance isSpoofOddPerfect_descartes q

/-- `σ(3^2) = 13`. -/
theorem sigma_three_sq : σ 1 (3 ^ 2) = 13 := by rw [sigma_prime_pow (by norm_num)]; decide

/-- `σ(13^2) = 3 * 61`. -/
theorem sigma_thirteen_sq : σ 1 (13 ^ 2) = 3 * 61 := by rw [sigma_prime_pow (by norm_num)]; decide

/-- A genuine 2-cycle at square exponents: `13 ∣ σ(3^2)` and `3 ∣ σ(13^2)`. -/
theorem two_cycle_three_thirteen : 13 ∣ σ 1 (3 ^ 2) ∧ 3 ∣ σ 1 (13 ^ 2) := by
  rw [sigma_three_sq, sigma_thirteen_sq]; decide

/-- If `p` is a prime dividing `a * b * c` with `a, b, c` prime, then `p` is one of them. -/
private lemma prime_dvd_three {p a b c : ℕ} (hp : p.Prime) (ha : a.Prime) (hb : b.Prime)
    (hc : c.Prime) (h : p ∣ a * b * c) : p = a ∨ p = b ∨ p = c := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp ha).mp h)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hb).mp h))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hc).mp h))

/-- `σ(79^2) = 6321 = 3 * 7^2 * 43`. -/
theorem sigma_seventy_nine_sq : σ 1 (79 ^ 2) = 3 * 7 ^ 2 * 43 := by
  rw [sigma_prime_pow (by norm_num)]; decide

/-- Every prime factor of `σ(79^2)` is smaller than `79`. -/
theorem prime_dvd_sigma_seventy_nine_sq_lt {p : ℕ} (hp : p.Prime) (h : p ∣ σ 1 (79 ^ 2)) :
    p < 79 := by
  rw [sigma_seventy_nine_sq, show 3 * 7 ^ 2 * 43 = 3 * 7 * 43 * 7 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases prime_dvd_three hp (by norm_num) (by norm_num) (by norm_num) h with
      rfl | rfl | rfl <;> norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h]; norm_num

/-- `σ(211^2) = 3 * 13 * 31 * 37`. -/
theorem sigma_two_hundred_eleven_sq : σ 1 (211 ^ 2) = 3 * 13 * 31 * 37 := by
  rw [sigma_prime_pow (by norm_num)]; decide

/-- Every prime factor of `σ(211^2)` is smaller than `211`. -/
theorem prime_dvd_sigma_two_hundred_eleven_sq_lt {p : ℕ} (hp : p.Prime)
    (h : p ∣ σ 1 (211 ^ 2)) : p < 211 := by
  rw [sigma_two_hundred_eleven_sq] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases prime_dvd_three hp (by norm_num) (by norm_num) (by norm_num) h with
      rfl | rfl | rfl <;> norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h]; norm_num

/-- `σ(61^2) = 3 * 13 * 97`. -/
theorem sigma_sixty_one_sq : σ 1 (61 ^ 2) = 3 * 13 * 97 := by
  rw [sigma_prime_pow (by norm_num)]; decide

/-- `13` divides `σ(3^2)`, `σ(61^2)`, and `σ(211^2)`: one primitive prime divisor serves several
components. -/
theorem thirteen_dvd_sigma_sq_of_three_sixty_one_two_hundred_eleven :
    13 ∣ σ 1 (3 ^ 2) ∧ 13 ∣ σ 1 (61 ^ 2) ∧ 13 ∣ σ 1 (211 ^ 2) := by
  rw [sigma_three_sq, sigma_sixty_one_sq, sigma_two_hundred_eleven_sq]; decide

/-- The bases `3`, `61`, `211` all have multiplicative order `3` modulo `13`. -/
theorem orderOf_mod_thirteen :
    orderOf (3 : ZMod 13) = 3 ∧ orderOf (61 : ZMod 13) = 3 ∧ orderOf (211 : ZMod 13) = 3 :=
  ⟨orderOf_eq_prime (by decide) (by decide), orderOf_eq_prime (by decide) (by decide),
    orderOf_eq_prime (by decide) (by decide)⟩

/-- `σ(3^4) = 11^2`: a component divisor sum can be a perfect power. -/
theorem sigma_three_pow_four : σ 1 (3 ^ 4) = 11 ^ 2 := by
  rw [sigma_prime_pow (by norm_num)]; decide

/-- `σ(3^4) = 121` is coprime to `13`: `3^2 ∣ N` does not force `13 ∣ N`; the exact exponent
matters. -/
theorem coprime_sigma_three_pow_four_thirteen : Nat.Coprime (σ 1 (3 ^ 4)) 13 := by
  rw [sigma_three_pow_four]; decide

/-- `18^2 + 18 + 1 = 7^3`, so `x^2 + x + 1` can be a perfect cube (here `18` is not prime). -/
theorem eighteen_sq_add : 18 ^ 2 + 18 + 1 = 7 ^ 3 ∧ ¬ Nat.Prime 18 := ⟨by norm_num, by norm_num⟩

end OddPerfect.Spoof

#print axioms OddPerfect.Spoof.geom_eq_sum
#print axioms OddPerfect.Spoof.sigma_prime_pow
#print axioms OddPerfect.Spoof.isSpoofOddPerfect_descartes
#print axioms OddPerfect.Spoof.formalSigma_eq_sigma
#print axioms OddPerfect.Spoof.oddPerfect_of_isSpoofOddPerfect
#print axioms OddPerfect.Spoof.exists_spoof_of_oddPerfect
#print axioms OddPerfect.Spoof.exists_spoof
#print axioms OddPerfect.Spoof.not_prime_22021
#print axioms OddPerfect.Spoof.eq_22021
#print axioms OddPerfect.Spoof.not_perfect_value_descartes
#print axioms OddPerfect.Spoof.touchard_descartes
#print axioms OddPerfect.Spoof.value_descartes_mod_four
#print axioms OddPerfect.Spoof.three_le_length_descartes
#print axioms OddPerfect.Spoof.factorization_list_prod
#print axioms OddPerfect.Spoof.geom_pos
#print axioms OddPerfect.Spoof.valuation_balance
#print axioms OddPerfect.Spoof.valuation_balance_descartes
#print axioms OddPerfect.Spoof.sigma_three_sq
#print axioms OddPerfect.Spoof.sigma_thirteen_sq
#print axioms OddPerfect.Spoof.two_cycle_three_thirteen
#print axioms OddPerfect.Spoof.sigma_seventy_nine_sq
#print axioms OddPerfect.Spoof.prime_dvd_sigma_seventy_nine_sq_lt
#print axioms OddPerfect.Spoof.sigma_two_hundred_eleven_sq
#print axioms OddPerfect.Spoof.prime_dvd_sigma_two_hundred_eleven_sq_lt
#print axioms OddPerfect.Spoof.sigma_sixty_one_sq
#print axioms OddPerfect.Spoof.thirteen_dvd_sigma_sq_of_three_sixty_one_two_hundred_eleven
#print axioms OddPerfect.Spoof.orderOf_mod_thirteen
#print axioms OddPerfect.Spoof.sigma_three_pow_four
#print axioms OddPerfect.Spoof.coprime_sigma_three_pow_four_thirteen
#print axioms OddPerfect.Spoof.eighteen_sq_add
