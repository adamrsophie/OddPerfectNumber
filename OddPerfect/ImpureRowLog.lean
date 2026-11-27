import OddPerfect.ImpureRowBase
import OddPerfect.UpperBound
import OddPerfect.OmegaSevenFinal
import OddPerfect.TwoExceptionsUniform

/-!
# An explicit bound for the number of impure rows under a common index prime

Let `N` be an odd perfect number with special prime `q` and `l` a prime dividing every ordinary
index `e_p + 1` (`p ≠ q` a prime factor of `N`). If every ordinary row `σ(p ^ e_p)` with `p`
outside a finite set `M` is a prime power, then `l - 1 < 16 ^ (M.card + 1)`
(`index_pred_lt_sixteen_pow_of_pure_outside`). So for `16 ^ K < l` at least `K` ordinary rows
are impure (`card_le_of_pure_outside_of_sixteen_pow_lt`). This is an explicit form of
`exists_index_bound_of_impure_rows`, whose bound was not explicit.

Put `X = insert q M` and `s = M.card + 1`. Every prime factor `p ∉ X` has index `l` and a row
`∑ i < l, p ^ i = r ^ w` with `r ∈ X`, `r ≠ l`. Two such primes `p < p'` with the same receiver
satisfy `p ^ (l - 1) < p'` (`pow_lt_of_common_receiver_power`), so a class of `m` of them
reaches `3 ^ ((l - 1) ^ (m - 1))` and `N ≥ 3 ^ ((l - 1) ^ m)`, while `ω(N) ≤ s (m + 1)`.
With `N < 2 ^ (4 ^ ω(N))` this gives `(l - 1) ^ m < (16 ^ s) ^ m`.

Restricted result; the common index family is not excluded; published method, see below;
novelty not verified. The odd perfect number conjecture remains open.

Method. The count of monomials `p ^ i * p' ^ j` below a prime power modulus, all of them roots
of `X ^ l = 1`, is Lemma 3.1 of T. Yamada, On finiteness of odd superperfect numbers
(arXiv 0803.0437v7). A gap of this kind between two primes with a common dominant receiver is
Lemma 3.2 there (with other constants), and the split of the sources into classes by dominant
receiver is the proof of Lemma 3.3 there. That paper does not state the theorems of this
module; no other source was checked.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.RowLog

open OddPerfect.ExcUniform

/-- A prime factor outside `insert q M` has index `l` and a pure row of length `l` whose
receiver lies in `insert q M` and differs from `l`. -/
theorem source {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) {M : Finset ℕ}
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) :
    ∀ p ∈ N.primeFactors, p ∉ insert q M → N.factorization p = l - 1 ∧
      ∃ r ∈ insert q M, r.Prime ∧ r ≠ l ∧ ∃ w, ∑ i ∈ Finset.range l, p ^ i = r ^ w := by
  intro p hp hpX
  have hqX : q ∈ insert q M := Finset.mem_insert_self q M
  have hpq : p ≠ q := fun e => hpX (e ▸ hqX)
  have hpM : p ∉ M := fun e => hpX (Finset.mem_insert_of_mem e)
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
  have he0 : N.factorization p ≠ 0 :=
    (hp'.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)).ne'
  obtain ⟨r0, w0, hr0, hrow0⟩ := hM p hp hpq hpM
  have hpr := prime_succ_of_sigma_prime_pow_eq_prime_pow hp' hp2
    (even_factorization_of_ne h hq hodd hp' hpq) he0 hr0 hrow0
  have he : N.factorization p + 1 = l :=
    ((Nat.prime_dvd_prime_iff_eq hl hpr).mp (hcomp p hp hpq)).symm
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  refine ⟨by omega, ?_⟩
  obtain ⟨r, hrX, w, hr, hrow⟩ := impureRow_cover h hq hodd hl hl2 hqX
    (fun p hp hpX => hcomp p hp (fun e => hpX (e ▸ hqX)))
    (fun p hp hpX => hM p hp (fun e => hpX (e ▸ hqX))
      (fun e => hpX (Finset.mem_insert_of_mem e))) p hp hpX
  have hsig : σ 1 (p ^ N.factorization p) = r ^ w := by
    rw [sigma_one_apply_prime_pow hp', he]
    exact hrow
  have hmod := receiver_mod_index_of_pure hp' hp2 (by omega) hr hsig
  rw [he] at hmod
  refine ⟨r, hrX, hr, ?_, w, hrow⟩
  intro e
  rw [e, Nat.mod_self] at hmod
  omega

/-- A set of numbers at least `3` in which `p < p'` forces `p ^ k < p'`, with `n + 1`
elements, has an element at least `3 ^ (k ^ n)`. -/
theorem chain_ge (k : ℕ) : ∀ (n : ℕ) (S : Finset ℕ), S.card = n + 1 → (∀ p ∈ S, 3 ≤ p) →
    (∀ p ∈ S, ∀ p' ∈ S, p < p' → p ^ k < p') → ∃ p ∈ S, 3 ^ (k ^ n) ≤ p := by
  intro n
  induction n with
  | zero =>
    intro S hS h3 _
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    refine ⟨p, hp, ?_⟩
    rw [pow_zero, pow_one]
    exact h3 p hp
  | succ n ih =>
    intro S hS h3 hg
    have hne : S.Nonempty := Finset.card_pos.mp (show 0 < S.card by omega)
    have hx := Finset.max'_mem S hne
    obtain ⟨p, hp, hpb⟩ := ih (S.erase (S.max' hne))
      (by rw [Finset.card_erase_of_mem hx]; omega)
      (fun p hp => h3 p (Finset.mem_of_mem_erase hp))
      (fun p hp p' hp' hlt => hg p (Finset.mem_of_mem_erase hp) p'
        (Finset.mem_of_mem_erase hp') hlt)
    have hpS := Finset.mem_of_mem_erase hp
    have hpx : p < S.max' hne :=
      lt_of_le_of_ne (Finset.le_max' S p hpS) (Finset.ne_of_mem_erase hp)
    refine ⟨S.max' hne, hx, ?_⟩
    calc 3 ^ (k ^ (n + 1)) = (3 ^ (k ^ n)) ^ k := by rw [pow_succ, pow_mul]
      _ ≤ p ^ k := Nat.pow_le_pow_left hpb k
      _ ≤ S.max' hne := (hg p hpS _ hx hpx).le

/-- `3 ^ a < 2 ^ b` forces `a < b`. -/
theorem lt_of_three_pow_lt {a b : ℕ} (h : 3 ^ a < 2 ^ b) : a < b := by
  by_contra hab
  push Not at hab
  have e1 : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hab
  have e2 : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
  omega

end OddPerfect.RowLog

namespace OddPerfect

open OddPerfect.ExcUniform OddPerfect.RowLog

/-- Let `N` be an odd perfect number with special prime `q` and `l` a prime dividing every
ordinary index. If every ordinary row `σ(p ^ e_p)` with `p ∉ M` is a prime power, then
`l - 1 < 16 ^ (M.card + 1)`. Restricted result; an explicit form of
`exists_index_bound_of_impure_rows` (the bound there was not explicit); the common index family
is not excluded; published method, see header; novelty not verified. The odd perfect number
conjecture remains open. -/
theorem index_pred_lt_sixteen_pow_of_pure_outside {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) :
    l - 1 < 16 ^ (M.card + 1) := by
  classical
  rcases hl.eq_two_or_odd with hl2 | hlo
  · have := Nat.one_lt_pow (n := M.card + 1) (a := 16) (by omega) (by norm_num)
    omega
  have hl2 : l ≠ 2 := by omega
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  set s := M.card + 1 with hs
  set X := insert q M with hXdef
  have hqX : q ∈ X := Finset.mem_insert_self q M
  have hX : X.card ≤ s := Finset.card_insert_le _ _
  have hsrc := source h hq hodd hl hl2 hcomp hM
  set P := N.primeFactors.filter (fun p => p ∉ X) with hPdef
  have hPm : ∀ p ∈ P, p ∈ N.primeFactors ∧ p ∉ X := fun p hp => Finset.mem_filter.mp hp
  have hexp : ∀ p ∈ P, N.factorization p = l - 1 := fun p hp =>
    (hsrc p (hPm p hp).1 (hPm p hp).2).1
  have hsrc' : ∀ p ∈ P, ∃ r, r ∈ X ∧ r.Prime ∧ r ≠ l ∧
      ∃ w, ∑ i ∈ Finset.range l, p ^ i = r ^ w := fun p hp => by
    obtain ⟨-, r, hrX, hr, hrl, w, hw⟩ := hsrc p (hPm p hp).1 (hPm p hp).2
    exact ⟨r, hrX, hr, hrl, w, hw⟩
  choose! rcv hrcv using hsrc'
  have hP3 : ∀ p ∈ P, 3 ≤ p := fun p hp => by
    have hpN := (hPm p hp).1
    have h1 := TwoExcGen.odd_of_mem h hpN
    have h2 := (Nat.prime_of_mem_primeFactors hpN).two_le
    omega
  -- two sources with one receiver are far apart
  have hcount : l < ∑ j ∈ Finset.range ((l - 1) / (l - 1) + 1), (l - 1 - (l - 1) * j + 1) := by
    rw [Nat.div_self (by omega), Finset.sum_range_succ, Finset.sum_range_one]
    omega
  have hgap : ∀ p ∈ P, ∀ p' ∈ P, rcv p = rcv p' → p < p' → p ^ (l - 1) < p' := by
    intro p hp p' hp' hr hlt
    obtain ⟨-, hrP, hrl, w, hw⟩ := hrcv p hp
    obtain ⟨-, -, -, w', hw'⟩ := hrcv p' hp'
    rw [← hr] at hw'
    have hpP := Nat.prime_of_mem_primeFactors (hPm p hp).1
    have hp'P := Nat.prime_of_mem_primeFactors (hPm p' hp').1
    have hx := pow_lt_R hl.two_le (show 1 ≤ p by have := hP3 p hp; omega)
    have hx' := pow_lt_R hl.two_le (show 1 ≤ p' by have := hP3 p' hp'; omega)
    have hpp : p ^ (l - 1) ≤ p' ^ (l - 1) := Nat.pow_le_pow_left hlt.le _
    rw [hw] at hx
    rw [hw'] at hx'
    exact pow_lt_of_common_receiver_power hl hrP hrl hpP hp'P hlt
      ⟨1, by rw [hw, mul_one]⟩ ⟨1, by rw [hw', mul_one]⟩ hx (by omega) hcount
  -- the receiver classes
  have hCm : ∀ r ∈ X, (P.filter (fun p => rcv p = r)).card ≤
      X.sup (fun r => (P.filter (fun p => rcv p = r)).card) := fun r hr =>
    Finset.le_sup (f := fun r => (P.filter (fun p => rcv p = r)).card) hr
  set m := X.sup (fun r => (P.filter (fun p => rcv p = r)).card) with hmdef
  have hPcard : P.card ≤ s * m := by
    have hsub : P ⊆ X.biUnion (fun r => P.filter (fun p => rcv p = r)) := by
      intro p hp
      rw [Finset.mem_biUnion]
      exact ⟨rcv p, (hrcv p hp).1, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
    calc P.card ≤ (X.biUnion (fun r => P.filter (fun p => rcv p = r))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ r ∈ X, (P.filter (fun p => rcv p = r)).card := Finset.card_biUnion_le
      _ ≤ X.card • m := Finset.sum_le_card_nsmul _ _ _ hCm
      _ = X.card * m := smul_eq_mul _ _
      _ ≤ s * m := Nat.mul_le_mul_right m hX
  have hω : N.primeFactors.card ≤ s + s * m := by
    have hsub : N.primeFactors ⊆ X ∪ P := by
      intro p hp
      by_cases hpX : p ∈ X
      · exact Finset.mem_union_left _ hpX
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hpX⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le X P)
    omega
  -- the size of `N`
  set m' := max m 1 with hm'def
  have hm'1 : 1 ≤ m' := le_max_right _ _
  have hmm' : m ≤ m' := le_max_left _ _
  have hN0 : 0 < N := h.pos
  have hsize : 3 ^ ((l - 1) ^ m') ≤ N := by
    by_cases hm : m = 0
    · have hm1 : m' = 1 := by omega
      rw [hm1, pow_one]
      obtain ⟨p, hp, hpq⟩ := Finset.exists_mem_ne
        (show 1 < N.primeFactors.card by have := seven_le_card_primeFactors h; omega) q
      have hpP := Nat.prime_of_mem_primeFactors hp
      have h1 := TwoExcGen.odd_of_mem h hp
      have h2 := hpP.two_le
      have hle := Nat.le_of_dvd (by omega) (hcomp p hp hpq)
      calc 3 ^ (l - 1) ≤ p ^ (l - 1) := Nat.pow_le_pow_left (by omega) _
        _ ≤ p ^ N.factorization p := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ N := Nat.le_of_dvd hN0 (Nat.ordProj_dvd N p)
    · have hmm : m' = m := by omega
      rw [hmm]
      obtain ⟨r0, hr0X, hr0⟩ := Finset.exists_mem_eq_sup X ⟨q, hqX⟩
        (fun r => (P.filter (fun p => rcv p = r)).card)
      have hr0' : (P.filter (fun p => rcv p = r0)).card = m := hr0.symm
      obtain ⟨p, hp, hpb⟩ := chain_ge (l - 1) (m - 1) (P.filter (fun p => rcv p = r0))
        (by omega)
        (fun p hp => hP3 p (Finset.mem_filter.mp hp).1)
        (fun p hp p' hp' hlt => hgap p (Finset.mem_filter.mp hp).1 p'
          (Finset.mem_filter.mp hp').1
          ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm) hlt)
      have hpP := (Finset.mem_filter.mp hp).1
      have hm1 : (l - 1) ^ m = (l - 1) ^ (m - 1) * (l - 1) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      calc 3 ^ ((l - 1) ^ m) = (3 ^ ((l - 1) ^ (m - 1))) ^ (l - 1) := by rw [hm1, pow_mul]
        _ ≤ p ^ (l - 1) := Nat.pow_le_pow_left hpb _
        _ = p ^ N.factorization p := by rw [hexp p hpP]
        _ ≤ N := Nat.le_of_dvd hN0 (Nat.ordProj_dvd N p)
  -- the upper bound for `N`
  have hub := lt_two_pow_four_pow h
  have hlt4 : (l - 1) ^ m' < 4 ^ N.primeFactors.card := lt_of_three_pow_lt (by omega)
  have hsm : s ≤ s * m' := Nat.le_mul_of_pos_right s hm'1
  have hsm2 : s * m ≤ s * m' := Nat.mul_le_mul_left s hmm'
  have e2 : 2 * s * m' = s * m' + s * m' := by ring
  have h4 : 4 ^ N.primeFactors.card ≤ 4 ^ (2 * s * m') :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e16 : (16 ^ s) ^ m' = 4 ^ (2 * s * m') := by
    rw [← pow_mul, show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, mul_assoc]
  by_contra hge
  push Not at hge
  have := Nat.pow_le_pow_left hge m'
  omega

/-- Let `N` be an odd perfect number with special prime `q` and `l` a prime dividing every
ordinary index, with `16 ^ K < l`. Every set `M` outside of which all ordinary rows
`σ(p ^ e_p)` are prime powers has at least `K` elements; so at least `K` ordinary rows are
impure. Restricted result; an explicit form of `exists_index_bound_of_impure_rows` (the bound
there was not explicit); the common index family is not excluded; published method, see
header; novelty not verified. The odd perfect number conjecture remains open. -/
theorem card_le_of_pure_outside_of_sixteen_pow_lt {N q l K : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hK : 16 ^ K < l)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) :
    K ≤ M.card := by
  by_contra hlt
  push Not at hlt
  have h1 := index_pred_lt_sixteen_pow_of_pure_outside h hq hodd hl hcomp M hM
  have h2 : 16 ^ (M.card + 1) ≤ 16 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end OddPerfect

#print axioms OddPerfect.RowLog.source
#print axioms OddPerfect.RowLog.chain_ge
#print axioms OddPerfect.RowLog.lt_of_three_pow_lt
#print axioms OddPerfect.index_pred_lt_sixteen_pow_of_pure_outside
#print axioms OddPerfect.card_le_of_pure_outside_of_sixteen_pow_lt
