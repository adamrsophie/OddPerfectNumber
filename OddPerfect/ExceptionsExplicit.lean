import OddPerfect.ImpureRowLog
import OddPerfect.ExceptionsUnboundedBase

/-!
# Any number of exceptions to a common index prime, with an explicit bound

Let `N` be an odd perfect number, `E` a finite set of at most `s` natural numbers and `l` a
prime with `16 ^ s < l`. If every prime factor `p ∉ E` of `N` has `l ∣ e_p + 1` and at least
one prime factor lies outside `E`, then `l ∣ N` (`dvd_of_exceptions_of_sixteen_pow_lt`). This
is an explicit form of `exists_index_bound_of_exceptions`, whose bound was not explicit. For
two and three exceptions the landed modules give the smaller bounds `l ≥ 23` and `l ≥ 359`.
The hypothesis that some prime factor lies outside `E` is needed: with every prime factor in
`E` the index hypothesis is empty. For at most six exceptions it holds automatically, since an
odd perfect number has at least seven prime factors (`dvd_of_six_exceptions_of_lt`).

Write `R(x) = ∑ i < l, x ^ i`, `A = (l - 1) / s` and `G = (A + 1) / (4 s)`, so `G ≥ 4 ^ s`. Every
compatible prime `p` has a receiver `d ∈ E` with `d ^ v_d(R(p)) > p ^ A`; two compatible primes
`p < p'` with one receiver satisfy `p ^ G < p'`. A largest receiver class of `m` primes gives a
prime `p ≥ 3 ^ (G ^ (m - 1))` with exponent at least `l - 1`, so
`3 ^ (G ^ (m - 1) (l - 1)) ≤ N < 2 ^ (4 ^ ω(N))` with `ω(N) ≤ s (m + 1)`, while
`G ^ (m - 1) (l - 1) ≥ (4 ^ s) ^ (m - 1) 16 ^ s = 4 ^ (s (m + 1))`.

Restricted result; published method, see below; novelty not verified. The odd perfect
number conjecture remains open.

Method. The count of monomials `p ^ i * p' ^ j` below a prime power modulus, all of them roots
of `X ^ l = 1`, is Lemma 3.1 of T. Yamada, On finiteness of odd superperfect numbers
(arXiv 0803.0437v7). A gap of this kind between two primes with a common dominant receiver is
Lemma 3.2 there (with other constants), and the split of the sources into classes by dominant
receiver is the proof of Lemma 3.3 there. That paper does not state the theorems of this
module; no other source was checked.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.ExcX

open OddPerfect.TwoExcGen OddPerfect.ExcUniform

/-- `4 s ^ 2 ≤ 4 ^ s` for `s ≥ 1`. -/
theorem four_mul_sq_le_four_pow : ∀ s : ℕ, 1 ≤ s → 4 * s ^ 2 ≤ 4 ^ s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : (n + 1) ^ 2 ≤ 4 * n ^ 2 := by nlinarith [Nat.mul_le_mul hn hn]
    calc 4 * (n + 1) ^ 2 ≤ 4 * (4 * n ^ 2) := Nat.mul_le_mul_left 4 h1
      _ = 4 * n ^ 2 * 4 := by ring
      _ ≤ 4 ^ n * 4 := Nat.mul_le_mul_right 4 ih
      _ = 4 ^ (n + 1) := (pow_succ 4 n).symm

/-- A row whose prime factors lie in a set of at most `s` numbers and which exceeds
`(p ^ A) ^ s` has a prime power part above `p ^ A`. -/
theorem dominant {l p A s : ℕ} {E : Finset ℕ} (hl : 2 ≤ l) (hp : 1 ≤ p) (hAs : A * s ≤ l - 1)
    (hsub : (∑ i ∈ Finset.range l, p ^ i).primeFactors ⊆ E) (hE : E.card ≤ s) :
    ∃ d, p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d := by
  have hR0 : (∑ i ∈ Finset.range l, p ^ i) ≠ 0 := by
    have := pow_lt_R hl hp
    omega
  have hlt := pow_lt_R hl hp
  have hp1 : 1 ≤ p ^ A := Nat.one_le_pow _ _ hp
  by_contra hno
  push Not at hno
  have e0 : ∏ s ∈ (∑ i ∈ Finset.range l, p ^ i).primeFactors,
      s ^ (∑ i ∈ Finset.range l, p ^ i).factorization s = ∑ i ∈ Finset.range l, p ^ i :=
    Nat.prod_factorization_pow_eq_self hR0
  have e1 : ∑ i ∈ Finset.range l, p ^ i ≤ ∏ s ∈ (∑ i ∈ Finset.range l, p ^ i).primeFactors,
      p ^ A := by
    calc _ = _ := e0.symm
      _ ≤ _ := Finset.prod_le_prod fun s _ => hno s
  rw [Finset.prod_const] at e1
  have e2 : (p ^ A) ^ (∑ i ∈ Finset.range l, p ^ i).primeFactors.card ≤ (p ^ A) ^ s :=
    Nat.pow_le_pow_right hp1 ((Finset.card_le_card hsub).trans hE)
  have e3 : (p ^ A) ^ s ≤ p ^ (l - 1) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp hAs
  omega

end OddPerfect.ExcX

namespace OddPerfect

open OddPerfect.TwoExcGen OddPerfect.ExcUniform OddPerfect.ExcX

/-- Let `N` be an odd perfect number, `E` a set of at most `s` natural numbers and `l` a prime
with `16 ^ s < l`. If some prime factor of `N` lies outside `E` and every prime factor `p ∉ E`
has `l ∣ e_p + 1`, then `l ∣ N`. Restricted result; an explicit form of
`exists_index_bound_of_exceptions` (the bound there was not explicit); for two and three
exceptions the landed modules give the smaller bounds `l ≥ 23` and `l ≥ 359`. The hypothesis
`hex` is needed: with every prime factor in `E` the index hypothesis is empty. Published method,
see header; novelty not verified. The odd perfect number conjecture remains open. -/
theorem dvd_of_exceptions_of_sixteen_pow_lt {N l s : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hs : 16 ^ s < l) (E : Finset ℕ) (hE : E.card ≤ s) (hex : ∃ p ∈ N.primeFactors, p ∉ E)
    (hcomp : ∀ p ∈ N.primeFactors, p ∉ E → l ∣ N.factorization p + 1) : l ∣ N := by
  classical
  by_contra hlN
  -- the case `s = 0`
  rcases Nat.eq_zero_or_pos s with hs0 | hs1
  · have hE0 : E = ∅ := Finset.card_eq_zero.mp (show E.card = 0 by omega)
    by_cases hl2 : l = 2
    · obtain ⟨q, hq, -, -, -, hev⟩ := exists_special_prime h
      obtain ⟨p, hp, hpq⟩ := Finset.exists_mem_ne
        (show 1 < N.primeFactors.card by have := seven_le_card_primeFactors h; omega) q
      have h1 := hcomp p hp (by rw [hE0]; exact Finset.notMem_empty p)
      have h2 := hev p (Nat.prime_of_mem_primeFactors hp) hpq
      rw [hl2] at h1
      obtain ⟨k, hk⟩ := h2
      omega
    · obtain ⟨p, hp, hpE⟩ := hex
      have hR := R_one_lt hl.two_le (Nat.prime_of_mem_primeFactors hp).two_le
      have hd := ExcS.keyE hl hl2 h hlN hcomp hp hpE (Nat.minFac_prime (by omega))
        (Nat.minFac_dvd _)
      rw [hE0] at hd
      exact Finset.notMem_empty _ hd.2.1
  have h16 : 16 ≤ 16 ^ s := Nat.le_self_pow (by omega) 16
  have hl2 : l ≠ 2 := by omega
  have h16l : 16 ^ s ≤ l - 1 := by omega
  obtain ⟨A, hA⟩ : ∃ A, A = (l - 1) / s := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = (A + 1) / (4 * s) := ⟨_, rfl⟩
  have hAs : A * s ≤ l - 1 := by rw [hA]; exact Nat.div_mul_le_self _ _
  -- `4 ^ s ≤ G`
  have hGs : 4 ^ s ≤ G := by
    have hlA : l - 1 < s * (A + 1) := by
      have h1 := Nat.div_add_mod (l - 1) s
      have h2 := Nat.mod_lt (l - 1) hs1
      rw [← hA] at h1
      have : s * (A + 1) = s * A + s := by ring
      omega
    have hsq := four_mul_sq_le_four_pow s hs1
    have e1 : 16 ^ s = 4 ^ s * 4 ^ s := by
      rw [show (16 : ℕ) = 4 * 4 by norm_num, mul_pow]
    have e2 : 4 ^ s * (4 * s ^ 2) ≤ 4 ^ s * 4 ^ s := Nat.mul_le_mul_left _ hsq
    have e3 : s * (4 ^ s * (4 * s)) = 4 ^ s * (4 * s ^ 2) := by ring
    have e4 : s * (4 ^ s * (4 * s)) < s * (A + 1) := by omega
    have e5 : 4 ^ s * (4 * s) < A + 1 := Nat.lt_of_mul_lt_mul_left e4
    rw [hG]
    exact (Nat.le_div_iff_mul_le (by omega)).mpr e5.le
  have hG1 : 1 ≤ G := le_trans (Nat.one_le_pow _ _ (by norm_num)) hGs
  have hcount : l < ∑ j ∈ Finset.range (A / G + 1), (A - G * j + 1) :=
    ExcS.count_gtS hs1 hA hG hG1 (by omega)
  -- compatible primes
  set P := N.primeFactors.filter (fun p => p ∉ E) with hPdef
  have hPm : ∀ p ∈ P, p ∈ N.primeFactors ∧ p ∉ E := fun p hp => Finset.mem_filter.mp hp
  have hP3 : ∀ p ∈ P, 3 ≤ p := fun p hp => by
    have hpN := (hPm p hp).1
    have h1 := odd_of_mem h hpN
    have h2 := (Nat.prime_of_mem_primeFactors hpN).two_le
    omega
  have hrecv : ∀ p ∈ P, ∀ d, p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d →
      d.Prime ∧ d ∈ E ∧ d ≠ l := by
    intro p hp d hd
    obtain ⟨hpN, hpE⟩ := hPm p hp
    have hv : (∑ i ∈ Finset.range l, p ^ i).factorization d ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hd
      exact absurd hd (not_lt.mpr (Nat.one_le_pow _ _ (by have := hP3 p hp; omega)))
    have hmem : d ∈ (∑ i ∈ Finset.range l, p ^ i).primeFactors := by
      rw [← Nat.support_factorization]
      exact Finsupp.mem_support_iff.mpr hv
    have hdP : d.Prime := Nat.prime_of_mem_primeFactors hmem
    obtain ⟨-, hdE, hdl⟩ := ExcS.keyE hl hl2 h hlN hcomp hpN hpE hdP
      (Nat.dvd_of_mem_primeFactors hmem)
    refine ⟨hdP, hdE, ?_⟩
    intro e
    rw [e, Nat.mod_self] at hdl
    omega
  have hdom : ∀ p ∈ P, ∃ d, p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d := by
    intro p hp
    obtain ⟨hpN, hpE⟩ := hPm p hp
    exact dominant hl.two_le (by have := hP3 p hp; omega) hAs
      (fun x hx => (ExcS.keyE hl hl2 h hlN hcomp hpN hpE (Nat.prime_of_mem_primeFactors hx)
        (Nat.dvd_of_mem_primeFactors hx)).2.1) hE
  choose! dom hdom using hdom
  -- two compatible primes with one receiver are far apart
  have hgap : ∀ p ∈ P, ∀ p' ∈ P, dom p = dom p' → p < p' → p ^ G < p' := by
    intro p hp p' hp' hr hlt
    obtain ⟨hdP, -, hdl⟩ := hrecv p hp (dom p) (hdom p hp)
    have hpP := Nat.prime_of_mem_primeFactors (hPm p hp).1
    have hp'P := Nat.prime_of_mem_primeFactors (hPm p' hp').1
    have h2 := hdom p' hp'
    rw [← hr] at h2
    exact pow_lt_of_common_receiver_power hl hdP hdl hpP hp'P hlt (Nat.ordProj_dvd _ _)
      (Nat.ordProj_dvd _ _) (hdom p hp) (lt_of_le_of_lt (Nat.pow_le_pow_left hlt.le A) h2)
      hcount
  -- the receiver classes
  set D := P.image dom with hDdef
  have hDE : D ⊆ E := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact (hrecv p hp (dom p) (hdom p hp)).2.1
  have hDcard : D.card ≤ s := (Finset.card_le_card hDE).trans hE
  have hCm : ∀ d ∈ D, (P.filter (fun p => dom p = d)).card ≤
      D.sup (fun d => (P.filter (fun p => dom p = d)).card) := fun d hd =>
    Finset.le_sup (f := fun d => (P.filter (fun p => dom p = d)).card) hd
  set m := D.sup (fun d => (P.filter (fun p => dom p = d)).card) with hmdef
  have hPcard : P.card ≤ s * m := by
    have hsub : P ⊆ D.biUnion (fun d => P.filter (fun p => dom p = d)) := by
      intro p hp
      rw [Finset.mem_biUnion]
      exact ⟨dom p, Finset.mem_image_of_mem _ hp, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
    calc P.card ≤ (D.biUnion (fun d => P.filter (fun p => dom p = d))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ d ∈ D, (P.filter (fun p => dom p = d)).card := Finset.card_biUnion_le
      _ ≤ D.card • m := Finset.sum_le_card_nsmul _ _ _ hCm
      _ = D.card * m := smul_eq_mul _ _
      _ ≤ s * m := Nat.mul_le_mul_right m hDcard
  have hω : N.primeFactors.card ≤ s + s * m := by
    have hsub : N.primeFactors ⊆ E ∪ P := by
      intro p hp
      by_cases hpE : p ∈ E
      · exact Finset.mem_union_left _ hpE
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hpE⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le E P)
    omega
  -- a largest class
  obtain ⟨p0, hp0N, hp0E⟩ := hex
  have hp0 : p0 ∈ P := Finset.mem_filter.mpr ⟨hp0N, hp0E⟩
  have hDne : D.Nonempty := ⟨dom p0, Finset.mem_image_of_mem _ hp0⟩
  have hm1 : 1 ≤ m := by
    have := hCm (dom p0) (Finset.mem_image_of_mem _ hp0)
    have h1 : 0 < (P.filter (fun p => dom p = dom p0)).card :=
      Finset.card_pos.mpr ⟨p0, Finset.mem_filter.mpr ⟨hp0, rfl⟩⟩
    omega
  obtain ⟨r0, -, hr0⟩ := Finset.exists_mem_eq_sup D hDne
    (fun d => (P.filter (fun p => dom p = d)).card)
  have hr0' : (P.filter (fun p => dom p = r0)).card = m := hr0.symm
  obtain ⟨p, hp, hpb⟩ := RowLog.chain_ge G (m - 1) (P.filter (fun p => dom p = r0))
    (by omega)
    (fun p hp => hP3 p (Finset.mem_filter.mp hp).1)
    (fun p hp p' hp' hlt => hgap p (Finset.mem_filter.mp hp).1 p'
      (Finset.mem_filter.mp hp').1
      ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm) hlt)
  have hpP := (Finset.mem_filter.mp hp).1
  have hpN := (hPm p hpP).1
  have hexp : l - 1 ≤ N.factorization p := by
    have := Nat.le_of_dvd (by omega) (hcomp p hpN (hPm p hpP).2)
    omega
  have hsize : 3 ^ (G ^ (m - 1) * (l - 1)) ≤ N :=
    calc 3 ^ (G ^ (m - 1) * (l - 1)) = (3 ^ (G ^ (m - 1))) ^ (l - 1) := pow_mul _ _ _
      _ ≤ p ^ (l - 1) := Nat.pow_le_pow_left hpb _
      _ ≤ p ^ N.factorization p := Nat.pow_le_pow_right (by have := hP3 p hpP; omega) hexp
      _ ≤ N := Nat.le_of_dvd h.pos (Nat.ordProj_dvd N p)
  have hub := lt_two_pow_four_pow h
  have hlt4 : G ^ (m - 1) * (l - 1) < 4 ^ N.primeFactors.card :=
    RowLog.lt_of_three_pow_lt (by omega)
  have h4 : 4 ^ N.primeFactors.card ≤ 4 ^ (s * (m + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by
      have : s * (m + 1) = s + s * m := by ring
      omega)
  have hlow : (4 ^ s) ^ (m - 1) * 16 ^ s ≤ G ^ (m - 1) * (l - 1) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hGs _) h16l
  have heq : (4 ^ s) ^ (m - 1) * 16 ^ s = 4 ^ (s * (m + 1)) := by
    have hm2 : m - 1 + 2 = m + 1 := by omega
    rw [← pow_mul, show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    calc s * (m - 1) + 2 * s = s * (m - 1 + 2) := by ring
      _ = s * (m + 1) := by rw [hm2]
  omega

/-- Let `N` be an odd perfect number, `E` a set of at most six natural numbers and `l` a prime
with `16 ^ 6 < l`. If every prime factor `p ∉ E` of `N` has `l ∣ e_p + 1`, then `l ∣ N`. Some
prime factor lies outside `E`, since `N` has at least seven prime factors. Restricted result;
an explicit form of `exists_index_bound_of_six_exceptions`; published method, see header;
novelty not verified. The odd perfect number conjecture remains open. -/
theorem dvd_of_six_exceptions_of_lt {N l : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hl6 : 16 ^ 6 < l) (E : Finset ℕ) (hE : E.card ≤ 6)
    (hcomp : ∀ p ∈ N.primeFactors, p ∉ E → l ∣ N.factorization p + 1) : l ∣ N := by
  refine dvd_of_exceptions_of_sixteen_pow_lt h hl hl6 E hE ?_ hcomp
  by_contra hno
  have hsub : N.primeFactors ⊆ E := fun p hp => by
    by_contra hpE
    exact hno ⟨p, hp, hpE⟩
  have h7 := seven_le_card_primeFactors h
  have := Finset.card_le_card hsub
  omega

end OddPerfect

#print axioms OddPerfect.ExcX.four_mul_sq_le_four_pow
#print axioms OddPerfect.ExcX.dominant
#print axioms OddPerfect.dvd_of_exceptions_of_sixteen_pow_lt
#print axioms OddPerfect.dvd_of_six_exceptions_of_lt
