import OddPerfect.ExceptionsExplicit
import OddPerfect.EulerPart

/-!
# Few receivers force a small common index prime

Write `R(x) = ∑ i < l, x ^ i`. Let `N` be an odd perfect number, `l` a prime, `T` a nonempty set
of prime factors of `N` with at most `c` prime factors of `N` outside it, and `X` a set of at
most `b ≥ 1` numbers. If `l ∣ e_p + 1` for every `p ∈ T` and every prime factor of `R(p)` is `l`
or lies in `X`, then `4 ^ (c + b) < l` and `16 b ^ 2 4 ^ b < l` cannot both hold
(`false_of_few_receivers`).

With `A = (l - 1) / (2 b)` and `G = (A + 1) / (8 b)` one has `4 ^ b ≤ G` and `l ≤ 3 ^ A`. Every
`p ∈ T` has a receiver `d` with `p ^ A < d ^ v_d(R(p))`; `d ≠ l` since `l ^ 2 ∤ R(p)`, so
`d ∈ X`. Two primes `p < p'` of `T` with one receiver satisfy `p ^ G < p'`. A largest receiver
class of `m` primes gives `3 ^ ((4 ^ b) ^ (m - 1) (l - 1)) ≤ N < 2 ^ (4 ^ ω(N))` with
`ω(N) ≤ b m + c`, while `(4 ^ b) ^ (m - 1) (l - 1) ≥ 4 ^ (b m + c)`.

Under a common index prime `l ≠ 2` (every ordinary index `e_p + 1` divisible by `l`) this gives
`l ≤ 16 b ^ 2 4 ^ b` with `b` the number of prime factors of `N` that are `1` mod `l`
(`index_le_of_common_index_receivers`), and with `b = ω(J) + 1` for the Euler index `J`
(`index_le_of_common_index_eulerIndex`).

Scope. With the exceptions as receivers the first theorem returns the landed threshold `16 ^ s`
and nothing better. The second sharpens `index_pred_lt_sixteen_pow_of_pure_outside` only through
the count of prime factors that are `1` mod `l`. The common index family is not excluded.
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

namespace OddPerfect.Squeeze

open OddPerfect.TwoExcGen OddPerfect.ExcUniform

/-- `n < 3 ^ n`. -/
theorem lt_three_pow : ∀ n : ℕ, n < 3 ^ n := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

/-- `(n + 1) ^ 2 ≤ 4 * 3 ^ n` for `n ≥ 1`. -/
theorem sq_le_four_mul_three_pow : ∀ n : ℕ, 1 ≤ n → (n + 1) ^ 2 ≤ 4 * 3 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : (n + 1 + 1) ^ 2 ≤ 3 * (n + 1) ^ 2 := by nlinarith
    calc (n + 1 + 1) ^ 2 ≤ 3 * (n + 1) ^ 2 := h1
      _ ≤ 3 * (4 * 3 ^ n) := Nat.mul_le_mul_left 3 ih
      _ = 4 * 3 ^ (n + 1) := by ring

/-- A prime power part of `n` above `p ^ A` belongs to a prime factor of `n`. -/
theorem mem_of_pow_lt {n p A d : ℕ} (hp : 1 ≤ p) (hd : p ^ A < d ^ n.factorization d) :
    d ∈ n.primeFactors := by
  have hv : n.factorization d ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hd
    exact absurd hd (not_lt.mpr (Nat.one_le_pow _ _ hp))
  rw [← Nat.support_factorization]
  exact Finsupp.mem_support_iff.mpr hv

/-- For an odd prime `l`, a prime `p` with `l ≤ p ^ A` and a prime power part of `R(p)` above
`p ^ A`, the receiver is not `l`. -/
theorem receiver_ne {l p A d : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hp : p.Prime) (hlA : l ≤ p ^ A)
    (hd : p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d) : d ≠ l := by
  rintro rfl
  have hR0 : (∑ i ∈ Finset.range d, p ^ i) ≠ 0 := by
    have := pow_lt_R hl.two_le hp.one_lt.le
    omega
  have hv : (∑ i ∈ Finset.range d, p ^ i).factorization d ≤ 1 := by
    by_contra hv
    push Not at hv
    have h2 : d ^ 2 ∣ ∑ i ∈ Finset.range d, p ^ i :=
      (hl.pow_dvd_iff_le_factorization hR0).mpr hv
    rw [R_eq_sigma hl.one_lt.le hp] at h2
    exact not_sq_dvd_sigma_pow_pred hl hl2 hp h2
  have h1 : d ^ (∑ i ∈ Finset.range d, p ^ i).factorization d ≤ d ^ 1 :=
    Nat.pow_le_pow_right hl.pos hv
  rw [pow_one] at h1
  omega

/-- The row of a prime divides the row of a larger exponent with a multiple index. -/
theorem R_dvd_sigma {l p e : ℕ} (hl : l.Prime) (hp : p.Prime) (hle : l ∣ e + 1) :
    ∑ i ∈ Finset.range l, p ^ i ∣ σ 1 (p ^ e) := by
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  rw [R_eq_sigma hl.one_lt.le hp]
  exact OPNExample.sigma_prime_pow_dvd (a := l - 1) hp (by rw [hl1]; exact hle)

/-- `σ(p ^ v_p(n)) ∣ σ(n)`. -/
theorem sigma_component_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    σ 1 (p ^ n.factorization p) ∣ σ 1 n := by
  have hcop := (Nat.coprime_ordCompl hp hn).pow_left (n.factorization p)
  calc σ 1 (ordProj[p] n) ∣ σ 1 (ordProj[p] n) * σ 1 (ordCompl[p] n) := dvd_mul_right _ _
    _ = σ 1 (ordProj[p] n * ordCompl[p] n) :=
      (isMultiplicative_sigma.map_mul_of_coprime hcop).symm
    _ = σ 1 n := by rw [Nat.ordProj_mul_ordCompl_eq_self]

/-- `4 ^ (1 + b) ≤ 16 * b ^ 2 * 4 ^ b` for `b ≥ 1`. -/
theorem four_pow_succ_le {b : ℕ} (hb : 1 ≤ b) : 4 ^ (1 + b) ≤ 16 * b ^ 2 * 4 ^ b := by
  have h1 : 4 ≤ 16 * b ^ 2 := by nlinarith
  calc 4 ^ (1 + b) = 4 * 4 ^ b := by rw [pow_add, pow_one]
    _ ≤ 16 * b ^ 2 * 4 ^ b := Nat.mul_le_mul_right _ h1

end OddPerfect.Squeeze

namespace OddPerfect

open OddPerfect.TwoExcGen OddPerfect.ExcUniform OddPerfect.ExcX OddPerfect.Squeeze

/-- Let `N` be an odd perfect number, `l` a prime, `T` a nonempty set of prime factors of `N`
with at most `c` prime factors of `N` outside `T`, and `X` a set of at most `b ≥ 1` numbers.
If `l ∣ e_p + 1` for every `p ∈ T` and every prime factor of `∑ i < l, p ^ i` is `l` or lies in
`X`, then `4 ^ (c + b) < l` and `16 b ^ 2 4 ^ b < l` cannot both hold. Restricted result; with
the exceptions as receivers this returns the landed threshold `16 ^ s` and nothing better. Published
method, see header; novelty not verified. The odd perfect number conjecture remains
open. -/
theorem false_of_few_receivers {N l b c : ℕ} (h : OddPerfect N) (hl : l.Prime) (hb : 1 ≤ b)
    (X T : Finset ℕ) (hX : X.card ≤ b) (hT : T ⊆ N.primeFactors) (hne : T.Nonempty)
    (hout : (N.primeFactors \ T).card ≤ c)
    (hidx : ∀ p ∈ T, l ∣ N.factorization p + 1)
    (hrec : ∀ p ∈ T, ∀ r, r.Prime → r ∣ ∑ i ∈ Finset.range l, p ^ i → r = l ∨ r ∈ X)
    (h1 : 4 ^ (c + b) < l) (h2 : 16 * b ^ 2 * 4 ^ b < l) : False := by
  classical
  have h4cb : 4 ≤ 4 ^ (c + b) := Nat.le_self_pow (by omega) 4
  have hl2 : l ≠ 2 := by omega
  obtain ⟨A, hA⟩ : ∃ A, A = (l - 1) / (2 * b) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = (A + 1) / (4 * (2 * b)) := ⟨_, rfl⟩
  have hAs : A * (2 * b) ≤ l - 1 := by rw [hA]; exact Nat.div_mul_le_self _ _
  have hlA : l - 1 < 2 * b * (A + 1) := by
    have h1 := Nat.div_add_mod (l - 1) (2 * b)
    have h2 := Nat.mod_lt (l - 1) (show 2 * b > 0 by omega)
    rw [← hA] at h1
    have : 2 * b * (A + 1) = 2 * b * A + 2 * b := by ring
    omega
  have e3 : 2 * b * (4 ^ b * (4 * (2 * b))) = 16 * b ^ 2 * 4 ^ b := by ring
  have e4 : 2 * b * (4 ^ b * (4 * (2 * b))) < 2 * b * (A + 1) := by omega
  have e5 : 4 ^ b * (4 * (2 * b)) < A + 1 := Nat.lt_of_mul_lt_mul_left e4
  have hGs : 4 ^ b ≤ G := by
    rw [hG]
    exact (Nat.le_div_iff_mul_le (by omega)).mpr e5.le
  have hG1 : 1 ≤ G := le_trans (Nat.one_le_pow _ _ (by norm_num)) hGs
  have hcount : l < ∑ j ∈ Finset.range (A / G + 1), (A - G * j + 1) :=
    ExcS.count_gtS (S := 2 * b) (by omega) hA hG hG1 (by omega)
  -- `l ≤ 3 ^ A`
  have h8b : 4 * (2 * b) < A + 1 := by
    have : 4 * (2 * b) ≤ 4 ^ b * (4 * (2 * b)) :=
      Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))
    omega
  have hl3A : l ≤ 3 ^ A := by
    have hsq := sq_le_four_mul_three_pow A (by omega)
    have k1 : 4 * (2 * b * (A + 1)) = 4 * (2 * b) * (A + 1) := by ring
    have k2 : 4 * (2 * b) * (A + 1) ≤ (A + 1) * (A + 1) := Nat.mul_le_mul_right _ h8b.le
    have k3 : (A + 1) ^ 2 = (A + 1) * (A + 1) := sq _
    omega
  have hTm : ∀ p ∈ T, p ∈ N.primeFactors := fun p hp => hT hp
  have hP3 : ∀ p ∈ T, 3 ≤ p := fun p hp => by
    have h1 := odd_of_mem h (hTm p hp)
    have h2 := (Nat.prime_of_mem_primeFactors (hTm p hp)).two_le
    omega
  have hpA : ∀ p ∈ T, l ≤ p ^ A := fun p hp =>
    hl3A.trans (Nat.pow_le_pow_left (hP3 p hp) A)
  have hEc : (insert l X).card ≤ 2 * b := (Finset.card_insert_le _ _).trans (by omega)
  have hdom : ∀ p ∈ T, ∃ d, p ^ A < d ^ (∑ i ∈ Finset.range l, p ^ i).factorization d := by
    intro p hp
    refine dominant hl.two_le (by have := hP3 p hp; omega) hAs (fun x hx => ?_) hEc
    rcases hrec p hp x (Nat.prime_of_mem_primeFactors hx) (Nat.dvd_of_mem_primeFactors hx)
      with e | e
    · rw [e]; exact Finset.mem_insert_self l X
    · exact Finset.mem_insert_of_mem e
  choose! dom hdom using hdom
  have hrecv : ∀ p ∈ T, (dom p).Prime ∧ dom p ∈ X ∧ dom p ≠ l := by
    intro p hp
    have hmem := mem_of_pow_lt (by have := hP3 p hp; omega) (hdom p hp)
    have hpP := Nat.prime_of_mem_primeFactors (hTm p hp)
    have hdl := receiver_ne hl hl2 hpP (hpA p hp) (hdom p hp)
    have hdP : (dom p).Prime := Nat.prime_of_mem_primeFactors hmem
    exact ⟨hdP, (hrec p hp _ hdP (Nat.dvd_of_mem_primeFactors hmem)).resolve_left hdl, hdl⟩
  -- two primes with one receiver are far apart
  have hgap : ∀ p ∈ T, ∀ p' ∈ T, dom p = dom p' → p < p' → p ^ G < p' := by
    intro p hp p' hp' hr hlt
    obtain ⟨hdP, -, hdl⟩ := hrecv p hp
    have hpP := Nat.prime_of_mem_primeFactors (hTm p hp)
    have hp'P := Nat.prime_of_mem_primeFactors (hTm p' hp')
    have h2 := hdom p' hp'
    rw [← hr] at h2
    exact pow_lt_of_common_receiver_power hl hdP hdl hpP hp'P hlt (Nat.ordProj_dvd _ _)
      (Nat.ordProj_dvd _ _) (hdom p hp) (lt_of_le_of_lt (Nat.pow_le_pow_left hlt.le A) h2)
      hcount
  -- the receiver classes
  set D := T.image dom with hDdef
  have hDX : D ⊆ X := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact (hrecv p hp).2.1
  have hDcard : D.card ≤ b := (Finset.card_le_card hDX).trans hX
  have hCm : ∀ d ∈ D, (T.filter (fun p => dom p = d)).card ≤
      D.sup (fun d => (T.filter (fun p => dom p = d)).card) := fun d hd =>
    Finset.le_sup (f := fun d => (T.filter (fun p => dom p = d)).card) hd
  set m := D.sup (fun d => (T.filter (fun p => dom p = d)).card) with hmdef
  have hTcard : T.card ≤ b * m := by
    have hsub : T ⊆ D.biUnion (fun d => T.filter (fun p => dom p = d)) := by
      intro p hp
      rw [Finset.mem_biUnion]
      exact ⟨dom p, Finset.mem_image_of_mem _ hp, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
    calc T.card ≤ (D.biUnion (fun d => T.filter (fun p => dom p = d))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ d ∈ D, (T.filter (fun p => dom p = d)).card := Finset.card_biUnion_le
      _ ≤ D.card • m := Finset.sum_le_card_nsmul _ _ _ hCm
      _ = D.card * m := smul_eq_mul _ _
      _ ≤ b * m := Nat.mul_le_mul_right m hDcard
  have hω : N.primeFactors.card ≤ b * m + c := by
    have hsub : N.primeFactors ⊆ T ∪ (N.primeFactors \ T) := by
      intro p hp
      by_cases hpT : p ∈ T
      · exact Finset.mem_union_left _ hpT
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp, hpT⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le T (N.primeFactors \ T))
    omega
  -- a largest class
  obtain ⟨p0, hp0⟩ := hne
  have hDne : D.Nonempty := ⟨dom p0, Finset.mem_image_of_mem _ hp0⟩
  have hm1 : 1 ≤ m := by
    have := hCm (dom p0) (Finset.mem_image_of_mem _ hp0)
    have h1 : 0 < (T.filter (fun p => dom p = dom p0)).card :=
      Finset.card_pos.mpr ⟨p0, Finset.mem_filter.mpr ⟨hp0, rfl⟩⟩
    omega
  obtain ⟨r0, -, hr0⟩ := Finset.exists_mem_eq_sup D hDne
    (fun d => (T.filter (fun p => dom p = d)).card)
  have hr0' : (T.filter (fun p => dom p = r0)).card = m := hr0.symm
  obtain ⟨p, hp, hpb⟩ := RowLog.chain_ge G (m - 1) (T.filter (fun p => dom p = r0))
    (by omega)
    (fun p hp => hP3 p (Finset.mem_filter.mp hp).1)
    (fun p hp p' hp' hlt => hgap p (Finset.mem_filter.mp hp).1 p'
      (Finset.mem_filter.mp hp').1
      ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm) hlt)
  have hpT := (Finset.mem_filter.mp hp).1
  have hexp : l - 1 ≤ N.factorization p := by
    have := Nat.le_of_dvd (by omega) (hidx p hpT)
    omega
  have hsize : 3 ^ (G ^ (m - 1) * (l - 1)) ≤ N :=
    calc 3 ^ (G ^ (m - 1) * (l - 1)) = (3 ^ (G ^ (m - 1))) ^ (l - 1) := pow_mul _ _ _
      _ ≤ p ^ (l - 1) := Nat.pow_le_pow_left hpb _
      _ ≤ p ^ N.factorization p := Nat.pow_le_pow_right (by have := hP3 p hpT; omega) hexp
      _ ≤ N := Nat.le_of_dvd h.pos (Nat.ordProj_dvd N p)
  have hub := lt_two_pow_four_pow h
  have hlt4 : G ^ (m - 1) * (l - 1) < 4 ^ N.primeFactors.card :=
    RowLog.lt_of_three_pow_lt (by omega)
  have h4 : 4 ^ N.primeFactors.card ≤ 4 ^ (b * m + c) :=
    Nat.pow_le_pow_right (by norm_num) hω
  have hlow : (4 ^ b) ^ (m - 1) * 4 ^ (c + b) ≤ G ^ (m - 1) * (l - 1) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hGs _) (by omega)
  have heq : (4 ^ b) ^ (m - 1) * 4 ^ (c + b) = 4 ^ (b * m + c) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    calc b * (m - 1) + (c + b) = b * (m - 1 + 1) + c := by ring
      _ = b * m + c := by rw [Nat.sub_add_cancel hm1]
  omega

/-- Let `N` be an odd perfect number with a prime `q` and a prime `l ≠ 2` dividing `e_p + 1`
for every prime factor `p ≠ q`. Then `l ≤ 16 b ^ 2 4 ^ b`, where `b` is the number of prime
factors of `N` that are `1` mod `l`. Restricted result; it sharpens
`index_pred_lt_sixteen_pow_of_pure_outside` only through the count of prime factors that are
`1` mod `l` (every ordinary one of them has a row that is not a prime power); the common index
family is not excluded. Published method, see header; novelty not verified. The odd perfect
number conjecture remains open. -/
theorem index_le_of_common_index_receivers {N q l : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hl2 : l ≠ 2)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) :
    l ≤ 16 * (N.primeFactors.filter fun r => r % l = 1).card ^ 2 *
      4 ^ (N.primeFactors.filter fun r => r % l = 1).card := by
  classical
  set X := N.primeFactors.filter fun r => r % l = 1 with hXdef
  by_contra hlt
  push Not at hlt
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  obtain ⟨T, hTdef⟩ : ∃ T, T = N.primeFactors.erase q := ⟨_, rfl⟩
  have hT : T ⊆ N.primeFactors := hTdef ▸ Finset.erase_subset _ _
  have hne : T.Nonempty := by
    rw [hTdef]
    refine Finset.card_pos.mp ?_
    have := Finset.pred_card_le_card_erase (s := N.primeFactors) (a := q)
    have := seven_le_card_primeFactors h
    omega
  have hout : (N.primeFactors \ T).card ≤ 1 := by
    have hsub : N.primeFactors \ T ⊆ {q} := by
      intro x hx
      obtain ⟨hxN, hxT⟩ := Finset.mem_sdiff.mp hx
      rw [Finset.mem_singleton]
      by_contra hxq
      rw [hTdef] at hxT
      exact hxT (Finset.mem_erase.mpr ⟨hxq, hxN⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_singleton q).le
  have hTe : ∀ p ∈ T, p ∈ N.primeFactors ∧ p ≠ q := fun p hp => by
    rw [hTdef] at hp
    exact ⟨Finset.mem_of_mem_erase hp, Finset.ne_of_mem_erase hp⟩
  have hidx : ∀ p ∈ T, l ∣ N.factorization p + 1 := fun p hp =>
    hcomp p (hTe p hp).1 (hTe p hp).2
  have hrec : ∀ p ∈ T, ∀ r, r.Prime → r ∣ ∑ i ∈ Finset.range l, p ^ i → r = l ∨ r ∈ X := by
    intro p hp r hr hrR
    have hpN := (hTe p hp).1
    have hpP := Nat.prime_of_mem_primeFactors hpN
    have hdv := R_dvd_sigma hl hpP (hidx p hp)
    rw [R_eq_sigma hl.one_lt.le hpP] at hrR
    rcases prime_dvd_sigma_prime_pow_of_prime_length hpP hr hl hrR with e | e
    · exact Or.inl e
    · right
      have hr2 : r ≠ 2 := by
        intro h2
        rw [h2] at e
        have : 2 % l = 2 := Nat.mod_eq_of_lt (by omega)
        omega
      rw [← R_eq_sigma hl.one_lt.le hpP] at hrR
      have hrN : r ∣ N := OPNStarter.force_prime h.perfect hpP rfl hr hr2 (hrR.trans hdv)
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩, e⟩
  rcases Nat.eq_zero_or_pos X.card with hb0 | hb1
  · obtain ⟨p, hp⟩ := hne
    have hpP := Nat.prime_of_mem_primeFactors (hT hp)
    have hX0 : X = ∅ := Finset.card_eq_zero.mp hb0
    have hsub : (∑ i ∈ Finset.range l, p ^ i).primeFactors ⊆ {l} := by
      intro x hx
      rcases hrec p hp x (Nat.prime_of_mem_primeFactors hx) (Nat.dvd_of_mem_primeFactors hx)
        with e | e
      · exact Finset.mem_singleton.mpr e
      · rw [hX0] at e
        exact absurd e (Finset.notMem_empty x)
    obtain ⟨d, hd⟩ := dominant (A := l - 1) (s := 1) hl.two_le hpP.one_lt.le (by omega) hsub
      (Finset.card_singleton l).le
    have hlA : l ≤ p ^ (l - 1) := by
      have h1 := lt_three_pow (l - 1)
      have h2 : 3 ^ (l - 1) ≤ p ^ (l - 1) :=
        Nat.pow_le_pow_left (by have := odd_of_mem h (hT hp); have := hpP.two_le; omega) _
      omega
    have hdl := receiver_ne hl hl2 hpP hlA hd
    have hmem := hsub (mem_of_pow_lt hpP.one_lt.le hd)
    exact hdl (Finset.mem_singleton.mp hmem)
  · exact false_of_few_receivers h hl hb1 X T le_rfl hT hne hout hidx hrec
      ((four_pow_succ_le hb1).trans_lt hlt) hlt

/-- Let `N = q ^ k m ^ 2` be an odd perfect number in Euler form with special prime `q`,
`q ∤ m`, and `l ≠ 2` a prime dividing `e_p + 1` for every prime factor `p ≠ q`. With `b` one
more than the number of prime factors of the Euler index `J = σ(m ^ 2) / q ^ k`,
`l ≤ 16 b ^ 2 4 ^ b`. Restricted result; the common index family is not excluded. Published method,
see header; novelty not verified. The odd perfect number conjecture remains open. -/
theorem index_le_of_common_index_eulerIndex {N q k m l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hl : l.Prime)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) :
    l ≤ 16 * ((eulerIndex q k m).primeFactors.card + 1) ^ 2 *
      4 ^ ((eulerIndex q k m).primeFactors.card + 1) := by
  classical
  set J := eulerIndex q k m with hJdef
  set b := J.primeFactors.card + 1 with hbdef
  by_contra hlt
  push Not at hlt
  have hb1 : 1 ≤ b := Nat.le_add_left 1 _
  set X := insert q J.primeFactors with hXdef
  have hX : X.card ≤ b := Finset.card_insert_le _ _
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact h.ne_zero (by rw [hN]; simp)
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm0
  have hsig : σ 1 (m ^ 2) = q ^ k * J := sigma_sq_eq_mul_eulerIndex h hq hN hqm
  have hJ0 : J ≠ 0 := by
    intro e
    rw [e, mul_zero] at hsig
    exact (sigma_pos 1 _ hm2).ne' hsig
  obtain ⟨T, hTdef⟩ : ∃ T, T = N.primeFactors.erase q := ⟨_, rfl⟩
  have hT : T ⊆ N.primeFactors := hTdef ▸ Finset.erase_subset _ _
  have hne : T.Nonempty := by
    rw [hTdef]
    refine Finset.card_pos.mp ?_
    have := Finset.pred_card_le_card_erase (s := N.primeFactors) (a := q)
    have := seven_le_card_primeFactors h
    omega
  have hout : (N.primeFactors \ T).card ≤ 1 := by
    have hsub : N.primeFactors \ T ⊆ {q} := by
      intro x hx
      obtain ⟨hxN, hxT⟩ := Finset.mem_sdiff.mp hx
      rw [Finset.mem_singleton]
      by_contra hxq
      rw [hTdef] at hxT
      exact hxT (Finset.mem_erase.mpr ⟨hxq, hxN⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_singleton q).le
  have hTe : ∀ p ∈ T, p ∈ N.primeFactors ∧ p ≠ q := fun p hp => by
    rw [hTdef] at hp
    exact ⟨Finset.mem_of_mem_erase hp, Finset.ne_of_mem_erase hp⟩
  have hidx : ∀ p ∈ T, l ∣ N.factorization p + 1 := fun p hp =>
    hcomp p (hTe p hp).1 (hTe p hp).2
  have hrec : ∀ p ∈ T, ∀ r, r.Prime → r ∣ ∑ i ∈ Finset.range l, p ^ i → r = l ∨ r ∈ X := by
    intro p hp r hr hrR
    right
    have hpq := (hTe p hp).2
    have hpP := Nat.prime_of_mem_primeFactors (hTe p hp).1
    have hfac : N.factorization p = (m ^ 2).factorization p := by
      rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hm2, Finsupp.add_apply,
        Nat.factorization_pow, hq.factorization]
      simp [Ne.symm hpq]
    have hdv := R_dvd_sigma hl hpP (hidx p hp)
    rw [hfac] at hdv
    have hrs : r ∣ q ^ k * J := by
      rw [← hsig]
      exact hrR.trans (hdv.trans (sigma_component_dvd hm2 hpP))
    rcases (Nat.Prime.dvd_mul hr).mp hrs with e | e
    · rw [(Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow e)]
      exact Finset.mem_insert_self q _
    · exact Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hr, e, hJ0⟩)
  exact false_of_few_receivers h hl hb1 X T hX hT hne hout hidx hrec
    ((four_pow_succ_le hb1).trans_lt hlt) hlt

end OddPerfect

#print axioms OddPerfect.Squeeze.lt_three_pow
#print axioms OddPerfect.Squeeze.sq_le_four_mul_three_pow
#print axioms OddPerfect.Squeeze.mem_of_pow_lt
#print axioms OddPerfect.Squeeze.receiver_ne
#print axioms OddPerfect.Squeeze.R_dvd_sigma
#print axioms OddPerfect.Squeeze.sigma_component_dvd
#print axioms OddPerfect.Squeeze.four_pow_succ_le
#print axioms OddPerfect.false_of_few_receivers
#print axioms OddPerfect.index_le_of_common_index_receivers
#print axioms OddPerfect.index_le_of_common_index_eulerIndex
