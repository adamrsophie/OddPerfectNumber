import OddPerfect.KanoldSquare
import OddPerfect.KanoldObstruction

/-!
# The fifth power theorem: the square case at the special prime

Let `N` be an odd perfect number with special prime `q` such that `q ^ 2` divides `e_p + 1`
for every ordinary prime `p`. `OddPerfect/KanoldSquare.lean` reduces `q ^ 10 ∣ N` to excluding
a normal form with `v_q(N) = 9`, and `OddPerfect/KanoldFive.lean` settles `q = 5`. This file
excludes the normal form for `q ≥ 13`, first with Kanold's obstruction `KanoldObstructionAt q`
as an explicit hypothesis, and assembles the fifth power theorem `t ^ 5 ∣ N`. The hypothesis is
then discharged, so the final theorems are unconditional. This is known mathematics: the
theorem is due to H.-J. Kanold (fourth power) and T. Yamada (fifth power, arXiv 2312.17059),
whose argument for the last case this file follows with two bounds repaired.

Notation: `kC q j s = 1 + Y + ... + Y ^ (q - 1)` with `Y = s ^ q ^ j`. For a member `s` of the
set `S` of prime factors `≡ 1 (mod q)` with `q ^ (j + 1) ∣ e_s + 1`, the number `kC q j s` is
`q` times a product of powers of members of `S` other than `s`, and the primes dividing
`kC q j s` and `kC q i s` for `i ≠ j` are different (their orders differ).

* `not_normal_form_of_obstruction`: the normal form is impossible for `q ≥ 13`.
* `pow_ten_dvd_of_special_sq_of_obstruction`: `q ^ 10 ∣ N`.
* `pow_five_dvd_of_forall_dvd_succ_of_obstruction`: the fifth power theorem `t ^ 5 ∣ N`.
* `pow_ten_dvd_of_special_sq`, `pow_five_dvd_of_forall_dvd_succ`: the same without the
  hypothesis, discharged by `kanold_obstruction` from `OddPerfect/KanoldObstruction.lean`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Kanold's obstruction, as a hypothesis. -/
def KanoldObstructionAt (p : ℕ) : Prop :=
  ∀ r s u v a b : ℕ, r.Prime → s.Prime → 0 < a → 0 < b →
    ∑ i ∈ Finset.range p, (r ^ p ^ u) ^ i = p * s ^ a →
    ∑ i ∈ Finset.range p, (s ^ p ^ v) ^ i = p * r ^ b → False

/-- The block `kC q j s = 1 + Y + ... + Y ^ (q - 1)` with `Y = s ^ q ^ j`. -/
def kC (q j s : ℕ) : ℕ := ∑ i ∈ Finset.range q, (s ^ q ^ j) ^ i

/-! ## Arithmetic of the blocks -/

/-- The geometric identity `kC q j s * (s ^ q ^ j - 1) = s ^ q ^ (j + 1) - 1` in any ring. -/
private theorem kC_mul_sub {R : Type*} [CommRing R] (q j s : ℕ) :
    ((kC q j s : ℕ) : R) * ((s : R) ^ q ^ j - 1) = (s : R) ^ q ^ (j + 1) - 1 := by
  unfold kC
  push_cast
  rw [geom_sum_mul, ← pow_mul, ← pow_succ]

/-- If `m ∣ kC q j s` then `s ^ q ^ (j + 1) ≡ 1 (mod m)`. -/
private theorem pow_modEq_one_of_dvd {m q j s : ℕ} (h : m ∣ kC q j s) :
    s ^ q ^ (j + 1) ≡ 1 [MOD m] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  have h0 : ((kC q j s : ℕ) : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  have := kC_mul_sub (R := ZMod m) q j s
  rw [h0, zero_mul] at this
  push_cast
  exact (sub_eq_zero.mp this.symm)

/-- If `m ∣ s ^ q ^ j` and `0 < q` then `kC q j s ≡ 1 (mod m)`. -/
private theorem kC_modEq_one {m q j s : ℕ} (hq : 0 < q) (h : m ∣ s ^ q ^ j) :
    kC q j s ≡ 1 [MOD m] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  have h0 : ((s ^ q ^ j : ℕ) : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  unfold kC
  rw [Finset.sum_range_succ']
  push_cast at h0 ⊢
  simp [h0]

/-- If `s ^ q ^ j ≡ 1 (mod m)` then `kC q j s ≡ q (mod m)`. -/
private theorem kC_modEq_self {m q j s : ℕ} (h : s ^ q ^ j ≡ 1 [MOD m]) :
    kC q j s ≡ q [MOD m] := by
  rw [← ZMod.natCast_eq_natCast_iff] at h ⊢
  unfold kC
  push_cast at h ⊢
  simp [h]

/-- Size of a geometric sum: `Y ^ (q - 1) < 1 + ... + Y ^ (q - 1) < q * Y ^ (q - 1)`. -/
private theorem geom_bounds {q Y : ℕ} (hq : 2 ≤ q) (hY : 2 ≤ Y) :
    Y ^ (q - 1) < ∑ i ∈ Finset.range q, Y ^ i ∧
      ∑ i ∈ Finset.range q, Y ^ i < q * Y ^ (q - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  constructor
  · rw [Finset.sum_range_succ]
    have : 1 ≤ ∑ i ∈ Finset.range r, Y ^ i := by
      obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
      rw [Finset.sum_range_succ']
      simp
    omega
  · have hlt : ∑ i ∈ Finset.range (r + 1), Y ^ i < ∑ _i ∈ Finset.range (r + 1), Y ^ r := by
      refine Finset.sum_lt_sum (fun i hi => Nat.pow_le_pow_right (by omega)
        (by simp at hi; omega)) ⟨0, by simp, ?_⟩
      simpa using Nat.one_lt_pow (by omega) (by omega : 1 < Y)
    simpa using hlt

/-- The product identity `∑_{i < a b} X ^ i = (∑_{i < a} X ^ i) (∑_{k < b} (X ^ a) ^ k)`. -/
private theorem geom_sum_mul_range (X a b : ℕ) :
    ∑ i ∈ Finset.range (a * b), X ^ i =
      (∑ i ∈ Finset.range a, X ^ i) * ∑ k ∈ Finset.range b, (X ^ a) ^ k := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [← pow_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add, mul_comm]

/-- `σ(s ^ (q ^ (j + 1) - 1)) = σ(s ^ (q ^ j - 1)) * kC q j s` for a prime `s`. -/
private theorem sigma_eq_mul_kC {q j s : ℕ} (hs : s.Prime) (hq : 0 < q) :
    σ 1 (s ^ (q ^ (j + 1) - 1)) = σ 1 (s ^ (q ^ j - 1)) * kC q j s := by
  have h1 : 0 < q ^ j := pow_pos hq j
  have h2 : 0 < q ^ (j + 1) := pow_pos hq (j + 1)
  rw [sigma_one_apply_prime_pow hs, sigma_one_apply_prime_pow hs, Nat.sub_add_cancel h1,
    Nat.sub_add_cancel h2, pow_succ, geom_sum_mul_range]
  rfl

/-! ## Blocks inside an odd perfect number -/

/-- A block of a prime factor `s` with `q ^ (j + 1) ∣ e_s + 1` divides `σ(s ^ e_s)`. -/
private theorem kC_dvd_sigma {N q j s : ℕ} (hs : s.Prime) (hq : 0 < q)
    (hj : q ^ (j + 1) ∣ N.factorization s + 1) : kC q j s ∣ σ 1 (s ^ N.factorization s) := by
  have h1 : kC q j s ∣ σ 1 (s ^ (q ^ (j + 1) - 1)) := by
    rw [sigma_eq_mul_kC hs hq]; exact dvd_mul_left _ _
  refine h1.trans (OPNExample.sigma_prime_pow_dvd hs ?_)
  rwa [Nat.sub_add_cancel (pow_pos hq (j + 1))]

/-- A block divides `2 N`. -/
private theorem kC_dvd_two_mul {N q j s : ℕ} (h : OddPerfect N) (hs : s.Prime) (hq : 0 < q)
    (hj : q ^ (j + 1) ∣ N.factorization s + 1) : kC q j s ∣ 2 * N :=
  (kC_dvd_sigma hs hq hj).trans (OPNStarter.component_sigma_dvd h.perfect hs rfl)

/-- Prime factors of a block. Let `s` be a prime factor of the odd perfect number `N` and
`q ^ (j + 1) ∣ e_s + 1`. A prime `t ≠ q` dividing `kC q j s` divides `N`, is `≡ 1 (mod q)`,
differs from `s`, and `s` has order `q ^ (j + 1)` modulo `t`. -/
private theorem prime_dvd_kC {N q j s t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hs : s ∈ N.primeFactors) (hj : q ^ (j + 1) ∣ N.factorization s + 1)
    (ht : t.Prime) (htd : t ∣ kC q j s) (htq : t ≠ q) :
    t ∈ N.primeFactors ∧ t % q = 1 ∧ t ≠ s ∧ orderOf (s : ZMod t) = q ^ (j + 1) := by
  have : Fact t.Prime := ⟨ht⟩
  have : Fact q.Prime := ⟨hq⟩
  have hsp := Nat.prime_of_mem_primeFactors hs
  have hs2 : s % 2 = 1 := by
    have : ¬ 2 ∣ s := fun h2 => h.not_two_dvd (h2.trans (Nat.dvd_of_mem_primeFactors hs))
    omega
  have hY : ¬ s ^ q ^ j ≡ 1 [MOD t] := by
    intro hY
    have h1 := kC_modEq_self (q := q) hY
    have h0 : kC q j s ≡ 0 [MOD t] := Nat.modEq_zero_iff_dvd.mpr htd
    have : t ∣ q := Nat.modEq_zero_iff_dvd.mp (h1.symm.trans h0)
    exact htq ((Nat.prime_dvd_prime_iff_eq ht hq).mp this)
  have ht2 : t ≠ 2 := by
    rintro rfl
    apply hY
    change s ^ q ^ j % 2 = 1 % 2
    rw [Nat.pow_mod, hs2]
    simp
  have htN : t ∣ N :=
    (ht.dvd_mul.mp (htd.trans (kC_dvd_two_mul h hsp hq.pos hj))).resolve_left fun h2 =>
      ht2 ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_two).mp h2)
  have hfin : (s : ZMod t) ^ q ^ (j + 1) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (pow_modEq_one_of_dvd htd)
    push_cast at this
    exact this
  have hnot : ¬ (s : ZMod t) ^ q ^ j = 1 := by
    intro h1
    apply hY
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact h1
  have hord : orderOf (s : ZMod t) = q ^ (j + 1) := orderOf_eq_prime_pow hnot hfin
  have hs0 : (s : ZMod t) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_ne_zero _ hq.ne_zero)] at hfin
    exact zero_ne_one hfin
  refine ⟨Nat.mem_primeFactors.mpr ⟨ht, htN, h.ne_zero⟩, ?_, ?_, hord⟩
  · have h1 := ZMod.orderOf_dvd_card_sub_one hs0
    rw [hord] at h1
    have h2 : q ∣ t - 1 := (dvd_pow_self q (Nat.succ_ne_zero j)).trans h1
    have h3 : 1 ≡ t [MOD q] := (Nat.modEq_iff_dvd' ht.one_lt.le).mpr h2
    rw [Nat.ModEq, Nat.mod_eq_of_lt hq.one_lt] at h3
    exact h3.symm
  · rintro rfl
    exact hs0 (ZMod.natCast_self t)

/-- A block of `s ≡ 1 (mod q)` is divisible by `q` exactly once. -/
private theorem factorization_kC_self {q j s : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hs : s.Prime)
    (hs1 : s % q = 1) : (kC q j s).factorization q = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hd : q ∣ s - 1 := by have := Nat.dvd_sub_mod (n := q) s; rwa [hs1] at this
  have hv : ∀ k, padicValNat q (σ 1 (s ^ (q ^ k - 1))) = k := fun k => by
    rw [padicValNat_sigma_prime_pow_of_dvd_pred hs hq hq2 hd,
      Nat.sub_add_cancel (pow_pos hq.pos k), padicValNat.prime_pow]
  have hσ : ∀ k, σ 1 (s ^ (q ^ k - 1)) ≠ 0 := fun k =>
    (ArithmeticFunction.sigma_pos 1 _ (pow_ne_zero _ hs.ne_zero)).ne'
  have hk : kC q j s ≠ 0 := by
    intro h0
    have := hσ (j + 1)
    rw [sigma_eq_mul_kC hs hq.pos, h0, mul_zero] at this
    exact this rfl
  have := hv (j + 1)
  rw [sigma_eq_mul_kC hs hq.pos, padicValNat.mul (hσ j) hk, hv j] at this
  rw [Nat.factorization_def _ hq]
  omega

/-- Exponents in a block are bounded by the exponents in `N`. -/
private theorem le_factorization_of_pow_dvd_kC {N q j s t k : ℕ} (h : OddPerfect N)
    (hq : 0 < q) (hs : s.Prime) (hj : q ^ (j + 1) ∣ N.factorization s + 1) (ht : t.Prime)
    (ht2 : t ≠ 2) (hd : t ^ k ∣ kC q j s) : k ≤ N.factorization t := by
  have h2 : t ^ k ∣ 2 * N := hd.trans (kC_dvd_two_mul h hs hq hj)
  have hc : (t ^ k).Coprime 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes ht Nat.prime_two).mpr ht2)
  exact (ht.pow_dvd_iff_le_factorization h.ne_zero).mp (hc.dvd_of_dvd_mul_left h2)

/-- A block is larger than `s`. -/
private theorem lt_kC {q j s : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) : s < kC q j s := by
  have hY : s ≤ s ^ q ^ j := Nat.le_self_pow (pow_ne_zero _ (by omega)) s
  have h1 := (geom_bounds hq (le_trans hs hY)).1
  have h2 : s ^ q ^ j ≤ (s ^ q ^ j) ^ (q - 1) := Nat.le_self_pow (by omega) _
  unfold kC
  omega

/-! ## The setting of the normal form -/

/-- The prime factors of `N` that are `≡ 1 (mod q)`. -/
def kS (N q : ℕ) : Finset ℕ := N.primeFactors.filter (fun p => p % q = 1)

/-- The normal form of the square case with `q ≥ 13`, together with Kanold's obstruction:
`|S| = 4`, `e_D + 1 = q ^ 3` for one member `D` of `S`, and `e_s + 1 = q ^ 2` for the others. -/
structure KSetup (N q D : ℕ) : Prop where
  opn : OddPerfect N
  prime : q.Prime
  le13 : 13 ≤ q
  obs : KanoldObstructionAt q
  card : (kS N q).card = 4
  memD : D ∈ kS N q
  expD : N.factorization D + 1 = q ^ 3
  exp : ∀ s ∈ kS N q, s ≠ D → N.factorization s + 1 = q ^ 2

/-- Kanold's pure relation: some block of `s` is `q` times a positive power of `t`. -/
def KPure (q s t : ℕ) : Prop := ∃ j a, 0 < a ∧ kC q j s = q * t ^ a

namespace KSetup

variable {N q D : ℕ}

/-- Members of `S` are prime factors `≡ 1 (mod q)`. -/
theorem mem {s : ℕ} (hs : s ∈ kS N q) : s ∈ N.primeFactors ∧ s % q = 1 :=
  Finset.mem_filter.mp hs

/-- Members of `S` are prime. -/
theorem prime_of {s : ℕ} (hs : s ∈ kS N q) : s.Prime :=
  Nat.prime_of_mem_primeFactors (mem hs).1

/-- Members of `S` exceed `q`. -/
theorem lt_of (st : KSetup N q D) {s : ℕ} (hs : s ∈ kS N q) : q < s := by
  have h1 := (mem hs).2
  have h2 := (prime_of hs).two_le
  by_contra hle
  rcases (show s < q ∨ s = q by omega) with hlt | rfl
  · rw [Nat.mod_eq_of_lt hlt] at h1; omega
  · rw [Nat.mod_self] at h1; omega

/-- Members of `S` are odd. -/
theorem ne_two (st : KSetup N q D) {s : ℕ} (hs : s ∈ kS N q) : s ≠ 2 := by
  have := st.lt_of hs; have := st.le13; omega

/-- The special prime is odd. -/
theorem q2 (st : KSetup N q D) : q ≠ 2 := by have := st.le13; omega

/-- Valid blocks: indices `0, 1` always, and `2` for `D`. -/
theorem valid (st : KSetup N q D) {s j : ℕ} (hs : s ∈ kS N q) (hj : j ≤ 1 ∨ (s = D ∧ j = 2)) :
    q ^ (j + 1) ∣ N.factorization s + 1 := by
  by_cases hsD : s = D
  · subst hsD; rw [st.expD]; exact pow_dvd_pow q (by omega)
  · rw [st.exp s hs hsD]; exact pow_dvd_pow q (by omega)

/-- Four distinct members exhaust `S`. -/
theorem cover (st : KSetup N q D) {a b c d : ℕ} (ha : a ∈ kS N q) (hb : b ∈ kS N q)
    (hc : c ∈ kS N q) (hd : d ∈ kS N q) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∀ t ∈ kS N q, t = a ∨ t = b ∨ t = c ∨ t = d := by
  have hsub : ({a, b, c, d} : Finset ℕ) ⊆ kS N q := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, d} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [st.card, hcard])
  intro t ht
  rw [← heq] at ht
  simpa using ht

/-- The factored form of a block: `kC q j s = q * a ^ v_a * b ^ v_b * c ^ v_c`, where
`a, b, c` are the other three members of `S`. -/
theorem form (st : KSetup N q D) {s j a b c : ℕ} (hs : s ∈ kS N q)
    (hj : q ^ (j + 1) ∣ N.factorization s + 1) (ha : a ∈ kS N q) (hb : b ∈ kS N q)
    (hc : c ∈ kS N q) (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    kC q j s = q * a ^ (kC q j s).factorization a * b ^ (kC q j s).factorization b *
      c ^ (kC q j s).factorization c := by
  have hq := st.prime
  have hn : kC q j s ≠ 0 := by
    have := lt_kC (j := j) hq.two_le (prime_of hs).two_le; omega
  have hcov := st.cover hs ha hb hc hsa hsb hsc hab hac hbc
  have hqa : q ≠ a := (st.lt_of ha).ne
  have hqb : q ≠ b := (st.lt_of hb).ne
  have hqc : q ≠ c := (st.lt_of hc).ne
  have hsub : (kC q j s).primeFactors ⊆ {q, a, b, c} := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    by_cases hpq : p = q
    · simp [hpq]
    obtain ⟨hpN, hp1, hps, -⟩ := prime_dvd_kC st.opn hq (mem hs).1 hj hpp hpd hpq
    rcases hcov p (Finset.mem_filter.mpr ⟨hpN, hp1⟩) with h | h | h | h
    · exact absurd h hps
    all_goals simp [h]
  have key := Nat.prod_factorization_pow_eq_self hn
  rw [Finsupp.prod, Nat.support_factorization, Finset.prod_subset hsub (fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization]), pow_zero])] at key
  rw [Finset.prod_insert (by simp [hqa, hqb, hqc]), Finset.prod_insert (by simp [hab, hac]),
    Finset.prod_insert (by simp [hbc]), Finset.prod_singleton,
    factorization_kC_self hq st.q2 (prime_of hs) (mem hs).2, pow_one] at key
  conv_lhs => rw [← key]
  ring

/-- Different blocks of `s` have no common prime factor in `S`. -/
theorem disj (st : KSetup N q D) {s i j t : ℕ} (hs : s ∈ kS N q)
    (hi : q ^ (i + 1) ∣ N.factorization s + 1) (hj : q ^ (j + 1) ∣ N.factorization s + 1)
    (hij : i ≠ j) (ht : t ∈ kS N q) :
    (kC q i s).factorization t = 0 ∨ (kC q j s).factorization t = 0 := by
  by_contra hc
  push Not at hc
  have htp := prime_of ht
  have htq : t ≠ q := (st.lt_of ht).ne'
  have h1 := (prime_dvd_kC st.opn st.prime (mem hs).1 hi htp
    (Nat.dvd_of_factorization_pos hc.1) htq).2.2.2
  have h2 := (prime_dvd_kC st.opn st.prime (mem hs).1 hj htp
    (Nat.dvd_of_factorization_pos hc.2) htq).2.2.2
  rw [h1] at h2
  exact hij (by have := Nat.pow_right_injective st.prime.two_le h2; omega)

/-- `q < kC q j s` for `s ∈ S`. -/
theorem big (st : KSetup N q D) {s : ℕ} (j : ℕ) (hs : s ∈ kS N q) : q < kC q j s :=
  lt_trans (st.lt_of hs) (lt_kC st.prime.two_le (prime_of hs).two_le)

/-- Kanold's obstruction in the pure language. -/
theorem noK (st : KSetup N q D) {s t : ℕ} (hs : s.Prime) (ht : t.Prime) (h1 : KPure q s t)
    (h2 : KPure q t s) : False := by
  obtain ⟨i, a, ha, h1⟩ := h1
  obtain ⟨j, b, hb, h2⟩ := h2
  exact st.obs s t i j a b hs ht ha hb h1 h2

/-- The facts about one block in the factored form used by the support analysis. -/
theorem block (st : KSetup N q D) {s j a b c : ℕ} (hs : s ∈ kS N q)
    (hj : q ^ (j + 1) ∣ N.factorization s + 1) (ha : a ∈ kS N q) (hb : b ∈ kS N q)
    (hc : c ∈ kS N q) (hsa : s ≠ a) (hsb : s ≠ b) (hsc : s ≠ c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    0 < (kC q j s).factorization a + (kC q j s).factorization b + (kC q j s).factorization c ∧
    ((kC q j s).factorization b = 0 → (kC q j s).factorization c = 0 → KPure q s a) ∧
    ((kC q j s).factorization a = 0 → (kC q j s).factorization c = 0 → KPure q s b) ∧
    ((kC q j s).factorization a = 0 → (kC q j s).factorization b = 0 → KPure q s c) := by
  have hf := st.form hs hj ha hb hc hsa hsb hsc hab hac hbc
  have hbig := st.big j hs
  set x := (kC q j s).factorization a
  set y := (kC q j s).factorization b
  set z := (kC q j s).factorization c
  refine ⟨?_, fun h1 h2 => ⟨j, x, ?_, ?_⟩, fun h1 h2 => ⟨j, y, ?_, ?_⟩,
    fun h1 h2 => ⟨j, z, ?_, ?_⟩⟩
  · by_contra h0
    have : x = 0 ∧ y = 0 ∧ z = 0 := by omega
    rw [hf, this.1, this.2.1, this.2.2] at hbig; simp at hbig
  · by_contra h0
    rw [hf, h1, h2, show x = 0 by omega] at hbig; simp at hbig
  · rw [hf, h1, h2]; simp
  · by_contra h0
    rw [hf, h1, h2, show y = 0 by omega] at hbig; simp at hbig
  · rw [hf, h1, h2]; simp
  · by_contra h0
    rw [hf, h1, h2, show z = 0 by omega] at hbig; simp at hbig
  · rw [hf, h1, h2]; simp

end KSetup

/-! ## Support analysis -/

private theorem or_of_imp {P : Prop} {a b : ℕ} (h : a = 0 → b = 0 → P) (hn : ¬ P) :
    0 < a ∨ 0 < b := by
  by_contra hc
  exact hn (h (by omega) (by omega))

namespace KSetup

variable {N q D : ℕ}

/-- If neither `s → x` nor `s → y` is pure, then `s → z` is pure (two disjoint nonempty
supports in `{x, y, z}` contain a singleton). -/
theorem split_two (st : KSetup N q D) {s x y z : ℕ} (hs : s ∈ kS N q) (hx : x ∈ kS N q)
    (hy : y ∈ kS N q) (hz : z ∈ kS N q) (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (nx : ¬ KPure q s x) (ny : ¬ KPure q s y) :
    KPure q s z := by
  have v0 := st.valid (j := 0) hs (Or.inl (Nat.zero_le 1))
  have v1 := st.valid (j := 1) hs (Or.inl le_rfl)
  obtain ⟨n0, p0x, p0y, p0z⟩ := st.block hs v0 hx hy hz hsx hsy hsz hxy hxz hyz
  obtain ⟨n1, p1x, p1y, p1z⟩ := st.block hs v1 hx hy hz hsx hsy hsz hxy hxz hyz
  have dx := st.disj hs v0 v1 (by norm_num) hx
  have dy := st.disj hs v0 v1 (by norm_num) hy
  have dz := st.disj hs v0 v1 (by norm_num) hz
  by_contra nz
  have a1 := or_of_imp p0x nx
  have a2 := or_of_imp p0y ny
  have a3 := or_of_imp p0z nz
  have a4 := or_of_imp p1x nx
  have a5 := or_of_imp p1y ny
  have a6 := or_of_imp p1z nz
  omega

/-- If `x` divides neither block of `s`, then `s → y` and `s → z` are pure. -/
theorem split_excl (st : KSetup N q D) {s x y z : ℕ} (hs : s ∈ kS N q) (hx : x ∈ kS N q)
    (hy : y ∈ kS N q) (hz : z ∈ kS N q) (hsx : s ≠ x) (hsy : s ≠ y) (hsz : s ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (h0 : ¬ x ∣ kC q 0 s) (h1 : ¬ x ∣ kC q 1 s) :
    KPure q s y ∧ KPure q s z := by
  have v0 := st.valid (j := 0) hs (Or.inl (Nat.zero_le 1))
  have v1 := st.valid (j := 1) hs (Or.inl le_rfl)
  obtain ⟨n0, -, p0y, p0z⟩ := st.block hs v0 hx hy hz hsx hsy hsz hxy hxz hyz
  obtain ⟨n1, -, p1y, p1z⟩ := st.block hs v1 hx hy hz hsx hsy hsz hxy hxz hyz
  have dy := st.disj hs v0 v1 (by norm_num) hy
  have dz := st.disj hs v0 v1 (by norm_num) hz
  have e0 := Nat.factorization_eq_zero_of_not_dvd h0
  have e1 := Nat.factorization_eq_zero_of_not_dvd h1
  rcases (by omega : ((kC q 0 s).factorization y = 0 ∧ (kC q 1 s).factorization z = 0) ∨
      ((kC q 0 s).factorization z = 0 ∧ (kC q 1 s).factorization y = 0)) with ⟨a, b⟩ | ⟨a, b⟩
  · exact ⟨p1y e1 b, p0z e0 a⟩
  · exact ⟨p0y e0 a, p1z e1 b⟩

end KSetup

/-! ## Congruence helpers -/

/-- From `a b ≡ 1` and `b ^ n ≡ 1` follows `a ^ n ≡ 1`. -/
private theorem pow_modEq_one_of_mul {a b n m : ℕ} (h1 : a * b ≡ 1 [MOD m])
    (h2 : b ^ n ≡ 1 [MOD m]) : a ^ n ≡ 1 [MOD m] :=
  calc a ^ n = a ^ n * 1 := (mul_one _).symm
    _ ≡ a ^ n * b ^ n [MOD m] := Nat.ModEq.mul_left _ h2.symm
    _ = (a * b) ^ n := (mul_pow a b n).symm
    _ ≡ 1 ^ n [MOD m] := Nat.ModEq.pow n h1
    _ = 1 := one_pow n

/-- From `x ^ n ≡ 1` follows `(x ^ k) ^ n ≡ 1`. -/
private theorem pow_pow_modEq_one {x n k m : ℕ} (h : x ^ n ≡ 1 [MOD m]) :
    (x ^ k) ^ n ≡ 1 [MOD m] := by
  rw [← pow_mul, mul_comm, pow_mul]; simpa using h.pow k

/-- For `2 ≤ q < D` and `n ≠ 0`, `q ^ n ≢ 1 (mod D ^ n)`. -/
private theorem not_pow_modEq_one {q D n : ℕ} (hq : 2 ≤ q) (hqD : q < D) (hn : n ≠ 0) :
    ¬ q ^ n ≡ 1 [MOD D ^ n] := by
  intro h
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have h2 := (Nat.modEq_iff_dvd' h1).mp h.symm
  have h3 : 1 < q ^ n := Nat.one_lt_pow hn (by omega)
  have h4 := Nat.le_of_dvd (by omega) h2
  have h5 : q ^ n < D ^ n := Nat.pow_lt_pow_left hqD hn
  omega

/-- The geometric identity in `ℕ`. -/
private theorem kC_mul_sub_nat {q j s : ℕ} (hs : 1 ≤ s) :
    kC q j s * (s ^ q ^ j - 1) = s ^ q ^ (j + 1) - 1 := by
  have h1 : 1 ≤ s ^ q ^ j := Nat.one_le_pow _ _ hs
  have h2 : 1 ≤ s ^ q ^ (j + 1) := Nat.one_le_pow _ _ hs
  have := kC_mul_sub (R := ℤ) q j s
  zify [h1, h2]
  exact this

/-- The square of the block relation: `m ∣ kC q 0 s` or `m ∣ kC q 1 s` gives
`s ^ q ^ 2 ≡ 1 (mod m)`. -/
private theorem pow_sq_modEq_one {m q s : ℕ} (h : m ∣ kC q 0 s ∨ m ∣ kC q 1 s) :
    s ^ q ^ 2 ≡ 1 [MOD m] := by
  rcases h with h | h
  · have := (pow_modEq_one_of_dvd h).pow q
    rw [← pow_mul] at this
    simpa [sq] using this
  · exact pow_modEq_one_of_dvd h

/-! ## Logarithmic sizes -/

private theorem log_lt_of_lt {x y : ℕ} (hx : 0 < x) (h : x < y) :
    Real.log x < Real.log y :=
  Real.log_lt_log (Nat.cast_pos.mpr hx) (Nat.cast_lt.mpr h)

/-- `(q - 1) q ^ j log s < log (kC q j s) < log q + (q - 1) q ^ j log s`. -/
private theorem log_kC_bounds {q j s : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) :
    ((q : ℝ) - 1) * (q : ℝ) ^ j * Real.log s < Real.log (kC q j s) ∧
      Real.log (kC q j s) < Real.log q + ((q : ℝ) - 1) * (q : ℝ) ^ j * Real.log s := by
  have hY : 2 ≤ s ^ q ^ j := le_trans hs (Nat.le_self_pow (pow_ne_zero _ (by omega)) s)
  obtain ⟨h1, h2⟩ := geom_bounds hq hY
  change (s ^ q ^ j) ^ (q - 1) < kC q j s at h1
  change kC q j s < q * (s ^ q ^ j) ^ (q - 1) at h2
  have e : Real.log (((s ^ q ^ j) ^ (q - 1) : ℕ) : ℝ) =
      ((q : ℝ) - 1) * (q : ℝ) ^ j * Real.log s := by
    rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
    ring
  have hpos : 0 < (s ^ q ^ j) ^ (q - 1) := by positivity
  constructor
  · rw [← e]; exact log_lt_of_lt hpos h1
  · have := log_lt_of_lt (by omega) h2
    rw [Nat.cast_mul, Real.log_mul (Nat.cast_pos.mpr (by omega)).ne'
      (Nat.cast_pos.mpr hpos).ne', e] at this
    exact this

private theorem log_mul_pow {q x a : ℕ} (hq : 0 < q) (hx : 0 < x) :
    Real.log ((q * x ^ a : ℕ) : ℝ) = Real.log q + a * Real.log x := by
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (Nat.cast_pos.mpr hq).ne'
    (pow_ne_zero _ (Nat.cast_pos.mpr hx).ne'), Real.log_pow]

private theorem log_mul_pow_pow {q x y a b : ℕ} (hq : 0 < q) (hx : 0 < x) (hy : 0 < y) :
    Real.log ((q * x ^ a * y ^ b : ℕ) : ℝ) =
      Real.log q + a * Real.log x + b * Real.log y := by
  rw [show ((q * x ^ a * y ^ b : ℕ) : ℝ) = ((q * x ^ a : ℕ) : ℝ) * (y : ℝ) ^ b by push_cast; ring,
    Real.log_mul (Nat.cast_pos.mpr (Nat.mul_pos hq (pow_pos hx a))).ne'
      (pow_ne_zero _ (Nat.cast_pos.mpr hy).ne'),
    log_mul_pow hq hx, Real.log_pow]

private theorem step6_real {Q l d a b e H e2 e4 f3 f4 k : ℝ} (hQ : 13 ≤ Q) (hl : 0 < l) (hld : l < d)
    (hla : l < a) (hlb : l < b) (hle : l < e) (hH : H ≤ Q - 1)
    (he2 : e2 ≤ Q ^ 2 - 1) (he4 : e4 ≤ Q ^ 3 - 1) (hf3 : f3 ≤ Q ^ 2 - 1) (hf4 : f4 ≤ Q ^ 3 - 1)
    (hk : 1 ≤ k)
    (R1 : (Q - 1) * Q ^ 2 * d < l + H * a) (R2 : (Q - 1) * Q * a < l + e2 * b + e4 * d)
    (R3 : (Q - 1) * Q * b < l + f3 * e + f4 * d)
    (R4 : k * b < (Q - 1) * d ∨ k * e < (Q - 1) * d) : False := by
  have hd : 0 < d := by linarith
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have he : 0 < e := by linarith
  have hQ0 : 0 < Q := by linarith
  have r1 : (Q - 1) * Q ^ 2 * d < d + (Q - 1) * a := by
    nlinarith [mul_le_mul_of_nonneg_right hH ha.le]
  have r2 : (Q - 1) * Q * a < d + Q ^ 2 * b + Q ^ 3 * d := by
    nlinarith [mul_le_mul_of_nonneg_right he2 hb.le, mul_le_mul_of_nonneg_right he4 hd.le]
  have r3 : (Q - 1) * Q * b < d + Q ^ 2 * e + Q ^ 3 * d := by
    nlinarith [mul_le_mul_of_nonneg_right hf3 he.le, mul_le_mul_of_nonneg_right hf4 hd.le]
  -- `x < Q d` gives a bound `y < c Q d` from `(Q - 1) Q y < d + Q ^ 2 x + Q ^ 3 d`
  have step : ∀ x y c : ℝ, 2 ≤ c → c ≤ 5 → x < c * Q * d →
      (Q - 1) * Q * y < d + Q ^ 2 * x + Q ^ 3 * d → y < (c + 2) * Q * d := by
    intro x y c hc2 hc5 hx hy
    by_contra hc
    push Not at hc
    have h1 : (Q - 1) * Q * ((c + 2) * Q * d) ≤ (Q - 1) * Q * y :=
      mul_le_mul_of_nonneg_left hc (by nlinarith)
    have h2 : Q ^ 2 * x < Q ^ 2 * (c * Q * d) := mul_lt_mul_of_pos_left hx (by positivity)
    have h3 : 0 < (Q ^ 3 - (c + 2) * Q ^ 2 - 1) * d := by
      apply mul_pos _ hd
      nlinarith [mul_le_mul_of_nonneg_left hc5 (by positivity : (0 : ℝ) ≤ Q ^ 2)]
    linarith
  have fin : a < 6 * Q * d → False := by
    intro ha6
    have h2 : (Q - 1) * a < (Q - 1) * (6 * Q * d) := mul_lt_mul_of_pos_left ha6 (by linarith)
    have h3 : 0 < (Q ^ 3 - 7 * Q ^ 2 + 6 * Q - 1) * d := by
      apply mul_pos _ hd; nlinarith
    nlinarith
  rcases R4 with R4 | R4
  · have hbq : b < 2 * Q * d := by nlinarith [mul_le_mul_of_nonneg_right hk hb.le]
    have := step b a 2 le_rfl (by norm_num) hbq r2
    exact fin (by nlinarith [mul_pos hQ0 hd])
  · have heq : e < 2 * Q * d := by nlinarith [mul_le_mul_of_nonneg_right hk he.le]
    have hb3 := step e b 2 le_rfl (by norm_num) heq r3
    have ha4 := step b a 4 (by norm_num) (by norm_num) (by linarith) r2
    exact fin (by linarith)

private theorem step7a_real {Q l d a b H e2 e4 f1 : ℝ} (hQ : 13 ≤ Q) (hl : 0 < l) (hld : l < d)
    (hla : l < a) (hlb : l < b) (hf1 : f1 ≤ Q - 4) (hH : H ≤ Q ^ 2 - 1)
    (he2 : e2 ≤ Q ^ 2 - 1) (he4 : e4 ≤ Q ^ 2 - 1)
    (T1 : (Q - 1) * b < l + f1 * a) (T2 : (Q - 1) * Q * a < l + e2 * b + e4 * d)
    (T3 : (Q - 1) * Q ^ 2 * d < l + H * a) : False := by
  have hd : 0 < d := by linarith
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have t1 : (Q - 1) * b < l + (Q - 4) * a := by nlinarith [mul_le_mul_of_nonneg_right hf1 ha.le]
  have t1' : (Q ^ 2 - 1) * b < (Q + 1) * l + (Q + 1) * (Q - 4) * a := by
    nlinarith [mul_lt_mul_of_pos_left t1 (by linarith : (0 : ℝ) < Q + 1)]
  have t2 : (Q - 1) * Q * a < l + (Q ^ 2 - 1) * b + e4 * d := by
    nlinarith [mul_le_mul_of_nonneg_right he2 hb.le]
  have t4 : (Q + 2) * a < e4 * d := by nlinarith
  have t5 : (Q + 2) * a < (Q ^ 2 - 1) * d := by nlinarith [mul_le_mul_of_nonneg_right he4 hd.le]
  have t3 : (Q - 1) * Q ^ 2 * d < d + (Q ^ 2 - 1) * a := by
    nlinarith [mul_le_mul_of_nonneg_right hH ha.le]
  have t6 := mul_lt_mul_of_pos_left t3 (by linarith : (0 : ℝ) < Q + 2)
  have t7 := mul_lt_mul_of_pos_left t5 (by nlinarith : (0 : ℝ) < Q ^ 2 - 1)
  have h3 : 0 < (Q ^ 3 - Q - 3) * d := by apply mul_pos _ hd; nlinarith
  nlinarith

private theorem step7b_real {Q l d a H : ℝ} (hQ : 13 ≤ Q) (hl : 0 < l) (hd2 : 2 * l < d)
    (hla : l < a) (hH : H ≤ Q ^ 2 - 1)
    (T0 : (Q - 3) * a < Q ^ 2 * l) (T3 : (Q - 1) * Q ^ 2 * d < l + H * a) : False := by
  have ha : 0 < a := by linarith
  have t3 : (Q - 1) * Q ^ 2 * (2 * l) < l + (Q ^ 2 - 1) * a := by
    nlinarith [mul_le_mul_of_nonneg_right hH ha.le,
      mul_lt_mul_of_pos_left hd2 (by nlinarith : (0 : ℝ) < (Q - 1) * Q ^ 2)]
  have t4 := mul_lt_mul_of_pos_left t3 (by linarith : (0 : ℝ) < Q - 3)
  have t5 := mul_lt_mul_of_pos_left T0 (by nlinarith : (0 : ℝ) < Q ^ 2 - 1)
  have h3 : 0 < (Q ^ 4 - 8 * Q ^ 3 + 7 * Q ^ 2 - Q + 3) * l := by
    apply mul_pos _ hl; nlinarith [sq_nonneg (Q ^ 2 - 8 * Q)]
  nlinarith

/-! ## The labeled configuration -/

namespace KSetup

variable {N q D : ℕ}

/-- The configuration after Steps 0 and 1. `D` has `e_D + 1 = q ^ 3`, its block `kC q 2 D` is
`q` times a power of `A`, its blocks `0, 1` are `q` times powers of `B` and of `E`, and the
blocks of `A` are `q * E ^ e3` and `q * B ^ e2 * D ^ e4`. This is impossible. -/
theorem core (st : KSetup N q D) {A B E : ℕ} (hA : A ∈ kS N q) (hB : B ∈ kS N q)
    (hE : E ∈ kS N q) (hDA : D ≠ A) (hDB : D ≠ B) (hDE : D ≠ E) (hAB : A ≠ B) (hAE : A ≠ E)
    (hBE : B ≠ E) {h : ℕ} (hh0 : 0 < h) (hh : kC q 2 D = q * A ^ h)
    (hDBp : ∃ i ≤ 1, ∃ k, 0 < k ∧ kC q i D = q * B ^ k)
    (hDEp : ∃ i ≤ 1, ∃ k, 0 < k ∧ kC q i D = q * E ^ k)
    (hD0 : ∃ k, 0 < k ∧ (kC q 0 D = q * B ^ k ∨ kC q 0 D = q * E ^ k))
    {γ e2 e3 e4 : ℕ} (hγ : γ ≤ 1) (he3 : 0 < e3) (he4 : 0 < e4)
    (hA3 : kC q γ A = q * E ^ e3) (hA2 : kC q (1 - γ) A = q * B ^ e2 * D ^ e4) : False := by
  have hq := st.prime
  have hq13 := st.le13
  have hD := st.memD
  have pD := prime_of hD
  have pA := prime_of hA
  have pB := prime_of hB
  have pE := prime_of hE
  have lD := st.lt_of hD
  have lA := st.lt_of hA
  have lB := st.lt_of hB
  have lE := st.lt_of hE
  obtain ⟨i, hi, k, hk, hiB⟩ := hDBp
  obtain ⟨i', hi', k', hk', hiE⟩ := hDEp
  have pDA : KPure q D A := ⟨2, h, hh0, hh⟩
  have pDB : KPure q D B := ⟨i, k, hk, hiB⟩
  have pDE : KPure q D E := ⟨i', k', hk', hiE⟩
  have pAE : KPure q A E := ⟨γ, e3, he3, hA3⟩
  have vD2 := st.valid (j := 2) hD (Or.inr ⟨rfl, rfl⟩)
  have vA1 := st.valid (j := 1) hA (Or.inl le_rfl)
  have vB0 := st.valid (j := 0) hB (Or.inl (Nat.zero_le 1))
  have vB1 := st.valid (j := 1) hB (Or.inl le_rfl)
  -- Step 2: `q ∣ e4`
  have hAinE : A ∣ kC q 0 E ∨ A ∣ kC q 1 E := by
    by_contra hc
    push Not at hc
    exact st.noK pD pE pDE (st.split_excl hE hA hB hD hAE.symm hBE.symm hDE.symm hAB hDA.symm
      hDB.symm hc.1 hc.2).2
  have hAinB : A ∣ kC q 0 B ∨ A ∣ kC q 1 B := by
    by_contra hc
    push Not at hc
    exact st.noK pD pB pDB (st.split_excl hB hA hE hD hAB.symm hBE hDB.symm hAE hDA.symm
      hDE.symm hc.1 hc.2).2
  have hEA : E ^ q ^ 2 ≡ 1 [MOD A] := pow_sq_modEq_one hAinE
  have hBA : B ^ q ^ 2 ≡ 1 [MOD A] := pow_sq_modEq_one hAinB
  have hA1 : ∀ j, kC q j A ≡ 1 [MOD A] := fun j =>
    kC_modEq_one hq.pos (dvd_pow_self A (pow_ne_zero _ hq.ne_zero))
  have hqA : q ^ q ^ 2 ≡ 1 [MOD A] :=
    pow_modEq_one_of_mul (b := E ^ e3) (by rw [← hA3]; exact hA1 γ) (pow_pow_modEq_one hEA)
  have hDA4 : (D ^ e4) ^ q ^ 2 ≡ 1 [MOD A] := by
    refine pow_modEq_one_of_mul (b := q * B ^ e2) ?_ ?_
    · have := hA1 (1 - γ); rw [hA2] at this; rwa [mul_comm]
    · rw [mul_pow]
      have := hqA.mul (pow_pow_modEq_one (k := e2) hBA)
      simpa using this
  have hordDA : orderOf (D : ZMod A) = q ^ (2 + 1) :=
    (prime_dvd_kC st.opn hq (mem hD).1 vD2 pA
      (by rw [hh]; exact dvd_mul_of_dvd_right (dvd_pow_self A hh0.ne') q) lA.ne').2.2.2
  have hqe4 : q ∣ e4 := by
    have : Fact A.Prime := ⟨pA⟩
    have h1 : (D : ZMod A) ^ (e4 * q ^ 2) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hDA4
      push_cast at this
      rwa [← pow_mul] at this
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hordDA, pow_succ] at h2
    exact Nat.dvd_of_mul_dvd_mul_right (pow_pos hq.pos 2) (by rwa [mul_comm] at h2)
  obtain ⟨c, hc⟩ := hqe4
  have hqe4' : q ≤ e4 := Nat.le_of_dvd he4 ⟨c, hc⟩
  have hqAD : ∀ m, m ∣ D ^ q ^ 2 → q * A ^ h ≡ 1 [MOD m] := fun m hm => by
    rw [← hh]; exact kC_modEq_one hq.pos hm
  have hDqe : D ^ q ∣ D ^ e4 := pow_dvd_pow D hqe4'
  have hDqq : D ^ q ∣ D ^ q ^ 2 := pow_dvd_pow D (Nat.le_self_pow two_ne_zero q)
  have hD4 : D ^ e4 ∣ kC q (1 - γ) A := by rw [hA2]; exact dvd_mul_left _ _
  -- Step 3: `γ = 0`
  have hγ0 : γ = 0 := by
    by_contra hγ1
    obtain rfl : γ = 1 := by omega
    have hAq : A ^ q ≡ 1 [MOD D ^ q] := by
      simpa using pow_modEq_one_of_dvd (j := 0) (hDqe.trans (by simpa using hD4))
    exact not_pow_modEq_one hq.two_le lD hq.ne_zero
      (pow_modEq_one_of_mul (hqAD _ hDqq) (pow_pow_modEq_one hAq))
  subst hγ0
  simp only [Nat.sub_zero] at hA2 hD4
  -- Step 4: `D ∤ q ^ q - 1` and `q ^ 2 < D`
  have hAq2 : A ^ q ^ 2 ≡ 1 [MOD D ^ q] := by
    simpa using pow_modEq_one_of_dvd (j := 1) (hDqe.trans hD4)
  have hqq2 : q ^ q ^ 2 ≡ 1 [MOD D ^ q] :=
    pow_modEq_one_of_mul (hqAD _ hDqq) (pow_pow_modEq_one hAq2)
  have hnotD : ¬ q ^ q ≡ 1 [MOD D] := by
    intro h1
    have h2 : kC q 1 q ≡ q [MOD D] := kC_modEq_self (by simpa using h1)
    have hnd : ¬ D ∣ kC q 1 q := fun hd => by
      have h3 : D ∣ q := (Nat.modEq_zero_iff_dvd).mp
        ((h2.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd)))
      have := Nat.le_of_dvd hq.pos h3
      omega
    have hcop : (D ^ q).Coprime (kC q 1 q) :=
      Nat.Coprime.pow_left q ((Nat.Prime.coprime_iff_not_dvd pD).mpr hnd)
    have hid : kC q 1 q * (q ^ q - 1) = q ^ q ^ 2 - 1 := by
      simpa using kC_mul_sub_nat (q := q) (j := 1) (s := q) hq.one_lt.le
    have hdv : D ^ q ∣ q ^ q ^ 2 - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq.pos)).mp hqq2.symm
    rw [← hid] at hdv
    exact not_pow_modEq_one hq.two_le lD hq.ne_zero
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq.pos)).mpr (hcop.dvd_of_dvd_mul_left hdv)).symm
  have hDbig : q ^ 2 < D := by
    have : Fact D.Prime := ⟨pD⟩
    have : Fact q.Prime := ⟨hq⟩
    have hfin : (q : ZMod D) ^ q ^ (1 + 1) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hqq2.of_dvd (dvd_pow_self D hq.ne_zero))
      push_cast at this
      exact this
    have hnot : ¬ (q : ZMod D) ^ q ^ 1 = 1 := by
      intro h1
      apply hnotD
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      simpa using h1
    have hord := orderOf_eq_prime_pow hnot hfin
    have hq0 : (q : ZMod D) ≠ 0 := by
      intro h0
      rw [h0, zero_pow (pow_ne_zero _ hq.ne_zero)] at hfin
      exact zero_ne_one hfin
    have h1 := ZMod.orderOf_dvd_card_sub_one hq0
    rw [hord] at h1
    have := Nat.le_of_dvd (by have := pD.two_le; omega) h1
    show q ^ (1 + 1) < D
    omega
  -- Step 5: `kC q 0 B = q * A ^ f1`
  have hBD : ¬ D ∣ kC q 0 B := by
    intro hd
    have h1 : B ^ q ≡ 1 [MOD D] := by simpa using pow_modEq_one_of_dvd (j := 0) hd
    have h2 : q * B ^ k ≡ 1 [MOD D] := by
      rw [← hiB]; exact kC_modEq_one hq.pos (dvd_pow_self D (pow_ne_zero _ hq.ne_zero))
    exact hnotD (pow_modEq_one_of_mul h2 (pow_pow_modEq_one h1))
  have hf0 := st.form hB vB0 hA hE hD hAB.symm hBE hDB.symm hAE hDA.symm hDE.symm
  have hf1 := st.form hB vB1 hA hE hD hAB.symm hBE hDB.symm hAE hDA.symm hDE.symm
  obtain ⟨n0, -, p0E, p0D⟩ := st.block hB vB0 hA hE hD hAB.symm hBE hDB.symm hAE hDA.symm
    hDE.symm
  obtain ⟨n1, -, -, p1D⟩ := st.block hB vB1 hA hE hD hAB.symm hBE hDB.symm hAE hDA.symm
    hDE.symm
  have dA := st.disj hB vB0 vB1 (by norm_num) hA
  have dE := st.disj hB vB0 vB1 (by norm_num) hE
  have z0 : (kC q 0 B).factorization D = 0 := Nat.factorization_eq_zero_of_not_dvd hBD
  set x0 := (kC q 0 B).factorization A with hx0
  set y0 := (kC q 0 B).factorization E with hy0
  set x1 := (kC q 1 B).factorization A with hx1
  set y1 := (kC q 1 B).factorization E with hy1
  set z1 := (kC q 1 B).factorization D with hz1
  have hxy : 0 < x0 ∧ y0 = 0 := by
    by_contra hcon
    rcases (by omega : x0 = 0 ∨ (0 < x0 ∧ 0 < y0)) with h1 | ⟨h1, h2⟩
    · have pBE : KPure q B E := p0E h1 z0
      exact st.noK pD pE pDE (st.split_two hE hA hB hD hAE.symm hBE.symm hDE.symm hAB hDA.symm
        hDB.symm (fun p => st.noK pE pA p pAE) (fun p => st.noK pE pB p pBE))
    · exact st.noK pD pB pDB (p1D (by omega) (by omega))
  have hx1z : x1 = 0 := by omega
  have hB0 : kC q 0 B = q * A ^ x0 := by
    rw [hf0, hxy.2, z0]; simp
  have hB1 : kC q 1 B = q * E ^ y1 * D ^ z1 := by
    rw [hf1, hx1z]; simp
  -- exponent bounds
  have bnd : ∀ {s j t a : ℕ}, s ∈ kS N q → q ^ (j + 1) ∣ N.factorization s + 1 → t ∈ kS N q →
      t ^ a ∣ kC q j s → a ≤ N.factorization t := fun hs hj ht hd =>
    le_factorization_of_pow_dvd_kC st.opn hq.pos (prime_of hs) hj (prime_of ht) (st.ne_two ht) hd
  have eB := st.exp B hB hDB.symm
  have eE := st.exp E hE hDE.symm
  have eA := st.exp A hA hDA.symm
  have eD := st.expD
  have be2 : e2 + 1 ≤ q ^ 2 := by
    have := bnd hA vA1 hB (by rw [hA2]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _); omega
  have be4 : e4 + 1 ≤ q ^ 3 := by
    have := bnd hA vA1 hD hD4; omega
  have by1 : y1 + 1 ≤ q ^ 2 := by
    have := bnd hB vB1 hE (by rw [hB1]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _); omega
  have bz1 : z1 + 1 ≤ q ^ 3 := by
    have := bnd hB vB1 hD (by rw [hB1]; exact dvd_mul_left _ _); omega
  have bh : h + 1 ≤ q ^ 2 := by
    have := bnd hD vD2 hA (by rw [hh]; exact dvd_mul_left _ _); omega
  -- logarithms
  have hl : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hld := log_lt_of_lt hq.pos lD
  have hla := log_lt_of_lt hq.pos lA
  have hlb := log_lt_of_lt hq.pos lB
  have hle := log_lt_of_lt hq.pos lE
  have hQ : (13 : ℝ) ≤ q := by exact_mod_cast hq13
  have L1 := (log_kC_bounds (j := 2) hq.two_le pD.two_le).1
  rw [hh, log_mul_pow hq.pos pA.pos] at L1
  have L2 := (log_kC_bounds (j := 1) hq.two_le pA.two_le).1
  rw [hA2, log_mul_pow_pow hq.pos pB.pos pD.pos, pow_one] at L2
  have rbh : (h : ℝ) ≤ (q : ℝ) ^ 2 - 1 := by
    have : ((h + 1 : ℕ) : ℝ) ≤ ((q ^ 2 : ℕ) : ℝ) := by exact_mod_cast bh
    push_cast at this; linarith
  have rbe2 : (e2 : ℝ) ≤ (q : ℝ) ^ 2 - 1 := by
    have : ((e2 + 1 : ℕ) : ℝ) ≤ ((q ^ 2 : ℕ) : ℝ) := by exact_mod_cast be2
    push_cast at this; linarith
  -- Step 6: `q ≤ h`
  have hhq : q ≤ h := by
    by_contra hlt
    push Not at hlt
    have L3 := (log_kC_bounds (j := 1) hq.two_le pB.two_le).1
    rw [hB1, log_mul_pow_pow hq.pos pE.pos pD.pos, pow_one] at L3
    obtain ⟨kk, hkk, hk0⟩ := hD0
    have L4 := (log_kC_bounds (j := 0) hq.two_le pD.two_le).2
    have rbe4 : (e4 : ℝ) ≤ (q : ℝ) ^ 3 - 1 := by
      have : ((e4 + 1 : ℕ) : ℝ) ≤ ((q ^ 3 : ℕ) : ℝ) := by exact_mod_cast be4
      push_cast at this; linarith
    have rby1 : (y1 : ℝ) ≤ (q : ℝ) ^ 2 - 1 := by
      have : ((y1 + 1 : ℕ) : ℝ) ≤ ((q ^ 2 : ℕ) : ℝ) := by exact_mod_cast by1
      push_cast at this; linarith
    have rbz1 : (z1 : ℝ) ≤ (q : ℝ) ^ 3 - 1 := by
      have : ((z1 + 1 : ℕ) : ℝ) ≤ ((q ^ 3 : ℕ) : ℝ) := by exact_mod_cast bz1
      push_cast at this; linarith
    have rhq : (h : ℝ) ≤ (q : ℝ) - 1 := by
      have : ((h + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hlt
      push_cast at this; linarith
    have rk : (1 : ℝ) ≤ kk := by exact_mod_cast hkk
    have R4 : (kk : ℝ) * Real.log B < ((q : ℝ) - 1) * Real.log D ∨
        (kk : ℝ) * Real.log E < ((q : ℝ) - 1) * Real.log D := by
      rcases hk0 with h0 | h0
      · rw [h0, log_mul_pow hq.pos pB.pos] at L4; left; simp at L4; linarith
      · rw [h0, log_mul_pow hq.pos pE.pos] at L4; right; simp at L4; linarith
    exact step6_real hQ hl hld hla hlb hle rhq rbe2 rbe4 rby1 rbz1 rk L1 L2 L3 R4
  -- Step 7
  by_cases hf : x0 + 4 ≤ q
  · have he4q : q ^ 2 ≤ e4 := by
      by_contra hlt
      push Not at hlt
      have T1 := (log_kC_bounds (j := 0) hq.two_le pB.two_le).1
      rw [hB0, log_mul_pow hq.pos pA.pos] at T1
      simp only [pow_zero, mul_one] at T1
      have rf : (x0 : ℝ) ≤ (q : ℝ) - 4 := by
        have : ((x0 + 4 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hf
        push_cast at this; linarith
      have re4 : (e4 : ℝ) ≤ (q : ℝ) ^ 2 - 1 := by
        have : ((e4 + 1 : ℕ) : ℝ) ≤ ((q ^ 2 : ℕ) : ℝ) := by exact_mod_cast hlt
        push_cast at this; linarith
      exact step7a_real hQ hl hld hla hlb rf rbh rbe2 re4 T1 L2 L1
    have hdvd : D ^ q ^ 2 ∣ kC q 1 A := (pow_dvd_pow D he4q).trans hD4
    have h1 : A ^ q ^ 2 ≡ 1 [MOD D ^ q ^ 2] := by
      simpa using pow_modEq_one_of_dvd (j := 1) hdvd
    exact not_pow_modEq_one hq.two_le lD (pow_ne_zero 2 hq.ne_zero)
      (pow_modEq_one_of_mul (hqAD _ dvd_rfl) (pow_pow_modEq_one h1))
  · push Not at hf
    set m := min (min x0 h) q with hm
    have hA1q : q * (B ^ e2 * D ^ e4) ≡ 1 [MOD A ^ m] := by
      have := kC_modEq_one (m := A ^ q) (j := 1) (s := A) hq.pos (by rw [pow_one])
      rw [hA2, mul_assoc] at this
      exact this.of_dvd (pow_dvd_pow A (by omega))
    have hBq : B ^ q ≡ 1 [MOD A ^ x0] := by
      simpa using pow_modEq_one_of_dvd (j := 0) (m := A ^ x0) (by rw [hB0]; exact dvd_mul_left _ _)
    have hDq : D ^ q ^ 3 ≡ 1 [MOD A ^ h] := by
      simpa using pow_modEq_one_of_dvd (j := 2) (m := A ^ h) (by rw [hh]; exact dvd_mul_left _ _)
    have hb : (B ^ e2 * D ^ e4) ^ q ^ 2 ≡ 1 [MOD A ^ m] := by
      have e : (B ^ e2 * D ^ e4) ^ q ^ 2 = (B ^ q) ^ (e2 * q) * (D ^ q ^ 3) ^ c := by
        rw [hc]; ring
      rw [e]
      have := ((hBq.of_dvd (pow_dvd_pow A (show m ≤ x0 by omega))).pow (e2 * q)).mul
        ((hDq.of_dvd (pow_dvd_pow A (show m ≤ h by omega))).pow c)
      simpa using this
    have hqm := pow_modEq_one_of_mul hA1q hb
    have hdv := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq.pos)).mp hqm.symm
    have hbig : 1 < q ^ q ^ 2 := Nat.one_lt_pow (pow_ne_zero 2 hq.ne_zero) hq.one_lt
    have hle := Nat.le_of_dvd (by omega) hdv
    have hlt : A ^ (q - 3) < q ^ q ^ 2 :=
      lt_of_le_of_lt (le_trans (Nat.pow_le_pow_right pA.pos (show q - 3 ≤ m by omega)) hle)
        (by omega)
    have T0 := log_lt_of_lt (pow_pos pA.pos _) hlt
    rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow,
      Nat.cast_sub (by omega : 3 ≤ q)] at T0
    push_cast at T0
    have hd2 : 2 * Real.log q < Real.log D := by
      have := log_lt_of_lt (pow_pos hq.pos 2) hDbig
      rw [Nat.cast_pow, Real.log_pow] at this
      push_cast at this
      exact this
    exact step7b_real hQ hl hd2 hla rbh T0 L1


/-- Step 0: the blocks of `D`, when `A` divides `kC q 2 D`. -/
theorem d_block (st : KSetup N q D) {A B E : ℕ} (hA : A ∈ kS N q) (hB : B ∈ kS N q)
    (hE : E ∈ kS N q) (hDA : D ≠ A) (hDB : D ≠ B) (hDE : D ≠ E) (hAB : A ≠ B) (hAE : A ≠ E)
    (hBE : B ≠ E) (hpos : 0 < (kC q 2 D).factorization A) :
    kC q 2 D = q * A ^ (kC q 2 D).factorization A ∧
      (∃ i ≤ 1, ∃ k, 0 < k ∧ kC q i D = q * B ^ k) ∧
      (∃ i ≤ 1, ∃ k, 0 < k ∧ kC q i D = q * E ^ k) ∧
      (∃ k, 0 < k ∧ (kC q 0 D = q * B ^ k ∨ kC q 0 D = q * E ^ k)) := by
  have hD := st.memD
  have vD0 := st.valid (j := 0) hD (Or.inl (Nat.zero_le 1))
  have vD1 := st.valid (j := 1) hD (Or.inl le_rfl)
  have vD2 := st.valid (j := 2) hD (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨n0, -, -, -⟩ := st.block hD vD0 hA hB hE hDA hDB hDE hAB hAE hBE
  obtain ⟨n1, -, -, -⟩ := st.block hD vD1 hA hB hE hDA hDB hDE hAB hAE hBE
  obtain ⟨n2, -, -, -⟩ := st.block hD vD2 hA hB hE hDA hDB hDE hAB hAE hBE
  have d01A := st.disj hD vD0 vD1 (by norm_num) hA
  have d01B := st.disj hD vD0 vD1 (by norm_num) hB
  have d01E := st.disj hD vD0 vD1 (by norm_num) hE
  have d02A := st.disj hD vD0 vD2 (by norm_num) hA
  have d02B := st.disj hD vD0 vD2 (by norm_num) hB
  have d02E := st.disj hD vD0 vD2 (by norm_num) hE
  have d12A := st.disj hD vD1 vD2 (by norm_num) hA
  have d12B := st.disj hD vD1 vD2 (by norm_num) hB
  have d12E := st.disj hD vD1 vD2 (by norm_num) hE
  have hf0 := st.form hD vD0 hA hB hE hDA hDB hDE hAB hAE hBE
  have hf1 := st.form hD vD1 hA hB hE hDA hDB hDE hAB hAE hBE
  have hf2 := st.form hD vD2 hA hB hE hDA hDB hDE hAB hAE hBE
  set a0 := (kC q 0 D).factorization A
  set b0 := (kC q 0 D).factorization B
  set e0 := (kC q 0 D).factorization E
  set a1 := (kC q 1 D).factorization A
  set b1 := (kC q 1 D).factorization B
  set e1 := (kC q 1 D).factorization E
  set a2 := (kC q 2 D).factorization A
  set b2 := (kC q 2 D).factorization B
  set e2 := (kC q 2 D).factorization E
  have z2 : b2 = 0 ∧ e2 = 0 ∧ a0 = 0 ∧ a1 = 0 := by clear hf0 hf1 hf2; omega
  have hcase : (0 < b0 ∧ e0 = 0 ∧ b1 = 0 ∧ 0 < e1) ∨ (0 < e0 ∧ b0 = 0 ∧ e1 = 0 ∧ 0 < b1) := by
    clear hf0 hf1 hf2; omega
  clear d01A d01B d01E d02A d02B d02E d12A d12B d12E n0 n1 n2
  refine ⟨by rw [hf2, z2.1, z2.2.1]; simp, ?_⟩
  rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · have e0' : kC q 0 D = q * B ^ b0 := by rw [hf0, z2.2.2.1, h2]; simp
    have e1' : kC q 1 D = q * E ^ e1 := by rw [hf1, z2.2.2.2, h3]; simp
    exact ⟨⟨0, by norm_num, _, h1, e0'⟩, ⟨1, le_rfl, _, h4, e1'⟩, ⟨_, h1, Or.inl e0'⟩⟩
  · have e0' : kC q 0 D = q * E ^ e0 := by rw [hf0, z2.2.2.1, h2]; simp
    have e1' : kC q 1 D = q * B ^ b1 := by rw [hf1, z2.2.2.2, h3]; simp
    exact ⟨⟨1, le_rfl, _, h4, e1'⟩, ⟨0, by norm_num, _, h1, e0'⟩, ⟨_, h1, Or.inr e0'⟩⟩

/-- Steps 0 and 1: the configuration where `A` divides the block `kC q 2 D` is impossible. -/
theorem mid (st : KSetup N q D) {A B E : ℕ} (hA : A ∈ kS N q) (hB : B ∈ kS N q)
    (hE : E ∈ kS N q) (hDA : D ≠ A) (hDB : D ≠ B) (hDE : D ≠ E) (hAB : A ≠ B) (hAE : A ≠ E)
    (hBE : B ≠ E) (hpos : 0 < (kC q 2 D).factorization A) : False := by
  have hD := st.memD
  have pD := prime_of hD
  have pA := prime_of hA
  have pB := prime_of hB
  have pE := prime_of hE
  obtain ⟨hh, hDBp, hDEp, hD0⟩ := st.d_block hA hB hE hDA hDB hDE hAB hAE hBE hpos
  have hD0' : ∃ k, 0 < k ∧ (kC q 0 D = q * E ^ k ∨ kC q 0 D = q * B ^ k) := by
    obtain ⟨k, hk, h⟩ := hD0; exact ⟨k, hk, h.symm⟩
  have pDA : KPure q D A := ⟨2, _, hpos, hh⟩
  have pDB : KPure q D B := by obtain ⟨i, -, k, hk, h⟩ := hDBp; exact ⟨i, k, hk, h⟩
  have pDE : KPure q D E := by obtain ⟨i, -, k, hk, h⟩ := hDEp; exact ⟨i, k, hk, h⟩
  -- Step 1: the blocks of `A`
  have vA0 := st.valid (j := 0) hA (Or.inl (Nat.zero_le 1))
  have vA1 := st.valid (j := 1) hA (Or.inl le_rfl)
  obtain ⟨nA0, pAB0, pAE0, pAD0⟩ :=
    st.block hA vA0 hB hE hD hAB hAE hDA.symm hBE hDB.symm hDE.symm
  obtain ⟨nA1, pAB1, pAE1, pAD1⟩ :=
    st.block hA vA1 hB hE hD hAB hAE hDA.symm hBE hDB.symm hDE.symm
  have dB := st.disj hA vA0 vA1 (by norm_num) hB
  have dE := st.disj hA vA0 vA1 (by norm_num) hE
  have dD := st.disj hA vA0 vA1 (by norm_num) hD
  have hfA0 := st.form hA vA0 hB hE hD hAB hAE hDA.symm hBE hDB.symm hDE.symm
  have hfA1 := st.form hA vA1 hB hE hD hAB hAE hDA.symm hBE hDB.symm hDE.symm
  have npAD : ¬ KPure q A D := fun p => st.noK pA pD p pDA
  have o0 := or_of_imp pAD0 npAD
  have o1 := or_of_imp pAD1 npAD
  have hDin : 0 < (kC q 0 A).factorization D ∨ 0 < (kC q 1 A).factorization D := by
    by_contra hc
    push Not at hc
    have hz0 : (kC q 0 A).factorization D = 0 := by omega
    have hz1 : (kC q 1 A).factorization D = 0 := by omega
    obtain ⟨pAB, pAE⟩ : KPure q A B ∧ KPure q A E := by
      rcases (by omega : ((kC q 0 A).factorization B = 0 ∧ (kC q 1 A).factorization E = 0) ∨
          ((kC q 0 A).factorization E = 0 ∧ (kC q 1 A).factorization B = 0)) with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨pAB1 b hz1, pAE0 a hz0⟩
      · exact ⟨pAB0 a hz0, pAE1 b hz1⟩
    have pBE := st.split_two hB hA hD hE hAB.symm hDB.symm hBE hDA.symm hAE hDE
      (fun p => st.noK pB pA p pAB) (fun p => st.noK pB pD p pDB)
    have pEB := st.split_two hE hA hD hB hAE.symm hDE.symm hBE.symm hDA.symm hAB hDB
      (fun p => st.noK pE pA p pAE) (fun p => st.noK pE pD p pDE)
    exact st.noK pB pE pBE pEB
  set b0 := (kC q 0 A).factorization B
  set e0 := (kC q 0 A).factorization E
  set c0 := (kC q 0 A).factorization D
  set b1 := (kC q 1 A).factorization B
  set e1 := (kC q 1 A).factorization E
  set c1 := (kC q 1 A).factorization D
  have pos_of : ∀ {x y z : ℕ}, 0 < x + y + z → y = 0 → z = 0 → 0 < x := by
    intro x y z h hy hz; subst hy hz; simpa using h
  rcases hDin with hc0 | hc1
  · have hc1 : c1 = 0 := dD.resolve_left hc0.ne'
    rcases Nat.eq_zero_or_pos b0 with hb0 | hb0
    · have he0 : 0 < e0 := o0.resolve_left (by rw [hb0]; exact lt_irrefl 0)
      have he1 : e1 = 0 := dE.resolve_left he0.ne'
      have hb1 : 0 < b1 := pos_of nA1 he1 hc1
      exact st.core hA hE hB hDA hDE hDB hAE hAB hBE.symm hpos hh hDEp hDBp hD0' (γ := 1)
        (e2 := e0) (e3 := b1) (e4 := c0) le_rfl hb1 hc0
        (by rw [hfA1, he1, hc1]; simp) (by rw [Nat.sub_self, hfA0, hb0]; simp)
    · have hb1 : b1 = 0 := dB.resolve_left hb0.ne'
      have he1 : 0 < e1 := by
        have := nA1; rw [hb1, hc1] at this; simpa using this
      have he0 : e0 = 0 := dE.resolve_right he1.ne'
      exact st.core hA hB hE hDA hDB hDE hAB hAE hBE hpos hh hDBp hDEp hD0 (γ := 1)
        (e2 := b0) (e3 := e1) (e4 := c0) le_rfl he1 hc0
        (by rw [hfA1, hb1, hc1]; simp) (by rw [Nat.sub_self, hfA0, he0]; simp)
  · have hc0 : c0 = 0 := dD.resolve_right hc1.ne'
    rcases Nat.eq_zero_or_pos b1 with hb1 | hb1
    · have he1 : 0 < e1 := o1.resolve_left (by rw [hb1]; exact lt_irrefl 0)
      have he0 : e0 = 0 := dE.resolve_right he1.ne'
      have hb0 : 0 < b0 := pos_of nA0 he0 hc0
      exact st.core hA hE hB hDA hDE hDB hAE hAB hBE.symm hpos hh hDEp hDBp hD0' (γ := 0)
        (e2 := e1) (e3 := b0) (e4 := c1) (Nat.zero_le 1) hb0 hc1
        (by rw [hfA0, he0, hc0]; simp) (by rw [Nat.sub_zero, hfA1, hb1]; simp)
    · have hb0 : b0 = 0 := dB.resolve_right hb1.ne'
      have he0 : 0 < e0 := by
        have := nA0; rw [hb0, hc0] at this; simpa using this
      have he1 : e1 = 0 := dE.resolve_left he0.ne'
      exact st.core hA hB hE hDA hDB hDE hAB hAE hBE hpos hh hDBp hDEp hD0 (γ := 0)
        (e2 := b1) (e3 := e0) (e4 := c1) (Nat.zero_le 1) he0 hc1
        (by rw [hfA0, hb0, hc0]; simp) (by rw [Nat.sub_zero, hfA1, he1]; simp)

/-- The setting `KSetup` is contradictory. -/
theorem false (st : KSetup N q D) : False := by
  have hD := st.memD
  have hcard : ((kS N q).erase D).card = 3 := by
    rw [Finset.card_erase_of_mem hD, st.card]
  obtain ⟨x, y, z, hxy, hxz, hyz, hS⟩ := Finset.card_eq_three.mp hcard
  have hmem : ∀ t ∈ ({x, y, z} : Finset ℕ), t ∈ kS N q ∧ D ≠ t := fun t ht => by
    rw [← hS] at ht
    exact ⟨Finset.mem_of_mem_erase ht, (Finset.ne_of_mem_erase ht).symm⟩
  obtain ⟨hx, hDx⟩ := hmem x (by simp)
  obtain ⟨hy, hDy⟩ := hmem y (by simp)
  obtain ⟨hz, hDz⟩ := hmem z (by simp)
  have vD2 := st.valid (j := 2) hD (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨n2, -, -, -⟩ := st.block hD vD2 hx hy hz hDx hDy hDz hxy hxz hyz
  rcases (by omega : 0 < (kC q 2 D).factorization x ∨ 0 < (kC q 2 D).factorization y ∨
      0 < (kC q 2 D).factorization z) with h | h | h
  · exact st.mid hx hy hz hDx hDy hDz hxy hxz hyz h
  · exact st.mid hy hx hz hDy hDx hDz hxy.symm hyz hxz h
  · exact st.mid hz hx hy hDz hDx hDy hxz.symm hyz.symm hxy h

end KSetup

/-! ## The targets -/

/-- The normal form of the square case is impossible for `q ≥ 13`, given Kanold's obstruction.
Let `N` be an odd perfect number with special prime `q ≥ 13`, `q ^ 2 ∣ e_p + 1` for every
ordinary prime `p`, and `v_q(N) = 9`. Then `KanoldObstructionAt q` gives a contradiction. -/
theorem not_normal_form_of_obstruction {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hK : KanoldObstructionAt q) (hq13 : 13 ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → q ^ 2 ∣ N.factorization p + 1)
    (h9 : N.factorization q = 9) : False := by
  obtain ⟨-, hcard, r, hr, hr3, hrest⟩ := kanold_square_normal_form h hq hodd hexp h9
  exact KSetup.false ⟨h, hq, hq13, hK, hcard, hr, hr3, hrest⟩

/-- The fifth power at the special prime with exponent `2`, given Kanold's obstruction: if
`q ^ 2 ∣ e_p + 1` for every ordinary prime `p`, then `q ^ 10 ∣ N`. -/
theorem pow_ten_dvd_of_special_sq_of_obstruction {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hK : KanoldObstructionAt q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → q ^ 2 ∣ N.factorization p + 1) : q ^ 10 ∣ N := by
  rcases pow_ten_dvd_or_normal_form h hq hodd hexp with h10 | ⟨h9, -⟩
  · exact h10
  · exfalso
    have hq4 := (mod_four_special h hq hodd).1
    by_cases hq5 : q = 5
    · subst hq5
      have := thirteen_le_factorization_five_of_special h hodd hexp
      omega
    · have hq13 : 13 ≤ q := by
        have h2 := hq.two_le
        have h9' : q ≠ 9 := by rintro rfl; norm_num at hq
        have h1 : q ≠ 1 := hq.one_lt.ne'
        omega
      exact not_normal_form_of_obstruction h hq hodd hK hq13 hexp h9

/-- Kanold's theorem in Yamada's fifth power form, given Kanold's obstruction at the special
prime: if `t ∣ e_p + 1` for every ordinary prime `p` of the odd perfect number `N` with special
prime `q`, then `t ^ 5 ∣ N`. -/
theorem pow_five_dvd_of_forall_dvd_succ_of_obstruction {N q t : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hK : KanoldObstructionAt q)
    (ht : ∀ p ∈ N.primeFactors, p ≠ q → t ∣ N.factorization p + 1) : t ^ 5 ∣ N := by
  have hN0 := h.ne_zero
  have ht0 : t ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp, hpq⟩ := exists_ordinary_prime h hq hodd
    have := ht p hp hpq
    simp at this
  refine (Nat.factorization_prime_le_iff_dvd (pow_ne_zero 5 ht0) hN0).mp fun l hl => ?_
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hexp : ∀ p ∈ N.primeFactors, p ≠ q → l ^ t.factorization l ∣ N.factorization p + 1 :=
    fun p hp hpq => (Nat.ordProj_dvd t l).trans (ht p hp hpq)
  have key : l ^ (5 * t.factorization l) ∣ N := by
    by_cases hlq : l = q
    · subst hlq
      by_cases ha : t.factorization l = 2
      · rw [ha] at hexp ⊢
        exact pow_ten_dvd_of_special_sq_of_obstruction h hl hodd hK hexp
      · exact pow_five_mul_dvd_of_special_of_ne_two h hl hodd ha hexp
    · exact pow_five_mul_dvd_of_ne_special h hq hodd hl hlq hexp
  exact (hl.pow_dvd_iff_le_factorization hN0).mp key


/-- Kanold's obstruction holds at every odd prime (`OddPerfect/KanoldObstruction.lean`). -/
theorem kanoldObstructionAt_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    KanoldObstructionAt p :=
  fun _ _ _ _ _ _ hr hs ha hb h1 h2 => kanold_obstruction hp hp2 hr hs ha hb h1 h2

/-- The fifth power at the special prime with exponent `2`: if `q ^ 2 ∣ e_p + 1` for every
ordinary prime `p` of the odd perfect number `N` with special prime `q`, then `q ^ 10 ∣ N`. -/
theorem pow_ten_dvd_of_special_sq {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → q ^ 2 ∣ N.factorization p + 1) : q ^ 10 ∣ N := by
  have hq4 := (mod_four_special h hq hodd).1
  exact pow_ten_dvd_of_special_sq_of_obstruction h hq hodd
    (kanoldObstructionAt_of_prime hq (by omega)) hexp

/-- Kanold's theorem in Yamada's fifth power form: if `t ∣ e_p + 1` for every ordinary prime
`p` of the odd perfect number `N` with special prime `q`, then `t ^ 5 ∣ N`. -/
theorem pow_five_dvd_of_forall_dvd_succ {N q t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (ht : ∀ p ∈ N.primeFactors, p ≠ q → t ∣ N.factorization p + 1) : t ^ 5 ∣ N := by
  have hq4 := (mod_four_special h hq hodd).1
  exact pow_five_dvd_of_forall_dvd_succ_of_obstruction h hq hodd
    (kanoldObstructionAt_of_prime hq (by omega)) ht

end OddPerfect

#print axioms OddPerfect.not_normal_form_of_obstruction
#print axioms OddPerfect.pow_ten_dvd_of_special_sq_of_obstruction
#print axioms OddPerfect.pow_five_dvd_of_forall_dvd_succ_of_obstruction
#print axioms OddPerfect.kanoldObstructionAt_of_prime
#print axioms OddPerfect.pow_ten_dvd_of_special_sq
#print axioms OddPerfect.pow_five_dvd_of_forall_dvd_succ
#print axioms OddPerfect.KSetup.mem
#print axioms OddPerfect.KSetup.prime_of
#print axioms OddPerfect.KSetup.lt_of
#print axioms OddPerfect.KSetup.ne_two
#print axioms OddPerfect.KSetup.q2
#print axioms OddPerfect.KSetup.valid
#print axioms OddPerfect.KSetup.cover
#print axioms OddPerfect.KSetup.form
#print axioms OddPerfect.KSetup.disj
#print axioms OddPerfect.KSetup.big
#print axioms OddPerfect.KSetup.noK
#print axioms OddPerfect.KSetup.block
#print axioms OddPerfect.KSetup.split_two
#print axioms OddPerfect.KSetup.split_excl
#print axioms OddPerfect.KSetup.core
#print axioms OddPerfect.KSetup.d_block
#print axioms OddPerfect.KSetup.mid
#print axioms OddPerfect.KSetup.false
