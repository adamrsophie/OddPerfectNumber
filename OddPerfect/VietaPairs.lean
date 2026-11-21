import OddPerfect.Phi3
import Mathlib.Tactic.NormNum.Prime

/-!
# Mutual divisibility pairs for `x ^ 2 + x + 1`

Bibby, Vyncke and Zelinsky (arXiv 1908.09420, Lemmas 5, 6 and 8). A *quasisolution* is a
pair of natural numbers `p, q` with `p ∣ phi3 q` and `q ∣ phi3 p`. We show:

* every quasisolution with `p ≤ q` is a consecutive pair `(quasiSeq n, quasiSeq (n + 1))`
  of the sequence `1, 1, 3, 13, 61, 291, 1393, ...` given by `t₀ = t₁ = 1` and
  `t (n + 2) = 5 t (n + 1) - t n - 1`, and conversely;
* hence every quasisolution satisfies `p ^ 2 + q ^ 2 + p + q + 1 = 5 p q` with no
  exceptions (positivity is automatic since `0 ∣ phi3 q` is false), and `gcd(p, q) = 1`;
* residues of the sequence modulo `3`, `4`, `5`, the growth `4 t n < t (n + 1) < 5 t n`
  for `n ≥ 2`, and the prime pairs among the first terms;
* Lemma 6 (`p ^ 2 ∣ phi3 q` and `q ∣ phi3 p` is impossible for primes) and Lemma 8 (two
  chained prime pairs are `3, 13, 61`);
* consequences for exact-square primes of an odd perfect number that feed each other.

The descent is done on the divisibility relations directly: from `(p, q)` with `p < q`
one passes to `(phi3 p / q, p)`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The quasisolution sequence `1, 1, 3, 13, 61, 291, ...` (indexed from `0`). -/
def quasiSeq : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => 5 * quasiSeq (n + 1) - quasiSeq n - 1

/-- `quasiSeq 0 = 1`. -/
@[simp] theorem quasiSeq_zero : quasiSeq 0 = 1 := rfl

/-- `quasiSeq 1 = 1`. -/
@[simp] theorem quasiSeq_one : quasiSeq 1 = 1 := rfl

/-- The defining recursion of `quasiSeq` (with truncated subtraction). -/
theorem quasiSeq_succ_succ (n : ℕ) :
    quasiSeq (n + 2) = 5 * quasiSeq (n + 1) - quasiSeq n - 1 := rfl

private theorem quasiSeq_pos_le (n : ℕ) : 1 ≤ quasiSeq n ∧ quasiSeq n ≤ quasiSeq (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine ⟨by omega, ?_⟩
    rw [quasiSeq_succ_succ]
    omega

/-- Every term is positive. -/
theorem one_le_quasiSeq (n : ℕ) : 1 ≤ quasiSeq n := (quasiSeq_pos_le n).1

/-- The sequence is monotone. -/
theorem quasiSeq_le_succ (n : ℕ) : quasiSeq n ≤ quasiSeq (n + 1) := (quasiSeq_pos_le n).2

/-- The recursion in additive form: `t (n + 2) + t n + 1 = 5 t (n + 1)`. -/
theorem quasiSeq_add_two (n : ℕ) :
    quasiSeq (n + 2) + quasiSeq n + 1 = 5 * quasiSeq (n + 1) := by
  have := quasiSeq_pos_le n
  rw [quasiSeq_succ_succ]
  omega

/-- Consecutive terms satisfy the quasisolution equation `p² + q² + p + q + 1 = 5 p q`. -/
theorem quasiSeq_invariant (n : ℕ) :
    quasiSeq n ^ 2 + quasiSeq (n + 1) ^ 2 + quasiSeq n + quasiSeq (n + 1) + 1 =
      5 * quasiSeq n * quasiSeq (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := quasiSeq_add_two n
    zify at h ih ⊢
    have e : (quasiSeq (n + 2) : ℤ) = 5 * quasiSeq (n + 1) - quasiSeq n - 1 := by linarith
    rw [e]
    linear_combination ih

/-- The product form of the recursion: `t n * t (n + 2) = phi3 (t (n + 1))`. -/
theorem quasiSeq_mul (n : ℕ) : quasiSeq n * quasiSeq (n + 2) = phi3 (quasiSeq (n + 1)) := by
  have h := quasiSeq_add_two n
  have hi := quasiSeq_invariant n
  unfold phi3
  zify at h hi ⊢
  have e : (quasiSeq (n + 2) : ℤ) = 5 * quasiSeq (n + 1) - quasiSeq n - 1 := by linarith
  rw [e]
  linear_combination -hi

/-- The equation `p² + q² + p + q + 1 = 5 p q` implies the two divisibilities. -/
theorem dvd_phi3_of_invariant {p q : ℕ} (h : p ^ 2 + q ^ 2 + p + q + 1 = 5 * p * q) :
    p ∣ phi3 q ∧ q ∣ phi3 p := by
  constructor
  · have e : phi3 q + p * (p + 1) = p * (5 * q) := by unfold phi3; linarith
    exact (Nat.dvd_add_left (dvd_mul_right p _)).mp (e ▸ dvd_mul_right p _)
  · have e : phi3 p + q * (q + 1) = q * (5 * p) := by unfold phi3; linarith
    exact (Nat.dvd_add_left (dvd_mul_right q _)).mp (e ▸ dvd_mul_right q _)

/-- Consecutive terms form a quasisolution. -/
theorem quasiSeq_dvd (n : ℕ) :
    quasiSeq n ∣ phi3 (quasiSeq (n + 1)) ∧ quasiSeq (n + 1) ∣ phi3 (quasiSeq n) :=
  dvd_phi3_of_invariant (quasiSeq_invariant n)

/-- The descent step: if `q * q' = phi3 p` and `p ∣ phi3 q` then `p ∣ phi3 q'`. -/
private theorem dvd_phi3_descent {p q q' : ℕ} (e : q * q' = phi3 p) (h : p ∣ phi3 q) :
    p ∣ phi3 q' := by
  have key : q' ^ 2 * phi3 q = phi3 q' + p * ((p + 1) * (p * (p + 1) + 2 + q')) := by
    calc q' ^ 2 * phi3 q = (q * q') ^ 2 + (q * q') * q' + q' ^ 2 := by unfold phi3; ring
      _ = phi3 p ^ 2 + phi3 p * q' + q' ^ 2 := by rw [e]
      _ = _ := by unfold phi3; ring
  have h2 : p ∣ q' ^ 2 * phi3 q := dvd_mul_of_dvd_right h _
  rw [key] at h2
  exact (Nat.dvd_add_left (dvd_mul_right p _)).mp h2

/-- **Classification of quasisolutions** (Bibby, Vyncke and Zelinsky, Lemma 5): if
`p ≤ q`, `p ∣ phi3 q` and `q ∣ phi3 p` then `(p, q)` is a consecutive pair of
`quasiSeq`. -/
theorem exists_quasiSeq_of_dvd {p q : ℕ} (hpq : p ≤ q) (h1 : p ∣ phi3 q)
    (h2 : q ∣ phi3 p) : ∃ n, p = quasiSeq n ∧ q = quasiSeq (n + 1) := by
  induction q using Nat.strong_induction_on generalizing p with
  | _ q ih =>
    have hp0 : p ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at h1
      unfold phi3 at h1
      omega
    rcases hpq.lt_or_eq with hlt | rfl
    · obtain ⟨q', e⟩ := h2
      have e' : q * q' = phi3 p := e.symm
      have hq'p : q' ≤ p := by
        by_contra hc
        push Not at hc
        have h3 : (p + 1) * (p + 1) ≤ q * q' := Nat.mul_le_mul hlt hc
        rw [e'] at h3
        unfold phi3 at h3
        have : 1 ≤ p := by omega
        nlinarith
      obtain ⟨n, hn1, hn2⟩ := ih p hlt hq'p ⟨q, by rw [← e']; ring⟩ (dvd_phi3_descent e' h1)
      refine ⟨n + 1, hn2, ?_⟩
      have hm := quasiSeq_mul n
      rw [← hn2, ← e', ← hn1] at hm
      have hpos : 0 < q' := by rw [hn1]; exact one_le_quasiSeq n
      exact (Nat.eq_of_mul_eq_mul_left hpos (by linarith [hm])).symm
    · have hp1 : p = 1 := by
        have hc := phi3_coprime_self p
        exact Nat.Coprime.eq_one_of_dvd hc.symm h1
      exact ⟨0, by simp [hp1], by simp [hp1]⟩

/-- Quasisolutions with `p ≤ q` are exactly consecutive pairs of `quasiSeq`. -/
theorem dvd_phi3_iff_quasiSeq {p q : ℕ} (hpq : p ≤ q) :
    (p ∣ phi3 q ∧ q ∣ phi3 p) ↔ ∃ n, p = quasiSeq n ∧ q = quasiSeq (n + 1) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact exists_quasiSeq_of_dvd hpq h1 h2
  · rintro ⟨n, rfl, rfl⟩
    exact quasiSeq_dvd n

/-- **Vieta invariant** (Lemma 5): every quasisolution satisfies
`p² + q² + p + q + 1 = 5 p q`. No positivity or other side condition is needed. -/
theorem invariant_of_dvd_phi3 {p q : ℕ} (h1 : p ∣ phi3 q) (h2 : q ∣ phi3 p) :
    p ^ 2 + q ^ 2 + p + q + 1 = 5 * p * q := by
  rcases le_total p q with hpq | hqp
  · obtain ⟨n, rfl, rfl⟩ := exists_quasiSeq_of_dvd hpq h1 h2
    exact quasiSeq_invariant n
  · obtain ⟨n, rfl, rfl⟩ := exists_quasiSeq_of_dvd hqp h2 h1
    linarith [quasiSeq_invariant n]

/-- A quasisolution is characterized by the Vieta equation. -/
theorem dvd_phi3_iff_invariant {p q : ℕ} :
    (p ∣ phi3 q ∧ q ∣ phi3 p) ↔ p ^ 2 + q ^ 2 + p + q + 1 = 5 * p * q :=
  ⟨fun h => invariant_of_dvd_phi3 h.1 h.2, dvd_phi3_of_invariant⟩

/-- The two entries of a quasisolution are coprime. -/
theorem coprime_of_dvd_phi3 {p q : ℕ} (h1 : p ∣ phi3 q) : Nat.Coprime p q :=
  Nat.Coprime.coprime_dvd_left h1 (phi3_coprime_self q)

/-! ### Residues -/

private theorem quasiSeq_mod_three_block (m : ℕ) :
    quasiSeq (3 * m) % 3 = 1 ∧ quasiSeq (3 * m + 1) % 3 = 1 ∧
      quasiSeq (3 * m + 2) % 3 = 0 := by
  induction m with
  | zero => simp [quasiSeq_succ_succ]
  | succ m ih =>
    have a1 : quasiSeq (3 * m + 3) + quasiSeq (3 * m + 1) + 1 = 5 * quasiSeq (3 * m + 2) :=
      quasiSeq_add_two _
    have a2 : quasiSeq (3 * m + 4) + quasiSeq (3 * m + 2) + 1 = 5 * quasiSeq (3 * m + 3) :=
      quasiSeq_add_two _
    have a3 : quasiSeq (3 * m + 5) + quasiSeq (3 * m + 3) + 1 = 5 * quasiSeq (3 * m + 4) :=
      quasiSeq_add_two _
    rw [show 3 * (m + 1) = 3 * m + 3 by ring, show 3 * m + 3 + 1 = 3 * m + 4 by ring,
      show 3 * m + 3 + 2 = 3 * m + 5 by ring]
    refine ⟨by omega, by omega, by omega⟩

/-- `quasiSeq n` is divisible by `3` when `n ≡ 2 (mod 3)` and is `1 (mod 3)` otherwise. -/
theorem quasiSeq_mod_three (n : ℕ) :
    quasiSeq n % 3 = if n % 3 = 2 then 0 else 1 := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 3 ∧ n = 3 * m + r :=
    ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 3).symm⟩
  obtain ⟨h0, h1, h2⟩ := quasiSeq_mod_three_block m
  interval_cases r
  · rw [if_neg (by omega)]; exact h0
  · rw [if_neg (by omega)]; exact h1
  · rw [if_pos (by omega)]; exact h2

private theorem quasiSeq_mod_four_block (m : ℕ) :
    quasiSeq (3 * m) % 4 = 1 ∧ quasiSeq (3 * m + 1) % 4 = 1 ∧
      quasiSeq (3 * m + 2) % 4 = 3 := by
  induction m with
  | zero => simp [quasiSeq_succ_succ]
  | succ m ih =>
    have a1 : quasiSeq (3 * m + 3) + quasiSeq (3 * m + 1) + 1 = 5 * quasiSeq (3 * m + 2) :=
      quasiSeq_add_two _
    have a2 : quasiSeq (3 * m + 4) + quasiSeq (3 * m + 2) + 1 = 5 * quasiSeq (3 * m + 3) :=
      quasiSeq_add_two _
    have a3 : quasiSeq (3 * m + 5) + quasiSeq (3 * m + 3) + 1 = 5 * quasiSeq (3 * m + 4) :=
      quasiSeq_add_two _
    rw [show 3 * (m + 1) = 3 * m + 3 by ring, show 3 * m + 3 + 1 = 3 * m + 4 by ring,
      show 3 * m + 3 + 2 = 3 * m + 5 by ring]
    refine ⟨by omega, by omega, by omega⟩

/-- `quasiSeq n` is `3 (mod 4)` when `n ≡ 2 (mod 3)` and is `1 (mod 4)` otherwise. -/
theorem quasiSeq_mod_four (n : ℕ) :
    quasiSeq n % 4 = if n % 3 = 2 then 3 else 1 := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 3 ∧ n = 3 * m + r :=
    ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 3).symm⟩
  obtain ⟨h0, h1, h2⟩ := quasiSeq_mod_four_block m
  interval_cases r
  · rw [if_neg (by omega)]; exact h0
  · rw [if_neg (by omega)]; exact h1
  · rw [if_pos (by omega)]; exact h2

private theorem quasiSeq_mod_five_block (m : ℕ) :
    quasiSeq (4 * m) % 5 = 1 ∧ quasiSeq (4 * m + 1) % 5 = 1 ∧
      quasiSeq (4 * m + 2) % 5 = 3 ∧ quasiSeq (4 * m + 3) % 5 = 3 := by
  induction m with
  | zero => simp [quasiSeq_succ_succ]
  | succ m ih =>
    have a1 : quasiSeq (4 * m + 4) + quasiSeq (4 * m + 2) + 1 = 5 * quasiSeq (4 * m + 3) :=
      quasiSeq_add_two _
    have a2 : quasiSeq (4 * m + 5) + quasiSeq (4 * m + 3) + 1 = 5 * quasiSeq (4 * m + 4) :=
      quasiSeq_add_two _
    have a3 : quasiSeq (4 * m + 6) + quasiSeq (4 * m + 4) + 1 = 5 * quasiSeq (4 * m + 5) :=
      quasiSeq_add_two _
    have a4 : quasiSeq (4 * m + 7) + quasiSeq (4 * m + 5) + 1 = 5 * quasiSeq (4 * m + 6) :=
      quasiSeq_add_two _
    rw [show 4 * (m + 1) = 4 * m + 4 by ring, show 4 * m + 4 + 1 = 4 * m + 5 by ring,
      show 4 * m + 4 + 2 = 4 * m + 6 by ring, show 4 * m + 4 + 3 = 4 * m + 7 by ring]
    refine ⟨by omega, by omega, by omega, by omega⟩

/-- `quasiSeq n` is `1 (mod 5)` when `n ≡ 0, 1 (mod 4)` and `3 (mod 5)` otherwise. -/
theorem quasiSeq_mod_five (n : ℕ) :
    quasiSeq n % 5 = if n % 4 < 2 then 1 else 3 := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 4 ∧ n = 4 * m + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  obtain ⟨h0, h1, h2, h3⟩ := quasiSeq_mod_five_block m
  interval_cases r
  · rw [if_pos (by omega)]; exact h0
  · rw [if_pos (by omega)]; exact h1
  · rw [if_neg (by omega)]; exact h2
  · rw [if_neg (by omega)]; exact h3

/-- `3 ∣ quasiSeq n` exactly when `n ≡ 2 (mod 3)`. -/
theorem three_dvd_quasiSeq_iff (n : ℕ) : 3 ∣ quasiSeq n ↔ n % 3 = 2 := by
  have := quasiSeq_mod_three n
  rw [Nat.dvd_iff_mod_eq_zero]
  split_ifs at this with h <;> simp [h, this]

/-! ### Growth -/

/-- Growth for a solution of the Vieta equation: if `2 ≤ p ≤ q` then `4 p < q < 5 p`. -/
theorem growth_of_invariant {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q)
    (h : p ^ 2 + q ^ 2 + p + q + 1 = 5 * p * q) : 4 * p < q ∧ q < 5 * p := by
  constructor
  · by_contra hc
    push Not at hc
    nlinarith [mul_le_mul hpq hc (Nat.zero_le _) (Nat.zero_le _)]
  · nlinarith

/-- `quasiSeq 2 = 3`. -/
@[simp] theorem quasiSeq_two : quasiSeq 2 = 3 := rfl

/-- From index `2` on every term is at least `3`. -/
theorem three_le_quasiSeq {n : ℕ} (hn : 2 ≤ n) : 3 ≤ quasiSeq n := by
  have hm : Monotone quasiSeq := monotone_nat_of_le_succ quasiSeq_le_succ
  simpa using hm hn

/-- **Growth** (Lemma 5): `4 t n < t (n + 1) < 5 t n` for `n ≥ 2`. This fails for
`n = 0, 1`. -/
theorem quasiSeq_growth {n : ℕ} (hn : 2 ≤ n) :
    4 * quasiSeq n < quasiSeq (n + 1) ∧ quasiSeq (n + 1) < 5 * quasiSeq n :=
  growth_of_invariant (by linarith [three_le_quasiSeq hn]) (quasiSeq_le_succ n)
    (quasiSeq_invariant n)

/-- The sequence is strictly increasing from index `1`. -/
theorem quasiSeq_lt_succ {n : ℕ} (hn : 1 ≤ n) : quasiSeq n < quasiSeq (n + 1) := by
  rcases hn.lt_or_eq with h | rfl
  · have := quasiSeq_growth (n := n) h
    omega
  · simp [quasiSeq_succ_succ]

/-- The sequence is injective on indices at least `1`. -/
theorem quasiSeq_inj {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : quasiSeq a = quasiSeq b) :
    a = b := by
  have hs : StrictMono fun n => quasiSeq (n + 1) :=
    strictMono_nat_of_lt_succ fun n => quasiSeq_lt_succ (by omega)
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' ha
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hb
  exact congrArg (· + 1) (hs.injective h)

/-! ### Prime pairs -/

/-- If two consecutive terms are both prime, then `n = 2` or `n ≡ 0 (mod 3)`. -/
theorem quasiSeq_prime_pair_index {n : ℕ} (h1 : (quasiSeq n).Prime)
    (h2 : (quasiSeq (n + 1)).Prime) : n = 2 ∨ n % 3 = 0 := by
  have key : ∀ m, (quasiSeq m).Prime → m % 3 = 2 → m = 2 := by
    intro m hm hm3
    have h3 : quasiSeq m = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hm).mp
        ((three_dvd_quasiSeq_iff m).2 hm3)).symm
    have hm1 : 1 ≤ m := by
      rcases m with _ | m
      · simp at hm3
      · omega
    exact quasiSeq_inj hm1 (by norm_num) (by rw [h3]; rfl)
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · exact Or.inr h
  · have := key (n + 1) h2 (by omega)
    have : n = 1 := by omega
    subst this
    exact absurd h1 Nat.not_prime_one
  · exact Or.inl (key n h1 h)

/-- The prime pairs among the first terms: for `n ≤ 20`, both `quasiSeq n` and
`quasiSeq (n + 1)` are prime exactly for `n = 2` (the pair `(3, 13)`) and `n = 3` (the
pair `(13, 61)`). The paper reports a further pair at `n = 21`; that is not verified
here. -/
theorem quasiSeq_prime_pair_iff {n : ℕ} (hn : n ≤ 20) :
    ((quasiSeq n).Prime ∧ (quasiSeq (n + 1)).Prime) ↔ n = 2 ∨ n = 3 := by
  have comp : ∀ m d, d ∣ quasiSeq m → 2 ≤ d → d < quasiSeq m → ¬ (quasiSeq m).Prime :=
    fun _ _ h a b => Nat.not_prime_of_dvd_of_lt h a b
  have v3 : quasiSeq 3 = 13 := by decide
  have v4 : quasiSeq 4 = 61 := by decide
  constructor
  · rintro ⟨h1, h2⟩
    have hi := quasiSeq_prime_pair_index h1 h2
    have : n = 0 ∨ n = 2 ∨ n = 3 ∨ n = 6 ∨ n = 9 ∨ n = 12 ∨ n = 15 ∨ n = 18 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd h1 (by simp [Nat.not_prime_one])
    · exact Or.inl rfl
    · exact Or.inr rfl
    · -- `quasiSeq 6 = 1393 = 7 * 199`
      exact absurd h1 (comp 6 7 (by decide) (by norm_num) (by decide))
    · -- `quasiSeq 9 = 153181 = 7 * 21883`
      exact absurd h1 (comp 9 7 (by decide) (by norm_num) (by decide))
    · -- `quasiSeq 12 = 16848481 = 13 * 1296037`
      exact absurd h1 (comp 12 13 (by decide) (by norm_num) (by decide))
    · -- `quasiSeq 16 = 8879117341 = 26947 * 329503`
      exact absurd h2 (comp 16 26947 (by decide) (by norm_num) (by decide))
    · -- `quasiSeq 18 = 203832917713 = 65437 * 3114949`
      exact absurd h1 (comp 18 65437 (by decide) (by norm_num) (by decide))
  · rintro (rfl | rfl)
    · rw [quasiSeq_two, v3]; norm_num
    · rw [v3, v4]; norm_num

/-! ### Lemmas 6 and 8 -/

/-- **Lemma 6**: there are no primes `p, q` with `p ^ 2 ∣ phi3 q` and `q ∣ phi3 p`. -/
theorem not_sq_dvd_phi3_pair {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : p ^ 2 ∣ phi3 q) (h2 : q ∣ phi3 p) : False := by
  have h1' : p ∣ phi3 q := (dvd_pow_self p two_ne_zero).trans h1
  have hinv := invariant_of_dvd_phi3 h1' h2
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  -- `p ≠ 3`: `9` never divides `phi3 q`
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact not_nine_dvd_phi3 q (by simpa using h1)
  -- `q ≠ 3`: then `p = 13` but `169 ∤ 13`
  have hq3 : q ≠ 3 := by
    rintro rfl
    have h13 : p ∣ 13 := by simpa [phi3] using h1'
    have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h13
    subst this
    norm_num [phi3] at h1
  obtain ⟨k, hk⟩ := h1
  -- `p < q`
  have hpq : p < q := by
    have hlt := phi3_lt_succ_sq (show 1 ≤ q by omega)
    have hpq' : p ≤ q := by
      by_contra hc
      push Not at hc
      have : (q + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hc 2
      have : p ^ 2 ≤ phi3 q := Nat.le_of_dvd (by unfold phi3; omega) ⟨k, hk⟩
      omega
    rcases hpq'.lt_or_eq with h | rfl
    · exact h
    · exact absurd (Nat.Coprime.eq_one_of_dvd (phi3_coprime_self p).symm h1') (by omega)
  obtain ⟨g1, g2⟩ := growth_of_invariant hp2 hpq.le hinv
  -- `5 q = (k + 1) p + 1`
  have hlin : 5 * q = (k + 1) * p + 1 := by
    have : p * (5 * q) = p * ((k + 1) * p + 1) := by
      unfold phi3 at hk
      nlinarith
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  -- `3 ∣ k`
  have hk3 : 3 ∣ k := by
    have hq1 : q % 3 = 1 := prime_dvd_phi3_mod_three hq hq3 h2
    have h3 : 3 ∣ p ^ 2 * k := hk ▸ (three_dvd_phi3_iff q).2 hq1
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h)) (Ne.symm hp3)
    · exact h
  -- `19 ≤ k ≤ 23`, so `k = 21`
  have hk19 : 19 ≤ k := by
    by_contra hc
    push Not at hc
    have : (k + 1) * p ≤ 19 * p := Nat.mul_le_mul_right p (by omega)
    omega
  have hk23 : k ≤ 23 := by
    by_contra hc
    push Not at hc
    have : 25 * p ≤ (k + 1) * p := Nat.mul_le_mul_right p (by omega)
    omega
  have hk21 : k = 21 := by omega
  subst hk21
  unfold phi3 at hk
  -- `41 p ^ 2 = 154 p + 31`, impossible for `p ≥ 2`
  have : 41 * p ^ 2 = 154 * p + 31 := by nlinarith
  have hp4 : p ≤ 4 := by nlinarith
  interval_cases p <;> omega

/-- **Lemma 8**: if `(p, q)` and `(q, r)` are both mutual divisibility pairs of primes with
`p ≠ r`, then `q = 13` and `{p, r} = {3, 61}`. -/
theorem chained_prime_pairs {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (h1 : p ∣ phi3 q) (h2 : q ∣ phi3 p) (h3 : r ∣ phi3 q) (h4 : q ∣ phi3 r) :
    q = 13 ∧ ((p = 3 ∧ r = 61) ∨ (p = 61 ∧ r = 3)) := by
  have i1 := invariant_of_dvd_phi3 h1 h2
  have i2 := invariant_of_dvd_phi3 h3 h4
  -- `p` and `r` are the two roots of the same quadratic, so `p + r + 1 = 5 q`
  have hsum : p + r + 1 = 5 * q := by
    have : ((p : ℤ) - r) * (p + r + 1 - 5 * q) = 0 := by
      zify at i1 i2
      linear_combination i1 - i2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by exact_mod_cast sub_eq_zero.mp h) hpr
    · zify; linarith
  have d13 : ∀ x : ℕ, x.Prime → x ∣ phi3 3 → x = 13 := fun x hx h =>
    (Nat.prime_dvd_prime_iff_eq hx (by norm_num)).mp (by simpa [phi3] using h)
  by_cases hq3 : q = 3
  · subst hq3
    exact absurd ((d13 p hp h1).trans (d13 r hr h3).symm) hpr
  by_cases hp3 : p = 3
  · subst hp3
    have := d13 q hq h2
    subst this
    exact ⟨rfl, Or.inl ⟨rfl, by omega⟩⟩
  by_cases hr3 : r = 3
  · subst hr3
    have := d13 q hq h4
    subst this
    exact ⟨rfl, Or.inr ⟨by omega, rfl⟩⟩
  have a := prime_dvd_phi3_mod_three hp hp3 h1
  have b := prime_dvd_phi3_mod_three hq hq3 h2
  have c := prime_dvd_phi3_mod_three hr hr3 h3
  omega

/-- A prime in a mutual divisibility pair is `3` or is `1 (mod 4)`. -/
theorem prime_of_dvd_phi3_pair_mod_four {p q : ℕ} (hp : p.Prime) (h1 : p ∣ phi3 q)
    (h2 : q ∣ phi3 p) : p = 3 ∨ p % 4 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = quasiSeq m := by
    rcases le_total p q with hpq | hqp
    · obtain ⟨n, h, -⟩ := exists_quasiSeq_of_dvd hpq h1 h2
      exact ⟨n, h⟩
    · obtain ⟨n, -, h⟩ := exists_quasiSeq_of_dvd hqp h2 h1
      exact ⟨n + 1, h⟩
  have h4 := quasiSeq_mod_four m
  split_ifs at h4 with hm
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      ((three_dvd_quasiSeq_iff m).2 hm)).symm
  · exact Or.inr h4

/-! ### Odd perfect numbers -/

/-- Two exact-square prime factors of `N` that feed each other (`q ∣ σ(p²)` and
`p ∣ σ(q²)`), with `p ≤ q`, form a consecutive pair of `quasiSeq`. -/
theorem exists_quasiSeq_of_sq_pair {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q)
    (hep : N.factorization p = 2) (heq : N.factorization q = 2)
    (h1 : q ∣ σ 1 (p ^ N.factorization p)) (h2 : p ∣ σ 1 (q ^ N.factorization q)) :
    ∃ n, p = quasiSeq n ∧ q = quasiSeq (n + 1) := by
  rw [hep, sigma_prime_sq hp] at h1
  rw [heq, sigma_prime_sq hq] at h2
  exact exists_quasiSeq_of_dvd hpq h2 h1

/-- If two exact-square prime factors of a perfect number feed each other, then `3 ∣ N`.
(This uses only `p ∣ σ(q²)`, not the classification.) -/
theorem three_dvd_of_sq_pair {N p q : ℕ} (hN : N.Perfect) (hp : p.Prime) (hq : q.Prime)
    (hep : N.factorization p = 2) (heq : N.factorization q = 2)
    (h2 : p ∣ σ 1 (q ^ N.factorization q)) : 3 ∣ N := by
  rw [heq, sigma_prime_sq hq] at h2
  by_cases hp3 : p = 3
  · subst hp3
    exact Nat.dvd_of_factorization_pos (by omega)
  · exact three_dvd_of_sq_mod_one hN hp hep (prime_dvd_phi3_mod_three hp hp3 h2)

/-- If two exact-square prime factors `p, q` of `N` feed each other, the edge `p → q`
has weight exactly one: `q ^ 2 ∤ σ(p²)` (by Lemma 6). -/
theorem sigmaWeight_eq_one_of_sq_pair {N p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hep : N.factorization p = 2) (heq : N.factorization q = 2)
    (h1 : q ∣ σ 1 (p ^ N.factorization p)) (h2 : p ∣ σ 1 (q ^ N.factorization q)) :
    sigmaWeight N p q = 1 := by
  rw [hep, sigma_prime_sq hp] at h1
  rw [heq, sigma_prime_sq hq] at h2
  have hne : phi3 p ≠ 0 := by unfold phi3; omega
  rw [sigmaWeight, hep, sigma_prime_sq hp]
  have hge : 1 ≤ (phi3 p).factorization q :=
    (hq.dvd_iff_one_le_factorization hne).mp h1
  have hle : (phi3 p).factorization q ≤ 1 := by
    by_contra hc
    push Not at hc
    exact not_sq_dvd_phi3_pair hq hp ((hq.pow_dvd_iff_le_factorization hne).mpr hc) h2
  omega

/-- If two exact-square prime factors of an odd perfect number feed each other, then
`9 ∣ N`, i.e. `2 ≤ v₃(N)`: either one of them is `3` (with exponent `2`), or both are
`1 (mod 3)` and each sends one unit of weight to `3`. -/
theorem two_le_factorization_three_of_sq_pair {N p q : ℕ} (h : OddPerfect N) (hp : p.Prime)
    (hq : q.Prime) (hep : N.factorization p = 2) (heq : N.factorization q = 2)
    (h1 : q ∣ σ 1 (p ^ N.factorization p)) (h2 : p ∣ σ 1 (q ^ N.factorization q)) :
    2 ≤ N.factorization 3 := by
  rw [hep, sigma_prime_sq hp] at h1
  rw [heq, sigma_prime_sq hq] at h2
  by_cases hp3 : p = 3
  · subst hp3; omega
  by_cases hq3 : q = 3
  · subst hq3; omega
  have hp1 := prime_dvd_phi3_mod_three hp hp3 h2
  have hq1 := prime_dvd_phi3_mod_three hq hq3 h1
  have hne : p ≠ q := by
    rintro rfl
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (phi3_coprime_self p).symm h2)
  have mem : ∀ x, x.Prime → N.factorization x = 2 → x % 3 = 1 →
      x ∈ N.primeFactors.filter fun p => N.factorization p = 2 ∧ p % 3 = 1 := by
    intro x hx hex hx1
    refine Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hx, ?_, h.ne_zero⟩, hex, hx1⟩
    exact Nat.dvd_of_factorization_pos (by omega)
  have hsub : ({p, q} : Finset ℕ) ⊆
      N.primeFactors.filter fun p => N.factorization p = 2 ∧ p % 3 = 1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact mem x hp hep hp1
    · rw [Finset.mem_singleton.mp hx]; exact mem q hq heq hq1
  have := (Finset.card_le_card hsub).trans (card_exact_sq_modEq_one_le h)
  rwa [Finset.card_pair hne] at this

/-- If `3` and a prime `q` are exact-square prime factors of a perfect number with
`q ∣ σ(3²)` (in particular if they feed each other), then `q = 13` and `61 ∣ N`. -/
theorem sq_pair_three {N q : ℕ} (hN : N.Perfect) (hq : q.Prime)
    (heq : N.factorization q = 2) (h1 : q ∣ σ 1 (3 ^ N.factorization 3))
    (he3 : N.factorization 3 = 2) : q = 13 ∧ 61 ∣ N := by
  rw [he3, sigma_prime_sq Nat.prime_three] at h1
  have hq13 : q = 13 :=
    (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (by simpa [phi3] using h1)
  subst hq13
  refine ⟨rfl, OPNStarter.force_prime hN hq heq (by norm_num) (by norm_num) ?_⟩
  rw [sigma_prime_sq hq]
  norm_num [phi3]

/-- Lemma 8 for an odd perfect number: if `p, q, r` are distinct exact-square prime factors
with `p, q` feeding each other and `q, r` feeding each other, then `q = 13` and
`{p, r} = {3, 61}`. -/
theorem chained_sq_pairs {N p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hep : N.factorization p = 2) (heq : N.factorization q = 2)
    (her : N.factorization r = 2)
    (h1 : q ∣ σ 1 (p ^ N.factorization p)) (h2 : p ∣ σ 1 (q ^ N.factorization q))
    (h3 : q ∣ σ 1 (r ^ N.factorization r)) (h4 : r ∣ σ 1 (q ^ N.factorization q)) :
    q = 13 ∧ ((p = 3 ∧ r = 61) ∨ (p = 61 ∧ r = 3)) := by
  rw [hep, sigma_prime_sq hp] at h1
  rw [heq, sigma_prime_sq hq] at h2 h4
  rw [her, sigma_prime_sq hr] at h3
  exact chained_prime_pairs hp hq hr hpr h2 h1 h4 h3

end OddPerfect

#print axioms OddPerfect.quasiSeq_zero
#print axioms OddPerfect.quasiSeq_one
#print axioms OddPerfect.quasiSeq_succ_succ
#print axioms OddPerfect.one_le_quasiSeq
#print axioms OddPerfect.quasiSeq_le_succ
#print axioms OddPerfect.quasiSeq_add_two
#print axioms OddPerfect.quasiSeq_invariant
#print axioms OddPerfect.quasiSeq_mul
#print axioms OddPerfect.dvd_phi3_of_invariant
#print axioms OddPerfect.quasiSeq_dvd
#print axioms OddPerfect.exists_quasiSeq_of_dvd
#print axioms OddPerfect.dvd_phi3_iff_quasiSeq
#print axioms OddPerfect.invariant_of_dvd_phi3
#print axioms OddPerfect.dvd_phi3_iff_invariant
#print axioms OddPerfect.coprime_of_dvd_phi3
#print axioms OddPerfect.quasiSeq_mod_three
#print axioms OddPerfect.quasiSeq_mod_four
#print axioms OddPerfect.quasiSeq_mod_five
#print axioms OddPerfect.three_dvd_quasiSeq_iff
#print axioms OddPerfect.growth_of_invariant
#print axioms OddPerfect.quasiSeq_two
#print axioms OddPerfect.three_le_quasiSeq
#print axioms OddPerfect.quasiSeq_growth
#print axioms OddPerfect.quasiSeq_lt_succ
#print axioms OddPerfect.quasiSeq_inj
#print axioms OddPerfect.quasiSeq_prime_pair_index
#print axioms OddPerfect.quasiSeq_prime_pair_iff
#print axioms OddPerfect.not_sq_dvd_phi3_pair
#print axioms OddPerfect.chained_prime_pairs
#print axioms OddPerfect.prime_of_dvd_phi3_pair_mod_four
#print axioms OddPerfect.exists_quasiSeq_of_sq_pair
#print axioms OddPerfect.three_dvd_of_sq_pair
#print axioms OddPerfect.sigmaWeight_eq_one_of_sq_pair
#print axioms OddPerfect.two_le_factorization_three_of_sq_pair
#print axioms OddPerfect.sq_pair_three
#print axioms OddPerfect.chained_sq_pairs
