import OddPerfect.Pratt

/-!
# Restrained odd perfect numbers: the exclusion tree checker

This module holds only the Boolean checker and its arithmetic soundness facts, with light
imports, so that the data modules `RestrainedSevenData*` load quickly. The number theoretic
soundness (`RestrainedSeven.chk_sound`) is in `OddPerfect.RestrainedSeven`.

Setting: `N` is an odd perfect number, `q` is a prime with odd exponent and `q ≡ 1 (mod 12)`,
and every prime factor of `N` other than `q` and `3` has exponent exactly 2. A certificate
shows that a prime `p` does not divide `N`, given a bit mask `M` whose set bits that are prime
are already known not to divide `N`. It is a binary tree (`Br`) over primes known to divide `N`:

* at a prime `t ∣ N` with `t ≠ 3`, either `t = q`, and then `t + 1 = σ(q) ∣ σ(q ^ k) ∣ 2N`
  (the exponent `k` is odd); or `t ≠ q`, the exponent of `t` is 2, and
  `t * t + t + 1 = σ(t ^ 2) ∣ 2N`;
* the case `t = q` is only possible when `t ≡ 1 (mod 12)` and `q` is not yet fixed;
* each source (`t + 1` or `t * t + t + 1`) is closed by a prime divisor whose bit is set in `M`
  (`Br.kill`) or continued at an odd prime divisor (`Br.node`).

Primality of a node `t` is checked by trial division up to the square root when
`t < 1000000`, and otherwise by a Pratt certificate carried by the node.
-/

namespace OddPerfect

namespace RestrainedSeven

/-! ## Primality -/

/-- `tdiv q f m`: with fuel `f`, no `k ≥ m` with `k ≡ m (mod 2)` and `k * k ≤ q` divides `q`. -/
def tdiv (q : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, m => decide (q < m * m) || (q % m != 0 && tdiv q f (m + 2))

theorem tdiv_sound {q : ℕ} : ∀ f m, tdiv q f m = true →
    ∀ k, m ≤ k → k % 2 = m % 2 → k * k ≤ q → q % k ≠ 0
  | 0, _, h => by simp [tdiv] at h
  | f + 1, m, h => by
    intro k hmk hpar hkq
    simp only [tdiv, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · exact absurd (lt_of_lt_of_le h (Nat.mul_le_mul hmk hmk)) (not_lt.mpr hkq)
    · rcases Nat.eq_or_lt_of_le hmk with rfl | hlt
      · exact h1
      · exact tdiv_sound f (m + 2) h2 k (by omega) (by omega) hkq

/-- An odd prime by trial division over odd numbers up to the square root. -/
def oddPrime (q : ℕ) : Bool := decide (3 ≤ q) && q % 2 == 1 && tdiv q q 3

theorem oddPrime_sound {q : ℕ} (h : oddPrime q = true) : q.Prime := by
  simp only [oddPrime, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h3, hodd⟩, ht⟩ := h
  by_contra hp
  have hm := Nat.minFac_prime (show q ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  have hdvd := Nat.minFac_dvd q
  have hm2 : q.minFac % 2 = 1 := by
    rcases hm.eq_two_or_odd with h' | h'
    · rw [h'] at hdvd
      omega
    · exact h'
  have hm3 : 3 ≤ q.minFac := by have := hm.two_le; omega
  exact tdiv_sound q 3 ht _ hm3 (by omega) (by simpa [pow_two] using hsq)
    (Nat.mod_eq_zero_of_dvd hdvd)

/-- Primality of a node: trial division below `1000000`, a Pratt certificate above. -/
def isPr (c : List (ℕ × ℕ × List ℕ)) (t : ℕ) : Bool :=
  if t < 1000000 then oddPrime t else Pratt.checkPrime t c

theorem isPr_sound {c : List (ℕ × ℕ × List ℕ)} {t : ℕ} (h : isPr c t = true) : t.Prime := by
  unfold isPr at h
  split_ifs at h
  · exact oddPrime_sound h
  · exact Pratt.prime_of_checkPrime h

/-! ## Trees and rows -/

/-- An exclusion tree. `skip` is an unused branch; `kill t` closes a source by its prime divisor
`t` with bit `t` set in the mask; `node t c qb ob` continues at the prime `t` (Pratt certificate `c`
when `t ≥ 1000000`), with the branch `qb` for `t = q` and the branch `ob` for exponent 2. -/
inductive Br where
  | skip : Br
  | kill (t : ℕ) : Br
  | node (t : ℕ) (c : List (ℕ × ℕ × List ℕ)) (qb ob : Br) : Br

/-- `chk M qv src b`: the branch `b` closes a source `src` dividing `2N`, where `qv = 0`
(the special prime is not fixed) or `qv = q`. A `kill t` needs `t` prime, so that the mask
only has to record primes. -/
def chk (M : ℕ) : ℕ → ℕ → Br → Bool
  | _, _, .skip => false
  | _, src, .kill t => src % t == 0 && M.testBit t && oddPrime t
  | qv, src, .node t c qb ob =>
    t % 2 == 1 && t != 3 && t != qv && src % t == 0 && isPr c t &&
      (!(qv == 0 && t % 12 == 1) || chk M t (t + 1) qb) && chk M qv (t * t + t + 1) ob

/-- The tree of a row `(p, qb, ob)` at `p ∣ N`, with the special prime not yet fixed. There is
no primality check: a row is only used when `p` is prime. -/
def chkRoot (M p : ℕ) (qb ob : Br) : Bool :=
  p % 2 == 1 && p != 3 && (p % 12 != 1 || chk M p (p + 1) qb) && chk M 0 (p * p + p + 1) ob

/-- Rows `(p, qb, ob)` in order, starting from the mask `M` and ending at the mask `M'`: the
tree of the row closes `p ∣ N` when `p` is prime, and bit `p` is then set. -/
def rowsOK : ℕ → List (ℕ × Br × Br) → ℕ → Bool
  | M, [], M' => M == M'
  | M, (p, qb, ob) :: rest, M' => chkRoot M p qb ob && rowsOK (M ||| 1 <<< p) rest M'

/-- The mask after the rows: bit `p` set for every row prime `p`. -/
def maskAfter (M : ℕ) : List (ℕ × Br × Br) → ℕ
  | [] => M
  | (p, _, _) :: rest => maskAfter (M ||| 1 <<< p) rest

/-- Accepted row lists chain: this splits a long kernel check into blocks. -/
theorem rowsOK_append {M' M'' : ℕ} :
    ∀ {M : ℕ} {r₁ r₂ : List (ℕ × Br × Br)}, rowsOK M r₁ M' = true → rowsOK M' r₂ M'' = true →
      rowsOK M (r₁ ++ r₂) M'' = true
  | _, [], _, h₁, h₂ => by
    simp only [rowsOK, beq_iff_eq] at h₁
    subst h₁
    exact h₂
  | _, (p, qb, ob) :: rest, _, h₁, h₂ => by
    simp only [rowsOK, Bool.and_eq_true, List.cons_append] at h₁ ⊢
    exact ⟨h₁.1, rowsOK_append h₁.2 h₂⟩

theorem testBit_or_shift {M p t : ℕ} (h : (M ||| 1 <<< p).testBit t = true) :
    M.testBit t = true ∨ t = p := by
  rw [Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  exact h.imp id Eq.symm

/-! ## Coverage of a range -/

/-- Every `m` with `lo ≤ m < lo + n` has its bit set in `M` or a divisor `d ∈ D` with
`2 ≤ d < m`. -/
def cover (M : ℕ) (D : List ℕ) (lo n : ℕ) : Bool :=
  (List.range' lo n).all fun m =>
    M.testBit m || D.any (fun d => decide (2 ≤ d) && decide (d < m) && m % d == 0)

/-- Adjacent ranges combine: this splits a long kernel check into blocks. -/
theorem cover_append {M : ℕ} {D : List ℕ} {lo n n' : ℕ} (h₁ : cover M D lo n = true)
    (h₂ : cover M D (lo + n) n' = true) : cover M D lo (n + n') = true := by
  simp only [cover, List.all_eq_true, List.mem_range'_1] at h₁ h₂ ⊢
  intro m hm
  rcases Nat.lt_or_ge m (lo + n) with h | h
  · exact h₁ m ⟨hm.1, h⟩
  · exact h₂ m ⟨h, by omega⟩

/-- `cover_append` with the arithmetic of the ranges as hypotheses. -/
theorem cover_append' {M : ℕ} {D : List ℕ} {lo lo' n n' m : ℕ} (h₁ : cover M D lo n = true)
    (h₂ : cover M D lo' n' = true) (hlo : lo + n = lo') (hm : n + n' = m) :
    cover M D lo m = true := by
  subst hlo hm
  exact cover_append h₁ h₂

/-- Soundness of `cover`: every prime in the range has its bit set. -/
theorem cover_sound {M : ℕ} {D : List ℕ} {lo n : ℕ} (h : cover M D lo n = true) {p : ℕ}
    (hp : p.Prime) (hlo : lo ≤ p) (hhi : p < lo + n) : M.testBit p = true := by
  simp only [cover, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h p ⟨hlo, hhi⟩ with hM | ⟨d, -, ⟨h2, hlt⟩, hdm⟩
  · exact hM
  · exfalso
    rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hdm) with rfl | rfl <;> omega

end RestrainedSeven

end OddPerfect

#print axioms OddPerfect.RestrainedSeven.tdiv_sound
#print axioms OddPerfect.RestrainedSeven.oddPrime_sound
#print axioms OddPerfect.RestrainedSeven.isPr_sound
#print axioms OddPerfect.RestrainedSeven.rowsOK_append
#print axioms OddPerfect.RestrainedSeven.testBit_or_shift
#print axioms OddPerfect.RestrainedSeven.cover_append
#print axioms OddPerfect.RestrainedSeven.cover_append'
#print axioms OddPerfect.RestrainedSeven.cover_sound
