import OddPerfect.CommonPrimeChain

/-!
# Common exponent families: the common `35` family

Let `N` be an odd perfect number with special prime `q`. A common `d` family means that `d`
divides `v_p(N) + 1` for every ordinary prime `p`. This file proves:

* in the common `5` family, `3 ∤ N` and `q ≡ 1 (mod 12)` (known; Evans and Pearlman);
* a target forcing checker (`CommonFam.tcheck`) with a soundness theorem, generic in `d`: from
  seeds dividing `N`, every target node of an accepted table divides `N`, whichever node is
  the special prime;
* a checker for abundant divisors (`CommonFam.abOK`);
* the common `35` family is impossible (known; Hagis and McDaniel), and hence the ordinary
  exponents cannot all equal one `E` with `35 ∣ E + 1`.

The whole common `5` family is impossible by the Main Theorem of Fletcher, Nielsen and Ochem
(Math. Comp. 81, 2012), which gives `5 ∤ N`, together with Kanold's theorem
(`OddPerfect.dvd_of_dvd_succ`), which gives `5 ∣ N`. That general statement is not proved in
this library; the modules for the common `35`, `55`, `65`, `85`, `95` and `115` families give
independent certificates checked by the kernel.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace CommonFam

open OddPerfect.EqChain (gm gm_eq)
open OddPerfect.CommonChain (iter iter_good rowsOK)

/-! ## Abundant divisors given by prime power lists -/

/-- `geomS p a = 1 + p + ... + p ^ a`. -/
def geomS (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | a + 1 => geomS p a + p ^ (a + 1)

/-- `geomS` is the geometric sum. -/
theorem geomS_eq (p : ℕ) : ∀ a, geomS p a = ∑ i ∈ Finset.range (a + 1), p ^ i
  | 0 => by simp [geomS]
  | a + 1 => by rw [geomS, geomS_eq p a, Finset.sum_range_succ _ (a + 1)]

/-- The product `∏ p ^ a` of a list of pairs `(p, a)`. -/
def pPow : List (ℕ × ℕ) → ℕ
  | [] => 1
  | e :: l => e.1 ^ e.2 * pPow l

/-- The product `∏ (1 + p + ... + p ^ a)` of a list of pairs `(p, a)`. -/
def pSig : List (ℕ × ℕ) → ℕ
  | [] => 1
  | e :: l => geomS e.1 e.2 * pSig l

/-- A prime is coprime to `pPow l` when it differs from the primes of `l`. -/
theorem coprime_pPow {p : ℕ} (hp : p.Prime) :
    ∀ l : List (ℕ × ℕ), (∀ e ∈ l, e.1.Prime ∧ e.1 ≠ p) → p.Coprime (pPow l)
  | [], _ => Nat.coprime_one_right p
  | e :: l, h => by
    rw [pPow]
    have he := h e List.mem_cons_self
    exact Nat.Coprime.mul_right
      (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp he.1).mpr (Ne.symm he.2)))
      (coprime_pPow hp l fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- If the primes of `l` are distinct and each `p ^ a` divides `N`, then `pPow l ∣ N` and
`σ(pPow l) = pSig l`. -/
theorem pPow_dvd_and_sigma {N : ℕ} : ∀ l : List (ℕ × ℕ), (∀ e ∈ l, e.1.Prime) →
    (l.map Prod.fst).Nodup → (∀ e ∈ l, e.1 ^ e.2 ∣ N) → pPow l ∣ N ∧ σ 1 (pPow l) = pSig l
  | [], _, _, _ => by simp [pPow, pSig]
  | e :: l, hP, hnd, hd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hd', hs⟩ := pPow_dvd_and_sigma l (fun e' he' => hP e' (List.mem_cons_of_mem _ he'))
      hnd.2 (fun e' he' => hd e' (List.mem_cons_of_mem _ he'))
    have hp := hP e List.mem_cons_self
    have hc : (e.1 ^ e.2).Coprime (pPow l) := Nat.Coprime.pow_left _
      (coprime_pPow hp l fun e' he' => ⟨hP e' (List.mem_cons_of_mem _ he'), fun h => hnd.1
        (List.mem_map.mpr ⟨e', he', h⟩)⟩)
    refine ⟨?_, ?_⟩
    · rw [pPow]
      exact hc.mul_dvd_of_dvd_of_dvd (hd e List.mem_cons_self) hd'
    · rw [pPow, pSig, isMultiplicative_sigma.map_mul_of_coprime hc, hs,
        sigma_one_apply_prime_pow hp, geomS_eq]

/-- A perfect number has no divisor `pPow l` with `2 · pPow l < pSig l`. -/
theorem not_perfect_of_pSig {N : ℕ} (hN : N.Perfect) (l : List (ℕ × ℕ))
    (hP : ∀ e ∈ l, e.1.Prime) (hnd : (l.map Prod.fst).Nodup) (hd : ∀ e ∈ l, e.1 ^ e.2 ∣ N)
    (hlt : 2 * pPow l < pSig l) : False := by
  obtain ⟨hdvd, hs⟩ := pPow_dvd_and_sigma l hP hnd hd
  have hpos : 0 < pPow l := Nat.pos_of_dvd_of_pos hdvd hN.2
  refine not_perfect_of_dvd_of_two_lt_abundancy hdvd ?_ hN
  rw [abundancy, hs, lt_div_iff₀ (by exact_mod_cast hpos)]
  exact_mod_cast hlt

/-- The exponent list: `b` gets exponent `1`, every other element exponent `4`. -/
def expL (S : List ℕ) (b : ℕ) : List (ℕ × ℕ) := S.map fun t => (t, if t = b then 1 else 4)

/-- `S` with `b` to the first power and the rest to the fourth power is abundant. -/
def abundant (S : List ℕ) (b : ℕ) : Bool := decide (2 * pPow (expL S b) < pSig (expL S b))

/-- The abundance checker: abundant for every `b ∈ S` with `b % m = c`, and for `b` outside. -/
def abOK (S : List ℕ) (m c : ℕ) : Bool :=
  (S.all fun b => b % m != c || abundant S b) && abundant S 0

/-- Soundness of `abOK`. Let `N` be perfect, `S` a list of distinct primes dividing `N` with
`t ^ 4 ∣ N` for every `t ∈ S` other than `q`, and `q % m = c`. Then `abOK S m c` fails. -/
theorem abOK_sound {N q m c : ℕ} (hN : N.Perfect) {S : List ℕ} (hP : ∀ t ∈ S, t.Prime)
    (hnd : S.Nodup) (hS : ∀ t ∈ S, t ∣ N) (h4 : ∀ t ∈ S, t ≠ q → t ^ 4 ∣ N) (hqm : q % m = c)
    (hab : abOK S m c = true) : False := by
  rw [abOK, Bool.and_eq_true] at hab
  have key : ∀ b, (∀ t ∈ S, t ≠ b → t ≠ q) → abundant S b = true → False := by
    intro b hb hb'
    rw [abundant, decide_eq_true_eq] at hb'
    have hfst : (expL S b).map Prod.fst = S := by simp [expL, Function.comp_def]
    refine not_perfect_of_pSig hN (expL S b) ?_ (by rw [hfst]; exact hnd) ?_ hb'
    · intro e he
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
      exact hP t ht
    · intro e he
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
      by_cases htb : t = b
      · simpa [htb] using hS t ht
      · simpa [htb] using h4 t ht (hb t ht htb)
  by_cases hqS : q ∈ S
  · have := (List.all_eq_true.mp hab.1) q hqS
    simp only [hqm, bne_self_eq_false, Bool.false_or] at this
    exact key q (fun _ _ h => h) this
  · exact key 0 (fun t ht _ htq => hqS (htq ▸ ht)) hab.2

/-! ## The target forcing checker -/

/-- All targets are reached from the seeds (the first `ns` nodes) by `passes` in order passes,
when the rows whose source equals `b` are never used. -/
def reachAll (nodes : List ℕ) (ns : ℕ) (rows : List (List ℕ)) (targets : List ℕ)
    (passes b : ℕ) : Bool :=
  targets.all fun j => (iter b nodes rows passes (2 ^ ns - 1)).testBit j

/-- The target forcing checker for a common `d` family: `d ≥ 1`, at least `ns` nodes, no node
equals `2`, every receiver `t` of the row of `s` divides `1 + s + ... + s ^ (d - 1)`, and all
targets are reached for every blocked node `b` with `b % m = c` and for the blocked value `0`
(standing for a value outside the table). -/
def tcheck (d m c : ℕ) (nodes : List ℕ) (ns : ℕ) (rows : List (List ℕ)) (targets : List ℕ)
    (passes : ℕ) : Bool :=
  decide (1 ≤ d) && decide (ns ≤ nodes.length) && nodes.all (fun t => t != 2) &&
    rowsOK d nodes rows &&
    nodes.all (fun b => b % m != c || reachAll nodes ns rows targets passes b) &&
    reachAll nodes ns rows targets passes 0

end CommonFam

open CommonFam CommonChain EqChain in
/-- Soundness of the target forcing checker. Let `N` be an odd perfect number and `q` a number
such that `d ∣ v_p(N) + 1` for every prime factor `p ≠ q` (for instance the special prime of a
common `d` family), with `q % m = c`. If the table with prime nodes `nodes`, whose first `ns`
nodes (the seeds) divide `N`, is accepted by `tcheck`, then every target node divides `N`. -/
theorem dvd_of_tcheck {N q d m c ns passes : ℕ} {nodes targets : List ℕ}
    {rows : List (List ℕ)} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → d ∣ N.factorization p + 1) (hqm : q % m = c)
    (hP : ∀ t ∈ nodes, t.Prime) (hseed : ∀ t ∈ nodes.take ns, t ∣ N)
    (hc : tcheck d m c nodes ns rows targets passes = true) :
    ∀ j ∈ targets, nodes.getD j 0 ∣ N := by
  rw [tcheck] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hd, hns⟩, h2⟩, hrows⟩, hcand⟩, h0⟩ := hc
  have hnodes : ∀ y ∈ nodes, y.Prime ∧ y ≠ 2 := fun y hy =>
    ⟨hP y hy, by simpa using (List.all_eq_true.mp h2) y hy⟩
  have hmem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hpN =>
    Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  have key : ∀ b, (∀ y ∈ nodes, y ≠ b → y ≠ q) →
      reachAll nodes ns rows targets passes b = true → ∀ j ∈ targets, nodes.getD j 0 ∣ N := by
    intro b hb hr
    have hstep : ∀ x ∈ nodes, x ∣ N → x ≠ b → ∀ t ∈ nodes, gm x t d = 0 → t ∣ N := by
      intro x hx hxN hxb t ht hg
      have hxp := (hnodes x hx).1
      exact dvd_of_dvd_geom_sum_of_dvd_succ h hxp hd (hexp x (hmem hxp hxN) (hb x hx hxb))
        (hnodes t ht).1 (hnodes t ht).2 (Nat.dvd_of_mod_eq_zero (by rw [← gm_eq]; exact hg))
    have hgm0 : ∀ x ∈ nodes, gm x 0 d ≠ 0 := by
      intro x hx
      rw [gm_eq, Nat.mod_zero]
      exact (Finset.sum_pos (fun i _ => pow_pos (hnodes x hx).1.pos i)
        (Finset.nonempty_range_iff.mpr (by omega))).ne'
    have hz : ∀ e ∈ nodes.zip rows, ∀ j ∈ e.2, gm e.1 (nodes.getD j 0) d = 0 := by
      intro e he j hj
      have := List.all_eq_true.mp (List.all_eq_true.mp hrows e he) j hj
      simpa using this
    have h1 : ∀ k, (2 ^ ns - 1).testBit k = true → nodes.getD k 0 ∣ N := by
      intro k hk
      rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at hk
      have hkl : k < nodes.length := by omega
      rw [List.getD_eq_getElem _ _ hkl]
      have hkt : k < (nodes.take ns).length := by simp; omega
      have : nodes[k] = (nodes.take ns)[k] := by simp
      rw [this]
      exact hseed _ (List.getElem_mem hkt)
    have hgood := iter_good hstep hgm0 hz passes _ h1
    intro j hj
    exact hgood j ((List.all_eq_true.mp hr) j hj)
  by_cases hqn : q ∈ nodes
  · have := (List.all_eq_true.mp hcand) q hqn
    simp only [hqm, bne_self_eq_false, Bool.false_or] at this
    exact key q (fun _ _ hy => hy) this
  · exact key 0 (fun y hy _ hyq => hqn (hyq ▸ hy)) h0

/-! ## The common `5` family -/

open CommonFam in
/-- In the common `5` family, `3 ∤ N` (known; Evans and Pearlman). Let `N` be an odd perfect
number with special prime `q` and `5 ∣ v_p(N) + 1` for every ordinary prime `p`. If `3 ∣ N`,
then `3` and `11 ∣ σ(3 ^ 4) = 121` are ordinary, as is `5`, all with exponent at least `4`, and
`3 ^ 4 · 5 ^ 4 · 11 ^ 4` is abundant. -/
theorem not_three_dvd_of_common_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1) : ¬ 3 ∣ N := by
  intro h3N
  have p3 : Nat.Prime 3 := by norm_num
  have p5 : Nat.Prime 5 := by norm_num
  have p11 : Nat.Prime 11 := by norm_num
  have hq4 := (mod_four_special h hq hodd).1
  have hmem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hpN =>
    Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  have hne : ∀ {p : ℕ}, p % 4 = 3 → p ≠ q := fun h3 hpq => by subst hpq; omega
  have e3 := hexp 3 (hmem p3 h3N) (hne (by norm_num))
  have h11N : 11 ∣ N := dvd_of_dvd_geom_sum_of_dvd_succ h p3 (by norm_num) e3 p11
    (by norm_num) (by norm_num [Finset.sum_range_succ])
  obtain ⟨h5N, h5q⟩ := five_dvd_and_ne_special_of_common h hq hodd hexp
  have four : ∀ {p : ℕ}, p.Prime → p ∣ N → p ≠ q → p ^ 4 ∣ N := fun hp hpN hpq =>
    (hp.pow_dvd_iff_le_factorization h.ne_zero).mpr
      (by have := Nat.le_of_dvd (by omega) (hexp _ (hmem hp hpN) hpq); omega)
  refine not_perfect_of_pSig h.perfect [(3, 4), (5, 4), (11, 4)] ?_ (by decide) ?_
    (by decide +kernel)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> assumption
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact four p3 h3N (hne (by norm_num))
    · exact four p5 h5N h5q
    · exact four p11 h11N (hne (by norm_num))

/-- In the common `5` family, the special prime is `≡ 1 (mod 12)` (known; Evans and
Pearlman). `q ≡ 1 (mod 4)`, and if `q ≡ 2 (mod 3)` then `3 ∣ q + 1 ∣ σ(q ^ v_q(N))`, so
`3 ∣ N`. -/
theorem special_mod_twelve_of_common_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1) : q % 12 = 1 := by
  have hq4 := (mod_four_special h hq hodd).1
  have h3 := not_three_dvd_of_common_five h hq hodd hexp
  have hq3 : q % 3 ≠ 0 := by
    intro h0
    have : 3 ∣ q := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.dvd_prime hq).mp this with h' | h'
    · omega
    · subst h'; norm_num at hq4
  have hq3' : q % 3 ≠ 2 := by
    intro h2
    exact h3 (prime_dvd_of_dvd_succ_special h hq hodd (by norm_num) (by norm_num)
      (by omega : 3 ∣ q + 1)).1
  omega

/-! ## The common `35` family -/

namespace CommonFam

/-- The nodes of the `d = 35` table; the seeds are `5, 7`. -/
def nodes35 : List ℕ :=
  [5, 7, 11, 71, 211, 631, 3851, 41, 1373, 43, 491, 281, 659, 101, 191, 1051, 29, 31, 271, 4831,
   197, 1871, 241, 251, 2591, 181, 151, 239, 1499, 113, 131, 61, 127]

/-- The rows of the `d = 35` table: receiver indices for each source node. -/
def rows35 : List (List ℕ) :=
  [[2, 3, 4, 5], [], [], [6], [], [7], [8], [9, 10], [11, 12], [], [13, 14, 15], [16, 17, 18],
   [19], [], [20, 21], [22], [], [], [23, 24], [25], [], [26], [], [], [27], [], [28], [],
   [29, 30], [], [31, 32]]

/-- The target indices of the `d = 35` table. -/
def targets35 : List ℕ :=
  [0, 1, 2, 16, 17, 7, 9, 31, 3, 13, 29, 32, 30, 26, 25, 14, 20, 4, 27, 22, 23, 18]

/-- The target primes of the `d = 35` table. -/
def vals35 : List ℕ :=
  [5, 7, 11, 29, 31, 41, 43, 61, 71, 101, 113, 127, 131, 151, 181, 191, 197, 211, 239, 241, 251,
   271]

/-- The target indices name the target primes. -/
theorem targets35_vals : targets35.map (nodes35.getD · 0) = vals35 := by decide +kernel

/-- The `d = 35` table is accepted, blocking the nodes `≡ 1 (mod 12)`, with one pass. -/
theorem check35 : tcheck 35 12 1 nodes35 2 rows35 targets35 1 = true := by decide +kernel

/-- The nodes of the `d = 35` table are prime (trial division). -/
theorem nodes35_trial : nodes35.all Pratt.trialPrime = true := by decide +kernel

/-- The nodes of the `d = 35` table are prime. -/
theorem nodes35_prime : ∀ t ∈ nodes35, t.Prime := fun _ ht =>
  Pratt.trialPrime_sound (List.all_eq_true.mp nodes35_trial _ ht)

/-- The target primes are distinct. -/
theorem vals35_nodup : vals35.Nodup := by decide +kernel

/-- The target primes with fourth powers, and any one of them `≡ 1 (mod 12)` to the first power,
give an abundant number. -/
theorem ab35 : abOK vals35 12 1 = true := by decide +kernel

end CommonFam

open CommonFam in
/-- The common `35` family is impossible (known; Hagis and McDaniel). Let `N` be an odd perfect
number with special prime `q`. Then `35 ∣ v_p(N) + 1` cannot hold for every ordinary prime
`p`. -/
theorem not_common_thirty_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 35 ∣ N.factorization p + 1) : False := by
  have hexp5 : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 5 ∣ 35).trans (hexp p hp hpq)
  have hexp7 : ∀ p ∈ N.primeFactors, p ≠ q → 7 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 7 ∣ 35).trans (hexp p hp hpq)
  have h5N := dvd_of_dvd_succ h hq hodd (by norm_num) (by norm_num) hexp5
  have h7N := dvd_of_dvd_succ h hq hodd (by norm_num) (by norm_num) hexp7
  have hq12 := special_mod_twelve_of_common_five h hq hodd hexp5
  have hseed : ∀ t ∈ nodes35.take 2, t ∣ N := by
    intro t ht
    have : nodes35.take 2 = [5, 7] := by decide +kernel
    rw [this] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h5N
    · exact h7N
  have hT := dvd_of_tcheck h hexp hq12 nodes35_prime hseed check35
  have hS : ∀ t ∈ vals35, t ∣ N := by
    rw [← targets35_vals]
    intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    exact hT j hj
  have hPS : ∀ t ∈ vals35, t.Prime := by
    rw [← targets35_vals]
    intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    refine nodes35_prime _ (List.getD_eq_getElem _ _ ?_ ▸ List.getElem_mem _)
    have : targets35.all (· < nodes35.length) = true := by decide +kernel
    simpa using (List.all_eq_true.mp this) j hj
  have h4 : ∀ t ∈ vals35, t ≠ q → t ^ 4 ∣ N := by
    intro t ht htq
    have hp := hPS t ht
    have hmem := Nat.mem_primeFactors.mpr ⟨hp, hS t ht, h.ne_zero⟩
    exact (hp.pow_dvd_iff_le_factorization h.ne_zero).mpr
      (by have := Nat.le_of_dvd (by omega) (hexp t hmem htq); omega)
  exact abOK_sound h.perfect hPS vals35_nodup hS h4 hq12 ab35

/-- The ordinary exponents of an odd perfect number cannot all equal one `E` with
`35 ∣ E + 1`. -/
theorem not_all_exponents_eq_of_thirty_five_dvd_succ {N q E : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : 35 ∣ E + 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = E) : False :=
  not_common_thirty_five h hq hodd fun p hp hpq => hexp p hp hpq ▸ hE

end OddPerfect

#print axioms OddPerfect.CommonFam.geomS_eq
#print axioms OddPerfect.CommonFam.coprime_pPow
#print axioms OddPerfect.CommonFam.pPow_dvd_and_sigma
#print axioms OddPerfect.CommonFam.not_perfect_of_pSig
#print axioms OddPerfect.CommonFam.abOK_sound
#print axioms OddPerfect.dvd_of_tcheck
#print axioms OddPerfect.not_three_dvd_of_common_five
#print axioms OddPerfect.special_mod_twelve_of_common_five
#print axioms OddPerfect.CommonFam.targets35_vals
#print axioms OddPerfect.CommonFam.check35
#print axioms OddPerfect.CommonFam.nodes35_trial
#print axioms OddPerfect.CommonFam.nodes35_prime
#print axioms OddPerfect.CommonFam.vals35_nodup
#print axioms OddPerfect.CommonFam.ab35
#print axioms OddPerfect.not_common_thirty_five
#print axioms OddPerfect.not_all_exponents_eq_of_thirty_five_dvd_succ
