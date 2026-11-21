import OddPerfect.CommonFamily

/-!
# Common exponent families: `7 ∤ N` in the common `5` family

Let `N` be an odd perfect number with special prime `q`. A common `d` family means that `d`
divides `v_p(N) + 1` for every ordinary prime `p`. This file proves:

* primality by trial division up to the square root (`FamInst.sqPrime`);
* target forcing reach checks (`FamInst.reach`) whose blocked candidates are the source nodes
  satisfying an arbitrary Boolean predicate that holds at the special prime, with soundness
  `dvd_of_reach`; the kernel evaluates the bit mask at every step, and the reached mask is
  compared with the target mask once per blocked value, so the checks can be split into parts;
* an abundance checker `FamInst.abOK2` that compares every case with the two full products
  once, and the combined closer `false_of_reach`;
* in the common `5` family, `7 ∤ N` (known; Evans and Pearlman 2007).
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.EqChain (gm gm_eq)
open OddPerfect.CommonChain (maskOf testBit_maskOf)
open OddPerfect.CommonFam (geomS pPow pSig expL not_perfect_of_pSig)

/-! ## Trial division up to the square root -/

/-- `tdiv q f m` checks with fuel `f` that no `k ≥ m` of the parity of `m` with `k * k ≤ q`
divides `q`. -/
def tdiv (q : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, m => decide (q < m * m) || (q % m != 0 && tdiv q f (m + 2))

/-- Soundness of `tdiv`. -/
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

/-- Primality by trial division over odd numbers up to the square root. -/
def sqPrime (q : ℕ) : Bool := decide (2 ≤ q) && (q == 2 || (q % 2 != 0 && tdiv q q 3))

/-- Soundness of `sqPrime`. -/
theorem sqPrime_sound {q : ℕ} (h : sqPrime q = true) : q.Prime := by
  simp only [sqPrime, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  rcases h with ⟨h2, rfl | ⟨hodd, ht⟩⟩
  · exact Nat.prime_two
  by_contra hp
  have hm := Nat.minFac_prime (show q ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  have hdvd := Nat.minFac_dvd q
  have hm2 : q.minFac % 2 = 1 := by
    rcases hm.eq_two_or_odd with h' | h'
    · rw [h'] at hdvd
      exact absurd (Nat.mod_eq_zero_of_dvd hdvd) hodd
    · exact h'
  have hm3 : 3 ≤ q.minFac := by have := hm.two_le; omega
  exact tdiv_sound q 3 ht _ hm3 (by omega) (by simpa [pow_two] using hsq)
    (Nat.mod_eq_zero_of_dvd hdvd)

/-- Primality: listed in an accepted Pratt certificate, or trial division up to the square
root. -/
def isPS (pc : List (ℕ × ℕ × List ℕ)) (r : ℕ) : Bool :=
  (pc.map Prod.fst).contains r || sqPrime r

/-- Soundness of `isPS`. -/
theorem isPS_sound {pc : List (ℕ × ℕ × List ℕ)} (hpc : Pratt.check pc = true) {r : ℕ}
    (h : isPS pc r = true) : r.Prime := by
  simp only [isPS, Bool.or_eq_true, List.contains_iff_mem, List.mem_map] at h
  rcases h with ⟨e, he, rfl⟩ | h
  · exact Pratt.check_sound hpc e he
  · exact sqPrime_sound h

/-! ## The target forcing checker with a candidate predicate -/

/-- One in order pass over the rows: row `i` is used when bit `i` of `M` is set and the source
node `x` differs from the blocked value `b`; it then sets the bits of its receivers. The test
selects the recursive call, so the kernel evaluates the mask at every step. -/
def fpass (b : ℕ) : ℕ → List ℕ → List (List ℕ) → ℕ → ℕ
  | _, [], _, M => M
  | _, _ :: _, [], M => M
  | i, x :: xs, row :: rs, M =>
    if M.testBit i && x != b then fpass b (i + 1) xs rs (M ||| maskOf row)
    else fpass b (i + 1) xs rs M

/-- At most `n` passes over the table, stopping once every bit of `tm` is set. -/
def fiter (b : ℕ) (nodes : List ℕ) (rows : List (List ℕ)) (tm : ℕ) : ℕ → ℕ → ℕ
  | 0, M => M
  | n + 1, M => if M &&& tm == tm then M else fiter b nodes rows tm n (fpass b 0 nodes rows M)

/-- Reading the head of a suffix. -/
theorem drop_facts {nodes xs : List ℕ} {i x : ℕ} (hd : nodes.drop i = x :: xs) :
    nodes.getD i 0 = x ∧ x ∈ nodes ∧ nodes.drop (i + 1) = xs := by
  refine ⟨?_, List.mem_of_mem_drop (hd ▸ List.mem_cons_self), ?_⟩
  · have := congrArg (fun l : List ℕ => l[0]?) hd
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at this
    rw [List.getD_eq_getElem?_getD, this, Option.getD_some]
  · rw [← List.drop_drop, hd, List.drop_one, List.tail_cons]

/-- A pass preserves the property that every set bit indexes a divisor of `N`. The source
nodes are the first `rows.length` nodes, and only their steps are needed. -/
theorem fpass_good {N r b : ℕ} {nodes : List ℕ} {rows : List (List ℕ)}
    (hstep : ∀ x ∈ nodes.take rows.length, x ∣ N → x ≠ b → ∀ t ∈ nodes, gm x t r = 0 → t ∣ N)
    (hgm0 : ∀ x ∈ nodes, gm x 0 r ≠ 0) :
    ∀ (xs : List ℕ) (rs : List (List ℕ)) (i M : ℕ), nodes.drop i = xs → rows.drop i = rs →
      (∀ e ∈ xs.zip rs, ∀ j ∈ e.2, gm e.1 (nodes.getD j 0) r = 0) →
      (∀ k, M.testBit k = true → nodes.getD k 0 ∣ N) →
      ∀ k, (fpass b i xs rs M).testBit k = true → nodes.getD k 0 ∣ N
  | [], _, _, _, _, _, _, hM => hM
  | _ :: _, [], _, _, _, _, _, hM => hM
  | x :: xs, row :: rs, i, M, hd, hr, hz, hM => by
    obtain ⟨hxi, hxn, hd'⟩ := drop_facts hd
    have hr' : rows.drop (i + 1) = rs := by
      rw [← List.drop_drop, hr, List.drop_one, List.tail_cons]
    have hi : i < rows.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hr
      exact List.cons_ne_nil _ _ hr.symm
    have hin : i < nodes.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hd
      exact List.cons_ne_nil _ _ hd.symm
    have hxs : x ∈ nodes.take rows.length := by
      rw [List.getD_eq_getElem _ _ hin] at hxi
      exact List.mem_take_iff_getElem.mpr ⟨i, by omega, hxi⟩
    have hz' := fun e he => hz e (List.mem_cons_of_mem _ he)
    rw [fpass]
    split_ifs with hc
    · refine fpass_good hstep hgm0 xs rs (i + 1) _ hd' hr' hz' ?_
      intro k hk
      rw [Nat.testBit_lor, Bool.or_eq_true, testBit_maskOf] at hk
      rcases hk with hk | hk
      · exact hM k hk
      simp only [Bool.and_eq_true, bne_iff_ne] at hc
      have hg := hz (x, row) List.mem_cons_self k hk
      have hxN : x ∣ N := hxi ▸ hM i hc.1
      by_cases hkl : k < nodes.length
      · rw [List.getD_eq_getElem _ _ hkl] at hg ⊢
        exact hstep x hxs hxN hc.2 _ (List.getElem_mem hkl) hg
      · rw [List.getD_eq_default _ _ (by omega)] at hg
        exact absurd hg (hgm0 x hxn)
    · exact fpass_good hstep hgm0 xs rs (i + 1) _ hd' hr' hz' hM

/-- `fiter` preserves the same property. -/
theorem fiter_good {N r b tm : ℕ} {nodes : List ℕ} {rows : List (List ℕ)}
    (hstep : ∀ x ∈ nodes.take rows.length, x ∣ N → x ≠ b → ∀ t ∈ nodes, gm x t r = 0 → t ∣ N)
    (hgm0 : ∀ x ∈ nodes, gm x 0 r ≠ 0)
    (hz : ∀ e ∈ nodes.zip rows, ∀ j ∈ e.2, gm e.1 (nodes.getD j 0) r = 0) :
    ∀ (n M : ℕ), (∀ k, M.testBit k = true → nodes.getD k 0 ∣ N) →
      ∀ k, (fiter b nodes rows tm n M).testBit k = true → nodes.getD k 0 ∣ N
  | 0, _, hM => hM
  | n + 1, M, hM => by
    rw [fiter]
    split_ifs
    · exact hM
    · exact fiter_good hstep hgm0 hz n _
        (fpass_good hstep hgm0 nodes rows 0 M List.drop_zero List.drop_zero hz hM)

/-- All bits of the target mask `tm` are reached from the seeds (the first `ns` nodes) by
`passes` in order passes, when the rows whose source equals `b` are never used. -/
def reach (nodes : List ℕ) (rows : List (List ℕ)) (ns tm passes b : ℕ) : Bool :=
  fiter b nodes rows tm passes (2 ^ ns - 1) &&& tm == tm

/-- The divisibility check of the rows: every receiver `t` of the row of `s` divides
`1 + s + ... + s ^ (d - 1)`. -/
def rowChk (d : ℕ) (nodes : List ℕ) (e : ℕ × List ℕ) : Bool :=
  e.2.all fun j => gm e.1 (nodes.getD j 0) d == 0

/-- A Boolean statement over a list follows from the same statement over its parts. -/
theorem all_of_parts {α : Type} {L : List α} {f : α → Bool} (parts : List (List α))
    (hL : L = parts.flatten) (hp : ∀ c ∈ parts, c.all f = true) : ∀ b ∈ L, f b = true := by
  subst hL
  intro b hb
  obtain ⟨c, hc, hbc⟩ := List.mem_flatten.mp hb
  exact List.all_eq_true.mp (hp c hc) b hbc

/-- Distinctness by a bit mask of the values seen so far. -/
def ndM : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, M => !M.testBit a && ndM l (M ||| 2 ^ a)

/-- Soundness of `ndM`. -/
theorem nodup_of_ndM : ∀ {l : List ℕ} {M : ℕ}, ndM l M = true →
    l.Nodup ∧ ∀ x ∈ l, M.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, fun _ hx => absurd hx List.not_mem_nil⟩
  | a :: l, M, h => by
    simp only [ndM, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hnd, hl⟩ := nodup_of_ndM h.2
    have hl' : ∀ x ∈ l, x ≠ a ∧ M.testBit x = false := by
      intro x hx
      have := hl x hx
      rw [Nat.testBit_lor, Bool.or_eq_false_iff, Nat.testBit_two_pow] at this
      exact ⟨fun hxa => by simp [hxa] at this, this.1⟩
    refine ⟨List.nodup_cons.mpr ⟨fun ha => (hl' a ha).1 rfl, hnd⟩, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact (hl' x hx).2

/-! ## The abundance checker -/

/-- The abundance checker, with `P` and `G` standing for the products of `t ^ 4` and of
`1 + t + ... + t ^ 4` over `S`: for every `b ∈ S` with `cand b`, replacing `b ^ 4` by `b` gives
an abundant number, and so does the full product. -/
def abOK2 (S : List ℕ) (cand : ℕ → Bool) (P G : ℕ) : Bool :=
  (S.all fun b => !cand b || decide (2 * P * geomS b 4 < G * (b + 1) * b ^ 3)) &&
    decide (2 * P < G)

/-- Unfolding `expL` at a cons. -/
theorem expL_cons (t : ℕ) (S : List ℕ) (b : ℕ) :
    expL (t :: S) b = (t, if t = b then 1 else 4) :: expL S b := rfl

/-- `expL S b = expL S 0` when no element of `S` is `b` or `0`. -/
theorem expL_eq_of_forall_ne {S : List ℕ} {b : ℕ} (h : ∀ t ∈ S, t ≠ b ∧ t ≠ 0) :
    expL S b = expL S 0 := by
  unfold expL
  refine List.map_congr_left fun t ht => ?_
  simp [(h t ht).1, (h t ht).2]

/-- Splitting off one element: with `b ∈ S`, distinct nonzero elements, the full products
`pPow (expL S 0)` and `pSig (expL S 0)` relate to those with `b` to the first power. -/
theorem pPow_pSig_split : ∀ {S : List ℕ} {b : ℕ}, (∀ t ∈ S, t ≠ 0) → S.Nodup → b ∈ S →
    pPow (expL S 0) = pPow (expL S b) * b ^ 3 ∧
      pSig (expL S 0) * (b + 1) = pSig (expL S b) * geomS b 4
  | [], _, _, _, hb => absurd hb List.not_mem_nil
  | t :: S, b, h0, hnd, hb => by
    rw [List.nodup_cons] at hnd
    have ht0 : t ≠ 0 := h0 t List.mem_cons_self
    have h0' : ∀ u ∈ S, u ≠ 0 := fun u hu => h0 u (List.mem_cons_of_mem _ hu)
    rw [expL_cons, expL_cons]
    by_cases htb : t = b
    · subst htb
      have he : expL S t = expL S 0 :=
        expL_eq_of_forall_ne fun u hu => ⟨fun h => hnd.1 (h ▸ hu), h0' u hu⟩
      simp only [pPow, pSig, if_neg ht0, he, ↓reduceIte, geomS]
      constructor <;> ring
    · have hbS : b ∈ S := by
        rcases List.mem_cons.mp hb with h | h
        · exact absurd h.symm htb
        · exact h
      obtain ⟨e1, e2⟩ := pPow_pSig_split h0' hnd.2 hbS
      simp only [pPow, pSig, if_neg htb, if_neg ht0]
      constructor
      · rw [e1]; ring
      · rw [mul_assoc, e2]; ring

end FamInst

open FamInst CommonChain EqChain in
/-- Soundness of the reach checks. Let `N` be an odd perfect number and `q` a number such that
`d ∣ v_p(N) + 1` for every prime factor `p ≠ q`, where `d ≥ 1`, with `cand q`. Take a table with
odd prime nodes `nodes`, whose first `ns` nodes divide `N` (with `ns` at most the number of
nodes), and whose rows pass `rowChk`. If all bits of `tm` are reached for every blocked source
node `b` (one of the first `rows.length` nodes) with `cand b`, and for the blocked value `0`,
then every node whose index is a bit of `tm` divides `N`. -/
theorem dvd_of_reach {N q d ns passes tm : ℕ} {cand : ℕ → Bool} {nodes : List ℕ}
    {rows : List (List ℕ)} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → d ∣ N.factorization p + 1) (hd : 1 ≤ d)
    (hcq : cand q = true) (hP : ∀ t ∈ nodes, t.Prime) (h2 : ∀ t ∈ nodes, t ≠ 2)
    (hseed : ∀ t ∈ nodes.take ns, t ∣ N) (hns : ns ≤ nodes.length)
    (hrows : ∀ e ∈ nodes.zip rows, rowChk d nodes e = true)
    (hcand : ∀ b ∈ nodes.take rows.length, cand b = true →
      reach nodes rows ns tm passes b = true)
    (h0 : reach nodes rows ns tm passes 0 = true) :
    ∀ k, tm.testBit k = true → nodes.getD k 0 ∣ N := by
  have hmem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hpN =>
    Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  have key : ∀ b, (∀ y ∈ nodes.take rows.length, y ≠ b → y ≠ q) →
      reach nodes rows ns tm passes b = true → ∀ k, tm.testBit k = true → nodes.getD k 0 ∣ N := by
    intro b hb hr
    have hstep : ∀ x ∈ nodes.take rows.length, x ∣ N → x ≠ b → ∀ t ∈ nodes, gm x t d = 0 →
        t ∣ N := by
      intro x hx hxN hxb t ht hg
      have hxp := hP x (List.mem_of_mem_take hx)
      exact dvd_of_dvd_geom_sum_of_dvd_succ h hxp hd (hexp x (hmem hxp hxN) (hb x hx hxb))
        (hP t ht) (h2 t ht) (Nat.dvd_of_mod_eq_zero (by rw [← gm_eq]; exact hg))
    have hgm0 : ∀ x ∈ nodes, gm x 0 d ≠ 0 := by
      intro x hx
      rw [gm_eq, Nat.mod_zero]
      exact (Finset.sum_pos (fun i _ => pow_pos (hP x hx).pos i)
        (Finset.nonempty_range_iff.mpr (by omega))).ne'
    have hz : ∀ e ∈ nodes.zip rows, ∀ j ∈ e.2, gm e.1 (nodes.getD j 0) d = 0 := by
      intro e he j hj
      have := List.all_eq_true.mp (hrows e he) j hj
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
    have hgood := fiter_good (tm := tm) hstep hgm0 hz passes _ h1
    intro k hk
    simp only [reach, beq_iff_eq] at hr
    apply hgood k
    rw [← hr, Nat.testBit_land, Bool.and_eq_true] at hk
    exact hk.1
  by_cases hqn : q ∈ nodes.take rows.length
  · exact key q (fun _ _ hy => hy) (hcand q hqn hcq)
  · exact key 0 (fun y hy _ hyq => hqn (hyq ▸ hy)) h0

open FamInst CommonFam in
/-- Soundness of `abOK2`. Let `N` be perfect, `S` a list of distinct primes dividing `N` with
`t ^ 4 ∣ N` for every `t ∈ S` other than `q`, and `cand q`. If `P` and `G` are the products of
`t ^ 4` and of `1 + t + ... + t ^ 4` over `S`, then `abOK2 S cand P G` fails. -/
theorem FamInst.abOK2_sound {N q P G : ℕ} {cand : ℕ → Bool} (hN : N.Perfect) {S : List ℕ}
    (hP : ∀ t ∈ S, t.Prime) (hnd : S.Nodup) (hS : ∀ t ∈ S, t ∣ N)
    (h4 : ∀ t ∈ S, t ≠ q → t ^ 4 ∣ N) (hcq : cand q = true)
    (hPG : pPow (expL S 0) = P ∧ pSig (expL S 0) = G) (hab : abOK2 S cand P G = true) :
    False := by
  rw [abOK2, Bool.and_eq_true] at hab
  have key : ∀ b, (∀ t ∈ S, t ≠ b → t ≠ q) → 2 * pPow (expL S b) < pSig (expL S b) →
      False := by
    intro b hb hb'
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
    simp only [hcq, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
    obtain ⟨e1, e2⟩ := pPow_pSig_split (fun t ht => (hP t ht).ne_zero) hnd hqS
    refine key q (fun _ _ h => h) (Nat.lt_of_mul_lt_mul_right (a := q ^ 3 * geomS q 4) ?_)
    rw [← hPG.1, ← hPG.2, e1] at this
    calc 2 * pPow (expL S q) * (q ^ 3 * geomS q 4)
        = 2 * (pPow (expL S q) * q ^ 3) * geomS q 4 := by ring
      _ < pSig (expL S 0) * (q + 1) * q ^ 3 := this
      _ = pSig (expL S q) * (q ^ 3 * geomS q 4) := by rw [e2]; ring
  · refine key 0 (fun t ht _ htq => hqS (htq ▸ ht)) ?_
    rw [hPG.1, hPG.2]
    simpa using hab.2

open FamInst CommonFam CommonChain in
/-- The combined closer. Let `N` be an odd perfect number and `q` a number with `cand q` and
`cand' q`, such that `d ∣ v_p(N) + 1` for every prime factor `p ≠ q`, where `d ≥ 5`. A table as
in `dvd_of_reach`, whose selected target primes `vals` (the nodes whose index is a bit of `tm`)
pass `abOK2` with `cand'`, gives a contradiction. -/
theorem false_of_reach {N q d ns passes tm P G : ℕ} {cand cand' : ℕ → Bool}
    {nodes vals : List ℕ} {rows : List (List ℕ)} (h : OddPerfect N)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → d ∣ N.factorization p + 1) (hd : 5 ≤ d)
    (hcq : cand q = true) (hcq' : cand' q = true) (hP : ∀ t ∈ nodes, t.Prime)
    (h2 : ∀ t ∈ nodes, t ≠ 2) (hseed : ∀ t ∈ nodes.take ns, t ∣ N) (hns : ns ≤ nodes.length)
    (hrows : ∀ e ∈ nodes.zip rows, rowChk d nodes e = true)
    (hcand : ∀ b ∈ nodes.take rows.length, cand b = true →
      reach nodes rows ns tm passes b = true)
    (h0 : reach nodes rows ns tm passes 0 = true) (hv : sel 0 tm 0 nodes = vals)
    (hnd : vals.Nodup) (hPG : pPow (expL vals 0) = P ∧ pSig (expL vals 0) = G)
    (hab : abOK2 vals cand' P G = true) : False := by
  have hT := dvd_of_reach h hexp (by omega) hcq hP h2 hseed hns hrows hcand h0
  have hS : ∀ t ∈ vals, t ∣ N := by
    rw [← hv]
    intro t ht
    obtain ⟨-, k, hk, rfl⟩ := mem_sel nodes 0 List.drop_zero t ht
    exact hT k hk
  have hPS : ∀ t ∈ vals, t.Prime := by
    rw [← hv]
    intro t ht
    exact hP t ((sel_sublist 0 tm 0 nodes).subset ht)
  have h4 : ∀ t ∈ vals, t ≠ q → t ^ 4 ∣ N := by
    intro t ht htq
    have hp := hPS t ht
    have hmem := Nat.mem_primeFactors.mpr ⟨hp, hS t ht, h.ne_zero⟩
    exact (hp.pow_dvd_iff_le_factorization h.ne_zero).mpr
      (by have := Nat.le_of_dvd (by omega) (hexp t hmem htq); omega)
  exact abOK2_sound h.perfect hPS hnd hS h4 hcq' hPG hab

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- The nodes of the `d = 5` table: seeds, other sources, then sinks. -/
def nodes57 : List ℕ :=
  [5, 7, 11, 71, 211, 2221, 1361, 292661, 271241, 17950001, 11831, 58044391, 191, 1021, 3724261, 421, 1871, 13001, 332441, 181, 228729421, 17981, 32491, 60661, 19622651, 3001, 97241, 10321, 613680341, 34031, 210875011, 61151, 274871, 20088011, 164881, 1478611, 101, 350411, 346331, 745631, 2131081, 2722199861, 2724573361, 6421, 520392931, 1381, 47791, 16240811, 5351, 9851, 187951, 142120211, 6971, 149111, 549071, 19976441, 13405541, 1091, 401, 1931, 815261, 2314061, 18541, 22274201, 2621, 26141, 34301, 431, 86680961, 1929249901, 2411, 82231, 1372961, 3911, 51431, 5514451, 1231, 382861, 50209751, 797201, 810991241, 631, 82543061, 102451, 8378281, 811771, 510101, 2531, 20390861, 3761, 990211, 1417631, 74551, 3491, 131663471, 22124771, 157061, 78191, 2522441, 11402011, 473861, 298021, 1721, 265471, 751, 9189941, 1337701, 126631, 1616711, 281, 55272601, 37394041, 1601, 212841901, 146234371, 707071, 148899791, 16637371, 468271, 43411, 44501, 46061, 125731, 109661, 119611, 35731, 414614141, 271, 148961, 49626701, 36451, 16292501, 2827381, 24851, 3541051, 288261341, 6571, 1531, 96911, 464351, 385741, 131, 3041, 4313591, 470881, 1571, 284741, 26712541, 713040791, 10135501, 5294671, 3334879201, 152211901, 1591242871, 1607201, 881, 973001, 6481, 246941, 5231, 118861, 3548401, 167771, 1135261, 168358511, 174931, 17791, 150961, 86011, 19121, 2311, 1151, 28151, 4651, 146521, 12601, 70321, 96821, 26613511, 7901, 12011, 29603771, 76261, 10211, 303571, 1734721, 127373801, 550531, 10631, 1427561, 1618996811, 4261, 105191791, 674737621, 147811, 6738091, 9065531, 13609121, 2671, 73181, 8919431, 9811, 1901, 3691, 33101561, 4451, 2716541, 121001, 37950361, 1291, 28631, 571, 126500041, 19081, 12281, 26951, 4051, 135701, 43651, 821, 45305551, 178091, 102701, 203112691, 18731, 446316151, 72931, 971, 9011, 1789091, 150352561, 163861, 598317611, 9687641, 4443631, 281531, 399851, 258031, 1166141, 153911, 5532551, 8821, 6701, 426301, 7121, 979291, 30931, 7541, 622077551, 15511, 8941, 34668391, 24181, 580901, 280931731, 651657031, 1145371, 41011, 42841, 8011, 1829424241, 18583531, 334521521, 121081, 2851, 12280841, 9341851, 131371, 24781, 63541, 29881, 9536591, 4482721, 1811, 32801, 19301, 198179341, 1451371, 470711, 51239341, 5596561, 43945861, 5531, 100741, 17021, 20411, 34017211, 4811311, 17321, 753736541, 16061, 1039741531, 7561, 12947101, 21191, 1471, 14878601, 82031, 35595181, 517721, 1052021381, 691, 14591, 8036261, 68053211, 33461, 15331, 14152441, 15392471, 39802921, 77261, 89891, 1226341, 87146351, 6121, 16533311, 254491, 46861, 3668251, 20603701, 2473613371, 17771321, 26731, 173880281, 17911, 19281151, 264078811, 74872741, 387313141, 164831, 30391, 4661551, 68581, 29761, 29411, 15451, 37951, 14221, 55431421, 75161, 275941, 13361021, 74381, 18701, 104891, 28647011, 74338681, 1113221, 293640301, 189565231, 6999611, 49031, 2910751, 55661, 320521, 4849651, 2920031, 25301, 31, 41, 61, 151, 241, 251, 311, 331, 461, 491, 521, 541, 601, 641, 661, 701, 761, 811, 911, 941, 991, 1031, 1051, 1061, 1171, 1201, 1301, 1321, 1451, 1481, 1511, 1801, 1831, 1861, 1951, 2011, 2081, 2131, 2161, 2251, 2351, 2371, 2381, 2441, 2521, 2551, 2591, 2711, 2741, 2801, 2971, 3011, 3221, 3301, 3371, 3391, 3511, 3571, 3581, 3631]

/-- The rows of the `d = 5` table: receiver indices for each source node. -/
def rows57 : List (List ℕ) :=
  [[2, 3],
   [407],
   [410],
   [4, 5],
   [6, 7],
   [8, 9],
   [10, 11],
   [12, 362],
   [13],
   [359],
   [14, 360],
   [15],
   [16, 17],
   [18, 386],
   [364],
   [19],
   [20, 361],
   [21, 22, 389],
   [23],
   [24],
   [25, 26],
   [27, 28, 411],
   [29],
   [30],
   [31],
   [32, 368],
   [33],
   [34],
   [35, 366],
   [36, 37],
   [38],
   [39],
   [40, 41],
   [42],
   [43],
   [44],
   [45, 358, 367],
   [46],
   [47],
   [48, 49],
   [50, 51],
   [52],
   [53, 374],
   [54, 55],
   [56],
   [57],
   [58, 371],
   [59, 60],
   [61],
   [62, 63],
   [64, 65, 66],
   [67, 68],
   [69],
   [70, 71],
   [72],
   [73],
   [391],
   [74, 75],
   [76, 77],
   [78],
   [79],
   [80],
   [81],
   [82],
   [83, 84],
   [85, 365],
   [412],
   [86],
   [48],
   [385],
   [87, 88],
   [377],
   [89],
   [90, 369, 395],
   [91],
   [92],
   [93, 94],
   [95],
   [96],
   [416],
   [97],
   [388],
   [98],
   [99],
   [383],
   [100],
   [101],
   [102, 103],
   [104],
   [105],
   [106],
   [107, 108],
   [109, 402],
   [110],
   [111],
   [382],
   [112, 113],
   [114],
   [115, 116],
   [117],
   [381],
   [118],
   [119],
   [120],
   [121, 122],
   [375],
   [123, 409],
   [124],
   [125, 126],
   [127, 128],
   [129],
   [130],
   [131],
   [132],
   [417],
   [398],
   [133],
   [134],
   [135],
   [136],
   [137],
   [394],
   [138],
   [139],
   [413],
   [140],
   [141, 142],
   [143, 363],
   [144],
   [145],
   [146, 147, 374],
   [397],
   [148],
   [149],
   [150],
   [151],
   [152],
   [153],
   [408],
   [154],
   [155],
   [156],
   [157],
   [158],
   [159, 160],
   [161],
   [162, 163, 164],
   [165],
   [166],
   [167],
   [168],
   [169],
   [170],
   [171, 172],
   [173],
   [174],
   [175],
   [415],
   [176],
   [370],
   [19, 177],
   [178],
   [179, 180],
   [181],
   [182],
   [368],
   [376, 379],
   [183],
   [184],
   [185, 186],
   [187, 404],
   [378],
   [188],
   [189],
   [190],
   [191, 192],
   [193],
   [194],
   [393],
   [195],
   [196],
   [197, 365],
   [67, 401],
   [198],
   [199],
   [200],
   [89],
   [201, 400],
   [202, 203, 204],
   [205],
   [206],
   [207],
   [208],
   [209],
   [210, 380],
   [73, 166],
   [384],
   [392],
   [211],
   [212],
   [213],
   [214],
   [215],
   [216],
   [217],
   [70],
   [381],
   [218, 359],
   [406],
   [219],
   [220],
   [390],
   [221],
   [222, 223],
   [224],
   [225],
   [226],
   [227],
   [228],
   [229],
   [230],
   [231],
   [198, 232],
   [233],
   [234],
   [235],
   [396],
   [399],
   [236],
   [237],
   [238],
   [239, 240],
   [241],
   [242],
   [243],
   [244],
   [245, 364],
   [246],
   [406],
   [247, 248],
   [377],
   [57, 380],
   [249],
   [250],
   [251],
   [252, 253],
   [254, 255],
   [256, 387],
   [257],
   [258],
   [259],
   [260],
   [261, 262],
   [263],
   [264],
   [265],
   [266, 373, 414],
   [25, 267],
   [268],
   [269],
   [382],
   [270],
   [271],
   [272],
   [273],
   [274],
   [275, 276],
   [409],
   [277],
   [385],
   [278, 279, 370],
   [145, 280],
   [281],
   [282],
   [283, 403],
   [405],
   [284, 285],
   [286],
   [415],
   [287],
   [288],
   [289],
   [290],
   [291],
   [64],
   [59],
   [292],
   [293, 383],
   [294],
   [295, 296],
   [372],
   [297],
   [298],
   [299],
   [300],
   [301],
   [13],
   [401],
   [295],
   [247, 302],
   [303],
   [304],
   [305],
   [306, 386],
   [307],
   [308],
   [309],
   [384],
   [310],
   [311],
   [81],
   [312, 313],
   [314],
   [315],
   [316],
   [317],
   [318],
   [398],
   [319],
   [320],
   [321],
   [322],
   [323],
   [324, 325],
   [326],
   [327, 328],
   [329],
   [330],
   [331],
   [332],
   [333],
   [334],
   [155],
   [335],
   [336],
   [337, 338],
   [339, 340],
   [341],
   [412],
   [342],
   [343],
   [344, 393],
   [345],
   [346, 392],
   [347],
   [348],
   [209],
   [349],
   [350],
   [351],
   [352],
   [353],
   [354],
   [170],
   [355],
   [356],
   [357],
   [416]]

/-- The target primes of the `d = 5` table, in node order. -/
def vals57 : List ℕ :=
  [5, 7, 11, 71, 211, 2221, 1361, 191, 1021, 421, 1871, 181, 3001, 101, 1381, 1091, 401, 1931, 2621, 431, 2411, 3911, 1231, 631, 2531, 3761, 3491, 1721, 751, 281, 1601, 271, 1531, 131, 3041, 1571, 881, 2311, 1151, 2671, 1901, 3691, 1291, 571, 821, 971, 2851, 1811, 1471, 691, 31, 41, 61, 151, 241, 251, 311, 331, 461, 491, 521, 541, 601, 641, 661, 701, 761, 811, 911, 941, 991, 1031, 1051, 1061, 1171, 1201, 1301, 1321, 1451, 1481, 1511, 1801, 1831, 1861, 1951, 2011, 2081, 2131, 2161, 2251, 2351, 2371, 2381, 2441, 2521, 2551, 2591, 2711, 2741, 2801, 2971, 3011, 3221, 3301, 3371, 3391, 3511, 3571, 3581, 3631]

/-- The target mask: bit `j` is set when node `j` is a target. -/
def tm57 : ℕ :=
  676921312041214564739625629732099241949645588294258069794817872507308209331449246912790033839785597649382479551140155569582207

/-- The product of `t ^ 4` over the target primes. -/
def P57 : ℕ :=
  235162411391603360209552998872286311590501096262914142050060205783167496241523728223231622057961362448346508172955299835405051620157460671330675813840004771665445601454618411389312426523793133170116050478362323731039930831975871204252995871491920666620330004476472609776431251401891471085288336795082786745279459905628691199177113170100526382309053016245485330735031499037721206684447976788550408966874509983996507552864527204241451967905860405316131798598691537622855536687274227095593390016998607171311121357211453433920577087146643525153179328427515018599282570143906458001460961922111855839219167177640713213163963713418790613059792083817364323507044276965952267797697970830387658580096717357987462075228759764003186990947410349982337625937051523685475020260486103300965643649913888056435357043458099695301364903616330056845909074673733750130315720733268868119524480353235498950127127579217605172087708860846756519760571642243489100043341000608757442491810808051896243812932870309169666282540718371737009012584390040031258404434795453763689434051547807687052977654073502288799193865435420107512314547644785695667533113656663753104312008174814591721957098912112064557559689710176567992217280784861081293828991480750959045992626529437674801998263605944061680876124915096040925966732029359238014851270334850625

/-- The product of `1 + t + ... + t ^ 4` over the target primes. -/
def G57 : ℕ :=
  470563072332840117210812034186701876319678550867415926301136694628853927236136970990490726810358613425607713723978379312086873978350894466507116487988085045742316544229719435166283141112153473604568922495007950275428457470849077175890986941779930770347947750293526094412540370276874504562024733581427826235397609108979359796106022310575970459131557524182410239262919535487611212291558342484134611525706898854533494574524002289418828854007307318742094868751446827606166938637454364329618264549440121770679834903933672200275706771948236409676732722223331145505197659316142344831990629012300498345675096151725377757831552772623779407519022227739367716497704351595012600727550954600891703629480555535493528449890764344571169617317290812789268973116618576201998123986223521725470877892260916108979144568881953111629868336542875967876692601896027750415907917395419285564916538119141661676768683587178124437904789397408084511707231007578163234012467027577502787083502003095097523451214525462773970670356670548848946777373369705773015724533828330793833882140437914626516923817940188949005053765209704589302235487803648663540736738985205694278324501384989570846967245560447800952929457525359125591818739983320470952387286814530789416418004880935552678183186303871747761302883465185653566464907271438278257846832275390625

/-- Source nodes, part 0. -/
def src57_0 : List ℕ :=
  [5, 7, 11, 71, 211, 2221, 1361, 292661, 271241, 17950001, 11831, 58044391, 191, 1021, 3724261, 421, 1871, 13001, 332441, 181, 228729421, 17981, 32491, 60661, 19622651, 3001, 97241, 10321, 613680341, 34031, 210875011, 61151, 274871, 20088011, 164881, 1478611, 101, 350411, 346331, 745631, 2131081, 2722199861, 2724573361, 6421, 520392931, 1381, 47791, 16240811, 5351, 9851, 187951, 142120211, 6971, 149111, 549071, 19976441, 13405541, 1091, 401, 1931, 815261, 2314061, 18541, 22274201, 2621, 26141, 34301, 431, 86680961, 1929249901, 2411, 82231, 1372961, 3911, 51431, 5514451, 1231, 382861, 50209751, 797201, 810991241, 631, 82543061, 102451, 8378281, 811771, 510101, 2531, 20390861, 3761, 990211, 1417631, 74551, 3491, 131663471, 22124771, 157061, 78191, 2522441, 11402011, 473861, 298021, 1721, 265471, 751, 9189941, 1337701, 126631, 1616711, 281, 55272601, 37394041, 1601, 212841901, 146234371, 707071, 148899791, 16637371, 468271, 43411]

/-- Source nodes, part 1. -/
def src57_1 : List ℕ :=
  [44501, 46061, 125731, 109661, 119611, 35731, 414614141, 271, 148961, 49626701, 36451, 16292501, 2827381, 24851, 3541051, 288261341, 6571, 1531, 96911, 464351, 385741, 131, 3041, 4313591, 470881, 1571, 284741, 26712541, 713040791, 10135501, 5294671, 3334879201, 152211901, 1591242871, 1607201, 881, 973001, 6481, 246941, 5231, 118861, 3548401, 167771, 1135261, 168358511, 174931, 17791, 150961, 86011, 19121, 2311, 1151, 28151, 4651, 146521, 12601, 70321, 96821, 26613511, 7901, 12011, 29603771, 76261, 10211, 303571, 1734721, 127373801, 550531, 10631, 1427561, 1618996811, 4261, 105191791, 674737621, 147811, 6738091, 9065531, 13609121, 2671, 73181, 8919431, 9811, 1901, 3691, 33101561, 4451, 2716541, 121001, 37950361, 1291, 28631, 571, 126500041, 19081, 12281, 26951, 4051, 135701, 43651, 821, 45305551, 178091, 102701, 203112691, 18731, 446316151, 72931, 971, 9011, 1789091, 150352561, 163861, 598317611, 9687641, 4443631, 281531, 399851, 258031, 1166141, 153911]

/-- Source nodes, part 2. -/
def src57_2 : List ℕ :=
  [5532551, 8821, 6701, 426301, 7121, 979291, 30931, 7541, 622077551, 15511, 8941, 34668391, 24181, 580901, 280931731, 651657031, 1145371, 41011, 42841, 8011, 1829424241, 18583531, 334521521, 121081, 2851, 12280841, 9341851, 131371, 24781, 63541, 29881, 9536591, 4482721, 1811, 32801, 19301, 198179341, 1451371, 470711, 51239341, 5596561, 43945861, 5531, 100741, 17021, 20411, 34017211, 4811311, 17321, 753736541, 16061, 1039741531, 7561, 12947101, 21191, 1471, 14878601, 82031, 35595181, 517721, 1052021381, 691, 14591, 8036261, 68053211, 33461, 15331, 14152441, 15392471, 39802921, 77261, 89891, 1226341, 87146351, 6121, 16533311, 254491, 46861, 3668251, 20603701, 2473613371, 17771321, 26731, 173880281, 17911, 19281151, 264078811, 74872741, 387313141, 164831, 30391, 4661551, 68581, 29761, 29411, 15451, 37951, 14221, 55431421, 75161, 275941, 13361021, 74381, 18701, 104891, 28647011, 74338681, 1113221, 293640301, 189565231, 6999611, 49031, 2910751, 55661, 320521, 4849651, 2920031, 25301]

/-- Nodes, part 0. -/
def nd57_0 : List ℕ :=
  [5, 7, 11, 71, 211, 2221, 1361, 292661, 271241, 17950001, 11831, 58044391, 191, 1021, 3724261, 421, 1871, 13001, 332441, 181, 228729421, 17981, 32491, 60661, 19622651, 3001, 97241, 10321, 613680341, 34031, 210875011, 61151, 274871, 20088011, 164881, 1478611, 101, 350411, 346331, 745631, 2131081, 2722199861, 2724573361, 6421, 520392931, 1381, 47791, 16240811, 5351, 9851, 187951, 142120211, 6971, 149111, 549071, 19976441, 13405541, 1091, 401, 1931, 815261, 2314061, 18541, 22274201, 2621, 26141, 34301, 431, 86680961, 1929249901, 2411, 82231, 1372961, 3911, 51431, 5514451, 1231, 382861, 50209751, 797201, 810991241, 631, 82543061, 102451, 8378281, 811771, 510101, 2531, 20390861, 3761, 990211, 1417631, 74551, 3491, 131663471, 22124771, 157061, 78191, 2522441, 11402011, 473861, 298021, 1721, 265471, 751, 9189941, 1337701, 126631, 1616711, 281, 55272601, 37394041, 1601, 212841901, 146234371, 707071, 148899791, 16637371, 468271, 43411]

/-- Nodes, part 1. -/
def nd57_1 : List ℕ :=
  [44501, 46061, 125731, 109661, 119611, 35731, 414614141, 271, 148961, 49626701, 36451, 16292501, 2827381, 24851, 3541051, 288261341, 6571, 1531, 96911, 464351, 385741, 131, 3041, 4313591, 470881, 1571, 284741, 26712541, 713040791, 10135501, 5294671, 3334879201, 152211901, 1591242871, 1607201, 881, 973001, 6481, 246941, 5231, 118861, 3548401, 167771, 1135261, 168358511, 174931, 17791, 150961, 86011, 19121, 2311, 1151, 28151, 4651, 146521, 12601, 70321, 96821, 26613511, 7901, 12011, 29603771, 76261, 10211, 303571, 1734721, 127373801, 550531, 10631, 1427561, 1618996811, 4261, 105191791, 674737621, 147811, 6738091, 9065531, 13609121, 2671, 73181, 8919431, 9811, 1901, 3691, 33101561, 4451, 2716541, 121001, 37950361, 1291, 28631, 571, 126500041, 19081, 12281, 26951, 4051, 135701, 43651, 821, 45305551, 178091, 102701, 203112691, 18731, 446316151, 72931, 971, 9011, 1789091, 150352561, 163861, 598317611, 9687641, 4443631, 281531, 399851, 258031, 1166141, 153911]

/-- Nodes, part 2. -/
def nd57_2 : List ℕ :=
  [5532551, 8821, 6701, 426301, 7121, 979291, 30931, 7541, 622077551, 15511, 8941, 34668391, 24181, 580901, 280931731, 651657031, 1145371, 41011, 42841, 8011, 1829424241, 18583531, 334521521, 121081, 2851, 12280841, 9341851, 131371, 24781, 63541, 29881, 9536591, 4482721, 1811, 32801, 19301, 198179341, 1451371, 470711, 51239341, 5596561, 43945861, 5531, 100741, 17021, 20411, 34017211, 4811311, 17321, 753736541, 16061, 1039741531, 7561, 12947101, 21191, 1471, 14878601, 82031, 35595181, 517721, 1052021381, 691, 14591, 8036261, 68053211, 33461, 15331, 14152441, 15392471, 39802921, 77261, 89891, 1226341, 87146351, 6121, 16533311, 254491, 46861, 3668251, 20603701, 2473613371, 17771321, 26731, 173880281, 17911, 19281151, 264078811, 74872741, 387313141, 164831, 30391, 4661551, 68581, 29761, 29411, 15451, 37951, 14221, 55431421, 75161, 275941, 13361021, 74381, 18701, 104891, 28647011, 74338681, 1113221, 293640301, 189565231, 6999611, 49031, 2910751, 55661, 320521, 4849651, 2920031, 25301, 31, 41]

/-- Nodes, part 3. -/
def nd57_3 : List ℕ :=
  [61, 151, 241, 251, 311, 331, 461, 491, 521, 541, 601, 641, 661, 701, 761, 811, 911, 941, 991, 1031, 1051, 1061, 1171, 1201, 1301, 1321, 1451, 1481, 1511, 1801, 1831, 1861, 1951, 2011, 2081, 2131, 2161, 2251, 2351, 2371, 2381, 2441, 2521, 2551, 2591, 2711, 2741, 2801, 2971, 3011, 3221, 3301, 3371, 3391, 3511, 3571, 3581, 3631]

/-- Pratt certificates for the large nodes of the `d = 5` table. -/
def pc57 : List (ℕ × ℕ × List ℕ) :=
  [(17950001, 3, [2, 2, 2, 2, 5, 5, 5, 5, 5, 359]),
   (23311, 3, [2, 3, 3, 5, 7, 37]),
   (58044391, 3, [2, 3, 5, 83, 23311]),
   (2069, 2, [2, 2, 11, 47]),
   (62071, 7, [2, 3, 5, 2069]),
   (3724261, 6, [2, 2, 3, 5, 62071]),
   (228729421, 2, [2, 2, 3, 3, 3, 3, 5, 271, 521]),
   (19622651, 2, [2, 5, 5, 601, 653]),
   (613680341, 2, [2, 2, 5, 7, 13, 31, 73, 149]),
   (40867, 2, [2, 3, 7, 7, 139]),
   (163469, 2, [2, 2, 40867]),
   (210875011, 10, [2, 3, 5, 43, 163469]),
   (20088011, 6, [2, 5, 29, 113, 613]),
   (2347, 3, [2, 3, 17, 23]),
   (1478611, 2, [2, 3, 3, 5, 7, 2347]),
   (2131081, 11, [2, 2, 2, 3, 5, 7, 43, 59]),
   (2741, 2, [2, 2, 5, 137]),
   (5483, 2, [2, 2741]),
   (136109993, 3, [2, 2, 2, 29, 107, 5483]),
   (2722199861, 2, [2, 2, 5, 136109993]),
   (1217, 3, [2, 2, 2, 2, 2, 2, 19]),
   (53549, 2, [2, 2, 11, 1217]),
   (11352389, 2, [2, 2, 53, 53549]),
   (2724573361, 19, [2, 2, 2, 2, 3, 5, 11352389]),
   (2477, 2, [2, 2, 619]),
   (520392931, 2, [2, 3, 5, 47, 149, 2477]),
   (1624081, 17, [2, 2, 2, 2, 3, 5, 67, 101]),
   (16240811, 2, [2, 5, 1624081]),
   (29983, 5, [2, 3, 19, 263]),
   (179899, 2, [2, 3, 29983]),
   (142120211, 2, [2, 5, 79, 179899]),
   (19976441, 3, [2, 2, 2, 5, 11, 83, 547]),
   (13405541, 2, [2, 2, 5, 29, 29, 797]),
   (1033, 5, [2, 2, 2, 3, 43]),
   (16529, 3, [2, 2, 2, 2, 1033]),
   (2314061, 3, [2, 2, 5, 7, 16529]),
   (22274201, 3, [2, 2, 2, 5, 5, 13, 13, 659]),
   (86680961, 7, [2, 2, 2, 2, 2, 2, 2, 5, 17, 31, 257]),
   (79393, 5, [2, 2, 2, 2, 2, 3, 827]),
   (1929249901, 2, [2, 2, 3, 3, 3, 3, 3, 5, 5, 79393]),
   (8581, 6, [2, 2, 3, 5, 11, 13]),
   (1372961, 3, [2, 2, 2, 2, 2, 5, 8581]),
   (5514451, 2, [2, 3, 5, 5, 97, 379]),
   (1877, 2, [2, 2, 7, 67]),
   (50209751, 13, [2, 5, 5, 5, 107, 1877]),
   (45767, 5, [2, 7, 7, 467]),
   (810991241, 6, [2, 2, 2, 5, 443, 45767]),
   (3307, 2, [2, 3, 19, 29]),
   (257947, 2, [2, 3, 13, 3307]),
   (4127153, 3, [2, 2, 2, 2, 257947]),
   (82543061, 2, [2, 2, 5, 4127153]),
   (8378281, 26, [2, 2, 2, 3, 3, 5, 17, 37, 37]),
   (20807, 5, [2, 101, 103]),
   (20390861, 11, [2, 2, 5, 7, 7, 20807]),
   (1417631, 13, [2, 5, 17, 31, 269]),
   (1889, 3, [2, 2, 2, 2, 2, 59]),
   (774491, 2, [2, 5, 41, 1889]),
   (131663471, 7, [2, 5, 17, 774491]),
   (1013, 3, [2, 2, 11, 23]),
   (26339, 2, [2, 13, 1013]),
   (2212477, 2, [2, 2, 3, 7, 26339]),
   (22124771, 2, [2, 5, 2212477]),
   (3319, 6, [2, 3, 7, 79]),
   (2522441, 3, [2, 2, 2, 5, 19, 3319]),
   (11402011, 3, [2, 3, 3, 5, 151, 839]),
   (1409, 3, [2, 2, 2, 2, 2, 2, 2, 11]),
   (2819, 2, [2, 1409]),
   (9189941, 3, [2, 2, 5, 163, 2819]),
   (1337701, 2, [2, 2, 3, 5, 5, 7, 7, 7, 13]),
   (1616711, 13, [2, 5, 19, 67, 127]),
   (1181, 7, [2, 2, 5, 59]),
   (30707, 2, [2, 13, 1181]),
   (55272601, 7, [2, 2, 2, 3, 3, 5, 5, 30707]),
   (4651, 3, [2, 3, 5, 5, 31]),
   (37394041, 21, [2, 2, 2, 3, 5, 67, 4651]),
   (1367, 5, [2, 683]),
   (212841901, 2, [2, 2, 3, 3, 5, 5, 173, 1367]),
   (1009, 11, [2, 2, 2, 2, 3, 3, 7]),
   (4831, 3, [2, 3, 5, 7, 23]),
   (146234371, 3, [2, 3, 5, 1009, 4831]),
   (2161, 23, [2, 2, 2, 2, 3, 3, 3, 5]),
   (21611, 2, [2, 5, 2161]),
   (148899791, 31, [2, 5, 13, 53, 21611]),
   (16637371, 3, [2, 3, 5, 661, 839]),
   (4909, 6, [2, 2, 3, 409]),
   (414614141, 2, [2, 2, 5, 41, 103, 4909]),
   (1931, 2, [2, 5, 193]),
   (49626701, 2, [2, 2, 5, 5, 257, 1931]),
   (16292501, 2, [2, 2, 5, 5, 5, 5, 7, 7, 7, 19]),
   (23561, 3, [2, 2, 2, 5, 19, 31]),
   (47123, 2, [2, 23561]),
   (2827381, 10, [2, 2, 3, 5, 47123]),
   (3541051, 2, [2, 3, 3, 3, 5, 5, 43, 61]),
   (306661, 2, [2, 2, 3, 5, 19, 269]),
   (288261341, 2, [2, 2, 5, 47, 306661]),
   (4447, 3, [2, 3, 3, 13, 19]),
   (4313591, 17, [2, 5, 97, 4447]),
   (74201, 6, [2, 2, 2, 5, 5, 7, 53]),
   (148403, 2, [2, 74201]),
   (26712541, 6, [2, 2, 3, 3, 5, 148403]),
   (926027, 2, [2, 23, 41, 491]),
   (713040791, 7, [2, 5, 7, 11, 926027]),
   (10135501, 2, [2, 2, 3, 5, 5, 5, 29, 233]),
   (1697, 3, [2, 2, 2, 2, 2, 53]),
   (176489, 3, [2, 2, 2, 13, 1697]),
   (5294671, 3, [2, 3, 5, 176489]),
   (3187, 2, [2, 3, 3, 3, 59]),
   (1389533, 2, [2, 2, 109, 3187]),
   (3334879201, 7, [2, 2, 2, 2, 2, 3, 5, 5, 1389533]),
   (1621, 2, [2, 2, 3, 3, 3, 3, 5]),
   (152211901, 6, [2, 2, 3, 5, 5, 313, 1621]),
   (19993, 10, [2, 2, 2, 3, 7, 7, 17]),
   (1591242871, 3, [2, 3, 5, 7, 379, 19993]),
   (1607201, 3, [2, 2, 2, 2, 2, 5, 5, 7, 7, 41]),
   (2957, 2, [2, 2, 739]),
   (3548401, 7, [2, 2, 2, 2, 3, 5, 5, 2957]),
   (1135261, 6, [2, 2, 3, 3, 5, 7, 17, 53]),
   (1987, 2, [2, 3, 331]),
   (168358511, 17, [2, 5, 37, 229, 1987]),
   (26613511, 6, [2, 3, 5, 7, 11, 41, 281]),
   (422911, 3, [2, 3, 3, 5, 37, 127]),
   (29603771, 7, [2, 5, 7, 422911]),
   (1734721, 11, [2, 2, 2, 2, 2, 2, 3, 5, 13, 139]),
   (21961, 17, [2, 2, 2, 3, 3, 5, 61]),
   (127373801, 3, [2, 2, 2, 5, 5, 29, 21961]),
   (1427561, 3, [2, 2, 2, 5, 89, 401]),
   (11243, 5, [2, 7, 11, 73]),
   (337291, 10, [2, 3, 5, 11243]),
   (161899681, 14, [2, 2, 2, 2, 2, 3, 5, 337291]),
   (1618996811, 10, [2, 5, 161899681]),
   (105191791, 3, [2, 3, 5, 11, 19, 19, 883]),
   (11245627, 2, [2, 3, 3, 7, 149, 599]),
   (674737621, 2, [2, 2, 3, 5, 11245627]),
   (224603, 2, [2, 7, 61, 263]),
   (6738091, 2, [2, 3, 5, 224603]),
   (8317, 6, [2, 2, 3, 3, 3, 7, 11]),
   (9065531, 2, [2, 5, 109, 8317]),
   (13609121, 3, [2, 2, 2, 2, 2, 5, 7, 29, 419]),
   (2287, 19, [2, 3, 3, 127]),
   (68611, 2, [2, 3, 5, 2287]),
   (8919431, 11, [2, 5, 13, 68611]),
   (1289, 6, [2, 2, 2, 7, 23]),
   (827539, 2, [2, 3, 107, 1289]),
   (33101561, 3, [2, 2, 2, 5, 827539]),
   (3671, 13, [2, 5, 367]),
   (2716541, 2, [2, 2, 5, 37, 3671]),
   (45179, 6, [2, 7, 7, 461]),
   (37950361, 13, [2, 2, 2, 3, 5, 7, 45179]),
   (1187, 2, [2, 593]),
   (9497, 3, [2, 2, 2, 1187]),
   (126500041, 11, [2, 2, 2, 3, 3, 5, 37, 9497]),
   (1213, 2, [2, 2, 3, 101]),
   (45305551, 6, [2, 3, 3, 5, 5, 83, 1213]),
   (615493, 2, [2, 2, 3, 3, 3, 41, 139]),
   (203112691, 3, [2, 3, 5, 11, 615493]),
   (18481, 13, [2, 2, 2, 2, 3, 5, 7, 11]),
   (446316151, 6, [2, 3, 5, 5, 7, 23, 18481]),
   (178909, 7, [2, 2, 3, 17, 877]),
   (1789091, 2, [2, 5, 178909]),
   (150352561, 19, [2, 2, 2, 2, 3, 3, 5, 367, 569]),
   (41521, 22, [2, 2, 2, 2, 3, 5, 173]),
   (598317611, 10, [2, 5, 11, 131, 41521]),
   (5153, 5, [2, 2, 2, 2, 2, 7, 23]),
   (9687641, 6, [2, 2, 2, 5, 47, 5153]),
   (8713, 5, [2, 2, 2, 3, 3, 11, 11]),
   (4443631, 3, [2, 3, 5, 17, 8713]),
   (1166141, 2, [2, 2, 5, 199, 293]),
   (2213, 2, [2, 2, 7, 79]),
   (110651, 2, [2, 5, 5, 2213]),
   (5532551, 13, [2, 5, 5, 110651]),
   (622077551, 7, [2, 5, 5, 23, 23, 29, 811]),
   (1155613, 2, [2, 2, 3, 23, 53, 79]),
   (34668391, 7, [2, 3, 5, 1155613]),
   (44381, 2, [2, 2, 5, 7, 317]),
   (280931731, 2, [2, 3, 5, 211, 44381]),
   (217219, 3, [2, 3, 41, 883]),
   (21721901, 2, [2, 2, 5, 5, 217219]),
   (651657031, 6, [2, 3, 5, 21721901]),
   (1145371, 2, [2, 3, 5, 73, 523]),
   (7723, 3, [2, 3, 3, 3, 11, 13]),
   (1829424241, 11, [2, 2, 2, 2, 3, 3, 5, 7, 47, 7723]),
   (1229, 2, [2, 2, 307]),
   (22123, 2, [2, 3, 3, 1229]),
   (88493, 2, [2, 2, 22123]),
   (18583531, 34, [2, 3, 5, 7, 88493]),
   (1811, 6, [2, 5, 181]),
   (3623, 5, [2, 1811]),
   (7247, 5, [2, 3623]),
   (334521521, 3, [2, 2, 2, 2, 5, 577, 7247]),
   (12280841, 3, [2, 2, 2, 5, 11, 13, 19, 113]),
   (9341851, 19, [2, 3, 5, 5, 7, 7, 31, 41]),
   (11353, 7, [2, 2, 2, 3, 11, 43]),
   (136237, 2, [2, 2, 3, 11353]),
   (9536591, 7, [2, 5, 7, 136237]),
   (4482721, 14, [2, 2, 2, 2, 2, 3, 3, 5, 11, 283]),
   (11273, 3, [2, 2, 2, 1409]),
   (198179341, 2, [2, 2, 3, 5, 293, 11273]),
   (1451371, 2, [2, 3, 5, 101, 479]),
   (51239341, 2, [2, 2, 3, 3, 5, 41, 53, 131]),
   (2591, 7, [2, 5, 7, 37]),
   (5596561, 7, [2, 2, 2, 2, 3, 3, 3, 5, 2591]),
   (2753, 3, [2, 2, 2, 2, 2, 2, 43]),
   (5507, 2, [2, 2753]),
   (43945861, 2, [2, 2, 3, 5, 7, 19, 5507]),
   (34017211, 2, [2, 3, 3, 5, 599, 631]),
   (1091, 2, [2, 5, 109]),
   (4811311, 13, [2, 3, 3, 5, 7, 7, 1091]),
   (133169, 3, [2, 2, 2, 2, 7, 29, 41]),
   (753736541, 2, [2, 2, 5, 283, 133169]),
   (1907, 2, [2, 953]),
   (148747, 2, [2, 3, 13, 1907]),
   (1039741531, 3, [2, 3, 5, 233, 148747]),
   (12947101, 2, [2, 2, 3, 5, 5, 103, 419]),
   (6763, 2, [2, 3, 7, 7, 23]),
   (14878601, 3, [2, 2, 2, 5, 5, 11, 6763]),
   (2273, 3, [2, 2, 2, 2, 2, 71]),
   (35595181, 6, [2, 2, 3, 3, 3, 5, 29, 2273]),
   (43151, 11, [2, 5, 5, 863]),
   (1052021381, 13, [2, 2, 5, 23, 53, 43151]),
   (401813, 2, [2, 2, 17, 19, 311]),
   (8036261, 2, [2, 2, 5, 401813]),
   (4549, 6, [2, 2, 3, 379]),
   (400313, 3, [2, 2, 2, 11, 4549]),
   (68053211, 6, [2, 5, 17, 400313]),
   (117937, 5, [2, 2, 2, 2, 3, 3, 3, 3, 7, 13]),
   (14152441, 22, [2, 2, 2, 3, 5, 117937]),
   (81013, 6, [2, 2, 3, 43, 157]),
   (15392471, 31, [2, 5, 19, 81013]),
   (331691, 2, [2, 5, 41, 809]),
   (39802921, 26, [2, 2, 2, 3, 5, 331691]),
   (1226341, 2, [2, 2, 3, 3, 3, 3, 5, 757]),
   (91733, 2, [2, 2, 17, 19, 71]),
   (87146351, 13, [2, 5, 5, 19, 91733]),
   (7873, 5, [2, 2, 2, 2, 2, 2, 3, 41]),
   (1653331, 2, [2, 3, 5, 7, 7873]),
   (16533311, 7, [2, 5, 1653331]),
   (3668251, 3, [2, 3, 5, 5, 5, 67, 73]),
   (20603701, 10, [2, 2, 3, 3, 3, 5, 5, 13, 587]),
   (2671, 7, [2, 3, 5, 89]),
   (9161531, 6, [2, 5, 7, 7, 7, 2671]),
   (2473613371, 3, [2, 3, 3, 3, 5, 9161531]),
   (1511, 11, [2, 5, 151]),
   (9067, 3, [2, 3, 1511]),
   (17771321, 11, [2, 2, 2, 5, 7, 7, 9067]),
   (11717, 2, [2, 2, 29, 101]),
   (173880281, 3, [2, 2, 2, 5, 7, 53, 11717]),
   (6121, 7, [2, 2, 2, 3, 3, 5, 17]),
   (19281151, 3, [2, 3, 3, 5, 5, 7, 6121]),
   (3323, 2, [2, 11, 151]),
   (264078811, 2, [2, 3, 3, 5, 883, 3323]),
   (1193, 3, [2, 2, 2, 149]),
   (1247879, 17, [2, 523, 1193]),
   (74872741, 6, [2, 2, 3, 5, 1247879]),
   (6455219, 2, [2, 7, 11, 167, 251]),
   (387313141, 2, [2, 2, 3, 5, 6455219]),
   (1151, 17, [2, 5, 5, 23]),
   (4661551, 6, [2, 3, 3, 3, 3, 5, 5, 1151]),
   (83987, 2, [2, 7, 7, 857]),
   (55431421, 6, [2, 2, 3, 5, 11, 83987]),
   (668051, 2, [2, 5, 5, 31, 431]),
   (13361021, 2, [2, 2, 5, 668051]),
   (4219, 2, [2, 3, 19, 37]),
   (28647011, 2, [2, 5, 7, 97, 4219]),
   (47653, 13, [2, 2, 3, 11, 19, 19]),
   (74338681, 11, [2, 2, 2, 3, 5, 13, 47653]),
   (55661, 2, [2, 2, 5, 11, 11, 23]),
   (1113221, 2, [2, 2, 5, 55661]),
   (293640301, 7, [2, 2, 3, 3, 5, 5, 431, 757]),
   (107099, 2, [2, 53549]),
   (189565231, 3, [2, 3, 5, 59, 107099]),
   (699961, 7, [2, 2, 2, 3, 5, 19, 307]),
   (6999611, 6, [2, 5, 699961]),
   (3881, 13, [2, 2, 2, 5, 97]),
   (2910751, 3, [2, 3, 5, 5, 5, 3881]),
   (4849651, 3, [2, 3, 3, 5, 5, 13, 829]),
   (2729, 3, [2, 2, 2, 11, 31]),
   (2920031, 7, [2, 5, 107, 2729])]
/-- Rows with their sources, part 0. -/
def zp57_0 : List (ℕ × List ℕ) := ((nodes57.zip rows57).drop 0).take 100

/-- Rows with their sources, part 1. -/
def zp57_1 : List (ℕ × List ℕ) := ((nodes57.zip rows57).drop 100).take 100

/-- Rows with their sources, part 2. -/
def zp57_2 : List (ℕ × List ℕ) := ((nodes57.zip rows57).drop 200).take 100

/-- Rows with their sources, part 3. -/
def zp57_3 : List (ℕ × List ℕ) := ((nodes57.zip rows57).drop 300).take 100

/-- The rows with their sources in parts. -/
theorem zp57_eq : nodes57.zip rows57 =
    [zp57_0, zp57_1, zp57_2, zp57_3].flatten := by
  decide +kernel

/-- The divisibility checks of the rows, part 0. -/
theorem rows57_0 : zp57_0.all (rowChk 5 nodes57) = true := by decide +kernel

/-- The divisibility checks of the rows, part 1. -/
theorem rows57_1 : zp57_1.all (rowChk 5 nodes57) = true := by decide +kernel

/-- The divisibility checks of the rows, part 2. -/
theorem rows57_2 : zp57_2.all (rowChk 5 nodes57) = true := by decide +kernel

/-- The divisibility checks of the rows, part 3. -/
theorem rows57_3 : zp57_3.all (rowChk 5 nodes57) = true := by decide +kernel

/-- The divisibility checks of all rows. -/
theorem hrows57 : ∀ e ∈ nodes57.zip rows57, rowChk 5 nodes57 e = true :=
  all_of_parts _ zp57_eq (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    exacts [rows57_0, rows57_1, rows57_2, rows57_3])

/-- No node is `2`. -/
theorem nodes57_ne2 : ∀ t ∈ nodes57, t ≠ 2 := by
  have : nodes57.all (· != 2) = true := by decide +kernel
  intro t ht
  simpa using List.all_eq_true.mp this t ht

/-- The source nodes in parts. -/
theorem src57_eq : nodes57.take rows57.length =
    [src57_0, src57_1, src57_2].flatten := by
  decide +kernel

/-- The nodes in parts. -/
theorem nd57_eq : nodes57 =
    [nd57_0, nd57_1, nd57_2, nd57_3].flatten := by
  decide +kernel

/-- The blocked candidates. -/
def cand57 (b : ℕ) : Bool := b % 12 == 1

/-- Reach checks for the blocked source nodes, part 0. -/
theorem reach57_0 :
    src57_0.all (fun b => !cand57 b || reach nodes57 rows57 2 tm57 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 1. -/
theorem reach57_1 :
    src57_1.all (fun b => !cand57 b || reach nodes57 rows57 2 tm57 3 b) = true := by
  decide +kernel

/-- Reach checks for the blocked source nodes, part 2. -/
theorem reach57_2 :
    src57_2.all (fun b => !cand57 b || reach nodes57 rows57 2 tm57 3 b) = true := by
  decide +kernel

/-- Reach check with no source blocked. -/
theorem reach57_none : reach nodes57 rows57 2 tm57 3 0 = true := by decide +kernel

/-- Every blocked source node passes the reach check. -/
theorem hcand57 : ∀ b ∈ nodes57.take rows57.length, cand57 b = true →
    reach nodes57 rows57 2 tm57 3 b = true := by
  intro b hb hcb
  have := all_of_parts (f := fun b => !cand57 b || reach nodes57 rows57 2 tm57 3 b)
    _ src57_eq (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    exacts [reach57_0, reach57_1, reach57_2]) b hb
  simpa [hcb] using this

/-- The Pratt certificates of the `d = 5` table are accepted. -/
theorem pc57_check : Pratt.check pc57 = true := by decide +kernel

/-- The nodes of part 0 are certified. -/
theorem nd57_0_isPS : nd57_0.all (isPS pc57) = true := by decide +kernel

/-- The nodes of part 1 are certified. -/
theorem nd57_1_isPS : nd57_1.all (isPS pc57) = true := by decide +kernel

/-- The nodes of part 2 are certified. -/
theorem nd57_2_isPS : nd57_2.all (isPS pc57) = true := by decide +kernel

/-- The nodes of part 3 are certified. -/
theorem nd57_3_isPS : nd57_3.all (isPS pc57) = true := by decide +kernel

/-- The nodes of the `d = 5` table are prime. -/
theorem nodes57_prime : ∀ t ∈ nodes57, t.Prime := fun t ht =>
  isPS_sound pc57_check (all_of_parts _ nd57_eq (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    exacts [nd57_0_isPS, nd57_1_isPS, nd57_2_isPS, nd57_3_isPS]) t ht)

/-- The target primes are the nodes selected by the target mask. -/
theorem vals57_sel : CommonChain.sel 0 tm57 0 nodes57 = vals57 := by decide +kernel

/-- The target primes are distinct. -/
theorem vals57_nodup : vals57.Nodup :=
  (nodup_of_ndM (M := 0) (by decide +kernel)).1

/-- The two full products over the target primes. -/
theorem PG57 : pPow (expL vals57 0) = P57 ∧ pSig (expL vals57 0) = G57 := by
  decide +kernel

/-- Abundance: the target primes with fourth powers, and with any one of them `≡ 1 (mod 12)` to
the first power. -/
theorem ab57 : abOK2 vals57 (fun b : ℕ => b % 12 == 1) P57 G57 = true := by decide +kernel

end FamInst

open FamInst in
/-- In the common `5` family, `7 ∤ N` (known; Evans and Pearlman 2007). Let `N` be an odd
perfect number with special prime `q` and `5 ∣ v_p(N) + 1` for every ordinary prime `p`. Then
`5 ∣ N` and `q ≡ 1 (mod 12)`; if `7 ∣ N`, the forcing table from the seeds `5, 7` reaches all
target primes whichever source node `≡ 1 (mod 12)` is special, and they give an abundant
divisor. -/
theorem not_seven_dvd_of_common_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1) : ¬ 7 ∣ N := by
  intro h7N
  have h5N := (five_dvd_and_ne_special_of_common h hq hodd hexp).1
  have hq12 := special_mod_twelve_of_common_five h hq hodd hexp
  have hcq : cand57 q = true := by simp [cand57, hq12]
  have hcq' : (fun b : ℕ => b % 12 == 1) q = true := by simp [hq12]
  have hseed : ∀ t ∈ nodes57.take 2, t ∣ N := by
    intro t ht
    have : nodes57.take 2 = [5, 7] := by decide +kernel
    rw [this] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h5N
    · exact h7N
  exact false_of_reach h hexp le_rfl hcq hcq' nodes57_prime nodes57_ne2 hseed
    (by decide +kernel) hrows57 hcand57 reach57_none vals57_sel vals57_nodup PG57 ab57

end OddPerfect

#print axioms OddPerfect.FamInst.tdiv_sound
#print axioms OddPerfect.FamInst.sqPrime_sound
#print axioms OddPerfect.FamInst.isPS_sound
#print axioms OddPerfect.FamInst.drop_facts
#print axioms OddPerfect.FamInst.fpass_good
#print axioms OddPerfect.FamInst.fiter_good
#print axioms OddPerfect.FamInst.all_of_parts
#print axioms OddPerfect.FamInst.nodup_of_ndM
#print axioms OddPerfect.FamInst.expL_cons
#print axioms OddPerfect.FamInst.expL_eq_of_forall_ne
#print axioms OddPerfect.FamInst.pPow_pSig_split
#print axioms OddPerfect.dvd_of_reach
#print axioms OddPerfect.FamInst.abOK2_sound
#print axioms OddPerfect.false_of_reach
#print axioms OddPerfect.FamInst.zp57_eq
#print axioms OddPerfect.FamInst.rows57_0
#print axioms OddPerfect.FamInst.rows57_1
#print axioms OddPerfect.FamInst.rows57_2
#print axioms OddPerfect.FamInst.rows57_3
#print axioms OddPerfect.FamInst.hrows57
#print axioms OddPerfect.FamInst.nodes57_ne2
#print axioms OddPerfect.FamInst.src57_eq
#print axioms OddPerfect.FamInst.nd57_eq
#print axioms OddPerfect.FamInst.reach57_0
#print axioms OddPerfect.FamInst.reach57_1
#print axioms OddPerfect.FamInst.reach57_2
#print axioms OddPerfect.FamInst.reach57_none
#print axioms OddPerfect.FamInst.hcand57
#print axioms OddPerfect.FamInst.pc57_check
#print axioms OddPerfect.FamInst.nd57_0_isPS
#print axioms OddPerfect.FamInst.nd57_1_isPS
#print axioms OddPerfect.FamInst.nd57_2_isPS
#print axioms OddPerfect.FamInst.nd57_3_isPS
#print axioms OddPerfect.FamInst.nodes57_prime
#print axioms OddPerfect.FamInst.vals57_sel
#print axioms OddPerfect.FamInst.vals57_nodup
#print axioms OddPerfect.FamInst.PG57
#print axioms OddPerfect.FamInst.ab57
#print axioms OddPerfect.not_seven_dvd_of_common_five
