import OddPerfect.ReciprocalSumThree

/-!
# The reciprocal sum of the prime factors exceeds 0.5960631

For an odd perfect number `N` we prove `5960631/10000000 < ∑_{p ∣ N} 1/p`, together with the four
statements by cases on whether `3` and `5` divide `N`:

* `3 ∣ N` and `5 ∣ N`: `0.5960631 < ∑ 1/p`;
* `3 ∣ N` and `5 ∤ N`: `0.604706 < ∑ 1/p`;
* `3 ∤ N` and `5 ∣ N`: `0.647648 < ∑ 1/p`;
* `3 ∤ N` and `5 ∤ N`: `0.667363 < ∑ 1/p`.

Comparison with the literature. Cohen (1980) gives the lower bound `0.596063` for the case
`15 ∣ N` and as the overall minimum; the comparison of the constant `0.5960631` proved here with
the literature was not verified. The constants of the three other cases were not compared with
the published ones either (the comparison with the literature was not verified).

The method. Let `H = {3, 5, ..., 43}` be the thirteen smallest odd primes, `T` the set of prime
factors of `N` in `H` and `R` the other prime factors (all at least `47`).

* With `q` the special prime of Euler, the product over `T` of `1 + 1/q` (at `q`) and
  `1 + 1/p + 1/p^2` (at the other primes) is at most the abundancy `2` of `N`.
* `log 2 < ∑_{p ∣ N} log(p/(p-1))`. On `T` we use the rational upper bounds `u(p)/10^15` of
  `log(p/(p-1))` from the table `fourUTable`. On `R`, if every prime of `R` is at least `m`, then
  `log(p/(p-1)) ≤ (1 + 1/(2(m-2))) / p`, so `∑_R 1/p` is at least
  `(log 2 - ∑_T u(p)/10^15) * 2(m-2)/(2m-3)`. We use `m = 257` when every prime of `R` is at
  least `257`; otherwise `R` contains a prime `p ≤ 255`, so `∑_R 1/p ≥ 1/255`, and also `m = 47`.
* `∑_T 1/p` is at least `∑_T ⌊10^15/p⌋ / 10^15`.

A finite check over all subsets `T` of `H`, all roles of the special prime and the case
restrictions on `3` and `5` shows that every admissible `T` gives the stated bound. The table and
the thresholds were computed outside Lean (generator `scripts/ReciprocalSum/gen_recip4.py`); the
kernel checks again every table entry, the subset check and the cover of the odd primes
below `47`.
-/

open Finset

namespace OddPerfect

/-- The truncated series upper bound for `log(p/(p-1)) = -log(1 - 1/p)`:
`∑_{k=1}^{n} 1/(k p^k) + (1/p)^(n+1)/(1 - 1/p)`. -/
def recipFourLogUp (p n : ℕ) : ℚ :=
  ∑ i ∈ range n, (1 / (p : ℚ)) ^ (i + 1) / ((i : ℚ) + 1) +
    (1 / (p : ℚ)) ^ (n + 1) / (1 - 1 / (p : ℚ))

/-- The upper bounds: for each head prime `p`, a natural number `u` with
`recipFourLogUp p 20 ≤ u / 10 ^ 15`. -/
def fourUTable : List (ℕ × ℕ) :=
  [(3, 405465108244884), (5, 223143551314213), (7, 154150679827259), (11, 95310179804325),
   (13, 80042707673537), (17, 60624621816435), (19, 54067221270276), (23, 44451762570834),
   (29, 35091319811271), (31, 32789822822991), (37, 27398974188115), (41, 24692612590372),
   (43, 23530497410195)]

/-- The thirteen head primes. -/
private def fourHead : List ℕ := fourUTable.map Prod.fst

/-- The table entry of `p`, or `0`. -/
private def fourU (p : ℕ) : ℕ := (fourUTable.lookup p).getD 0

/-- The leaf test for the threshold `t / 10^15`, with `r` the scaled lower bound of `∑_T 1/p` and
`u` the scaled upper bound of `∑_T log(p/(p-1))`. -/
private def fourLeaf (t r u : ℕ) : Bool :=
  decide (t < r) ||
    ((decide (255 * t < 255 * r + 1000000000000000) ||
        decide (91 * t + 90 * u ≤ 91 * r + 90 * 693147180300000)) &&
      decide (511 * t + 510 * u ≤ 511 * r + 510 * 693147180300000))

/-- The subset check. A branch fixes, for each prime of the list, whether it is outside the head
set (not allowed for primes of `req`), an ordinary member, or the special member (allowed once,
only for `p ≡ 1 (mod 4)`); members are not allowed for primes of `exc`. `num` and `den` carry
the product of the factors, `r` and `u` the scaled sums. Each leaf must have product above `2`
or pass `fourLeaf`. -/
private def fourCheck (t : ℕ) (req exc : List ℕ) : List ℕ → ℕ → ℕ → ℕ → ℕ → Bool → Bool
  | [], num, den, r, u, _ => decide (2 * den < num) || fourLeaf t r u
  | p :: l, num, den, r, u, sp =>
      (req.contains p || fourCheck t req exc l num den r u sp) &&
      (exc.contains p ||
        (fourCheck t req exc l (num * (p * p + p + 1)) (den * (p * p))
            (r + 1000000000000000 / p) (u + fourU p) sp &&
          (sp || decide (p % 4 ≠ 1) ||
            fourCheck t req exc l (num * (p + 1)) (den * p)
              (r + 1000000000000000 / p) (u + fourU p) true)))

/-- The factor of `p` in the abundancy bound when `q` is the special prime. -/
private def fourRole (q p : ℕ) : ℚ :=
  if p = q then ((p + 1 : ℕ) : ℚ) / (p : ℚ) else ((p * p + p + 1 : ℕ) : ℚ) / ((p * p : ℕ) : ℚ)

private theorem log_div_sub_one_le_recipFourLogUp {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    Real.log ((p : ℝ) / (p - 1)) ≤ (recipFourLogUp p n : ℝ) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [log_div_sub_one_eq (by linarith)]
  have h := neg_log_one_sub_le (x := 1 / (p : ℝ)) (by positivity)
    (by rw [div_lt_one (by linarith)]; linarith) n
  unfold recipFourLogUp
  push_cast
  exact h

/-- For `3 ≤ m ≤ p`: `log(p/(p-1)) ≤ (2m - 3)/(2(m - 2)) * (1/p)`. -/
private theorem log_div_sub_one_le_mul_inv {p m : ℝ} (hm : 3 ≤ m) (hp : m ≤ p) :
    Real.log (p / (p - 1)) ≤ (2 * m - 3) / (2 * (m - 2)) * (1 / p) := by
  have h := log_div_sub_one_sub_inv_le (p := p) (by linarith)
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have e : (1 / 4 : ℝ) * (1 / (p - 2) - 1 / p) = 1 / (2 * p * (p - 2)) := by
    field_simp
    ring
  have hle : 1 / (2 * p * (p - 2)) ≤ 1 / (2 * (m - 2) * p) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have e2 : (2 * m - 3) / (2 * (m - 2)) * (1 / p) = 1 / p + 1 / (2 * (m - 2) * p) := by
    field_simp
    ring
  rw [e2]
  linarith

private theorem fourCheck_sound (t q : ℕ) (S : Finset ℕ) (req exc : List ℕ) :
    ∀ (l : List ℕ) (num den r u : ℕ) (sp : Bool), fourCheck t req exc l num den r u sp = true →
      l.Nodup → (∀ p ∈ l, 0 < p) → 0 < den →
      (sp = true → ∀ p ∈ l, p ∈ S → p ≠ q) → (q ∈ l → q ∈ S → q % 4 = 1) →
      (∀ p ∈ l, p ∈ req → p ∈ S) → (∀ p ∈ l, p ∈ exc → p ∉ S) →
      (num : ℚ) / den * ((l.filter (· ∈ S)).map (fourRole q)).prod ≤ 2 →
      fourLeaf t (r + ((l.filter (· ∈ S)).map (fun p => 1000000000000000 / p)).sum)
        (u + ((l.filter (· ∈ S)).map fourU).sum) = true := by
  intro l
  induction l with
  | nil =>
    intro num den r u sp hc _ _ hden _ _ _ _ hprod
    simp only [fourCheck, Bool.or_eq_true, decide_eq_true_eq] at hc
    simp only [List.filter_nil, List.map_nil, List.prod_nil, mul_one, List.sum_nil,
      add_zero] at hprod ⊢
    rcases hc with hc | hc
    · exfalso
      have hd : (0 : ℚ) < den := by exact_mod_cast hden
      rw [div_le_iff₀ hd] at hprod
      have : ((2 * den : ℕ) : ℚ) < num := by exact_mod_cast hc
      push_cast at this
      linarith
    · exact hc
  | cons p l ih =>
    intro num den r u sp hc hnd hpos hden hsp hq hreq hexc hprod
    simp only [fourCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      List.contains_iff_mem] at hc
    obtain ⟨h1, h2⟩ := hc
    have hp0 : 0 < p := hpos p List.mem_cons_self
    obtain ⟨hpl, hnd'⟩ := List.nodup_cons.mp hnd
    have hpos' : ∀ x ∈ l, 0 < x := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have hreq' : ∀ x ∈ l, x ∈ req → x ∈ S := fun x hx => hreq x (List.mem_cons_of_mem _ hx)
    have hexc' : ∀ x ∈ l, x ∈ exc → x ∉ S := fun x hx => hexc x (List.mem_cons_of_mem _ hx)
    by_cases hpS : p ∈ S
    · have h2' := h2.resolve_left (fun hm => hexc p List.mem_cons_self hm hpS)
      obtain ⟨h2a, h3⟩ := h2'
      rw [List.filter_cons_of_pos (by simpa using hpS)] at hprod ⊢
      rw [List.map_cons, List.prod_cons] at hprod
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ← add_assoc, ← add_assoc]
      by_cases hpq : p = q
      · subst hpq
        have hsp' : sp = false := by
          cases sp
          · rfl
          · exact absurd rfl (hsp rfl p List.mem_cons_self hpS)
        have h4 := hq List.mem_cons_self hpS
        subst hsp'
        have h3' : fourCheck t req exc l (num * (p + 1)) (den * p) (r + 1000000000000000 / p)
            (u + fourU p) true = true := by
          rcases h3 with (h | h) | h
          · exact absurd h (by simp)
          · exact absurd h4 h
          · exact h
        refine ih _ _ _ _ _ h3' hnd' hpos' (Nat.mul_pos hden hp0)
          (fun _ x hx _ hxq => hpl (hxq ▸ hx)) (fun hx _ => absurd hx hpl) hreq' hexc' ?_
        rw [fourRole, if_pos rfl] at hprod
        refine le_of_eq_of_le ?_ hprod
        simp only [← mul_assoc, div_mul_div_comm, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      · have hrf : fourRole q p = ((p * p + p + 1 : ℕ) : ℚ) / ((p * p : ℕ) : ℚ) := by
          rw [fourRole, if_neg hpq]
        refine ih _ _ _ _ _ h2a hnd' hpos' (Nat.mul_pos hden (Nat.mul_pos hp0 hp0))
          (fun hs x hx hxS => hsp hs x (List.mem_cons_of_mem _ hx) hxS)
          (fun hx hxS => hq (List.mem_cons_of_mem _ hx) hxS) hreq' hexc' ?_
        rw [hrf] at hprod
        refine le_of_eq_of_le ?_ hprod
        simp only [← mul_assoc, div_mul_div_comm, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    · have h1' := h1.resolve_left (fun hm => hpS (hreq p List.mem_cons_self hm))
      rw [List.filter_cons_of_neg (by simpa using hpS)] at hprod ⊢
      exact ih _ _ _ _ _ h1' hnd' hpos' hden
        (fun hs x hx hxS => hsp hs x (List.mem_cons_of_mem _ hx) hxS)
        (fun hx hxS => hq (List.mem_cons_of_mem _ hx) hxS) hreq' hexc' hprod

/-- The abundancy bound on the head: the product of the role factors over distinct prime
factors of `N` is at most `2`. -/
private theorem prod_fourRole_le_two {N : ℕ} (h : OddPerfect N) {q : ℕ}
    (hev : ∀ p : ℕ, p.Prime → p ≠ q → Even (N.factorization p)) {l : List ℕ} (hnd : l.Nodup)
    (hl : ∀ p ∈ l, p ∈ N.primeFactors) : (l.map (fourRole q)).prod ≤ 2 := by
  rw [← List.prod_toFinset _ hnd]
  have hab : abundancy N = 2 := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  have hfac : ∀ p ∈ N.primeFactors, p.Prime ∧ 0 < N.factorization p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    exact ⟨hp', hp'.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)⟩
  have hone : ∀ p ∈ N.primeFactors, 1 ≤ abundancy (p ^ N.factorization p) := by
    intro p hp
    obtain ⟨hp', ha⟩ := hfac p hp
    have := one_add_inv_le_abundancy_prime_pow hp' ha
    have : (0 : ℚ) ≤ (p : ℚ)⁻¹ := by positivity
    linarith
  calc ∏ p ∈ l.toFinset, fourRole q p
      ≤ ∏ p ∈ l.toFinset, abundancy (p ^ N.factorization p) := by
        refine Finset.prod_le_prod (fun p _ => ?_) (fun p hp => ?_)
        · unfold fourRole
          split_ifs <;> positivity
        · have hpN := hl p (List.mem_toFinset.mp hp)
          obtain ⟨hp', ha⟩ := hfac p hpN
          have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp'.ne_zero
          unfold fourRole
          split_ifs with hpq
          · refine le_of_eq_of_le ?_ (one_add_inv_le_abundancy_prime_pow hp' ha)
            push_cast
            field_simp
          · obtain ⟨k, hk⟩ := hev p hp' hpq
            refine le_trans (le_of_eq ?_) (abundancy_prime_pow_mono hp' (a := 2) (by omega))
            rw [abundancy_prime_pow hp']
            simp only [Finset.sum_range_succ, Finset.sum_range_zero]
            push_cast
            field_simp
            ring
    _ ≤ ∏ p ∈ N.primeFactors, abundancy (p ^ N.factorization p) := by
        refine Finset.prod_le_prod_of_subset_of_one_le (fun p hp => hl p (List.mem_toFinset.mp hp))
          (fun p hp => le_trans zero_le_one (hone p (hl p (List.mem_toFinset.mp hp))))
          (fun p hp _ => hone p hp)
    _ = 2 := by rw [← abundancy_eq_prod_primeFactors h.ne_zero, hab]

private theorem fourHead_ok : fourHead.Nodup ∧ (∀ p ∈ fourHead, 0 < p) ∧
    coverCheck 47 7 fourHead = true := by
  decide +kernel

private theorem fourU_ok :
    fourHead.all (fun p => decide (recipFourLogUp p 20 ≤ (fourU p : ℚ) / 1000000000000000)) =
      true := by
  decide +kernel

/-- The transfer: a passed check for the threshold `t / 10^15` and the case lists `req` (primes
that divide `N`) and `exc` (primes that do not divide `N`) gives `t / 10^15 < ∑_{p ∣ N} 1/p`. -/
private theorem lt_sum_inv_of_fourCheck {N : ℕ} (h : OddPerfect N) (t : ℕ) (req exc : List ℕ)
    (hreq : ∀ p ∈ req, p ∈ N.primeFactors) (hexc : ∀ p ∈ exc, p ∉ N.primeFactors)
    (hc : fourCheck t req exc fourHead 1 1 0 0 false = true) :
    (t : ℝ) / 1000000000000000 < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) := by
  set S := N.primeFactors with hS
  set L : ℕ → ℝ := fun p => Real.log ((p : ℝ) / (p - 1)) with hL
  have hodd : ∀ p ∈ S, 3 ≤ p ∧ Odd p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have ho : Odd p := h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    refine ⟨?_, ho⟩
    have := hp'.two_le
    obtain ⟨k, rfl⟩ := ho
    omega
  obtain ⟨hndH, hposH, hcov⟩ := fourHead_ok
  have hU : ∀ p ∈ fourHead, recipFourLogUp p 20 ≤ (fourU p : ℚ) / 1000000000000000 := by
    have := fourU_ok
    rw [List.all_eq_true] at this
    exact fun p hp => of_decide_eq_true (this p hp)
  -- the head
  obtain ⟨q, -, -, hq4, -, hev⟩ := exists_special_prime h
  set T := fourHead.filter (· ∈ S) with hT
  have hTnd : T.Nodup := hndH.filter _
  have hTS : ∀ p ∈ T, p ∈ S := fun p hp => by simpa using (List.mem_filter.mp hp).2
  have hTH : ∀ p ∈ T, p ∈ fourHead := fun p hp => (List.mem_filter.mp hp).1
  have hleaf := fourCheck_sound t q S req exc fourHead 1 1 0 0 false hc hndH hposH one_pos
    (by simp) (fun _ _ => hq4) (fun p _ hp => hreq p hp) (fun p _ hp => hexc p hp)
    (by simpa using prod_fourRole_le_two h hev hTnd hTS)
  rw [← hT, zero_add, zero_add] at hleaf
  set rT := (T.map (fun p => 1000000000000000 / p)).sum with hrT
  set uT := (T.map fourU).sum with huT
  set A := S.filter (· ∈ fourHead) with hA
  set R := S.filter (· ∉ fourHead) with hR
  have hAT : A = T.toFinset := by
    ext p
    simp [hA, hT, and_comm]
  -- the reciprocal sum over the head
  have hrA : (rT : ℝ) / 1000000000000000 ≤ ∑ p ∈ A, 1 / (p : ℝ) := by
    have e : (rT : ℝ) / 1000000000000000 =
        ∑ p ∈ A, ((1000000000000000 / p : ℕ) : ℝ) / 1000000000000000 := by
      rw [← Finset.sum_div, ← Nat.cast_sum, hAT, List.sum_toFinset _ hTnd]
    rw [e]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp0 : 0 < p := hposH p (hTH p (List.mem_toFinset.mp (hAT ▸ hp)))
    have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
    have hmul : ((1000000000000000 / p : ℕ) : ℝ) * p ≤ 1000000000000000 := by
      exact_mod_cast Nat.div_mul_le_self 1000000000000000 p
    rw [div_le_div_iff₀ (by norm_num) hp0']
    linarith
  -- the logarithms over the head
  have huA : ∑ p ∈ A, L p ≤ (uT : ℝ) / 1000000000000000 := by
    have e : (uT : ℝ) / 1000000000000000 = ∑ p ∈ A, ((fourU p : ℕ) : ℝ) / 1000000000000000 := by
      rw [← Finset.sum_div, ← Nat.cast_sum, hAT, List.sum_toFinset _ hTnd]
    rw [e]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpT := List.mem_toFinset.mp (hAT ▸ hp)
    have h3 := (hodd p (hTS p hpT)).1
    refine (log_div_sub_one_le_recipFourLogUp (by omega) 20).trans ?_
    have := (Rat.cast_le (K := ℝ)).mpr (hU p (hTH p hpT))
    push_cast at this
    exact this
  -- the other prime factors are at least 47
  have hR47 : ∀ p ∈ R, 47 ≤ p := by
    intro p hp
    rw [hR, Finset.mem_filter] at hp
    by_contra hlt
    have := (hodd p hp.1).1
    exact hp.2 (mem_of_coverCheck hcov (by omega) (Nat.prime_of_mem_primeFactors hp.1) (by omega))
  have hRm : ∀ m : ℕ, 3 ≤ m → (∀ p ∈ R, m ≤ p) →
      ∑ p ∈ R, L p ≤ (2 * (m : ℝ) - 3) / (2 * ((m : ℝ) - 2)) * ∑ p ∈ R, 1 / (p : ℝ) := by
    intro m hm hmR
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hmp : (m : ℝ) ≤ p := by exact_mod_cast hmR p hp
    exact log_div_sub_one_le_mul_inv hm' hmp
  have hRnn : 0 ≤ ∑ p ∈ R, 1 / (p : ℝ) := Finset.sum_nonneg fun p _ => by positivity
  -- the two splittings
  have hlog := log_two_lt_sum_log h
  rw [← hS, ← Finset.sum_filter_add_sum_filter_not S (· ∈ fourHead)] at hlog
  have hsum := Finset.sum_filter_add_sum_filter_not S (· ∈ fourHead) (fun p => 1 / (p : ℝ))
  rw [← hsum]
  change Real.log 2 < ∑ p ∈ A, L p + ∑ p ∈ R, L p at hlog
  change (t : ℝ) / 1000000000000000 < ∑ p ∈ A, 1 / (p : ℝ) + ∑ p ∈ R, 1 / (p : ℝ)
  have hl2 := Real.log_two_gt_d9
  norm_num at hl2
  simp only [fourLeaf, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hleaf
  rcases hleaf with h0 | ⟨ha, hb⟩
  · have : (t : ℝ) < rT := by exact_mod_cast h0
    linarith
  · by_cases hall : ∀ p ∈ R, 257 ≤ p
    · have h257 := hRm 257 (by norm_num) hall
      have hb' : (511 * t + 510 * uT : ℝ) ≤ 511 * rT + 510 * 693147180300000 := by
        exact_mod_cast hb
      rw [show (2 * ((257 : ℕ) : ℝ) - 3) / (2 * (((257 : ℕ) : ℝ) - 2)) = 511 / 510 by norm_num]
        at h257
      linarith
    · push Not at hall
      obtain ⟨p, hpR, hp257⟩ := hall
      rcases ha with ha | ha
      · have hpS : p ∈ S := (Finset.mem_filter.mp hpR).1
        have hpo := (hodd p hpS).2
        have hp255 : p ≤ 255 := by
          obtain ⟨k, rfl⟩ := hpo
          omega
        have hp0 : (0 : ℝ) < p := by
          have := hR47 p hpR
          exact_mod_cast (by omega : 0 < p)
        have h1p : (1 : ℝ) / 255 ≤ 1 / (p : ℝ) := by
          apply one_div_le_one_div_of_le hp0
          exact_mod_cast hp255
        have hsingle : 1 / (p : ℝ) ≤ ∑ p ∈ R, 1 / (p : ℝ) :=
          Finset.single_le_sum (f := fun p : ℕ => 1 / (p : ℝ))
            (fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg p)) hpR
        have ha' : (255 * t : ℝ) < 255 * rT + 1000000000000000 := by exact_mod_cast ha
        linarith
      · have h47 := hRm 47 (by norm_num) hR47
        have ha' : (91 * t + 90 * uT : ℝ) ≤ 91 * rT + 90 * 693147180300000 := by
          exact_mod_cast ha
        rw [show (2 * ((47 : ℕ) : ℝ) - 3) / (2 * (((47 : ℕ) : ℝ) - 2)) = 91 / 90 by norm_num]
          at h47
        linarith

private theorem fourCheck_three_five :
    fourCheck 596063100000000 [3, 5] [] fourHead 1 1 0 0 false = true := by
  decide +kernel

private theorem fourCheck_three_not_five :
    fourCheck 604706000000000 [3] [5] fourHead 1 1 0 0 false = true := by
  decide +kernel

private theorem fourCheck_five_not_three :
    fourCheck 647648000000000 [5] [3] fourHead 1 1 0 0 false = true := by
  decide +kernel

private theorem fourCheck_not_three_not_five :
    fourCheck 667363000000000 [] [3, 5] fourHead 1 1 0 0 false = true := by
  decide +kernel

private theorem mem_primeFactors_of_dvd' {N p : ℕ} (h : OddPerfect N) (hp : p.Prime)
    (hd : p ∣ N) : p ∈ N.primeFactors :=
  Nat.mem_primeFactors.mpr ⟨hp, hd, h.ne_zero⟩

/-- For an odd perfect number divisible by `3` and by `5`, `0.5960631 < ∑_{p ∣ N} 1/p`. -/
theorem sum_inv_gt_5960631_of_three_five {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) (h5 : 5 ∣ N) :
    (5960631 / 10000000 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) := by
  have := lt_sum_inv_of_fourCheck h 596063100000000 [3, 5] []
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact mem_primeFactors_of_dvd' h Nat.prime_three h3
      · exact mem_primeFactors_of_dvd' h Nat.prime_five h5)
    (by simp) fourCheck_three_five
  norm_num at this ⊢
  linarith

/-- For an odd perfect number divisible by `3` and not by `5`, `0.604706 < ∑_{p ∣ N} 1/p`. -/
theorem sum_inv_gt_604706_of_three_not_five {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N)
    (h5 : ¬ 5 ∣ N) : (604706 / 1000000 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) := by
  have := lt_sum_inv_of_fourCheck h 604706000000000 [3] [5]
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact mem_primeFactors_of_dvd' h Nat.prime_three h3)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact fun hm => h5 (Nat.dvd_of_mem_primeFactors hm))
    fourCheck_three_not_five
  norm_num at this ⊢
  linarith

/-- For an odd perfect number divisible by `5` and not by `3`, `0.647648 < ∑_{p ∣ N} 1/p`. -/
theorem sum_inv_gt_647648_of_five_not_three {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (h5 : 5 ∣ N) : (647648 / 1000000 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) := by
  have := lt_sum_inv_of_fourCheck h 647648000000000 [5] [3]
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact mem_primeFactors_of_dvd' h Nat.prime_five h5)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact fun hm => h3 (Nat.dvd_of_mem_primeFactors hm))
    fourCheck_five_not_three
  norm_num at this ⊢
  linarith

/-- For an odd perfect number divisible neither by `3` nor by `5`,
`0.667363 < ∑_{p ∣ N} 1/p`. -/
theorem sum_inv_gt_667363_of_not_three_not_five {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (h5 : ¬ 5 ∣ N) : (667363 / 1000000 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) := by
  have := lt_sum_inv_of_fourCheck h 667363000000000 [] [3, 5] (by simp)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact fun hm => h3 (Nat.dvd_of_mem_primeFactors hm)
      · exact fun hm => h5 (Nat.dvd_of_mem_primeFactors hm))
    fourCheck_not_three_not_five
  norm_num at this ⊢
  linarith

/-- For an odd perfect number, `0.5960631 < ∑_{p ∣ N} 1/p`. Cohen (1980) gives the bound
`0.596063`; the comparison with the literature was not verified. -/
theorem sum_inv_gt_5960631_div_10000000 {N : ℕ} (h : OddPerfect N) :
    (5960631 / 10000000 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) := by
  by_cases h3 : 3 ∣ N <;> by_cases h5 : 5 ∣ N
  · exact sum_inv_gt_5960631_of_three_five h h3 h5
  · have := sum_inv_gt_604706_of_three_not_five h h3 h5
    linarith
  · have := sum_inv_gt_647648_of_five_not_three h h3 h5
    linarith
  · have := sum_inv_gt_667363_of_not_three_not_five h h3 h5
    linarith

end OddPerfect

#print axioms OddPerfect.sum_inv_gt_5960631_of_three_five
#print axioms OddPerfect.sum_inv_gt_604706_of_three_not_five
#print axioms OddPerfect.sum_inv_gt_647648_of_five_not_three
#print axioms OddPerfect.sum_inv_gt_667363_of_not_three_not_five
#print axioms OddPerfect.sum_inv_gt_5960631_div_10000000
