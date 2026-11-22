import OddPerfect.ReciprocalSumFour
import OddPerfect.ReciprocalLogTwo

/-!
# Upper bounds for the reciprocal sum of the prime factors, by cases on `3` and `5`

For an odd perfect number `N` we prove

* `3 ∣ N` and `5 ∣ N`: `∑_{p ∣ N} 1/p < 0.673634`;
* `3 ∣ N` and `5 ∤ N`: `∑_{p ∣ N} 1/p < 0.657304`;
* `3 ∤ N` and `5 ∣ N`: `∑_{p ∣ N} 1/p < 0.677637`;

hence `∑_{p ∣ N} 1/p < 0.677637` whenever `3 ∣ N` or `5 ∣ N`. With the lower bounds of
`OddPerfect.ReciprocalSumFour` this gives a window for each class; in the class `3 ∤ N`,
`5 ∤ N` the upper end stays the landed bound `log 2`.

Comparison with the literature. The rows are the four classes of `gcd(N, 15)`; the entries are
upper bounds for `∑_{p ∣ N} 1/p`, read from the source (`0.693148` is `log 2` rounded up).

* `1970`: the bounds of Suryanarayana and Hagis (1970), as reprinted in Table 1 (page 370) of
  G. L. Cohen, "On odd perfect numbers (II), multiperfect numbers and quasiperfect numbers",
  J. Austral. Math. Soc. Ser. A 29 (1980), 369 to 384.
* `1980`: Table 2 (page 370) of the same paper, Cohen's improved bounds.
* `2024`: Proposition 1 (page 3) of J. Zelinsky, "The sum of the reciprocals of the prime
  divisors of an odd perfect or odd primitive non-deficient number", arXiv:2402.14234 (version
  5, 2025), which summarizes the results of Cohen, Hagis and Suryanarayana; its values are those
  of the column `1970`.
* `this file`: the constants proved here.

| gcd(N, 15) | 1970     | 1980     | 2024     | this file |
|------------|----------|----------|----------|-----------|
| 15         | 0.673770 | 0.673634 | 0.673770 | 0.673634  |
| 3          | 0.657304 | 0.657304 | 0.657304 | 0.657304  |
| 5          | 0.678036 | 0.677637 | 0.678036 | 0.677637  |
| 1          | 0.693148 | 0.693148 | 0.693148 | log 2     |

Against Cohen (1980): tied in all four classes, to six decimal places. Against the columns
`1970` and `2024`: ahead in the classes `15` and `5`, tied in the classes `3` and `1`.

The method. Write `A_p = σ(p^e)/p^e` for the exact exponent `e` of `p` in `N`, so that
`∑_{p ∣ N} log A_p = log 2`, and let `q` be the special prime. For a set `P` of prime factors,
`∑_{p ∣ N} 1/p ≤ log 2 + ∑_{p ∈ P} (1/p - log A_p) + c`, where `c = 0` if `q ∈ P` and
`c = 1/(2q^2)` otherwise: an ordinary prime has `1/p < log(1 + 1/p + 1/p^2) ≤ log A_p`, and
`1/q - log(1 + 1/q) ≤ 1/(2q^2)`. The check `upChk` walks through the odd primes below `71` in
increasing order and decides for each whether it divides `N` and in which role:

* ordinary with exponent exactly `2`: then every odd prime factor of `σ(p^2)` divides `N`;
* ordinary with exponent at least `4`;
* special with exponent exactly `1`: then every odd prime factor of `p + 1` divides `N`;
* special with exponent at least `5`.

The forced primes must not be excluded by the case or by an earlier decision. When `3` has
exponent exactly `2`, the exponents of `3` in the divisor sums of the components add up to `2`,
so the decided exact components may carry at most two factors `3` in all. A branch stops as soon
as the decided primes give the bound; if the special prime is not decided yet it is at least the
next entry of the list rounded up to a number `≡ 1 (mod 4)`, or at least `71` at the end. The table `upTable` (rational
lower bounds of the logarithms by a truncated series, reciprocals rounded up, forced lists and
exponents of `3`) was computed outside Lean (generator `scripts/ReciprocalSum/gen_recipupper.py`);
the kernel checks again every table entry and every branch.
-/

open Finset
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- A record of the table: the prime `p`, the number `n` of series terms, `r = ⌈10^15/p⌉`,
lower bounds `w2, w4, w1, w5` of `10^15 log(σ(p^a)/p^a)` for `a = 2, 4, 1, 5`, the forced
lists `f2` (odd primes below `71` dividing `σ(p^2)`) and `f1` (odd primes below `71` dividing
`p + 1`), and lower bounds `v2, v1` of the exponent of `3` in `σ(p^2)` and in `p + 1`. -/
structure URec where
  p : ℕ
  n : ℕ
  r : ℕ
  w2 : ℕ
  w4 : ℕ
  w1 : ℕ
  w5 : ℕ
  f2 : List ℕ
  f1 : List ℕ
  v2 : ℕ
  v1 : ℕ

/-- The table: for each odd prime `p < 71` the record
`⟨p, n, r, w2, w4, w1, w5, f2, f1, v2, v1⟩` described at `URec`. -/
def upTable : List URec :=
  [⟨3, 37, 333333333333334, 367724780125317, 401341390924302, 0, 0, [13], [], 0, 0⟩,
   ⟨5, 25, 200000000000000, 215111379616945, 222823500103284, 182321556793954, 223079549266122, [31], [3], 0, 1⟩,
   ⟨7, 21, 142857142857143, 151230969723923, 154091179038855, 0, 0, [3, 19], [], 1, 0⟩,
   ⟨11, 17, 90909090909091, 94558582625012, 95303970571817, 0, 0, [7, 19], [], 0, 0⟩,
   ⟨13, 16, 76923076923077, 79587437918347, 80040014379166, 74107972153721, 80042500497303, [3, 61], [7], 1, 0⟩,
   ⟨17, 14, 58823529411765, 60421059474764, 60623917519909, 57158413839948, 60624580387241, [], [3], 0, 2⟩,
   ⟨19, 14, 52631578947369, 53921416793820, 54066817409120, 0, 0, [3], [], 1, 0⟩,
   ⟨23, 13, 43478260869566, 44369569664035, 44451607203091, 0, 0, [7], [], 0, 0⟩,
   ⟨29, 12, 34482758620690, 35050316879554, 35091271057296, 33901551675681, 35091318130098, [13, 67], [3, 5], 0, 1⟩,
   ⟨31, 12, 32258064516130, 32756255074880, 32789787893557, 0, 0, [3], [], 1, 0⟩,
   ⟨37, 11, 27027027027028, 27379231825940, 27398959767247, 26668247082161, 27398973798361, [3, 7, 67], [19], 1, 0⟩,
   ⟨41, 11, 24390243902440, 24678103119314, 24692603958981, 24097551579060, 24692612379849, [], [3, 7], 0, 1⟩,
   ⟨43, 11, 23255813953489, 23517919822198, 23530490607863, 0, 0, [3], [], 1, 0⟩,
   ⟨47, 10, 21276595744681, 21496573397418, 21506200860720, 0, 0, [37, 61], [], 0, 0⟩,
   ⟨53, 10, 18867924528302, 19041477993871, 19048192579468, 18692133012152, 19048194925577, [7], [3], 0, 3⟩,
   ⟨59, 10, 16949152542373, 17089564300464, 17094431960550, 0, 0, [], [], 0, 0⟩,
   ⟨61, 10, 16393442622951, 16524896286406, 16529300767212, 16260520871780, 16529301931800, [3, 13], [31], 1, 0⟩,
   ⟨67, 9, 14925373134329, 15034552481950, 15037876623868, 0, 0, [3, 7, 31], [], 1, 0⟩]

/-- `σ(p^a)/p^a = ∑_{i ≤ a} (1/p)^i` as a rational. -/
def upGeo (p a : ℕ) : ℚ := ∑ i ∈ range (a + 1), ((p : ℚ)⁻¹) ^ i

/-- The truncated series lower bound `∑_{k=1}^{n} x^k/k - x^(n+1)/(1 - x)` for `-log(1 - x)`. -/
def serLow (x : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ range n, x ^ (i + 1) / ((i : ℚ) + 1) - x ^ (n + 1) / (1 - x)

/-- The lower bound for `log(σ(p^a)/p^a)` used in the table. -/
def upLow (p a n : ℕ) : ℚ := serLow (1 - 1 / upGeo p a) n

/-- A trial division primality test. -/
def upPrime (x : ℕ) : Bool := decide (2 ≤ x) && (List.range x).all fun d => d < 2 || x % d != 0

/-- The checks of one table record. -/
def upRecOk (e : URec) : Bool :=
  decide (1000000000000000 ≤ e.r * e.p) &&
  decide ((e.w2 : ℚ) / 1000000000000000 ≤ upLow e.p 2 e.n) &&
  decide ((e.w4 : ℚ) / 1000000000000000 ≤ upLow e.p 4 e.n) &&
  (decide (e.p % 4 ≠ 1) ||
    (decide ((e.w1 : ℚ) / 1000000000000000 ≤ upLow e.p 1 e.n) &&
     decide ((e.w5 : ℚ) / 1000000000000000 ≤ upLow e.p 5 e.n))) &&
  e.f2.all (fun x => upPrime x && x != 2 && (e.p * e.p + e.p + 1) % x == 0) &&
  e.f1.all (fun x => upPrime x && x != 2 && (e.p + 1) % x == 0) &&
  (e.p * e.p + e.p + 1) % 3 ^ e.v2 == 0 && (e.p + 1) % 3 ^ e.v1 == 0

/-- The cost bound `⌊10^15/(2m^2)⌋ + 1` for a special prime at least `m`. -/
def upCost (m : ℕ) : ℕ := 1000000000000000 / (2 * m * m) + 1

/-- The cost bound when the special prime is not among the decided primes. -/
def upCst : List URec → ℕ
  | [] => upCost 71
  | e :: _ => upCost (e.p + (5 - e.p % 4) % 4)

/-- The stop test for the threshold `t / 10^15`. -/
def upStop (t : ℕ) (l : List URec) (R A : ℕ) (sp : Bool) : Bool :=
  decide (R + 693147180800000 + (if sp then 0 else upCst l) ≤ t + A)

/-- The upper bound check. -/
def upChk (t : ℕ) (req exc : List ℕ) :
    List URec → ℕ → ℕ → Bool → List ℕ → List ℕ → ℕ → Bool → Bool
  | [], R, A, sp, _, _, _, _ => upStop t [] R A sp
  | e :: l, R, A, sp, ab, nd, v, b3 =>
    upStop t (e :: l) R A sp ||
    ((req.contains e.p || nd.contains e.p || upChk t req exc l R A sp (e.p :: ab) nd v b3) &&
     (exc.contains e.p ||
      ((e.f2.any (fun x => ab.contains x || exc.contains x) ||
          ((b3 || e.p == 3) && decide (2 < v + e.v2)) ||
          upChk t req exc l (R + e.r) (A + e.w2) sp ab (e.f2 ++ nd) (v + e.v2) (b3 || e.p == 3)) &&
       upChk t req exc l (R + e.r) (A + e.w4) sp ab nd v b3 &&
       (sp || decide (e.p % 4 ≠ 1) ||
        ((e.f1.any (fun x => ab.contains x || exc.contains x) ||
            (b3 && decide (2 < v + e.v1)) ||
            upChk t req exc l (R + e.r) (A + e.w1) true ab (e.f1 ++ nd) (v + e.v1) b3) &&
         upChk t req exc l (R + e.r) (A + e.w5) true ab nd v b3)))))

private theorem upTable_ok : upTable.all upRecOk = true := by
  decide +kernel

private theorem upHead_ok : (upTable.map URec.p).Pairwise (· < ·) ∧
    coverCheck 71 9 (upTable.map URec.p) = true ∧ (upTable.map URec.p).all (· < 71) = true := by
  decide +kernel

private theorem upChk_three_five :
    upChk 673634000000000 [3, 5] [7] upTable 0 0 false [] [] 0 false = true := by
  decide +kernel

private theorem upChk_three_not_five :
    upChk 657304000000000 [3] [5] upTable 0 0 false [] [] 0 false = true := by
  decide +kernel

private theorem upChk_five_not_three :
    upChk 677637000000000 [5] [3] upTable 0 0 false [] [] 0 false = true := by
  decide +kernel

/-! ## Soundness -/

variable {N : ℕ}

/-- `log(σ(p^e)/p^e)` for the exact exponent `e` of `p` in `N`. -/
noncomputable def upLA (N p : ℕ) : ℝ := Real.log ((abundancy (p ^ N.factorization p) : ℚ) : ℝ)

/-- The exponent of `3` in `σ(p^e)` for the exact exponent `e` of `p` in `N`. -/
def upC3 (N p : ℕ) : ℕ := (σ 1 (p ^ N.factorization p)).factorization 3

private theorem upPrime_sound {x : ℕ} (h : upPrime x = true) : x.Prime := by
  simp only [upPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  rw [Nat.prime_def_lt']
  refine ⟨h.1, fun m hm hmx hd => ?_⟩
  rcases h.2 m hmx with h1 | h1
  · omega
  · exact h1 (Nat.mod_eq_zero_of_dvd hd)

private theorem one_le_upGeo (p a : ℕ) : (1 : ℚ) ≤ upGeo p a := by
  unfold upGeo
  rw [Finset.sum_range_succ']
  have : 0 ≤ ∑ i ∈ range a, ((p : ℚ)⁻¹) ^ (i + 1) := Finset.sum_nonneg fun i _ => by positivity
  simp only [pow_zero]
  linarith

private theorem abund_pos {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (0 : ℝ) < ((abundancy (p ^ a) : ℚ) : ℝ) := by
  rw [abundancy_prime_pow hp]
  have := one_le_upGeo p a
  have h' : (0 : ℚ) < upGeo p a := by linarith
  exact_mod_cast h'

private theorem upLow_le_log {p : ℕ} (hp : p.Prime) (a n : ℕ) :
    ((upLow p a n : ℚ) : ℝ) ≤ Real.log ((abundancy (p ^ a) : ℚ) : ℝ) := by
  rw [abundancy_prime_pow hp]
  change ((upLow p a n : ℚ) : ℝ) ≤ Real.log ((upGeo p a : ℚ) : ℝ)
  have hg : (1 : ℝ) ≤ ((upGeo p a : ℚ) : ℝ) := by exact_mod_cast one_le_upGeo p a
  set g : ℝ := ((upGeo p a : ℚ) : ℝ) with hgdef
  have hx0 : 0 ≤ 1 - 1 / g := by
    have : 1 / g ≤ 1 := by rw [div_le_one (by linarith)]; exact hg
    linarith
  have hx1 : 1 - 1 / g < 1 := by
    have : 0 < 1 / g := by positivity
    linarith
  have h := le_neg_log_one_sub hx0 hx1 n
  have e : Real.log g = -Real.log (1 - (1 - 1 / g)) := by
    rw [sub_sub_cancel, one_div, Real.log_inv, neg_neg]
  rw [e]
  refine le_of_eq_of_le ?_ h
  unfold upLow serLow
  push_cast
  rfl

private theorem log_abund_mono {p a b : ℕ} (hp : p.Prime) (hab : a ≤ b) :
    Real.log ((abundancy (p ^ a) : ℚ) : ℝ) ≤ Real.log ((abundancy (p ^ b) : ℚ) : ℝ) :=
  Real.log_le_log (abund_pos hp a) (by exact_mod_cast abundancy_prime_pow_mono hp hab)

/-- A table bound `w` for the exponent `a ≤ e_p` gives `w ≤ 10^15 log(σ(p^e)/p^e)`. -/
private theorem w_le_upLA {p a n w : ℕ} (hp : p.Prime) (ha : a ≤ N.factorization p)
    (hw : (w : ℚ) / 1000000000000000 ≤ upLow p a n) :
    (w : ℝ) ≤ upLA N p * 1000000000000000 := by
  have h1 := (Rat.cast_le (K := ℝ)).mpr hw
  push_cast at h1
  have h2 := (upLow_le_log hp a n).trans (log_abund_mono hp ha)
  unfold upLA
  linarith

private theorem log_two_eq_sum_upLA (h : OddPerfect N) :
    Real.log 2 = ∑ p ∈ N.primeFactors, upLA N p := by
  have h2 : (2 : ℚ) = ∏ p ∈ N.primeFactors, abundancy (p ^ N.factorization p) := by
    rw [← abundancy_eq_prod_primeFactors h.ne_zero,
      (perfect_iff_abundancy_eq_two h.pos).mp h.perfect]
  have h2' : (2 : ℝ) = ∏ p ∈ N.primeFactors, ((abundancy (p ^ N.factorization p) : ℚ) : ℝ) := by
    rw [← Rat.cast_prod, ← h2]
    norm_num
  unfold upLA
  rw [h2', Real.log_prod]
  intro p hp
  exact (abund_pos (Nat.prime_of_mem_primeFactors hp) _).ne'

private theorem sigma_pow_eq {p : ℕ} (hp : p.Prime) (a : ℕ) :
    σ 1 (p ^ a) = ∑ i ∈ range (a + 1), p ^ i :=
  sigma_one_apply_prime_pow hp

/-- The stop bound: for `Pd ⊆ S`,
`∑_S 1/p ≤ log 2 + ∑_{Pd} (1/p - log A_p) + (0 if q ∈ Pd, else 1/(2q^2))`. -/
private theorem sum_inv_le_stop (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) {Pd : Finset ℕ} (hPd : Pd ⊆ N.primeFactors) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) ≤ Real.log 2 + ∑ p ∈ Pd, (1 / (p : ℝ) - upLA N p) +
      (if q ∈ Pd then 0 else 1 / (2 * (q : ℝ) ^ 2)) := by
  set S := N.primeFactors
  have hqS : q ∈ S := by
    rw [Nat.mem_primeFactors]
    refine ⟨hq, Nat.dvd_of_factorization_pos ?_, h.ne_zero⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  have hsplit : ∑ p ∈ S, 1 / (p : ℝ) =
      ∑ p ∈ S, (1 / (p : ℝ) - upLA N p) + ∑ p ∈ S, upLA N p := by
    rw [← Finset.sum_add_distrib]
    simp
  rw [hsplit, ← log_two_eq_sum_upLA h, ← Finset.sum_sdiff hPd]
  have hpt : ∀ p ∈ S \ Pd, 1 / (p : ℝ) - upLA N p ≤
      if p = q then 1 / (2 * (q : ℝ) ^ 2) else 0 := by
    intro p hp
    have hpS := (Finset.mem_sdiff.mp hp).1
    have hpr := Nat.prime_of_mem_primeFactors hpS
    have he : 0 < N.factorization p :=
      hpr.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hpS)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
    split_ifs with hpq
    · subst hpq
      have h1 := log_abund_mono hpr (a := 1) he
      have e1 : ((abundancy (p ^ 1) : ℚ) : ℝ) = 1 + 1 / (p : ℝ) := by
        rw [abundancy_prime_pow hpr]
        simp [Finset.sum_range_succ]
      rw [e1] at h1
      have h2 := sub_log_one_add_le_sq (x := 1 / (p : ℝ)) (by positivity)
      have e2 : (1 / (p : ℝ)) ^ 2 / 2 = 1 / (2 * (p : ℝ) ^ 2) := by field_simp
      unfold upLA
      linarith
    · obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hpr hpq
      have h1 := log_abund_mono hpr (a := 2) (b := N.factorization p) (by omega)
      have e1 : ((abundancy (p ^ 2) : ℚ) : ℝ) = 1 + 1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2 := by
        rw [abundancy_prime_pow hpr]
        simp [Finset.sum_range_succ]
      rw [e1] at h1
      have h2 := lt_log_one_add_add_sq (x := 1 / (p : ℝ)) (by positivity)
        (by rw [div_le_one (by linarith)]; linarith)
      unfold upLA
      linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_ite_eq'] at hsum
  have hfin : (if q ∈ S \ Pd then 1 / (2 * (q : ℝ) ^ 2) else 0) =
      (if q ∈ Pd then 0 else 1 / (2 * (q : ℝ) ^ 2)) := by
    by_cases hqP : q ∈ Pd
    · rw [if_pos hqP, if_neg (fun hm => (Finset.mem_sdiff.mp hm).2 hqP)]
    · rw [if_neg hqP, if_pos (Finset.mem_sdiff.mpr ⟨hqS, hqP⟩)]
  rw [hfin] at hsum
  linarith

private theorem upCost_bound {m q : ℕ} (hm : 0 < m) (hmq : m ≤ q) :
    1 / (2 * (q : ℝ) ^ 2) * 1000000000000000 ≤ (upCost m : ℝ) := by
  have hk : 0 < 2 * m * m := by positivity
  have h1 := Nat.lt_mul_div_succ 1000000000000000 hk
  have h2 : 2 * m * m ≤ 2 * q * q := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hmq) hmq
  have h3 : 1000000000000000 ≤ 2 * q * q * upCost m := by
    unfold upCost
    exact h1.le.trans (Nat.mul_le_mul_right _ h2)
  have h3' : (1000000000000000 : ℝ) ≤ 2 * q * q * (upCost m : ℝ) := by exact_mod_cast h3
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

private theorem stop_bound (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) {t R A : ℕ} {sp : Bool} {l : List URec} {Pd : Finset ℕ}
    (hs : upStop t l R A sp = true) (hPd : Pd ⊆ N.primeFactors) (hsp1 : sp = true → q ∈ Pd)
    (hsp2 : sp = false → q ∉ Pd)
    (hcost : sp = false → 1 / (2 * (q : ℝ) ^ 2) * 1000000000000000 ≤ (upCst l : ℝ))
    (hR : (∑ p ∈ Pd, 1 / (p : ℝ)) * 1000000000000000 ≤ R)
    (hA : (A : ℝ) ≤ (∑ p ∈ Pd, upLA N p) * 1000000000000000) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < (t : ℝ) / 1000000000000000 := by
  have key := sum_inv_le_stop h hq hodd hPd
  rw [Finset.sum_sub_distrib] at key
  have hl2 := Real.log_two_lt_d9
  norm_num at hl2
  rw [lt_div_iff₀ (by norm_num)]
  unfold upStop at hs
  cases sp
  · simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at hs
    rw [if_neg (hsp2 rfl)] at key
    have hs' : (R : ℝ) + 693147180800000 + (upCst l : ℝ) ≤ t + A := by exact_mod_cast hs
    have hc := hcost rfl
    linarith
  · simp only [if_true, add_zero, decide_eq_true_eq] at hs
    rw [if_pos (hsp1 rfl)] at key
    have hs' : (R : ℝ) + 693147180800000 ≤ t + A := by exact_mod_cast hs
    linarith

private theorem upRecOk_facts {e : URec} (h : upRecOk e = true) :
    1000000000000000 ≤ e.r * e.p ∧
    (e.w2 : ℚ) / 1000000000000000 ≤ upLow e.p 2 e.n ∧
    (e.w4 : ℚ) / 1000000000000000 ≤ upLow e.p 4 e.n ∧
    (e.p % 4 = 1 → (e.w1 : ℚ) / 1000000000000000 ≤ upLow e.p 1 e.n ∧
      (e.w5 : ℚ) / 1000000000000000 ≤ upLow e.p 5 e.n) ∧
    (∀ x ∈ e.f2, x.Prime ∧ x ≠ 2 ∧ x ∣ e.p * e.p + e.p + 1) ∧
    (∀ x ∈ e.f1, x.Prime ∧ x ≠ 2 ∧ x ∣ e.p + 1) ∧
    3 ^ e.v2 ∣ e.p * e.p + e.p + 1 ∧ 3 ^ e.v1 ∣ e.p + 1 := by
  simp only [upRecOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, fun hp => h4.resolve_left (by omega), fun x hx => ?_, fun x hx => ?_,
    Nat.dvd_of_mod_eq_zero h7, Nat.dvd_of_mod_eq_zero h8⟩
  · obtain ⟨⟨ha, hb⟩, hc⟩ := h5 x hx
    exact ⟨upPrime_sound ha, hb, Nat.dvd_of_mod_eq_zero hc⟩
  · obtain ⟨⟨ha, hb⟩, hc⟩ := h6 x hx
    exact ⟨upPrime_sound ha, hb, Nat.dvd_of_mod_eq_zero hc⟩

private theorem mem_pf {N p : ℕ} (h : OddPerfect N) (hp : p.Prime) (hd : p ∣ N) :
    p ∈ N.primeFactors :=
  Nat.mem_primeFactors.mpr ⟨hp, hd, h.ne_zero⟩

private theorem c3_ge {N p a v : ℕ} (hp : p.Prime) (he : N.factorization p = a)
    (hv : 3 ^ v ∣ σ 1 (p ^ a)) : v ≤ upC3 N p := by
  unfold upC3
  rw [he]
  exact (Nat.prime_three.pow_dvd_iff_le_factorization
    (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne').mp hv

private theorem sum_insert_inv {Pd : Finset ℕ} {p : ℕ} (hp : p ∉ Pd) (f : ℕ → ℝ) :
    ∑ x ∈ insert p Pd, f x = f p + ∑ x ∈ Pd, f x := Finset.sum_insert hp


private theorem sum_inv_mem_q (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : q ∈ N.primeFactors := by
  rw [Nat.mem_primeFactors]
  refine ⟨hq, Nat.dvd_of_factorization_pos ?_, h.ne_zero⟩
  obtain ⟨k, hk⟩ := hodd
  omega

/-- The soundness of `upChk`. -/
private theorem upChk_sound (h : OddPerfect N) {q : ℕ} (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hq4 : q % 4 = 1) (t : ℕ) (req exc : List ℕ)
    (hreq : ∀ x ∈ req, x ∈ N.primeFactors) (hexc : ∀ x ∈ exc, x ∉ N.primeFactors) :
    ∀ (l : List URec) (R A : ℕ) (sp : Bool) (ab nd : List ℕ) (v : ℕ) (b3 : Bool)
      (Pd : Finset ℕ),
      upChk t req exc l R A sp ab nd v b3 = true →
      (∀ e ∈ l, upRecOk e = true) →
      (l.map URec.p).Pairwise (· < ·) →
      Pd ⊆ N.primeFactors → (∀ e ∈ l, e.p ∉ Pd) →
      (∀ x ∈ ab, x ∉ N.primeFactors) → (∀ x ∈ nd, x ∈ N.primeFactors) →
      (sp = true → q ∈ Pd) →
      (sp = false → q ∉ Pd ∧ (q ∈ l.map URec.p ∨ ((∀ e ∈ l, e.p < q) ∧ 71 ≤ q))) →
      v + (((l.map URec.p).filter (· ∈ N.primeFactors)).map (upC3 N)).sum ≤
        N.factorization 3 →
      (b3 = true → N.factorization 3 = 2) →
      (∑ p ∈ Pd, 1 / (p : ℝ)) * 1000000000000000 ≤ R →
      (A : ℝ) ≤ (∑ p ∈ Pd, upLA N p) * 1000000000000000 →
      ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < (t : ℝ) / 1000000000000000 := by
  intro l
  induction l with
  | nil =>
    intro R A sp ab nd v b3 Pd hc _ _ hPd _ _ _ hsp1 hsp2 _ _ hR hA
    refine stop_bound h hq hodd hc hPd hsp1 (fun hs => (hsp2 hs).1) (fun hs => ?_) hR hA
    have h71 : 71 ≤ q := by
      rcases (hsp2 hs).2 with hm | ⟨-, h71⟩
      · simp at hm
      · exact h71
    exact upCost_bound (by norm_num) h71
  | cons e l ih =>
    intro R A sp ab nd v b3 Pd hc hok hpw hPd hPdl hab hnd hsp1 hsp2 hval hb3 hR hA
    rw [List.map_cons, List.pairwise_cons] at hpw
    obtain ⟨hlt, hpw'⟩ := hpw
    have hok' : ∀ e' ∈ l, upRecOk e' = true := fun e' he' => hok e' (List.mem_cons_of_mem _ he')
    have hlt' : ∀ e' ∈ l, e.p < e'.p := fun e' he' => hlt e'.p (List.mem_map_of_mem he')
    have hPdl' : ∀ e' ∈ l, e'.p ∉ Pd := fun e' he' => hPdl e' (List.mem_cons_of_mem _ he')
    have hePd : e.p ∉ Pd := hPdl e List.mem_cons_self
    simp only [upChk, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hstop | ⟨h1, h2⟩
    · refine stop_bound h hq hodd hstop hPd hsp1 (fun hs => (hsp2 hs).1) (fun hs => ?_) hR hA
      have hle : e.p ≤ q := by
        rcases (hsp2 hs).2 with hm | ⟨hall, -⟩
        · rw [List.map_cons, List.mem_cons] at hm
          rcases hm with hm | hm
          · omega
          · exact (hlt q hm).le
        · exact (hall e List.mem_cons_self).le
      exact upCost_bound (by omega) (by omega)
    obtain ⟨hr, hw2, hw4, hw15, hf2, hf1, hv2, hv1⟩ := upRecOk_facts (hok e List.mem_cons_self)
    rw [List.map_cons] at hval hsp2
    by_cases hpS : e.p ∈ N.primeFactors
    · -- `e.p` divides `N`
      rw [List.filter_cons_of_pos (by simpa using hpS), List.map_cons, List.sum_cons] at hval
      have hpr := Nat.prime_of_mem_primeFactors hpS
      have hpos : 0 < N.factorization e.p :=
        hpr.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hpS)
      have hnex : e.p ∉ exc := fun hm => hexc _ hm hpS
      simp only [List.contains_iff_mem, hnex, false_or] at h2
      obtain ⟨⟨h2a, h2b⟩, h2c⟩ := h2
      have hp0 : (0 : ℝ) < e.p := by exact_mod_cast hpr.pos
      have hrr : 1 / (e.p : ℝ) * 1000000000000000 ≤ e.r := by
        have : (1000000000000000 : ℝ) ≤ e.r * e.p := by exact_mod_cast hr
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hp0]
        linarith
      have hPd' : insert e.p Pd ⊆ N.primeFactors := Finset.insert_subset hpS hPd
      have hPdl'' : ∀ e' ∈ l, e'.p ∉ insert e.p Pd := by
        intro e' he' hm
        rcases Finset.mem_insert.mp hm with hm | hm
        · exact (hlt' e' he').ne' hm
        · exact hPdl' e' he' hm
      have hR' : (∑ p ∈ insert e.p Pd, 1 / (p : ℝ)) * 1000000000000000 ≤ ((R + e.r : ℕ) : ℝ) := by
        rw [sum_insert_inv hePd]
        push_cast
        linarith
      have hA' : ∀ w : ℕ, (w : ℝ) ≤ upLA N e.p * 1000000000000000 →
          ((A + w : ℕ) : ℝ) ≤ (∑ p ∈ insert e.p Pd, upLA N p) * 1000000000000000 := by
        intro w hw
        rw [sum_insert_inv hePd]
        push_cast
        linarith
      by_cases hpq : e.p = q
      · -- the special prime
        have hsp : sp = false := by
          cases sp
          · rfl
          · exact absurd (hpq ▸ hsp1 rfl) hePd
        subst hsp
        have hp4 : e.p % 4 = 1 := hpq ▸ hq4
        have hoddp : Odd (N.factorization e.p) := hpq ▸ hodd
        have hk4 := (special_mod_four h hpr hoddp).2
        simp only [Bool.false_eq_true, decide_eq_true_eq, false_or, hp4, ne_eq,
          not_true_eq_false] at h2c
        obtain ⟨h2d, h2e⟩ := h2c
        obtain ⟨hw1, hw5⟩ := hw15 hp4
        have hsp1' : true = true → q ∈ insert e.p Pd := fun _ => hpq ▸ Finset.mem_insert_self _ _
        have hsp2' : true = false → q ∉ insert e.p Pd ∧
            (q ∈ l.map URec.p ∨ ((∀ e' ∈ l, e'.p < q) ∧ 71 ≤ q)) := fun hf => absurd hf (by simp)
        rcases (show N.factorization e.p = 1 ∨ 5 ≤ N.factorization e.p by omega) with he1 | he5
        · have hfS : ∀ x ∈ e.f1, x ∈ N.primeFactors := by
            intro x hx
            obtain ⟨hxp, hx2, hxd⟩ := hf1 x hx
            have := prime_dvd_of_dvd_succ_special h hpr hoddp hxp hx2 hxd
            exact mem_pf h hxp this.1
          have hc3 : e.v1 ≤ upC3 N e.p := by
            refine c3_ge hpr he1 ?_
            rw [sigma_pow_eq hpr]
            simpa [Finset.sum_range_succ, add_comm] using hv1
          simp only [List.any_eq_true, Bool.or_eq_true, List.contains_iff_mem] at h2d
          rcases h2d with (⟨x, hx, hxm⟩ | ⟨hb, hlt2⟩) | hrec
          · rcases hxm with hxm | hxm
            · exact absurd (hfS x hx) (hab x hxm)
            · exact absurd (hfS x hx) (hexc x hxm)
          · have := hb3 hb
            omega
          · refine ih _ _ _ _ _ _ _ _ hrec hok' hpw' hPd' hPdl'' hab ?_ hsp1' hsp2' (by omega)
              hb3 hR' (hA' _ (w_le_upLA hpr (by omega) hw1))
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hfS x hx
            · exact hnd x hx
        · exact ih _ _ _ _ _ _ _ _ h2e hok' hpw' hPd' hPdl'' hab hnd hsp1' hsp2' (by omega)
            hb3 hR' (hA' _ (w_le_upLA hpr he5 hw5))
      · -- an ordinary prime
        obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hpr hpq
        have hsp1' : sp = true → q ∈ insert e.p Pd := fun hs => Finset.mem_insert_of_mem (hsp1 hs)
        have hsp2' : sp = false → q ∉ insert e.p Pd ∧
            (q ∈ l.map URec.p ∨ ((∀ e' ∈ l, e'.p < q) ∧ 71 ≤ q)) := by
          intro hs
          obtain ⟨hqP, hor⟩ := hsp2 hs
          refine ⟨fun hm => ?_, ?_⟩
          · rcases Finset.mem_insert.mp hm with hm | hm
            · exact hpq hm.symm
            · exact hqP hm
          · rcases hor with hm | ⟨hall, h71⟩
            · rcases List.mem_cons.mp hm with hm | hm
              · exact absurd hm.symm hpq
              · exact Or.inl hm
            · exact Or.inr ⟨fun e' he' => hall e' (List.mem_cons_of_mem _ he'), h71⟩
        rcases (show N.factorization e.p = 2 ∨ 4 ≤ N.factorization e.p by omega) with he2 | he4
        · have hfS : ∀ x ∈ e.f2, x ∈ N.primeFactors := by
            intro x hx
            obtain ⟨hxp, hx2, hxd⟩ := hf2 x hx
            refine mem_pf h hxp (OPNStarter.force_prime h.perfect hpr he2 hxp hx2 ?_)
            rw [sigma_pow_eq hpr]
            simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc, sq] using hxd
          have hc3 : e.v2 ≤ upC3 N e.p := by
            refine c3_ge hpr he2 ?_
            rw [sigma_pow_eq hpr]
            simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc, sq] using hv2
          simp only [List.any_eq_true, Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq,
            beq_iff_eq] at h2a
          rcases h2a with (⟨x, hx, hxm⟩ | ⟨hb, hlt2⟩) | hrec
          · rcases hxm with hxm | hxm
            · exact absurd (hfS x hx) (hab x hxm)
            · exact absurd (hfS x hx) (hexc x hxm)
          · have h32 : N.factorization 3 = 2 := by
              rcases hb with hb | hb
              · exact hb3 hb
              · rw [← hb]; exact he2
            omega
          · refine ih _ _ _ _ _ _ _ _ hrec hok' hpw' hPd' hPdl'' hab ?_ hsp1' hsp2' (by omega)
              ?_ hR' (hA' _ (w_le_upLA hpr (by omega) hw2))
            · intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hfS x hx
              · exact hnd x hx
            · intro hb
              simp only [Bool.or_eq_true, beq_iff_eq] at hb
              rcases hb with hb | hb
              · exact hb3 hb
              · rw [← hb]; exact he2
        · exact ih _ _ _ _ _ _ _ _ h2b hok' hpw' hPd' hPdl'' hab hnd hsp1' hsp2' (by omega)
            hb3 hR' (hA' _ (w_le_upLA hpr he4 hw4))
    · -- `e.p` does not divide `N`
      rw [List.filter_cons_of_neg (by simpa using hpS)] at hval
      have hnr : e.p ∉ req := fun hm => hpS (hreq _ hm)
      have hnn : e.p ∉ nd := fun hm => hpS (hnd _ hm)
      simp only [List.contains_iff_mem, hnr, hnn, false_or] at h1
      refine ih _ _ _ _ _ _ _ _ h1 hok' hpw' hPd hPdl' ?_ hnd hsp1 ?_ hval hb3 hR hA
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hpS
        · exact hab x hx
      · intro hs
        obtain ⟨hqP, hor⟩ := hsp2 hs
        refine ⟨hqP, ?_⟩
        rcases hor with hm | ⟨hall, h71⟩
        · rcases List.mem_cons.mp hm with hm | hm
          · exact absurd (hm ▸ (sum_inv_mem_q h hq hodd)) hpS
          · exact Or.inl hm
        · exact Or.inr ⟨fun e' he' => hall e' (List.mem_cons_of_mem _ he'), h71⟩

private theorem head_c3_le (h : OddPerfect N) :
    (((upTable.map URec.p).filter (· ∈ N.primeFactors)).map (upC3 N)).sum ≤
      N.factorization 3 := by
  set L := (upTable.map URec.p).filter (· ∈ N.primeFactors)
  have hnd : L.Nodup := (upHead_ok.1.imp (fun h => ne_of_lt h)).filter _
  have hsub : L.toFinset ⊆ N.primeFactors := by
    intro x hx
    simpa [L] using (List.mem_filter.mp (List.mem_toFinset.mp hx)).2
  have hbal := OPNStarter.valuation_balance h.perfect 3
  have h20 : (Nat.factorization 2) 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [h20, zero_add] at hbal
  rw [← List.sum_toFinset _ hnd, hbal]
  exact Finset.sum_le_sum_of_subset hsub

/-- The transfer: a passed check for the threshold `t / 10^15` and the case lists `req` (primes
that divide `N`) and `exc` (primes that do not divide `N`) gives `∑_{p ∣ N} 1/p < t / 10^15`. -/
private theorem sum_inv_lt_of_upChk (h : OddPerfect N) (t : ℕ) (req exc : List ℕ)
    (hreq : ∀ x ∈ req, x ∈ N.primeFactors) (hexc : ∀ x ∈ exc, x ∉ N.primeFactors)
    (hc : upChk t req exc upTable 0 0 false [] [] 0 false = true) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < (t : ℝ) / 1000000000000000 := by
  obtain ⟨q, hq, -, hq4, hk4, -⟩ := exists_special_prime h
  have hodd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
  obtain ⟨hpw, hcov, hall⟩ := upHead_ok
  have hok : ∀ e ∈ upTable, upRecOk e = true := List.all_eq_true.mp upTable_ok
  refine upChk_sound h hq hodd hq4 t req exc hreq hexc upTable 0 0 false [] [] 0 false ∅ hc hok
    hpw (Finset.empty_subset _) (fun _ _ => Finset.notMem_empty _) (by simp) (by simp)
    (by simp) (fun _ => ⟨Finset.notMem_empty _, ?_⟩) (by simpa using head_c3_le h) (by simp)
    (by simp) (by simp)
  by_cases h71 : q < 71
  · exact Or.inl (mem_of_coverCheck hcov h71 hq (by omega))
  · refine Or.inr ⟨fun e he => ?_, by omega⟩
    have := List.all_eq_true.mp hall e.p (List.mem_map_of_mem he)
    simp only [decide_eq_true_eq] at this
    omega

/-- For an odd perfect number divisible by `3` and by `5`, `∑_{p ∣ N} 1/p < 0.673634`. -/
theorem sum_inv_lt_673634_of_three_five (h : OddPerfect N) (h3 : 3 ∣ N) (h5 : 5 ∣ N) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < 673634 / 1000000 := by
  have := sum_inv_lt_of_upChk h 673634000000000 [3, 5] [7]
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact mem_pf h Nat.prime_three h3
      · exact mem_pf h Nat.prime_five h5)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact fun hm => not_seven_dvd_of_three_five h h3 h5 (Nat.dvd_of_mem_primeFactors hm))
    upChk_three_five
  norm_num at this ⊢
  linarith

/-- For an odd perfect number divisible by `3` and not by `5`, `∑_{p ∣ N} 1/p < 0.657304`. -/
theorem sum_inv_lt_657304_of_three_not_five (h : OddPerfect N) (h3 : 3 ∣ N) (h5 : ¬ 5 ∣ N) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < 657304 / 1000000 := by
  have := sum_inv_lt_of_upChk h 657304000000000 [3] [5]
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact mem_pf h Nat.prime_three h3)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact fun hm => h5 (Nat.dvd_of_mem_primeFactors hm))
    upChk_three_not_five
  norm_num at this ⊢
  linarith

/-- For an odd perfect number divisible by `5` and not by `3`, `∑_{p ∣ N} 1/p < 0.677637`. -/
theorem sum_inv_lt_677637_of_five_not_three (h : OddPerfect N) (h3 : ¬ 3 ∣ N) (h5 : 5 ∣ N) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < 677637 / 1000000 := by
  have := sum_inv_lt_of_upChk h 677637000000000 [5] [3]
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact mem_pf h Nat.prime_five h5)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact fun hm => h3 (Nat.dvd_of_mem_primeFactors hm))
    upChk_five_not_three
  norm_num at this ⊢
  linarith

/-- For an odd perfect number divisible by `3` or by `5`, `∑_{p ∣ N} 1/p < 0.677637`. -/
theorem sum_inv_lt_677637_of_three_or_five (h : OddPerfect N) (h35 : 3 ∣ N ∨ 5 ∣ N) :
    ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < 677637 / 1000000 := by
  by_cases h3 : 3 ∣ N <;> by_cases h5 : 5 ∣ N
  · have := sum_inv_lt_673634_of_three_five h h3 h5
    linarith
  · have := sum_inv_lt_657304_of_three_not_five h h3 h5
    linarith
  · exact sum_inv_lt_677637_of_five_not_three h h3 h5
  · exact absurd h35 (by tauto)

/-- If `∑_{p ∣ N} 1/p ≥ 0.677637` for an odd perfect number `N`, then neither `3` nor `5`
divides `N`. -/
theorem not_three_not_five_of_le_sum_inv (h : OddPerfect N)
    (hs : (677637 / 1000000 : ℝ) ≤ ∑ p ∈ N.primeFactors, 1 / (p : ℝ)) : ¬ 3 ∣ N ∧ ¬ 5 ∣ N := by
  by_contra hc
  have := sum_inv_lt_677637_of_three_or_five h (by tauto)
  linarith

/-- The window for `15 ∣ N`: `0.5960631 < ∑_{p ∣ N} 1/p < 0.673634`. -/
theorem sum_inv_window_three_five (h : OddPerfect N) (h3 : 3 ∣ N) (h5 : 5 ∣ N) :
    (5960631 / 10000000 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) ∧
      ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < 673634 / 1000000 :=
  ⟨sum_inv_gt_5960631_of_three_five h h3 h5, sum_inv_lt_673634_of_three_five h h3 h5⟩

/-- The window for `3 ∣ N`, `5 ∤ N`: `0.604706 < ∑_{p ∣ N} 1/p < 0.657304`. -/
theorem sum_inv_window_three_not_five (h : OddPerfect N) (h3 : 3 ∣ N) (h5 : ¬ 5 ∣ N) :
    (604706 / 1000000 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) ∧
      ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < 657304 / 1000000 :=
  ⟨sum_inv_gt_604706_of_three_not_five h h3 h5, sum_inv_lt_657304_of_three_not_five h h3 h5⟩

/-- The window for `5 ∣ N`, `3 ∤ N`: `0.647648 < ∑_{p ∣ N} 1/p < 0.677637`. -/
theorem sum_inv_window_five_not_three (h : OddPerfect N) (h3 : ¬ 3 ∣ N) (h5 : 5 ∣ N) :
    (647648 / 1000000 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) ∧
      ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < 677637 / 1000000 :=
  ⟨sum_inv_gt_647648_of_five_not_three h h3 h5, sum_inv_lt_677637_of_five_not_three h h3 h5⟩

/-- The window for `3 ∤ N`, `5 ∤ N`: `0.667363 < ∑_{p ∣ N} 1/p < log 2`. The upper end is the
landed bound `sum_inv_lt_log_two`; the check of this file gives no bound below `log 2` here. -/
theorem sum_inv_window_not_three_not_five (h : OddPerfect N) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) :
    (667363 / 1000000 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) ∧
      ∑ p ∈ N.primeFactors, 1 / (p : ℝ) < Real.log 2 :=
  ⟨sum_inv_gt_667363_of_not_three_not_five h h3 h5, sum_inv_lt_log_two h⟩

end OddPerfect

#print axioms OddPerfect.sum_inv_lt_673634_of_three_five
#print axioms OddPerfect.sum_inv_lt_657304_of_three_not_five
#print axioms OddPerfect.sum_inv_lt_677637_of_five_not_three
#print axioms OddPerfect.sum_inv_lt_677637_of_three_or_five
#print axioms OddPerfect.not_three_not_five_of_le_sum_inv
#print axioms OddPerfect.sum_inv_window_three_five
#print axioms OddPerfect.sum_inv_window_three_not_five
#print axioms OddPerfect.sum_inv_window_five_not_three
#print axioms OddPerfect.sum_inv_window_not_three_not_five
