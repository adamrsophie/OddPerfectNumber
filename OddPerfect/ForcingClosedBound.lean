import OddPerfect.ForcingClosed
import OddPerfect.Pratt
import OddPerfect.Cyclotomic

/-!
# Forcing closed configurations have a large node

A greatest fixed point computation, rerun by the kernel. Start from the odd primes up to `P0`
and repeatedly delete every prime `p` that has no move inside the current list `A`:

* a special move: `p % 4 = 1` and every prime factor of `p + 1` divides `2 * A.prod`;
* an ordinary move: an odd prime `l` with `2 * l + 1 ≤ P0` such that every prime factor of
  `(p ^ l - 1) / (p - 1) = σ(p ^ (l - 1))` divides `2 * A.prod`.

Smoothness is tested exactly through `n ∣ M ^ K` with an explicit `n < 2 ^ K` (`K = p + 1` for
the special move, `K = p * l` for a row), by fast modular exponentiation.
By `ForcingClosed.reduce`, the support of a forcing closed configuration whose nodes are all
at most `P0` survives every round, so it is empty once the iteration reaches `[]`.

* `exists_gt_of_iterate`: the general criterion, for any `P0` and number of rounds.
* `ForcingClosed.exists_gt`: every forcing closed configuration has a node above `1000`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace ForcingClosedBound

/-- Exact smoothness test with an exponent `K`: `true` iff `n ∣ M ^ K`. Used with `n < 2 ^ K`,
where it accepts exactly the `n` whose prime factors all divide `M`. -/
def smoothB (M n K : ℕ) : Bool := Pratt.powMod M K n == 0

/-- If `n < 2 ^ K` and every prime factor of `n ≠ 0` divides `M`, then `n ∣ M ^ K`. -/
theorem dvd_pow_of_lt {n M K : ℕ} (hn : n ≠ 0) (hK : n < 2 ^ K)
    (h : ∀ r ∈ n.primeFactors, r ∣ M) : n ∣ M ^ K := by
  have hK0 : K ≠ 0 := by rintro rfl; simp at hK; omega
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · rw [zero_pow hK0]; exact dvd_zero n
  rw [← Nat.factorization_le_iff_dvd hn (pow_ne_zero _ hM.ne')]
  intro r
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hr : r ∈ n.primeFactors
  · have hrp := Nat.prime_of_mem_primeFactors hr
    have h1 : 1 ≤ M.factorization r :=
      (hrp.dvd_iff_one_le_factorization hM.ne').mp (h r hr)
    have h2 : n.factorization r < K := by
      have h21 := Nat.ordProj_le r hn
      have h22 : 2 ^ n.factorization r ≤ n :=
        le_trans (Nat.pow_le_pow_left hrp.two_le _) h21
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt h22 hK)
    nlinarith
  · have : n.factorization r = 0 := by
      rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]
    rw [this]; exact Nat.zero_le _

/-- Completeness of `smoothB`: it accepts every `n ≠ 0` with `n < 2 ^ K` whose prime factors
divide `M`. -/
theorem smoothB_eq_true {n M K : ℕ} (hn : n ≠ 0) (hK : n < 2 ^ K)
    (h : ∀ r ∈ n.primeFactors, r ∣ M) : smoothB M n K = true := by
  unfold smoothB
  rw [Pratt.powMod_eq, beq_iff_eq]
  exact Nat.mod_eq_zero_of_dvd (dvd_pow_of_lt hn hK h)

/-- A cheap filter passed by every prime: no `d` with `2 ≤ d ≤ 31` and `d < q` divides `q`.
Below `1024` it passes exactly the primes `q ≥ 2`; above, it may also pass composites, which
costs nothing for soundness. -/
def smallSieveB (q : ℕ) : Bool := (List.range' 2 30).all fun d => q ≤ d || q % d != 0

/-- Every prime passes `smallSieveB`. -/
theorem smallSieveB_of_prime {q : ℕ} (hq : q.Prime) : smallSieveB q = true := by
  simp only [smallSieveB, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq]
  intro d hd
  by_cases hqd : q ≤ d
  · exact Or.inl hqd
  · right
    intro h0
    rcases hq.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega

/-- Candidate ordinary lengths: every odd prime `l` with `2 * l + 1 ≤ P0` is in this list. -/
def lengths (P0 : ℕ) : List ℕ := (List.range' 3 ((P0 - 1) / 2 - 2)).filter smallSieveB

/-- Does `p` have a move inside a list with product data `M = 2 * A.prod`? -/
def keepB (M : ℕ) (Ls : List ℕ) (p : ℕ) : Bool :=
  (p % 4 == 1 && smoothB M (p + 1) (p + 1)) ||
    Ls.any fun l => smoothB M ((p ^ l - 1) / (p - 1)) (p * l)

/-- One round: delete every prime of `A` without a move inside `A`. -/
def step (P0 : ℕ) (A : List ℕ) : List ℕ := A.filter (keepB (2 * A.prod) (lengths P0))

/-- A round evaluated with its product and its lengths given as literals, so that the kernel
evaluates each of them once rather than once per test. -/
theorem step_eq {P0 M : ℕ} {A B Ls : List ℕ} (hL : lengths P0 = Ls) (hM : 2 * A.prod = M)
    (h : A.filter (keepB M Ls) = B) : step P0 A = B := by
  rw [step, hM, hL, h]

/-- The starting list: it contains every odd prime up to `P0`. -/
def initial (P0 : ℕ) : List ℕ := (List.range' 3 (P0 - 2)).filter smallSieveB

/-- `σ(p ^ a) = (p ^ (a + 1) - 1) / (p - 1)`. -/
theorem sigma_eq_div {p : ℕ} (hp : p.Prime) (a : ℕ) :
    σ 1 (p ^ a) = (p ^ (a + 1) - 1) / (p - 1) := by
  rw [← sigma_prime_pow_mul_pred hp a, Nat.mul_div_cancel _ (by have := hp.two_le; omega)]

variable {S : Finset ℕ} {e : ℕ → ℕ}

/-- **The criterion.** If the kernel iteration from the odd primes up to `P0` reaches `[]`,
then every forcing closed configuration has a node above `P0`. -/
theorem exists_gt_of_iterate {P0 k : ℕ} (hk : (step P0)^[k] (initial P0) = [])
    (hF : ForcingClosed S e) : ∃ s ∈ S, P0 < s := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  obtain ⟨q, hq, hq4, -, -, hR, hRq, hRord⟩ := hF.reduce
  set e' := ForcingClosed.reduceExp q e
  -- prime factors of a row divide `2 * A.prod` once the support lies in `A`
  have hdvdM : ∀ A : List ℕ, (∀ s ∈ S, s ∈ A) → ∀ s ∈ S,
      ∀ r ∈ (σ 1 (s ^ e' s)).primeFactors, r ∣ 2 * A.prod := by
    intro A hA s hs r hr
    by_cases hr2 : r = 2
    · rw [hr2]; exact dvd_mul_right 2 _
    · exact (List.dvd_prod (hA r (hR.2.2.1 s hs r hr hr2))).mul_left 2
  have hrow0 : ∀ s ∈ S, σ 1 (s ^ e' s) ≠ 0 := fun s hs =>
    (sigma_pos 1 _ (pow_ne_zero _ (hR.1 s hs).1.ne_zero)).ne'
  have hkeep : ∀ A : List ℕ, (∀ s ∈ S, s ∈ A) → ∀ s ∈ S,
      keepB (2 * A.prod) (lengths P0) s = true := by
    intro A hA s hs
    have hsp := (hR.1 s hs).1
    have hrow := sigma_eq_div hsp (e' s)
    unfold keepB
    rw [Bool.or_eq_true]
    by_cases hsq : s = q
    · left
      have hqp := (hR.1 q hq).1
      have h1 : σ 1 (q ^ e' q) = q + 1 := by
        rw [hRq, sigma_one_apply_prime_pow hqp]
        simp [Finset.sum_range_succ]
        ring
      rw [hsq, Bool.and_eq_true, beq_iff_eq]
      refine ⟨hq4, ?_⟩
      have hlt : σ 1 (q ^ e' q) < 2 ^ (q + 1) := by
        rw [h1]; exact Nat.lt_two_pow_self
      have := smoothB_eq_true (hrow0 q hq) hlt (hdvdM A hA q hq)
      rwa [h1] at this
    · right
      obtain ⟨hl, hl2⟩ := hRord s hs hsq
      have hl3 : 3 ≤ e' s + 1 := by have := hl.two_le; omega
      obtain ⟨r, hr, -, hmod⟩ := hR.exists_mem_mod_eq_one hs (by omega)
      obtain ⟨hrp, hr2, -⟩ := hR.1 r hr
      have hrle := hcon r hr
      -- `r ≡ 1 (mod l)` with `r` and `l` odd forces `2 * l + 1 ≤ r`
      have hlr : 2 * (e' s + 1) + 1 ≤ r := by
        have hd := Nat.div_add_mod r (e' s + 1)
        rw [hmod] at hd
        have hrodd : r % 2 = 1 := (hrp.eq_one_or_self_of_dvd 2 |> fun h =>
          by rcases Nat.even_or_odd r with ⟨t, ht⟩ | ⟨t, ht⟩
             · exact absurd (h ⟨t, by omega⟩) (by omega)
             · omega)
        have hlodd : (e' s + 1) % 2 = 1 := by
          rcases hl.eq_two_or_odd with h | h
          · exact absurd h hl2
          · exact h
        rcases Nat.lt_or_ge (r / (e' s + 1)) 2 with ht | ht
        · interval_cases ht' : r / (e' s + 1)
          · have := hrp.two_le; omega
          · omega
        · nlinarith
      rw [List.any_eq_true]
      refine ⟨e' s + 1, ?_, ?_⟩
      · unfold lengths
        rw [List.mem_filter, List.mem_range'_1]
        exact ⟨⟨by omega, by omega⟩, smallSieveB_of_prime hl⟩
      · rw [← hrow]
        -- `σ(s ^ a) ≤ s ^ (a + 1) - 1 < s ^ (a + 1) < (2 ^ s) ^ (a + 1)`
        have hlt : σ 1 (s ^ e' s) < 2 ^ (s * (e' s + 1)) := by
          rw [hrow, pow_mul]
          calc (s ^ (e' s + 1) - 1) / (s - 1) ≤ s ^ (e' s + 1) - 1 := Nat.div_le_self _ _
            _ < s ^ (e' s + 1) := Nat.sub_lt (Nat.pow_pos hsp.pos) Nat.one_pos
            _ ≤ (2 ^ s) ^ (e' s + 1) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
        exact smoothB_eq_true (hrow0 s hs) hlt (hdvdM A hA s hs)
  -- the support survives every round
  have hall : ∀ n, ∀ s ∈ S, s ∈ (step P0)^[n] (initial P0) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      obtain ⟨hsp, hs2, -⟩ := hR.1 s hs
      have := hsp.two_le
      have := hcon s hs
      simp only [Function.iterate_zero, id, initial, List.mem_filter, List.mem_range'_1]
      exact ⟨⟨by omega, by omega⟩, smallSieveB_of_prime hsp⟩
    | succ n ih =>
      intro s hs
      rw [Function.iterate_succ_apply', step, List.mem_filter]
      exact ⟨ih s hs, hkeep _ ih s hs⟩
  have := hall k q hq
  rw [hk] at this
  simp at this

/-- The odd primes `l` with `2 * l + 1 ≤ 1000`. -/
private lemma lengths_eq : lengths 1000 = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499] := by decide +kernel

/-- The odd primes up to `1000`. -/
private lemma initial_eq : initial 1000 = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997] := by decide +kernel

/-- Round 1 of the deletion. -/
private lemma round1 : step 1000 [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997] = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 73, 79, 83, 89, 97, 101, 107, 109, 113, 137, 139, 149, 157, 163, 173, 181, 191, 193, 197, 211, 227, 229, 233, 241, 257, 263, 269, 277, 281, 283, 293, 307, 313, 317, 337, 349, 353, 359, 373, 379, 389, 397, 401, 409, 421, 431, 433, 439, 449, 457, 461, 499, 509, 521, 541, 547, 557, 569, 571, 577, 587, 593, 601, 613, 617, 631, 641, 653, 661, 673, 677, 701, 709, 733, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 829, 853, 857, 877, 881, 919, 929, 937, 941, 947, 953, 971, 977, 991, 997] :=
  step_eq lengths_eq (by decide +kernel : 2 * List.prod [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997] = 19590340644999083431262508198206381046123972390589368223882605328968666316379870661851951648789482321596229559115436019149189529725215266728292282990852649023362731392404017939142010958261393634959471483757196721672243410067118516227661133135192488848989914892157188308679896875137439519338903968094905549750386407106033836586660683539201011635917900039904495065203299749542985993134669814805318474080581207891125910)
    (by decide +kernel)

/-- Round 2 of the deletion. -/
private lemma round2 : step 1000 [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 73, 79, 83, 89, 97, 101, 107, 109, 113, 137, 139, 149, 157, 163, 173, 181, 191, 193, 197, 211, 227, 229, 233, 241, 257, 263, 269, 277, 281, 283, 293, 307, 313, 317, 337, 349, 353, 359, 373, 379, 389, 397, 401, 409, 421, 431, 433, 439, 449, 457, 461, 499, 509, 521, 541, 547, 557, 569, 571, 577, 587, 593, 601, 613, 617, 631, 641, 653, 661, 673, 677, 701, 709, 733, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 829, 853, 857, 877, 881, 919, 929, 937, 941, 947, 953, 971, 977, 991, 997] = [3, 5, 7, 11, 13, 17, 23, 29, 37, 41, 43, 47, 53, 61, 67, 73, 79, 89, 97, 101, 109, 113, 137, 139, 149, 157, 163, 173, 181, 191, 193, 197, 211, 227, 229, 233, 241, 257, 263, 269, 277, 281, 293, 307, 313, 317, 337, 349, 353, 359, 373, 379, 389, 401, 409, 421, 431, 433, 439, 449, 457, 461, 499, 509, 521, 547, 557, 569, 577, 587, 593, 601, 613, 631, 641, 653, 673, 677, 701, 757, 769, 773, 797, 809, 811, 821, 829, 853, 857, 877, 881, 919, 929, 937, 941, 953, 971, 977, 991, 997] :=
  step_eq lengths_eq (by decide +kernel : 2 * List.prod [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 73, 79, 83, 89, 97, 101, 107, 109, 113, 137, 139, 149, 157, 163, 173, 181, 191, 193, 197, 211, 227, 229, 233, 241, 257, 263, 269, 277, 281, 283, 293, 307, 313, 317, 337, 349, 353, 359, 373, 379, 389, 397, 401, 409, 421, 431, 433, 439, 449, 457, 461, 499, 509, 521, 541, 547, 557, 569, 571, 577, 587, 593, 601, 613, 617, 631, 641, 653, 661, 673, 677, 701, 709, 733, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 829, 853, 857, 877, 881, 919, 929, 937, 941, 947, 953, 971, 977, 991, 997] = 7282831500618250073232202526640558210775194449508892103239518531835162241499984246708512680864257849848258605285047787624727891851244674249605879117430106917295046914596961361809561441729343410180168782559298726866158626838625239231735643469293374612238515941895629904525380105032670)
    (by decide +kernel)

/-- Round 3 of the deletion. -/
private lemma round3 : step 1000 [3, 5, 7, 11, 13, 17, 23, 29, 37, 41, 43, 47, 53, 61, 67, 73, 79, 89, 97, 101, 109, 113, 137, 139, 149, 157, 163, 173, 181, 191, 193, 197, 211, 227, 229, 233, 241, 257, 263, 269, 277, 281, 293, 307, 313, 317, 337, 349, 353, 359, 373, 379, 389, 401, 409, 421, 431, 433, 439, 449, 457, 461, 499, 509, 521, 547, 557, 569, 577, 587, 593, 601, 613, 631, 641, 653, 673, 677, 701, 757, 769, 773, 797, 809, 811, 821, 829, 853, 857, 877, 881, 919, 929, 937, 941, 953, 971, 977, 991, 997] = [3, 5, 13, 17, 23, 29, 37, 41, 43, 47, 53, 61, 73, 79, 89, 97, 101, 109, 113, 137, 139, 149, 157, 173, 181, 193, 197, 229, 233, 241, 257, 263, 269, 277, 281, 293, 313, 317, 337, 349, 359, 373, 389, 401, 409, 421, 449, 457, 461, 499, 509, 521, 547, 577, 587, 593, 601, 613, 631, 653, 673, 677, 701, 757, 769, 773, 809, 821, 853, 857, 877, 881, 937, 941, 953, 971, 977, 991, 997] :=
  step_eq lengths_eq (by decide +kernel : 2 * List.prod [3, 5, 7, 11, 13, 17, 23, 29, 37, 41, 43, 47, 53, 61, 67, 73, 79, 89, 97, 101, 109, 113, 137, 139, 149, 157, 163, 173, 181, 191, 193, 197, 211, 227, 229, 233, 241, 257, 263, 269, 277, 281, 293, 307, 313, 317, 337, 349, 353, 359, 373, 379, 389, 401, 409, 421, 431, 433, 439, 449, 457, 461, 499, 509, 521, 547, 557, 569, 577, 587, 593, 601, 613, 631, 641, 653, 673, 677, 701, 757, 769, 773, 797, 809, 811, 821, 829, 853, 857, 877, 881, 919, 929, 937, 941, 953, 971, 977, 991, 997] = 6872499757459587002017800595668618037757485019846829611248749984805409180219783051807570326930102444515055005459109829676992398068095422308302749058627079182367611287334086900037871691643010078972657756678435595993396110359008742244410925990)
    (by decide +kernel)

/-- Round 4 of the deletion. -/
private lemma round4 : step 1000 [3, 5, 13, 17, 23, 29, 37, 41, 43, 47, 53, 61, 73, 79, 89, 97, 101, 109, 113, 137, 139, 149, 157, 173, 181, 193, 197, 229, 233, 241, 257, 263, 269, 277, 281, 293, 313, 317, 337, 349, 359, 373, 389, 401, 409, 421, 449, 457, 461, 499, 509, 521, 547, 577, 587, 593, 601, 613, 631, 653, 673, 677, 701, 757, 769, 773, 809, 821, 853, 857, 877, 881, 937, 941, 953, 971, 977, 991, 997] = [3, 5, 13, 17, 29, 43, 47, 53, 61, 73, 89, 101, 113, 137, 139, 149, 157, 173, 181, 193, 229, 233, 257, 269, 277, 281, 313, 317, 337, 389, 409, 449, 457, 509, 521, 577, 587, 653, 673, 677, 701, 773, 809, 821, 941, 953, 997] :=
  step_eq lengths_eq (by decide +kernel : 2 * List.prod [3, 5, 13, 17, 23, 29, 37, 41, 43, 47, 53, 61, 73, 79, 89, 97, 101, 109, 113, 137, 139, 149, 157, 173, 181, 193, 197, 229, 233, 241, 257, 263, 269, 277, 281, 293, 313, 317, 337, 349, 359, 373, 389, 401, 409, 421, 449, 457, 461, 499, 509, 521, 547, 577, 587, 593, 601, 613, 631, 653, 673, 677, 701, 757, 769, 773, 809, 821, 853, 857, 877, 881, 937, 941, 953, 971, 977, 991, 997] = 2856587430962482903795895201407012498912219832282020379901904523369087645850521716900311739884221225404267439671107974043447887138907336441407594320350941843555307861028901875757278763547330)
    (by decide +kernel)

/-- Round 5 of the deletion. -/
private lemma round5 : step 1000 [3, 5, 13, 17, 29, 43, 47, 53, 61, 73, 89, 101, 113, 137, 139, 149, 157, 173, 181, 193, 229, 233, 257, 269, 277, 281, 313, 317, 337, 389, 409, 449, 457, 509, 521, 577, 587, 653, 673, 677, 701, 773, 809, 821, 941, 953, 997] = [3, 5, 13, 17, 29, 53, 89, 101, 149, 173, 233, 257, 269, 277, 281, 313, 317, 337, 389, 449, 457, 509, 521, 577, 673, 677, 701, 773, 809, 821, 941, 953] :=
  step_eq lengths_eq (by decide +kernel : 2 * List.prod [3, 5, 13, 17, 29, 43, 47, 53, 61, 73, 89, 101, 113, 137, 139, 149, 157, 173, 181, 193, 229, 233, 257, 269, 277, 281, 313, 317, 337, 389, 409, 449, 457, 509, 521, 577, 587, 653, 673, 677, 701, 773, 809, 821, 941, 953, 997] = 675903285681571578775354290664379444683693927117101994474984216773697104786836474029038974560493718898062870)
    (by decide +kernel)

/-- Round 6 of the deletion. -/
private lemma round6 : step 1000 [3, 5, 13, 17, 29, 53, 89, 101, 149, 173, 233, 257, 269, 277, 281, 313, 317, 337, 389, 449, 457, 509, 521, 577, 673, 677, 701, 773, 809, 821, 941, 953] = [3, 5, 17, 29, 53, 89, 101, 149, 173, 233, 269, 317, 337, 389, 449, 509, 521, 577, 673, 701, 809, 953] :=
  step_eq lengths_eq (by decide +kernel : 2 * List.prod [3, 5, 13, 17, 29, 53, 89, 101, 149, 173, 233, 257, 269, 277, 281, 313, 317, 337, 389, 449, 457, 509, 521, 577, 673, 677, 701, 773, 809, 821, 941, 953] = 177791490417225277590983483619460832847300773712111717010762079107712097630)
    (by decide +kernel)

/-- Round 7 of the deletion. -/
private lemma round7 : step 1000 [3, 5, 17, 29, 53, 89, 101, 149, 173, 233, 269, 317, 337, 389, 449, 509, 521, 577, 673, 701, 809, 953] = [5, 17, 29, 53, 89, 101, 149, 173, 269, 317, 449, 509, 521, 577, 673, 809, 953] :=
  step_eq lengths_eq (by decide +kernel : 2 * List.prod [3, 5, 17, 29, 53, 89, 101, 149, 173, 233, 269, 317, 337, 389, 449, 509, 521, 577, 673, 701, 809, 953] = 11821890305579130144359446559195326607815339846590)
    (by decide +kernel)

/-- Round 8 of the deletion. -/
private lemma round8 : step 1000 [5, 17, 29, 53, 89, 101, 149, 173, 269, 317, 449, 509, 521, 577, 673, 809, 953] = [577] :=
  step_eq lengths_eq (by decide +kernel : 2 * List.prod [5, 17, 29, 53, 89, 101, 149, 173, 269, 317, 449, 509, 521, 577, 673, 809, 953] = 184040002010336542283469799148691393370)
    (by decide +kernel)

/-- Round 9 of the deletion. -/
private lemma round9 : step 1000 [577] = [] :=
  step_eq lengths_eq (by decide +kernel : 2 * List.prod [577] = 1154)
    (by decide +kernel)

/-- The deletion from the odd primes up to `1000` empties in 9 rounds. -/
private lemma iterate_eq : (step 1000)^[9] (initial 1000) = [] := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id, initial_eq, round1, round2, round3, round4, round5, round6, round7, round8, round9]


end ForcingClosedBound

/-- **No small forcing closed configuration.** Every forcing closed configuration has a node
above `1000`. Kernel checked, one round per lemma: the deletion rounds from the odd primes
up to `1000` reach `[]` after nine rounds. -/
theorem ForcingClosed.exists_gt {S : Finset ℕ} {e : ℕ → ℕ} (hF : ForcingClosed S e) :
    ∃ s ∈ S, 1000 < s :=
  ForcingClosedBound.exists_gt_of_iterate ForcingClosedBound.iterate_eq hF

end OddPerfect

#print axioms OddPerfect.ForcingClosedBound.dvd_pow_of_lt
#print axioms OddPerfect.ForcingClosedBound.smoothB_eq_true
#print axioms OddPerfect.ForcingClosedBound.smallSieveB_of_prime
#print axioms OddPerfect.ForcingClosedBound.sigma_eq_div
#print axioms OddPerfect.ForcingClosedBound.step_eq
#print axioms OddPerfect.ForcingClosedBound.exists_gt_of_iterate
#print axioms OddPerfect.ForcingClosed.exists_gt
