import OddPerfect.Euler
import OddPerfect.Seed.Example
import OddPerfect.Seed.Starter
import OddPerfect.Pratt
import OddPerfect.OmegaFive
import OddPerfect.SmallestPrime
import Mathlib

/-!
# A kernel checked lower bound for odd perfect numbers

The method is the classical one of factor chains (Kanold, Hagis, Brent and Cohen), organized as
a proof tree whose leaves either reach a contradiction or show `L < N` for the target `L`.

A state is a list of facts about the unknown odd perfect number `N`: lower bounds on prime
powers, divisors of `e + 1` where `e` is an exponent, exact exponents, and excluded primes.
The tree is flattened into a list of instructions, run on a stack of states by `run`. Each
instruction pops a state and pushes the states of its children; leaves push nothing.

The main leaf rule `big` uses two divisors of `N` that need no factorization: the least common
multiple of the recorded prime powers, and the product `∏ σ(p ^ a)` over components with
`a + 1 ∣ e + 1`, which divides `σ(N) = 2 N` (halved if even).
-/

set_option Elab.async false

namespace OddPerfect.LowerBound

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ## Facts and states -/

/-- A statement about the unknown number `N`; every variant except `nd` records a prime. -/
inductive Fact where
  /-- `p` is prime and `p ^ e ∣ N`. -/
  | pw (p e : ℕ)
  /-- `p` is prime and `d ∣ N.factorization p + 1`. -/
  | dv (p d : ℕ)
  /-- `p` is prime and `N.factorization p = e`. -/
  | ex (p e : ℕ)
  /-- `¬ p ∣ N`. -/
  | nd (p : ℕ)

/-- The meaning of a fact. -/
def Fact.Holds (N : ℕ) : Fact → Prop
  | .pw p e => p.Prime ∧ p ^ e ∣ N
  | .dv p d => p.Prime ∧ d ∣ N.factorization p + 1
  | .ex p e => p.Prime ∧ N.factorization p = e
  | .nd p => ¬ p ∣ N

/-- A state holds for `N` when each of its facts does. -/
def Holds (N : ℕ) (s : List Fact) : Prop := ∀ f ∈ s, f.Holds N

/-- The prime a fact is about. -/
def Fact.prime : Fact → ℕ
  | .pw p _ => p
  | .dv p _ => p
  | .ex p _ => p
  | .nd p => p

/-! ## Computable helpers -/

/-- The fact gives `p ^ e ∣ N`. -/
def lowP (p e : ℕ) : Fact → Bool
  | .pw q e' => Nat.beq q p && Nat.ble e e'
  | .dv q d => Nat.beq q p && Nat.ble (e + 1) d
  | .ex q e' => Nat.beq q p && Nat.ble e e'
  | .nd _ => false

/-- The state gives `p ^ e ∣ N` with `p` prime. -/
def hasPow (s : List Fact) (p e : ℕ) : Bool := s.any (lowP p e)

/-- The fact gives `a + 1 ∣ N.factorization p + 1`. -/
def compP (p a : ℕ) : Fact → Bool
  | .ex q e => Nat.beq q p && Nat.beq ((e + 1) % (a + 1)) 0
  | .dv q d => Nat.beq q p && Nat.beq (d % (a + 1)) 0
  | _ => false

/-- The fact says that the exponent of its prime is odd. -/
def oddP : Fact → Bool
  | .ex _ e => Nat.beq (e % 2) 1
  | .dv _ d => Nat.beq (d % 2) 0
  | _ => false

/-- The fact excludes the exponent class `1 mod 4` at `p`. -/
def bad4 (p : ℕ) : Fact → Bool
  | .ex q e => Nat.beq q p && !Nat.beq (e % 4) 1
  | .dv q d => Nat.beq q p && Nat.beq (d % 4) 0
  | _ => false

/-- The fact is `dv p d`. -/
def isDv (p d : ℕ) : Fact → Bool
  | .dv q d' => Nat.beq q p && Nat.beq d' d
  | _ => false

/-- The fact is `ex p e`. -/
def isEx (p e : ℕ) : Fact → Bool
  | .ex q e' => Nat.beq q p && Nat.beq e' e
  | _ => false

/-- The fact is `nd p`. -/
def isNd (p : ℕ) : Fact → Bool
  | .nd q => Nat.beq q p
  | _ => false

/-- `gs p a = 1 + p + ⋯ + p ^ a` for `p ≥ 2`. -/
def gs (p a : ℕ) : ℕ := (p ^ (a + 1) - 1) / (p - 1)

/-- The product of `gs p a` over a list of components. -/
def Dv : List (ℕ × ℕ) → ℕ
  | [] => 1
  | c :: l => gs c.1 c.2 * Dv l

/-- No repetitions. -/
def nodupB : List ℕ → Bool
  | [] => true
  | x :: l => l.all (fun y => !Nat.beq y x) && nodupB l

/-- The components `(p, a)` have distinct primes and satisfy `a + 1 ∣ e_p + 1`. -/
def compsOK (s : List Fact) (cs : List (ℕ × ℕ)) : Bool :=
  nodupB (cs.map Prod.fst) && cs.all (fun c => s.any (compP c.1 c.2))

/-- Halve an even number. -/
def half (D : ℕ) : ℕ := if D % 2 = 0 then D / 2 else D

/-- The prime power recorded by a fact. -/
def base : Fact → ℕ
  | .pw p e => p ^ e
  | .dv p d => p ^ (d - 1)
  | .ex p e => p ^ e
  | .nd _ => 1

/-- The least common multiple of the recorded prime powers. -/
def Av : List Fact → ℕ
  | [] => 1
  | f :: l => Nat.lcm (base f) (Av l)

/-- `∏ p ^ e` over a list of pairs. -/
def dprod : List (ℕ × ℕ) → ℕ
  | [] => 1
  | c :: l => c.1 ^ c.2 * dprod l

/-- `∏ gs p e` over a list of pairs. -/
def sprod : List (ℕ × ℕ) → ℕ
  | [] => 1
  | c :: l => gs c.1 c.2 * sprod l

/-- Trial division by `d, d + 1, …` while `d * d ≤ n`. -/
def tdAux (n : ℕ) : ℕ → ℕ → Bool
  | 0, d => Nat.blt n (d * d)
  | fuel + 1, d => Nat.blt n (d * d) || (!Nat.beq (n % d) 0 && tdAux n fuel (d + 1))

/-- Trial division primality test up to the square root. -/
def tdPrime (n : ℕ) : Bool := Nat.ble 2 n && tdAux n n 2

/-- A table of primes with Pratt data, stored as a binary search tree keyed by the prime. -/
inductive PT where
  /-- The empty table. -/
  | leaf
  /-- A node for `p` with a witness `a` and the factorization `fs` of `p - 1` as pairs
  `(prime, exponent)`. -/
  | node (l : PT) (p a : ℕ) (fs : List (ℕ × ℕ)) (r : PT)

/-- Lookup of a key in the table. -/
def PT.mem : PT → ℕ → Bool
  | .leaf, _ => false
  | .node l p _ _ r, q => if Nat.blt q p then l.mem q else if Nat.blt p q then r.mem q else true

/-- `∏ f ^ k` over a list of pairs `(f, k)`. -/
def ppow : List (ℕ × ℕ) → ℕ
  | [] => 1
  | c :: l => c.1 ^ c.2 * ppow l

/-- Binary modular exponentiation with fuel: `acc * b ^ e % n` when `e < fuel`. -/
def pm (n : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc % n
  | fuel + 1, b, e, acc =>
    cond (Nat.beq e 0) (acc % n)
      (pm n fuel (b * b % n) (e / 2) (cond (Nat.beq (e % 2) 1) (acc * b % n) acc))

/-- The Lucas condition for one entry: `p > 1`, `p - 1 = ∏ f ^ k`, `a ^ (p - 1) ≡ 1`, and for
each `f`: `f < p`, `f` is in the table `T` or passes trial division, and
`a ^ ((p - 1) / f) ≢ 1 (mod p)`. -/
def entryOK (T : PT) (p a : ℕ) (fs : List (ℕ × ℕ)) : Bool :=
  Nat.blt 1 p && Nat.beq (ppow fs) (p - 1) && Nat.beq (pm p p a (p - 1) 1) 1 &&
    fs.all (fun c => Nat.blt c.1 p && (T.mem c.1 || tdPrime c.1) &&
      !Nat.beq (pm p p a ((p - 1) / c.1) 1) 1)

/-- Every entry of a table passes `entryOK` against `T`. -/
def PT.allOK (T : PT) : PT → Bool
  | .leaf => true
  | .node l p a fs r => entryOK T p a fs && PT.allOK T l && PT.allOK T r

/-- The primes below `1000`, listed explicitly. -/
def smallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
  97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
  191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
  283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
  401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
  509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
  631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743,
  751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
  877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]
/-- The primes below `R`. -/
def primesBelow (R : ℕ) : List ℕ :=
  if Nat.ble R 1000 then smallPrimes.filter (fun r => Nat.blt r R)
  else (List.range R).filter tdPrime

/-! ## Instructions -/

/-- One instruction of a flattened proof tree. -/
inductive Ins where
  /-- Exponent split at `p`, given `d ∣ e + 1` (or `p ∣ N` when `d = 1`): either
  `e + 1 = d`, or `d r ∣ e + 1` for a prime `r < R`, or `p ^ (d R - 1) ∣ N`. -/
  | rs (p d R : ℕ)
  /-- Force `q ^ k ∣ N` from `q ^ k ∣ ∏ σ(p ^ a)` over the components `cs`; the prime `q`
  must be in the prime table. -/
  | force (q k : ℕ) (cs : List (ℕ × ℕ))
  /-- Raise an odd lower exponent `e` at an ordinary prime to `e + 1`. -/
  | up (p e : ℕ)
  /-- Leaf: the known divisor of `N` exceeds the target. -/
  | big (cs : List (ℕ × ℕ))
  /-- Leaf: `p ∣ N` against `¬ p ∣ N`. -/
  | ndc (p : ℕ)
  /-- Leaf: `q ^ (f + 1) ∣ ∏ σ(p ^ a)` against the exact exponent `f` at `q`. -/
  | ovf (q f : ℕ) (cs : List (ℕ × ℕ))
  /-- Leaf: two distinct primes with odd exponent. -/
  | par2 (p q : ℕ)
  /-- Leaf: an odd exponent at `p` that is not of Euler's form. -/
  | parS (p : ℕ)
  /-- Leaf: an abundant divisor. -/
  | abund (l : List (ℕ × ℕ))

/-- The child `e + 1 = d` of an exponent split, present when `d ≥ 2`. -/
def exKid (p d : ℕ) (s : List Fact) : List (List Fact) :=
  if 2 ≤ d then [.ex p (d - 1) :: s] else []

/-- One step: the children of a state, or `none` if the instruction does not apply. -/
def step (L : ℕ) (T : PT) : Ins → List Fact → Option (List (List Fact))
  | .rs p d R, s =>
    if (Nat.beq d 1 && hasPow s p 1) || (Nat.ble 2 d && s.any (isDv p d)) then
      some (exKid p d s ++
        ((primesBelow R).map fun r => .dv p (d * r) :: s) ++ [.pw p (d * R - 1) :: s])
    else none
  | .force q k cs, s =>
    if compsOK s cs && !Nat.beq q 2 && T.mem q && Nat.beq (Dv cs % q ^ k) 0 then
      some [.pw q k :: s]
    else none
  | .up p e, s =>
    if hasPow s p e && Nat.beq (e % 2) 1 && (Nat.beq (e % 4) 3 || !Nat.beq (p % 4) 1 ||
        s.any (fun f => !Nat.beq f.prime p && oddP f)) then
      some [.pw p (e + 1) :: s]
    else none
  | .big cs, s => if compsOK s cs && Nat.blt L (Nat.lcm (Av s) (half (Dv cs))) then some []
    else none
  | .ndc p, s => if hasPow s p 1 && s.any (isNd p) then some [] else none
  | .ovf q f cs, s =>
    if compsOK s cs && s.any (isEx q f) && !Nat.beq q 2 && Nat.beq (Dv cs % q ^ (f + 1)) 0 then
      some []
    else none
  | .par2 p q, s =>
    if !Nat.beq p q && s.any (fun f => Nat.beq f.prime p && oddP f) &&
        s.any (fun f => Nat.beq f.prime q && oddP f) then some [] else none
  | .parS p, s =>
    if s.any (fun f => Nat.beq f.prime p && oddP f) && (!Nat.beq (p % 4) 1 || s.any (bad4 p)) then
      some []
    else none
  | .abund l, s =>
    if nodupB (l.map Prod.fst) && l.all (fun c => hasPow s c.1 c.2) &&
        Nat.blt (2 * dprod l) (sprod l) then some [] else none

/-- Run a list of instructions on a stack of states. -/
def run (L : ℕ) (T : PT) : List Ins → List (List Fact) → Bool
  | [], stk => stk.isEmpty
  | _ :: _, [] => false
  | i :: is, s :: stk =>
    match step L T i s with
    | some cs => run L T is (cs ++ stk)
    | none => false

/-- A state is good for the target `L` when every odd perfect number satisfying it exceeds `L`. -/
def Good (L : ℕ) (s : List Fact) : Prop := ∀ N, OddPerfect N → Holds N s → L < N

/-! ## Soundness of the helpers -/

variable {N : ℕ}

/-- Negated `Nat.beq`. -/
theorem nbeq_iff {a b : ℕ} : (!Nat.beq a b) = true ↔ a ≠ b := by
  cases h : Nat.beq a b
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

/-- A fact accepted by `lowP p e` gives `p ^ e ∣ N` with `p` prime. -/
theorem lowP_sound {p e : ℕ} {f : Fact} (hf : f.Holds N) (h : lowP p e f = true) :
    p.Prime ∧ p ^ e ∣ N := by
  cases f with
  | pw q e' =>
    simp only [lowP, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
    obtain ⟨rfl, hle⟩ := h
    exact ⟨hf.1, (Nat.pow_dvd_pow q hle).trans hf.2⟩
  | dv q d =>
    simp only [lowP, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
    obtain ⟨rfl, hle⟩ := h
    have := Nat.le_of_dvd (Nat.succ_pos _) hf.2
    exact ⟨hf.1, (Nat.pow_dvd_pow q (by omega)).trans (Nat.ordProj_dvd N q)⟩
  | ex q e' =>
    simp only [lowP, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
    obtain ⟨rfl, hle⟩ := h
    have he : N.factorization q = e' := hf.2
    exact ⟨hf.1, (Nat.pow_dvd_pow q (by omega)).trans (he ▸ Nat.ordProj_dvd N q)⟩
  | nd q => simp [lowP] at h

/-- Soundness of `hasPow`. -/
theorem hasPow_sound {s : List Fact} {p e : ℕ} (hs : Holds N s) (h : hasPow s p e = true) :
    p.Prime ∧ p ^ e ∣ N := by
  obtain ⟨f, hf, h⟩ := List.any_eq_true.mp h
  exact lowP_sound (hs f hf) h

/-- A fact accepted by `compP p a` gives `a + 1 ∣ N.factorization p + 1` with `p` prime. -/
theorem compP_sound {p a : ℕ} {f : Fact} (hf : f.Holds N) (h : compP p a f = true) :
    p.Prime ∧ a + 1 ∣ N.factorization p + 1 := by
  cases f with
  | ex q e =>
    simp only [compP, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨rfl, hm⟩ := h
    have he : N.factorization q = e := hf.2
    exact ⟨hf.1, he ▸ Nat.dvd_of_mod_eq_zero hm⟩
  | dv q d =>
    simp only [compP, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨rfl, hm⟩ := h
    exact ⟨hf.1, (Nat.dvd_of_mod_eq_zero hm).trans hf.2⟩
  | pw q e => simp [compP] at h
  | nd q => simp [compP] at h

/-- A fact accepted by `oddP` records a prime with odd exponent. -/
theorem oddP_sound {f : Fact} (hf : f.Holds N) (h : oddP f = true) :
    f.prime.Prime ∧ Odd (N.factorization f.prime) := by
  cases f with
  | ex q e =>
    simp only [oddP, Nat.beq_eq] at h
    have he : N.factorization q = e := hf.2
    exact ⟨hf.1, Nat.odd_iff.mpr (by simp only [Fact.prime]; omega)⟩
  | dv q d =>
    simp only [oddP, Nat.beq_eq] at h
    obtain ⟨k, hk⟩ := hf.2
    refine ⟨hf.1, Nat.odd_iff.mpr ?_⟩
    simp only [Fact.prime]
    have : (d * k) % 2 = 0 := by rw [Nat.mul_mod, h]; simp
    omega
  | pw q e => simp [oddP] at h
  | nd q => simp [oddP] at h

/-- An odd exponent forces the special prime of Euler's form. -/
theorem special_of_odd (h : OddPerfect N) {p : ℕ} (hp : p.Prime) (ho : Odd (N.factorization p)) :
    p % 4 = 1 ∧ N.factorization p % 4 = 1 ∧
      ∀ r, r.Prime → Odd (N.factorization r) → r = p := by
  obtain ⟨q, hq, -, hq4, hqe, hev⟩ := exists_special_prime h
  have hpq : p = q := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr ho) (hev p hp hne)
  subst hpq
  refine ⟨hq4, hqe, fun r hr hro => ?_⟩
  by_contra hne
  exact (Nat.not_even_iff_odd.mpr hro) (hev r hr hne)

/-- For prime `p`, `σ (p ^ a) = gs p a`. -/
theorem gs_eq {p : ℕ} (hp : p.Prime) (a : ℕ) : σ 1 (p ^ a) = gs p a := by
  rw [sigma_one_apply_prime_pow hp, Nat.geomSum_eq hp.two_le]
  rfl

/-- Unpacks `nodupB` on a cons. -/
theorem nodupB_cons {x : ℕ} {l : List ℕ} (h : nodupB (x :: l) = true) :
    (∀ y ∈ l, y ≠ x) ∧ nodupB l = true := by
  simp only [nodupB, Bool.and_eq_true, List.all_eq_true, nbeq_iff, ne_eq] at h
  exact ⟨h.1, h.2⟩

/-- The product of component divisor sums divides `σ M`. -/
theorem Dv_dvd_sigma : ∀ (cs : List (ℕ × ℕ)) (M : ℕ), M ≠ 0 → nodupB (cs.map Prod.fst) = true →
    (∀ c ∈ cs, c.1.Prime ∧ c.2 + 1 ∣ M.factorization c.1 + 1) → Dv cs ∣ σ 1 M
  | [], _, _, _, _ => by simp [Dv]
  | (p, a) :: l, M, hM, hnd, hc => by
    obtain ⟨hne, hnd⟩ := nodupB_cons hnd
    obtain ⟨hp, hpa⟩ := hc (p, a) List.mem_cons_self
    have hM' : ordCompl[p] M ≠ 0 := (Nat.ordCompl_pos p hM).ne'
    have hcop : Nat.Coprime (p ^ M.factorization p) (ordCompl[p] M) :=
      (Nat.coprime_ordCompl hp hM).pow_left _
    have hσ : σ 1 M = σ 1 (p ^ M.factorization p) * σ 1 (ordCompl[p] M) := by
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self M p]
      exact isMultiplicative_sigma.map_mul_of_coprime hcop
    have ih := Dv_dvd_sigma l (ordCompl[p] M) hM' hnd (fun c hc' => by
      obtain ⟨h1, h2⟩ := hc c (List.mem_cons_of_mem _ hc')
      have hcp : c.1 ≠ p := hne c.1 (List.mem_map_of_mem hc')
      rw [Nat.factorization_ordCompl, Finsupp.erase_ne hcp]
      exact ⟨h1, h2⟩)
    rw [hσ, Dv, ← gs_eq hp]
    exact mul_dvd_mul (OPNExample.sigma_prime_pow_dvd hp hpa) ih

/-- Accepted components give `∏ σ(p ^ a) ∣ 2 N`. -/
theorem compsOK_sound {s : List Fact} {cs : List (ℕ × ℕ)} (h : OddPerfect N) (hs : Holds N s)
    (hc : compsOK s cs = true) : Dv cs ∣ 2 * N := by
  simp only [compsOK, Bool.and_eq_true, List.all_eq_true] at hc
  rw [← h.sigma_eq]
  refine Dv_dvd_sigma cs N h.ne_zero hc.1 fun c hc' => ?_
  obtain ⟨f, hf, h'⟩ := List.any_eq_true.mp (hc.2 c hc')
  exact compP_sound (hs f hf) h'

/-- If `D ∣ 2 N` then `half D ∣ N`. -/
theorem half_dvd {D : ℕ} (hD : D ∣ 2 * N) : half D ∣ N := by
  unfold half
  split_ifs with h2
  · obtain ⟨m, rfl⟩ : 2 ∣ D := Nat.dvd_of_mod_eq_zero h2
    rw [Nat.mul_div_cancel_left _ two_pos]
    exact Nat.dvd_of_mul_dvd_mul_left two_pos hD
  · have hc : Nat.Coprime D 2 := (Nat.coprime_comm.mp ((Nat.coprime_two_left).mpr
      (Nat.odd_iff.mpr (by omega))))
    exact hc.dvd_of_dvd_mul_left hD

/-- The prime power recorded by a fact divides `N`. -/
theorem base_dvd {f : Fact} (hf : f.Holds N) : base f ∣ N := by
  cases f with
  | pw p e => exact hf.2
  | dv p d =>
    have := Nat.le_of_dvd (Nat.succ_pos _) hf.2
    exact (Nat.pow_dvd_pow p (by omega)).trans (Nat.ordProj_dvd N p)
  | ex p e =>
    have he : N.factorization p = e := hf.2
    exact he ▸ Nat.ordProj_dvd N p
  | nd p => exact one_dvd N

/-- The least common multiple of the recorded prime powers divides `N`. -/
theorem Av_dvd : ∀ {s : List Fact}, Holds N s → Av s ∣ N
  | [], _ => one_dvd N
  | f :: _, hs => Nat.lcm_dvd (base_dvd (hs f List.mem_cons_self))
      (Av_dvd fun g hg => hs g (List.mem_cons_of_mem _ hg))

/-- Soundness of the trial division loop. -/
theorem tdAux_sound {n : ℕ} : ∀ fuel d, tdAux n fuel d = true →
    ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n
  | 0, d, h, m, hdm, hmn, _ => by
    simp only [tdAux, Nat.blt_eq] at h
    have := Nat.mul_le_mul hdm hdm
    omega
  | fuel + 1, d, h, m, hdm, hmn, hmd => by
    simp only [tdAux, Bool.or_eq_true, Nat.blt_eq, Bool.and_eq_true, nbeq_iff,
      ne_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · have := Nat.mul_le_mul hdm hdm
      omega
    · rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
      · exact h1 (Nat.mod_eq_zero_of_dvd hmd)
      · exact tdAux_sound fuel (d + 1) h2 m hlt hmn hmd

/-- Soundness of trial division. -/
theorem tdPrime_sound {n : ℕ} (h : tdPrime n = true) : n.Prime := by
  simp only [tdPrime, Bool.and_eq_true, Nat.ble_eq] at h
  by_contra hn
  have hm := Nat.minFac_prime (show n ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (by omega) hn
  exact tdAux_sound n 2 h.2 n.minFac hm.two_le (by nlinarith) (Nat.minFac_dvd n)

/-- The trial division loop accepts primes when the fuel suffices. -/
theorem tdAux_complete {n : ℕ} (hn : n.Prime) : ∀ fuel d, 2 ≤ d → n < fuel + d →
    tdAux n fuel d = true
  | 0, d, _, h => by
    simp only [tdAux, Nat.blt_eq]
    nlinarith
  | fuel + 1, d, hd, h => by
    simp only [tdAux, Bool.or_eq_true, Nat.blt_eq, Bool.and_eq_true, nbeq_iff, ne_eq]
    by_cases hlt : n < d * d
    · exact Or.inl hlt
    · refine Or.inr ⟨fun hmod => ?_, tdAux_complete hn fuel (d + 1) (by omega) (by omega)⟩
      have hdn : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
      rcases (Nat.dvd_prime hn).mp hdn with h1 | h1
      · omega
      · subst h1
        nlinarith

/-- Trial division accepts every prime. -/
theorem tdPrime_complete {n : ℕ} (hn : n.Prime) : tdPrime n = true := by
  simp only [tdPrime, Bool.and_eq_true, Nat.ble_eq]
  exact ⟨hn.two_le, tdAux_complete hn n 2 le_rfl (by omega)⟩


/-- `smallPrimes` contains every prime below `1000`. -/
theorem smallPrimes_check :
    (List.range 1000).all (fun r => !tdPrime r || smallPrimes.contains r) = true := by
  decide +kernel

/-- Every prime below `1000` is in `smallPrimes`. -/
theorem mem_smallPrimes {r : ℕ} (hr : r.Prime) (h : r < 1000) : r ∈ smallPrimes := by
  have := List.all_eq_true.mp smallPrimes_check r (List.mem_range.mpr h)
  simpa [tdPrime_complete hr] using this

/-- Every prime below `R` is listed by `primesBelow R`. -/
theorem mem_primesBelow {r R : ℕ} (hr : r.Prime) (hR : r < R) : r ∈ primesBelow R := by
  unfold primesBelow
  split_ifs with h
  · simp only [Nat.ble_eq] at h
    exact List.mem_filter.mpr ⟨mem_smallPrimes hr (by omega), by simpa using hR⟩
  · exact List.mem_filter.mpr ⟨List.mem_range.mpr hR, tdPrime_complete hr⟩

/-- A key found in a table has an entry passing `entryOK`. -/
theorem PT.allOK_mem (T : PT) : ∀ {U : PT} {q : ℕ}, PT.allOK T U = true → U.mem q = true →
    ∃ a fs, entryOK T q a fs = true
  | .leaf, _, _, h => by simp [PT.mem] at h
  | .node l p a fs r, q, hok, hm => by
    simp only [PT.allOK, Bool.and_eq_true] at hok
    simp only [PT.mem] at hm
    split_ifs at hm with h1 h2
    · exact PT.allOK_mem T hok.1.2 hm
    · exact PT.allOK_mem T hok.2 hm
    · simp only [Nat.blt_eq, not_lt] at h1 h2
      exact ⟨a, fs, (show q = p by omega) ▸ hok.1.1⟩

/-- `pm` agrees with the project's binary modular exponentiation. -/
theorem pm_eq_powModAux (n : ℕ) :
    ∀ fuel b e acc, pm n fuel b e acc = Pratt.powModAux n fuel b e acc
  | 0, _, _, _ => rfl
  | fuel + 1, b, e, acc => by
    simp only [pm, Pratt.powModAux, pm_eq_powModAux n fuel]
    cases h0 : Nat.beq e 0
    · have he : e ≠ 0 := Nat.ne_of_beq_eq_false h0
      cases h1 : Nat.beq (e % 2) 1
      · have he2 : e % 2 ≠ 1 := Nat.ne_of_beq_eq_false h1
        simp [he, he2]
      · have he2 : e % 2 = 1 := Nat.eq_of_beq_eq_true h1
        simp [he, he2]
    · have he : e = 0 := Nat.eq_of_beq_eq_true h0
      simp [he]

/-- Correctness of `pm` with the fuel used by `entryOK`. -/
theorem pm_eq (n a e : ℕ) (h : e < n) : pm n n a e 1 = a ^ e % n := by
  rw [pm_eq_powModAux, Pratt.powModAux_eq n n a e 1 h, one_mul]

/-- A prime dividing `∏ f ^ k`, where every `f` is prime, is one of the `f`. -/
theorem mem_of_dvd_ppow {q : ℕ} (hq : q.Prime) : ∀ {fs : List (ℕ × ℕ)},
    (∀ c ∈ fs, c.1.Prime) → q ∣ ppow fs → ∃ c ∈ fs, c.1 = q
  | [], _, h => absurd (Nat.le_of_dvd one_pos h) (by have := hq.two_le; omega)
  | c :: l, hp, h => by
    rw [ppow] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
    · exact ⟨c, List.mem_cons_self, ((Nat.prime_dvd_prime_iff_eq hq
        (hp c List.mem_cons_self)).mp (hq.dvd_of_dvd_pow h1)).symm⟩
    · obtain ⟨d, hd, hdq⟩ := mem_of_dvd_ppow hq (fun x hx => hp x (List.mem_cons_of_mem _ hx)) h1
      exact ⟨d, List.mem_cons_of_mem _ hd, hdq⟩

/-- Every key of a table whose entries all pass `entryOK` against the table itself is prime. -/
theorem PT.prime_of_mem {T : PT} (hT : T.allOK T = true) : ∀ q, T.mem q = true → q.Prime := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ p ih =>
    intro hq
    obtain ⟨a, fs, h⟩ := PT.allOK_mem T hT hq
    simp only [entryOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Nat.blt_eq,
      Nat.beq_eq, nbeq_iff] at h
    obtain ⟨⟨⟨hp1, hprod⟩, hpow⟩, hall⟩ := h
    have hfs : ∀ c ∈ fs, c.1.Prime := fun c hc =>
      (hall c hc).1.2.elim (ih c.1 (hall c hc).1.1) tdPrime_sound
    have key : ∀ k, ((a : ZMod p) ^ k = 1 ↔ a ^ k % p = 1) := fun k => by
      rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp1]
    refine lucas_primality p (a : ZMod p) ((key _).2 ?_) fun q hqp hd => ?_
    · rw [← pm_eq _ _ _ (by omega)]; exact hpow
    · rw [← hprod] at hd
      obtain ⟨c, hc, rfl⟩ := mem_of_dvd_ppow hqp hfs hd
      rw [Ne, key, ← pm_eq _ _ _ (by have := Nat.div_le_self (p - 1) c.1; omega)]
      exact (hall c hc).2

/-- A prime outside the list is coprime to the recorded product. -/
theorem coprime_dprod {p : ℕ} (hp : p.Prime) : ∀ {l : List (ℕ × ℕ)},
    (∀ c ∈ l, c.1.Prime) → (∀ c ∈ l, c.1 ≠ p) → Nat.Coprime p (dprod l)
  | [], _, _ => by simp [dprod]
  | c :: l, hpr, hne => by
    rw [dprod]
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp
      (hpr c List.mem_cons_self)).mpr (hne c List.mem_cons_self).symm)) ?_
    exact coprime_dprod hp (fun x hx => hpr x (List.mem_cons_of_mem _ hx))
      (fun x hx => hne x (List.mem_cons_of_mem _ hx))

/-- The recorded product divides `N`, and its divisor sum is `sprod`. -/
theorem dprod_sound : ∀ {l : List (ℕ × ℕ)}, nodupB (l.map Prod.fst) = true →
    (∀ c ∈ l, c.1.Prime ∧ c.1 ^ c.2 ∣ N) → dprod l ∣ N ∧ σ 1 (dprod l) = sprod l
  | [], _, _ => by simp [dprod, sprod]
  | c :: l, hnd, hc => by
    obtain ⟨hne, hnd⟩ := nodupB_cons hnd
    obtain ⟨hp, hpd⟩ := hc c List.mem_cons_self
    have hcop : Nat.Coprime (c.1 ^ c.2) (dprod l) :=
      (coprime_dprod hp (fun x hx => (hc x (List.mem_cons_of_mem _ hx)).1)
        (fun x hx => hne x.1 (List.mem_map_of_mem hx))).pow_left _
    obtain ⟨hd, hσ⟩ := dprod_sound hnd (fun x hx => hc x (List.mem_cons_of_mem _ hx))
    rw [dprod, sprod, isMultiplicative_sigma.map_mul_of_coprime hcop, hσ, gs_eq hp]
    exact ⟨hcop.mul_dvd_of_dvd_of_dvd hpd hd, rfl⟩

/-! ## Soundness of a step -/

/-- Adding a valid fact keeps a state valid. -/
theorem holds_cons (f : Fact) {s : List Fact} (hf : f.Holds N) (hs : Holds N s) :
    Holds N (f :: s) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hs g hg

/-- Soundness of one step: if all children are good, the state is good. -/
theorem step_sound {L : ℕ} {T : PT} (hT : ∀ x, T.mem x = true → x.Prime) {i : Ins}
    {s : List Fact} {cs : List (List Fact)} (hst : step L T i s = some cs) (hcs : ∀ c ∈ cs, Good L c) : Good L s := by
  intro N h hs
  have hN := h.ne_zero
  cases i with
  | rs p d R =>
    simp only [step] at hst
    split_ifs at hst with hc
    obtain rfl := Option.some.inj hst
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hc
    -- the prime `p` and `d ∣ e + 1`
    have key : p.Prime ∧ d ∣ N.factorization p + 1 ∧ (d = 1 → 1 ≤ N.factorization p) := by
      rcases hc with ⟨rfl, hpow⟩ | ⟨hd2, hdv⟩
      · obtain ⟨hp, hpd⟩ := hasPow_sound hs hpow
        exact ⟨hp, one_dvd _, fun _ => (hp.pow_dvd_iff_le_factorization hN).mp hpd⟩
      · obtain ⟨f, hf, hfd⟩ := List.any_eq_true.mp hdv
        cases f with
        | dv q d' =>
          simp only [isDv, Bool.and_eq_true, Nat.beq_eq] at hfd
          obtain ⟨rfl, rfl⟩ := hfd
          exact ⟨(hs _ hf).1, (hs _ hf).2, fun h1 => by omega⟩
        | pw _ _ => simp [isDv] at hfd
        | ex _ _ => simp [isDv] at hfd
        | nd _ => simp [isDv] at hfd
    obtain ⟨hp, ⟨m, hm⟩, hd1⟩ := key
    set k := N.factorization p with hk
    have hd0 : d ≠ 0 := by rintro rfl; omega
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · -- `m = 1`, so `k = d - 1` and `d ≥ 2`
      have hm1 : m = 1 := by
        rcases m with _ | _ | m
        · omega
        · rfl
        · omega
      subst hm1
      have hd2 : 2 ≤ d := by
        by_contra hlt
        have : d = 1 := by omega
        have := hd1 this
        omega
      refine hcs _ ?_ N h (holds_cons (.ex p (d - 1)) ⟨hp, by omega⟩ hs)
      simp [exKid, hd2]
    · have hmf := Nat.minFac_prime (show m ≠ 1 by omega)
      by_cases hr : m.minFac < R
      · refine hcs (.dv p (d * m.minFac) :: s) ?_ N h (holds_cons (.dv p (d * m.minFac)) ⟨hp, ?_⟩ hs)
        · simp only [List.mem_append, List.mem_map]
          exact Or.inl (Or.inr ⟨_, mem_primesBelow hmf hr, rfl⟩)
        · rw [hm]
          exact Nat.mul_dvd_mul_left d (Nat.minFac_dvd m)
      · have hmR : R ≤ m := (Nat.not_lt.mp hr).trans (Nat.minFac_le (by omega))
        refine hcs (.pw p (d * R - 1) :: s) (by simp) N h (holds_cons (.pw p (d * R - 1)) ⟨hp, ?_⟩ hs)
        have : d * R ≤ d * m := Nat.mul_le_mul_left d hmR
        exact (Nat.pow_dvd_pow p (by omega)).trans (Nat.ordProj_dvd N p)
  | force q k cs' =>
    simp only [step] at hst
    split_ifs at hst with hc
    obtain rfl := Option.some.inj hst
    simp only [Bool.and_eq_true, nbeq_iff, ne_eq, Nat.beq_eq] at hc
    obtain ⟨⟨⟨hok, hq2⟩, hpc⟩, hmod⟩ := hc
    have hq := hT q hpc
    have hD := compsOK_sound h hs hok
    have hqk : q ^ k ∣ 2 * N := (Nat.dvd_of_mod_eq_zero hmod).trans hD
    have hcop : Nat.Coprime (q ^ k) 2 :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
    refine hcs _ (by simp) N h (holds_cons (.pw q k) ⟨hq, ?_⟩ hs)
    exact hcop.dvd_of_dvd_mul_left hqk
  | up p e =>
    simp only [step] at hst
    split_ifs at hst with hc
    obtain rfl := Option.some.inj hst
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, nbeq_iff, ne_eq] at hc
    obtain ⟨⟨hpow, he⟩, hcase⟩ := hc
    obtain ⟨hp, hpd⟩ := hasPow_sound hs hpow
    have hle := (hp.pow_dvd_iff_le_factorization hN).mp hpd
    have hne : N.factorization p ≠ e := by
      intro heq
      obtain ⟨h4, he4, huniq⟩ := special_of_odd h hp (Nat.odd_iff.mpr (by omega))
      rcases hcase with (h3 | h3) | hoth
      · omega
      · exact h3 h4
      · obtain ⟨f, hf, hfo⟩ := List.any_eq_true.mp hoth
        simp only [Bool.and_eq_true, nbeq_iff, ne_eq] at hfo
        obtain ⟨hfp, hodd⟩ := oddP_sound (hs f hf) hfo.2
        exact hfo.1 (huniq _ hfp hodd)
    refine hcs _ (by simp) N h (holds_cons (.pw p (e + 1)) ⟨hp, ?_⟩ hs)
    exact (hp.pow_dvd_iff_le_factorization hN).mpr (by omega)
  | big cs' =>
    simp only [step] at hst
    split_ifs at hst with hc
    simp only [Bool.and_eq_true, Nat.blt_eq] at hc
    have hdvd : Nat.lcm (Av s) (half (Dv cs')) ∣ N :=
      Nat.lcm_dvd (Av_dvd hs) (half_dvd (compsOK_sound h hs hc.1))
    exact lt_of_lt_of_le hc.2 (Nat.le_of_dvd h.pos hdvd)
  | ndc p =>
    simp only [step] at hst
    split_ifs at hst with hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨hp, hpd⟩ := hasPow_sound hs hc.1
    obtain ⟨f, hf, hfd⟩ := List.any_eq_true.mp hc.2
    cases f with
    | nd q =>
      simp only [isNd, Nat.beq_eq] at hfd
      subst hfd
      exact absurd (by simpa using hpd) (hs _ hf)
    | pw _ _ => simp [isNd] at hfd
    | dv _ _ => simp [isNd] at hfd
    | ex _ _ => simp [isNd] at hfd
  | ovf q f cs' =>
    simp only [step] at hst
    split_ifs at hst with hc
    simp only [Bool.and_eq_true, nbeq_iff, ne_eq, Nat.beq_eq] at hc
    obtain ⟨⟨⟨hok, hex⟩, hq2⟩, hmod⟩ := hc
    obtain ⟨g, hg, hgd⟩ := List.any_eq_true.mp hex
    cases g with
    | ex q' e' =>
      simp only [isEx, Bool.and_eq_true, Nat.beq_eq] at hgd
      obtain ⟨rfl, rfl⟩ := hgd
      obtain ⟨hq, hqe⟩ := hs _ hg
      have hD := compsOK_sound h hs hok
      have hqk : q' ^ (e' + 1) ∣ 2 * N := (Nat.dvd_of_mod_eq_zero hmod).trans hD
      have hcop : Nat.Coprime (q' ^ (e' + 1)) 2 :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
      have := (hq.pow_dvd_iff_le_factorization hN).mp
        (hcop.dvd_of_dvd_mul_left hqk)
      omega
    | pw _ _ => simp [isEx] at hgd
    | dv _ _ => simp [isEx] at hgd
    | nd _ => simp [isEx] at hgd
  | par2 p q =>
    simp only [step] at hst
    split_ifs at hst with hc
    simp only [Bool.and_eq_true, nbeq_iff, ne_eq] at hc
    obtain ⟨⟨hpq, hp⟩, hq⟩ := hc
    obtain ⟨f, hf, hfo⟩ := List.any_eq_true.mp hp
    obtain ⟨g, hg, hgo⟩ := List.any_eq_true.mp hq
    simp only [Bool.and_eq_true, Nat.beq_eq] at hfo hgo
    obtain ⟨hf1, hf2⟩ := oddP_sound (hs f hf) hfo.2
    obtain ⟨hg1, hg2⟩ := oddP_sound (hs g hg) hgo.2
    obtain ⟨-, -, hu⟩ := special_of_odd h hf1 hf2
    exact absurd (hfo.1 ▸ hgo.1 ▸ hu _ hg1 hg2) (Ne.symm hpq)
  | parS p =>
    simp only [step] at hst
    split_ifs at hst with hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, nbeq_iff, ne_eq] at hc
    obtain ⟨hp, hcase⟩ := hc
    obtain ⟨f, hf, hfo⟩ := List.any_eq_true.mp hp
    simp only [Bool.and_eq_true, Nat.beq_eq] at hfo
    obtain ⟨hf1, hf2⟩ := oddP_sound (hs f hf) hfo.2
    rw [hfo.1] at hf1 hf2
    obtain ⟨h4, he4, -⟩ := special_of_odd h hf1 hf2
    rcases hcase with h3 | hb
    · exact absurd h4 h3
    · obtain ⟨g, hg, hgb⟩ := List.any_eq_true.mp hb
      cases g with
      | ex q e =>
        simp only [bad4, Bool.and_eq_true, Nat.beq_eq, nbeq_iff, ne_eq] at hgb
        obtain ⟨rfl, hne⟩ := hgb
        have : N.factorization q = e := (hs _ hg).2
        omega
      | dv q d =>
        simp only [bad4, Bool.and_eq_true, Nat.beq_eq] at hgb
        obtain ⟨rfl, h0⟩ := hgb
        obtain ⟨j, hj⟩ := (hs _ hg).2
        have : (d * j) % 4 = 0 := by rw [Nat.mul_mod, h0]; simp
        omega
      | pw _ _ => simp [bad4] at hgb
      | nd _ => simp [bad4] at hgb
  | abund l =>
    simp only [step] at hst
    split_ifs at hst with hc
    simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at hc
    obtain ⟨⟨hnd, hall⟩, hlt⟩ := hc
    obtain ⟨hd, hσ⟩ := dprod_sound hnd (fun c hc' => hasPow_sound hs (hall c hc'))
    have hlt' : 2 * dprod l < σ 1 (dprod l) := hσ ▸ hlt
    rw [sigma_one_apply] at hlt'
    have hab := (Nat.abundant_iff_sum_divisors.mpr hlt').of_dvd hd hN
    exact absurd hab ((Nat.perfect_iff_not_abundant_and_not_deficient h.pos.ne).mp h.perfect).1

/-- Soundness of the runner: every state on an accepted stack is good. -/
theorem run_sound {L : ℕ} {T : PT} (hT : ∀ x, T.mem x = true → x.Prime) :
    ∀ (is : List Ins) (stk : List (List Fact)), run L T is stk = true → ∀ s ∈ stk, Good L s
  | [], stk, h => by
    simp only [run, List.isEmpty_iff] at h
    simp [h]
  | _ :: _, [], h => by simp [run] at h
  | i :: is, s :: stk, h => by
    simp only [run] at h
    split at h
    · rename_i cs hst
      have ih := run_sound hT is (cs ++ stk) h
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact step_sound hT hst fun c hc => ih c (List.mem_append_left _ hc)
      · exact ih t (List.mem_append_right _ ht)
    · simp at h

/-! ## Size from the number of prime factors -/

/-- A finite set of odd numbers, all at least `m`, with at least `k` elements has product at
least `m (m + 2) ⋯ (m + 2 (k - 1))`. -/
theorem prod_range_le_prod (S : Finset ℕ) : ∀ {m k : ℕ}, (∀ s ∈ S, Odd s ∧ m ≤ s) →
    k ≤ S.card → ∏ i ∈ Finset.range k, (m + 2 * i) ≤ ∏ s ∈ S, s := by
  induction S using Finset.induction_on_min with
  | empty =>
    intro m k _ hk
    simp only [Finset.card_empty, Nat.le_zero] at hk
    subst hk
    simp
  | insert a S ha ih =>
    intro m k hS hk
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    rw [Finset.prod_insert haS]
    obtain ⟨hao, hma⟩ := hS a (Finset.mem_insert_self a S)
    have hpos : 0 < ∏ s ∈ S, s := Finset.prod_pos fun s hs =>
      (hS s (Finset.mem_insert_of_mem hs)).1.pos
    rcases k with _ | k
    · simp only [Finset.range_zero, Finset.prod_empty]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hao.pos.ne' hpos.ne')
    · rw [Finset.card_insert_of_notMem haS] at hk
      have h1 := ih (m := m + 2) (k := k) (fun s hs => by
        obtain ⟨hso, -⟩ := hS s (Finset.mem_insert_of_mem hs)
        refine ⟨hso, ?_⟩
        have := ha s hs
        obtain ⟨i, rfl⟩ := hao
        obtain ⟨j, rfl⟩ := hso
        omega) (by omega)
      rw [Finset.prod_range_succ']
      calc (∏ i ∈ Finset.range k, (m + 2 * (i + 1))) * (m + 2 * 0)
          = (∏ i ∈ Finset.range k, (m + 2 + 2 * i)) * m := by
            congr 1
            · exact Finset.prod_congr rfl fun i _ => by ring
          _ ≤ (∏ s ∈ S, s) * a := Nat.mul_le_mul h1 hma
          _ = a * ∏ s ∈ S, s := mul_comm _ _

/-- `consec m l`: a gap check. For each entry `x` in turn, `m ≤ x` and no prime lies in `[m, x)`;
then the check continues from `x + 1`. The entries themselves are not required to be prime: for
instance `consec 8 [8] = true`. So the `i`-th entry is a lower bound for the `i`-th prime that
is at least `m`, which is all that `prod_consec_le_prod` uses. -/
def consec : ℕ → List ℕ → Bool
  | _, [] => true
  | m, x :: l => Nat.ble m x && (List.range' m (x - m)).all (fun p => !tdPrime p) &&
      consec (x + 1) l

/-- A finite set of primes, all at least `m`, with at least `|l|` elements has product at least
`∏ l` when `l` lists the consecutive primes from `m`. -/
theorem prod_consec_le_prod : ∀ (l : List ℕ) (S : Finset ℕ) {m : ℕ}, consec m l = true →
    (∀ s ∈ S, s.Prime ∧ m ≤ s) → l.length ≤ S.card → l.prod ≤ ∏ s ∈ S, s
  | [], S, _, _, hS, _ => by
    simp only [List.prod_nil]
    exact Finset.prod_pos fun s hs => (hS s hs).1.pos
  | x :: l, S, m, hc, hS, hk => by
    simp only [consec, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, List.mem_range'_1,
      Bool.not_eq_eq_eq_not, Bool.not_true] at hc
    obtain ⟨⟨hmx, hgap⟩, hc⟩ := hc
    have hne : S.Nonempty := Finset.card_pos.mp (by simp at hk; omega)
    set a := S.min' hne
    have haS : a ∈ S := S.min'_mem hne
    have hxa : x ≤ a := by
      by_contra hlt
      have := hgap a ⟨(hS a haS).2, by omega⟩
      rw [tdPrime_complete (hS a haS).1] at this
      exact Bool.noConfusion this
    have ih := prod_consec_le_prod l (S.erase a) (m := x + 1) hc (fun s hs => by
      have hsS := Finset.mem_of_mem_erase hs
      have : a < s := lt_of_le_of_ne (S.min'_le s hsS) (Finset.ne_of_mem_erase hs).symm
      exact ⟨(hS s hsS).1, by omega⟩) (by
        rw [Finset.card_erase_of_mem haS]; simp at hk; omega)
    rw [List.prod_cons, ← Finset.mul_prod_erase S (fun s => s) haS]
    exact Nat.mul_le_mul hxa ih

/-- If every prime factor of an odd perfect number is at least `m`, there are more than `|l|`
of them, and `l` lists the consecutive primes from `m`, then `N ≥ m (∏ l) ^ 2`. -/
theorem le_of_card_primeFactors_consec (h : OddPerfect N) {m : ℕ} (l : List ℕ)
    (hl : consec m l = true) (hm : ∀ p ∈ N.primeFactors, m ≤ p)
    (hk : l.length + 1 ≤ N.primeFactors.card) : m * l.prod ^ 2 ≤ N := by
  obtain ⟨q, hq, hqN, -, hqe, hev⟩ := exists_special_prime h
  have hqmem : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩
  have h1 := prod_consec_le_prod l (N.primeFactors.erase q) hl (fun s hs =>
    ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hs),
      hm s (Finset.mem_of_mem_erase hs)⟩) (by rw [Finset.card_erase_of_mem hqmem]; omega)
  have hN : N = q ^ N.factorization q *
      ∏ p ∈ N.primeFactors.erase q, p ^ N.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self h.ne_zero]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    exact (Finset.mul_prod_erase _ (fun p => p ^ N.factorization p) hqmem).symm
  have h2 : (∏ p ∈ N.primeFactors.erase q, p) ^ 2 ≤
      ∏ p ∈ N.primeFactors.erase q, p ^ N.factorization p := by
    rw [← Finset.prod_pow]
    refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp => ?_
    have hpS := Finset.mem_of_mem_erase hp
    have hpp := Nat.prime_of_mem_primeFactors hpS
    obtain ⟨j, hj⟩ := hev p hpp (Finset.ne_of_mem_erase hp)
    have hpos : 1 ≤ N.factorization p :=
      (hpp.pow_dvd_iff_le_factorization h.ne_zero).mp
        (by simpa using Nat.dvd_of_mem_primeFactors hpS)
    exact Nat.pow_le_pow_right hpp.pos (by omega)
  have h3 : m ≤ q ^ N.factorization q :=
    (hm q hqmem).trans (Nat.le_self_pow (by omega) q)
  rw [hN]
  exact Nat.mul_le_mul h3 ((Nat.pow_le_pow_left h1 2).trans h2)

/-- Structural bound with no search: an odd perfect number has at least five distinct prime
factors (Sylvester), all odd, and all but the special one have exponent at least two, so
`N ≥ 3 (3 · 5 · 7 · 11) ^ 2`. -/
theorem structural_lower_bound {N : ℕ} (h : OddPerfect N) : 4002075 ≤ N := by
  have hm : ∀ p ∈ N.primeFactors, 3 ≤ p := fun p hp => by
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h2 := hpp.two_le
    by_contra hlt
    have : p = 2 := by omega
    subst this
    exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
  have h5 := five_le_card_primeFactors h
  have := le_of_card_primeFactors_consec h [3, 5, 7, 11] (by decide +kernel) hm (by simpa using h5)
  norm_num at this
  exact this

/-- If every prime factor of an odd perfect number is at least `m` and there are more than `k`
of them, then `N ≥ m (m (m + 2) ⋯ (m + 2 (k - 1))) ^ 2`: all prime factors but the special one
have exponent at least two. -/
theorem le_of_card_primeFactors (h : OddPerfect N) {m k : ℕ}
    (hm : ∀ p ∈ N.primeFactors, m ≤ p) (hk : k + 1 ≤ N.primeFactors.card) :
    m * (∏ i ∈ Finset.range k, (m + 2 * i)) ^ 2 ≤ N := by
  obtain ⟨q, hq, hqN, -, hqe, hev⟩ := exists_special_prime h
  have hqmem : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩
  have hcard : k ≤ (N.primeFactors.erase q).card := by
    rw [Finset.card_erase_of_mem hqmem]; omega
  have h1 := prod_range_le_prod (N.primeFactors.erase q) (m := m) (fun s hs =>
    ⟨h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hs)),
      hm s (Finset.mem_of_mem_erase hs)⟩) hcard
  have hN : N = q ^ N.factorization q *
      ∏ p ∈ N.primeFactors.erase q, p ^ N.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self h.ne_zero]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    exact (Finset.mul_prod_erase _ (fun p => p ^ N.factorization p) hqmem).symm
  have h2 : (∏ p ∈ N.primeFactors.erase q, p) ^ 2 ≤
      ∏ p ∈ N.primeFactors.erase q, p ^ N.factorization p := by
    rw [← Finset.prod_pow]
    refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp => ?_
    have hpS := Finset.mem_of_mem_erase hp
    have hpp := Nat.prime_of_mem_primeFactors hpS
    obtain ⟨j, hj⟩ := hev p hpp (Finset.ne_of_mem_erase hp)
    have hpos : 1 ≤ N.factorization p :=
      (hpp.pow_dvd_iff_le_factorization h.ne_zero).mp
        (by simpa using Nat.dvd_of_mem_primeFactors hpS)
    exact Nat.pow_le_pow_right hpp.pos (by omega)
  have h3 : m ≤ q ^ N.factorization q :=
    (hm q hqmem).trans (Nat.le_self_pow (by omega) q)
  rw [hN]
  exact Nat.mul_le_mul h3 ((Nat.pow_le_pow_left h1 2).trans h2)

/-- If no prime below `P` divides an odd perfect number `N`, and `T` is a list of distinct
numbers in `[2, L]` containing every prime in `[P, L]` with `∏ t/(t-1) < 2 L/(L-1)`, then `N`
has at least `|T|` distinct prime factors. -/
theorem length_le_card_primeFactors (h : OddPerfect N) {P L : ℕ} (T : List ℕ) (hnd : T.Nodup)
    (hP : ∀ p, p.Prime → p < P → ¬ p ∣ N) (hT : ∀ t ∈ T, 2 ≤ t ∧ t ≤ L)
    (hcover : (List.range (L + 1)).all
      (fun p => !tdPrime p || Nat.blt p P || T.contains p) = true)
    (hval : (T.map fun t : ℕ => (t : ℚ) / (t - 1)).prod < 2 * ((L : ℚ) / (L - 1))) :
    T.length ≤ N.primeFactors.card := by
  rw [← List.toFinset_card_of_nodup hnd]
  by_contra hlt
  push Not at hlt
  have key := prod_div_sub_one_mul_le_of_card_lt (S := N.primeFactors) (T := T.toFinset) (L := L)
    (fun t ht => hT t (List.mem_toFinset.mp ht))
    (fun s hs => (Nat.prime_of_mem_primeFactors hs).two_le)
    (by
      intro s hs hsT
      by_contra hle
      push Not at hle
      have hsp := Nat.prime_of_mem_primeFactors hs
      have hPs : P ≤ s := by
        by_contra hlt'
        exact hP s hsp (by omega) (Nat.dvd_of_mem_primeFactors hs)
      have := List.all_eq_true.mp hcover s (List.mem_range.mpr (by omega))
      simp only [tdPrime_complete hsp, Bool.not_true, Bool.false_or, Bool.or_eq_true,
        Nat.blt_eq, List.contains_iff_mem] at this
      rcases this with h1 | h1
      · omega
      · exact hsT (List.mem_toFinset.mpr h1))
    hlt
  rw [List.prod_toFinset _ hnd] at key
  have h2 := two_lt_prod_primeFactors h
  obtain ⟨t, ht⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hlt)
  have hL : (2 : ℚ) ≤ L := by exact_mod_cast (hT t (List.mem_toFinset.mp ht)).2.trans' (hT t
    (List.mem_toFinset.mp ht)).1
  have hpos : (0 : ℚ) < L / (L - 1) := div_pos (by linarith) (by linarith)
  have := mul_lt_mul_of_pos_right h2 hpos
  linarith

/-! ## Generated trees (BEGIN) -/

/-- Part of the prime table. -/
def tab0 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 3 2 [(2, 1)]
    PT.leaf) 7 3 [(2, 1), (3, 1)]
    PT.leaf) 11 2 [(2, 1), (5, 1)]
    (PT.node PT.leaf 13 2 [(2, 2), (3, 1)]
    PT.leaf)) 19 2 [(2, 1), (3, 2)]
    (PT.node (PT.node PT.leaf 31 3 [(2, 1), (3, 1), (5, 1)]
    PT.leaf) 61 2 [(2, 2), (3, 1), (5, 1)]
    (PT.node PT.leaf 71 7 [(2, 1), (5, 1), (7, 1)]
    PT.leaf))) 97 5 [(2, 5), (3, 1)]
    (PT.node (PT.node (PT.node PT.leaf 101 2 [(2, 2), (5, 2)]
    PT.leaf) 103 5 [(2, 1), (3, 1), (17, 1)]
    (PT.node PT.leaf 107 2 [(2, 1), (53, 1)]
    PT.leaf)) 109 6 [(2, 2), (3, 3)]
    (PT.node (PT.node PT.leaf 113 3 [(2, 4), (7, 1)]
    PT.leaf) 127 3 [(2, 1), (3, 2), (7, 1)]
    (PT.node PT.leaf 131 2 [(2, 1), (5, 1), (13, 1)]
    PT.leaf)))) 137 3 [(2, 3), (17, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 139 2 [(2, 1), (3, 1), (23, 1)]
    PT.leaf) 149 2 [(2, 2), (37, 1)]
    PT.leaf) 151 6 [(2, 1), (3, 1), (5, 2)]
    (PT.node PT.leaf 157 5 [(2, 2), (3, 1), (13, 1)]
    PT.leaf)) 163 2 [(2, 1), (3, 4)]
    (PT.node (PT.node PT.leaf 167 5 [(2, 1), (83, 1)]
    PT.leaf) 173 2 [(2, 2), (43, 1)]
    (PT.node PT.leaf 179 2 [(2, 1), (89, 1)]
    PT.leaf))) 181 2 [(2, 2), (3, 2), (5, 1)]
    (PT.node (PT.node (PT.node PT.leaf 191 19 [(2, 1), (5, 1), (19, 1)]
    PT.leaf) 193 5 [(2, 6), (3, 1)]
    (PT.node PT.leaf 197 2 [(2, 2), (7, 2)]
    PT.leaf)) 199 3 [(2, 1), (3, 2), (11, 1)]
    (PT.node (PT.node PT.leaf 211 2 [(2, 1), (3, 1), (5, 1), (7, 1)]
    PT.leaf) 223 3 [(2, 1), (3, 1), (37, 1)]
    (PT.node PT.leaf 227 2 [(2, 1), (113, 1)]
    PT.leaf))))) 229 6 [(2, 2), (3, 1), (19, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 233 3 [(2, 3), (29, 1)]
    PT.leaf) 239 7 [(2, 1), (7, 1), (17, 1)]
    PT.leaf) 241 7 [(2, 4), (3, 1), (5, 1)]
    (PT.node PT.leaf 251 6 [(2, 1), (5, 3)]
    PT.leaf)) 257 3 [(2, 8)]
    (PT.node (PT.node PT.leaf 263 5 [(2, 1), (131, 1)]
    PT.leaf) 269 2 [(2, 2), (67, 1)]
    (PT.node PT.leaf 271 6 [(2, 1), (3, 3), (5, 1)]
    PT.leaf))) 277 5 [(2, 2), (3, 1), (23, 1)]
    (PT.node (PT.node (PT.node PT.leaf 281 3 [(2, 3), (5, 1), (7, 1)]
    PT.leaf) 283 3 [(2, 1), (3, 1), (47, 1)]
    (PT.node PT.leaf 293 2 [(2, 2), (73, 1)]
    PT.leaf)) 307 5 [(2, 1), (3, 2), (17, 1)]
    (PT.node (PT.node PT.leaf 311 17 [(2, 1), (5, 1), (31, 1)]
    PT.leaf) 313 10 [(2, 3), (3, 1), (13, 1)]
    (PT.node PT.leaf 317 2 [(2, 2), (79, 1)]
    PT.leaf)))) 331 3 [(2, 1), (3, 1), (5, 1), (11, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 337 10 [(2, 4), (3, 1), (7, 1)]
    PT.leaf) 347 2 [(2, 1), (173, 1)]
    (PT.node PT.leaf 349 2 [(2, 2), (3, 1), (29, 1)]
    PT.leaf)) 353 3 [(2, 5), (11, 1)]
    (PT.node (PT.node PT.leaf 359 7 [(2, 1), (179, 1)]
    PT.leaf) 367 6 [(2, 1), (3, 1), (61, 1)]
    (PT.node PT.leaf 373 2 [(2, 2), (3, 1), (31, 1)]
    PT.leaf))) 379 2 [(2, 1), (3, 3), (7, 1)]
    (PT.node (PT.node (PT.node PT.leaf 383 5 [(2, 1), (191, 1)]
    PT.leaf) 389 2 [(2, 2), (97, 1)]
    (PT.node PT.leaf 397 5 [(2, 2), (3, 2), (11, 1)]
    PT.leaf)) 401 3 [(2, 4), (5, 2)]
    (PT.node (PT.node PT.leaf 409 21 [(2, 3), (3, 1), (17, 1)]
    PT.leaf) 419 2 [(2, 1), (11, 1), (19, 1)]
    (PT.node PT.leaf 421 2 [(2, 2), (3, 1), (5, 1), (7, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab1 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 433 5 [(2, 4), (3, 3)]
    PT.leaf) 439 15 [(2, 1), (3, 1), (73, 1)]
    PT.leaf) 443 2 [(2, 1), (13, 1), (17, 1)]
    (PT.node PT.leaf 449 3 [(2, 6), (7, 1)]
    PT.leaf)) 457 13 [(2, 3), (3, 1), (19, 1)]
    (PT.node (PT.node PT.leaf 461 2 [(2, 2), (5, 1), (23, 1)]
    PT.leaf) 463 3 [(2, 1), (3, 1), (7, 1), (11, 1)]
    (PT.node PT.leaf 467 2 [(2, 1), (233, 1)]
    PT.leaf))) 479 13 [(2, 1), (239, 1)]
    (PT.node (PT.node (PT.node PT.leaf 487 3 [(2, 1), (3, 5)]
    PT.leaf) 491 2 [(2, 1), (5, 1), (7, 2)]
    (PT.node PT.leaf 499 7 [(2, 1), (3, 1), (83, 1)]
    PT.leaf)) 503 5 [(2, 1), (251, 1)]
    (PT.node (PT.node PT.leaf 509 2 [(2, 2), (127, 1)]
    PT.leaf) 521 3 [(2, 3), (5, 1), (13, 1)]
    (PT.node PT.leaf 523 2 [(2, 1), (3, 2), (29, 1)]
    PT.leaf)))) 541 2 [(2, 2), (3, 3), (5, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 547 2 [(2, 1), (3, 1), (7, 1), (13, 1)]
    PT.leaf) 557 2 [(2, 2), (139, 1)]
    PT.leaf) 563 2 [(2, 1), (281, 1)]
    (PT.node PT.leaf 569 3 [(2, 3), (71, 1)]
    PT.leaf)) 571 3 [(2, 1), (3, 1), (5, 1), (19, 1)]
    (PT.node (PT.node PT.leaf 577 5 [(2, 6), (3, 2)]
    PT.leaf) 587 2 [(2, 1), (293, 1)]
    (PT.node PT.leaf 593 3 [(2, 4), (37, 1)]
    PT.leaf))) 599 7 [(2, 1), (13, 1), (23, 1)]
    (PT.node (PT.node (PT.node PT.leaf 601 7 [(2, 3), (3, 1), (5, 2)]
    PT.leaf) 607 3 [(2, 1), (3, 1), (101, 1)]
    (PT.node PT.leaf 613 2 [(2, 2), (3, 2), (17, 1)]
    PT.leaf)) 617 3 [(2, 3), (7, 1), (11, 1)]
    (PT.node (PT.node PT.leaf 619 2 [(2, 1), (3, 1), (103, 1)]
    PT.leaf) 631 3 [(2, 1), (3, 2), (5, 1), (7, 1)]
    (PT.node PT.leaf 641 3 [(2, 7), (5, 1)]
    PT.leaf))))) 643 11 [(2, 1), (3, 1), (107, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 647 5 [(2, 1), (17, 1), (19, 1)]
    PT.leaf) 653 2 [(2, 2), (163, 1)]
    PT.leaf) 659 2 [(2, 1), (7, 1), (47, 1)]
    (PT.node PT.leaf 661 2 [(2, 2), (3, 1), (5, 1), (11, 1)]
    PT.leaf)) 673 5 [(2, 5), (3, 1), (7, 1)]
    (PT.node (PT.node PT.leaf 683 5 [(2, 1), (11, 1), (31, 1)]
    PT.leaf) 691 3 [(2, 1), (3, 1), (5, 1), (23, 1)]
    (PT.node PT.leaf 701 2 [(2, 2), (5, 2), (7, 1)]
    PT.leaf))) 709 2 [(2, 2), (3, 1), (59, 1)]
    (PT.node (PT.node (PT.node PT.leaf 719 11 [(2, 1), (359, 1)]
    PT.leaf) 727 5 [(2, 1), (3, 1), (11, 2)]
    (PT.node PT.leaf 733 6 [(2, 2), (3, 1), (61, 1)]
    PT.leaf)) 739 3 [(2, 1), (3, 2), (41, 1)]
    (PT.node (PT.node PT.leaf 743 5 [(2, 1), (7, 1), (53, 1)]
    PT.leaf) 751 3 [(2, 1), (3, 1), (5, 3)]
    (PT.node PT.leaf 761 6 [(2, 3), (5, 1), (19, 1)]
    PT.leaf)))) 769 11 [(2, 8), (3, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 773 2 [(2, 2), (193, 1)]
    PT.leaf) 787 2 [(2, 1), (3, 1), (131, 1)]
    (PT.node PT.leaf 797 2 [(2, 2), (199, 1)]
    PT.leaf)) 809 3 [(2, 3), (101, 1)]
    (PT.node (PT.node PT.leaf 811 3 [(2, 1), (3, 4), (5, 1)]
    PT.leaf) 821 2 [(2, 2), (5, 1), (41, 1)]
    (PT.node PT.leaf 823 3 [(2, 1), (3, 1), (137, 1)]
    PT.leaf))) 827 2 [(2, 1), (7, 1), (59, 1)]
    (PT.node (PT.node (PT.node PT.leaf 829 2 [(2, 2), (3, 2), (23, 1)]
    PT.leaf) 839 11 [(2, 1), (419, 1)]
    (PT.node PT.leaf 853 2 [(2, 2), (3, 1), (71, 1)]
    PT.leaf)) 859 2 [(2, 1), (3, 1), (11, 1), (13, 1)]
    (PT.node (PT.node PT.leaf 881 3 [(2, 4), (5, 1), (11, 1)]
    PT.leaf) 883 2 [(2, 1), (3, 2), (7, 2)]
    (PT.node PT.leaf 907 2 [(2, 1), (3, 1), (151, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab2 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 919 7 [(2, 1), (3, 3), (17, 1)]
    PT.leaf) 929 3 [(2, 5), (29, 1)]
    PT.leaf) 937 5 [(2, 3), (3, 2), (13, 1)]
    (PT.node PT.leaf 941 2 [(2, 2), (5, 1), (47, 1)]
    PT.leaf)) 947 2 [(2, 1), (11, 1), (43, 1)]
    (PT.node (PT.node PT.leaf 953 3 [(2, 3), (7, 1), (17, 1)]
    PT.leaf) 967 5 [(2, 1), (3, 1), (7, 1), (23, 1)]
    (PT.node PT.leaf 977 3 [(2, 4), (61, 1)]
    PT.leaf))) 983 5 [(2, 1), (491, 1)]
    (PT.node (PT.node (PT.node PT.leaf 991 6 [(2, 1), (3, 2), (5, 1), (11, 1)]
    PT.leaf) 997 7 [(2, 2), (3, 1), (83, 1)]
    (PT.node PT.leaf 1009 11 [(2, 4), (3, 2), (7, 1)]
    PT.leaf)) 1013 3 [(2, 2), (11, 1), (23, 1)]
    (PT.node (PT.node PT.leaf 1019 2 [(2, 1), (509, 1)]
    PT.leaf) 1021 10 [(2, 2), (3, 1), (5, 1), (17, 1)]
    (PT.node PT.leaf 1031 14 [(2, 1), (5, 1), (103, 1)]
    PT.leaf)))) 1033 5 [(2, 3), (3, 1), (43, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 1039 3 [(2, 1), (3, 1), (173, 1)]
    PT.leaf) 1049 3 [(2, 3), (131, 1)]
    PT.leaf) 1051 7 [(2, 1), (3, 1), (5, 2), (7, 1)]
    (PT.node PT.leaf 1061 2 [(2, 2), (5, 1), (53, 1)]
    PT.leaf)) 1063 3 [(2, 1), (3, 2), (59, 1)]
    (PT.node (PT.node PT.leaf 1069 6 [(2, 2), (3, 1), (89, 1)]
    PT.leaf) 1091 2 [(2, 1), (5, 1), (109, 1)]
    (PT.node PT.leaf 1093 5 [(2, 2), (3, 1), (7, 1), (13, 1)]
    PT.leaf))) 1097 3 [(2, 3), (137, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1109 2 [(2, 2), (277, 1)]
    PT.leaf) 1117 2 [(2, 2), (3, 2), (31, 1)]
    (PT.node PT.leaf 1123 2 [(2, 1), (3, 1), (11, 1), (17, 1)]
    PT.leaf)) 1129 11 [(2, 3), (3, 1), (47, 1)]
    (PT.node (PT.node PT.leaf 1151 17 [(2, 1), (5, 2), (23, 1)]
    PT.leaf) 1153 5 [(2, 7), (3, 2)]
    (PT.node PT.leaf 1163 5 [(2, 1), (7, 1), (83, 1)]
    PT.leaf))))) 1171 2 [(2, 1), (3, 2), (5, 1), (13, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 1181 7 [(2, 2), (5, 1), (59, 1)]
    PT.leaf) 1187 2 [(2, 1), (593, 1)]
    PT.leaf) 1193 3 [(2, 3), (149, 1)]
    (PT.node PT.leaf 1201 11 [(2, 4), (3, 1), (5, 2)]
    PT.leaf)) 1213 2 [(2, 2), (3, 1), (101, 1)]
    (PT.node (PT.node PT.leaf 1217 3 [(2, 6), (19, 1)]
    PT.leaf) 1223 5 [(2, 1), (13, 1), (47, 1)]
    (PT.node PT.leaf 1229 2 [(2, 2), (307, 1)]
    PT.leaf))) 1237 2 [(2, 2), (3, 1), (103, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1249 7 [(2, 5), (3, 1), (13, 1)]
    PT.leaf) 1259 2 [(2, 1), (17, 1), (37, 1)]
    (PT.node PT.leaf 1277 2 [(2, 2), (11, 1), (29, 1)]
    PT.leaf)) 1279 3 [(2, 1), (3, 2), (71, 1)]
    (PT.node (PT.node PT.leaf 1283 2 [(2, 1), (641, 1)]
    PT.leaf) 1289 6 [(2, 3), (7, 1), (23, 1)]
    (PT.node PT.leaf 1291 2 [(2, 1), (3, 1), (5, 1), (43, 1)]
    PT.leaf)))) 1297 10 [(2, 4), (3, 4)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 1301 2 [(2, 2), (5, 2), (13, 1)]
    PT.leaf) 1303 6 [(2, 1), (3, 1), (7, 1), (31, 1)]
    (PT.node PT.leaf 1307 2 [(2, 1), (653, 1)]
    PT.leaf)) 1319 13 [(2, 1), (659, 1)]
    (PT.node (PT.node PT.leaf 1321 13 [(2, 3), (3, 1), (5, 1), (11, 1)]
    PT.leaf) 1327 3 [(2, 1), (3, 1), (13, 1), (17, 1)]
    (PT.node PT.leaf 1361 3 [(2, 4), (5, 1), (17, 1)]
    PT.leaf))) 1367 5 [(2, 1), (683, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1373 2 [(2, 2), (7, 3)]
    PT.leaf) 1381 2 [(2, 2), (3, 1), (5, 1), (23, 1)]
    (PT.node PT.leaf 1399 13 [(2, 1), (3, 1), (233, 1)]
    PT.leaf)) 1409 3 [(2, 7), (11, 1)]
    (PT.node (PT.node PT.leaf 1423 3 [(2, 1), (3, 2), (79, 1)]
    PT.leaf) 1427 2 [(2, 1), (23, 1), (31, 1)]
    (PT.node PT.leaf 1429 6 [(2, 2), (3, 1), (7, 1), (17, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab3 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 1439 7 [(2, 1), (719, 1)]
    PT.leaf) 1451 2 [(2, 1), (5, 2), (29, 1)]
    PT.leaf) 1453 2 [(2, 2), (3, 1), (11, 2)]
    (PT.node PT.leaf 1459 3 [(2, 1), (3, 6)]
    PT.leaf)) 1471 6 [(2, 1), (3, 1), (5, 1), (7, 2)]
    (PT.node (PT.node PT.leaf 1481 3 [(2, 3), (5, 1), (37, 1)]
    PT.leaf) 1493 2 [(2, 2), (373, 1)]
    (PT.node PT.leaf 1511 11 [(2, 1), (5, 1), (151, 1)]
    PT.leaf))) 1523 2 [(2, 1), (761, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1531 2 [(2, 1), (3, 2), (5, 1), (17, 1)]
    PT.leaf) 1549 2 [(2, 2), (3, 2), (43, 1)]
    (PT.node PT.leaf 1559 19 [(2, 1), (19, 1), (41, 1)]
    PT.leaf)) 1567 3 [(2, 1), (3, 3), (29, 1)]
    (PT.node (PT.node PT.leaf 1579 3 [(2, 1), (3, 1), (263, 1)]
    PT.leaf) 1583 5 [(2, 1), (7, 1), (113, 1)]
    (PT.node PT.leaf 1601 3 [(2, 6), (5, 2)]
    PT.leaf)))) 1607 5 [(2, 1), (11, 1), (73, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 1609 7 [(2, 3), (3, 1), (67, 1)]
    PT.leaf) 1613 3 [(2, 2), (13, 1), (31, 1)]
    (PT.node PT.leaf 1619 2 [(2, 1), (809, 1)]
    PT.leaf)) 1621 2 [(2, 2), (3, 4), (5, 1)]
    (PT.node (PT.node PT.leaf 1627 3 [(2, 1), (3, 1), (271, 1)]
    PT.leaf) 1657 11 [(2, 3), (3, 2), (23, 1)]
    (PT.node PT.leaf 1663 3 [(2, 1), (3, 1), (277, 1)]
    PT.leaf))) 1667 2 [(2, 1), (7, 2), (17, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1693 2 [(2, 2), (3, 2), (47, 1)]
    PT.leaf) 1699 3 [(2, 1), (3, 1), (283, 1)]
    (PT.node PT.leaf 1709 3 [(2, 2), (7, 1), (61, 1)]
    PT.leaf)) 1723 3 [(2, 1), (3, 1), (7, 1), (41, 1)]
    (PT.node (PT.node PT.leaf 1733 2 [(2, 2), (433, 1)]
    PT.leaf) 1741 2 [(2, 2), (3, 1), (5, 1), (29, 1)]
    (PT.node PT.leaf 1747 2 [(2, 1), (3, 2), (97, 1)]
    PT.leaf))))) 1753 7 [(2, 3), (3, 1), (73, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 1759 6 [(2, 1), (3, 1), (293, 1)]
    PT.leaf) 1777 5 [(2, 4), (3, 1), (37, 1)]
    PT.leaf) 1783 10 [(2, 1), (3, 4), (11, 1)]
    (PT.node PT.leaf 1787 2 [(2, 1), (19, 1), (47, 1)]
    PT.leaf)) 1811 6 [(2, 1), (5, 1), (181, 1)]
    (PT.node (PT.node PT.leaf 1823 5 [(2, 1), (911, 1)]
    PT.leaf) 1831 3 [(2, 1), (3, 1), (5, 1), (61, 1)]
    (PT.node PT.leaf 1847 5 [(2, 1), (13, 1), (71, 1)]
    PT.leaf))) 1861 2 [(2, 2), (3, 1), (5, 1), (31, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1867 2 [(2, 1), (3, 1), (311, 1)]
    PT.leaf) 1871 14 [(2, 1), (5, 1), (11, 1), (17, 1)]
    (PT.node PT.leaf 1873 10 [(2, 4), (3, 2), (13, 1)]
    PT.leaf)) 1879 6 [(2, 1), (3, 1), (313, 1)]
    (PT.node (PT.node PT.leaf 1889 3 [(2, 5), (59, 1)]
    PT.leaf) 1901 2 [(2, 2), (5, 2), (19, 1)]
    (PT.node PT.leaf 1907 2 [(2, 1), (953, 1)]
    PT.leaf)))) 1913 3 [(2, 3), (239, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 1931 2 [(2, 1), (5, 1), (193, 1)]
    PT.leaf) 1933 5 [(2, 2), (3, 1), (7, 1), (23, 1)]
    (PT.node PT.leaf 1951 3 [(2, 1), (3, 1), (5, 2), (13, 1)]
    PT.leaf)) 1973 2 [(2, 2), (17, 1), (29, 1)]
    (PT.node (PT.node PT.leaf 1987 2 [(2, 1), (3, 1), (331, 1)]
    PT.leaf) 2003 5 [(2, 1), (7, 1), (11, 1), (13, 1)]
    (PT.node PT.leaf 2011 3 [(2, 1), (3, 1), (5, 1), (67, 1)]
    PT.leaf))) 2017 5 [(2, 5), (3, 2), (7, 1)]
    (PT.node (PT.node (PT.node PT.leaf 2039 7 [(2, 1), (1019, 1)]
    PT.leaf) 2053 2 [(2, 2), (3, 3), (19, 1)]
    (PT.node PT.leaf 2063 5 [(2, 1), (1031, 1)]
    PT.leaf)) 2081 3 [(2, 5), (5, 1), (13, 1)]
    (PT.node (PT.node PT.leaf 2083 2 [(2, 1), (3, 1), (347, 1)]
    PT.leaf) 2099 2 [(2, 1), (1049, 1)]
    (PT.node PT.leaf 2129 3 [(2, 4), (7, 1), (19, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab4 : PT :=
  PT.node tab0 431 7 [(2, 1), (5, 1), (43, 1)] tab1

/-- Part of the prime table. -/
def tab5 : PT :=
  PT.node tab2 1433 3 [(2, 3), (179, 1)] tab3

/-- Part of the prime table. -/
def tab6 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 2141 2 [(2, 2), (5, 1), (107, 1)]
    PT.leaf) 2143 3 [(2, 1), (3, 2), (7, 1), (17, 1)]
    PT.leaf) 2203 5 [(2, 1), (3, 1), (367, 1)]
    (PT.node PT.leaf 2213 2 [(2, 2), (7, 1), (79, 1)]
    PT.leaf)) 2221 2 [(2, 2), (3, 1), (5, 1), (37, 1)]
    (PT.node (PT.node PT.leaf 2237 2 [(2, 2), (13, 1), (43, 1)]
    PT.leaf) 2239 3 [(2, 1), (3, 1), (373, 1)]
    (PT.node PT.leaf 2243 2 [(2, 1), (19, 1), (59, 1)]
    PT.leaf))) 2251 7 [(2, 1), (3, 2), (5, 3)]
    (PT.node (PT.node (PT.node PT.leaf 2267 2 [(2, 1), (11, 1), (103, 1)]
    PT.leaf) 2269 2 [(2, 2), (3, 4), (7, 1)]
    (PT.node PT.leaf 2309 2 [(2, 2), (577, 1)]
    PT.leaf)) 2311 3 [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1)]
    (PT.node (PT.node PT.leaf 2347 3 [(2, 1), (3, 1), (17, 1), (23, 1)]
    PT.leaf) 2351 13 [(2, 1), (5, 2), (47, 1)]
    (PT.node PT.leaf 2377 5 [(2, 3), (3, 3), (11, 1)]
    PT.leaf)))) 2381 3 [(2, 2), (5, 1), (7, 1), (17, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 2383 5 [(2, 1), (3, 1), (397, 1)]
    PT.leaf) 2389 2 [(2, 2), (3, 1), (199, 1)]
    PT.leaf) 2411 6 [(2, 1), (5, 1), (241, 1)]
    (PT.node PT.leaf 2423 5 [(2, 1), (7, 1), (173, 1)]
    PT.leaf)) 2459 2 [(2, 1), (1229, 1)]
    (PT.node (PT.node PT.leaf 2467 2 [(2, 1), (3, 2), (137, 1)]
    PT.leaf) 2473 5 [(2, 3), (3, 1), (103, 1)]
    (PT.node PT.leaf 2521 17 [(2, 3), (3, 2), (5, 1), (7, 1)]
    PT.leaf))) 2531 2 [(2, 1), (5, 1), (11, 1), (23, 1)]
    (PT.node (PT.node (PT.node PT.leaf 2549 2 [(2, 2), (7, 2), (13, 1)]
    PT.leaf) 2557 2 [(2, 2), (3, 2), (71, 1)]
    (PT.node PT.leaf 2593 7 [(2, 5), (3, 4)]
    PT.leaf)) 2617 5 [(2, 3), (3, 1), (109, 1)]
    (PT.node (PT.node PT.leaf 2647 3 [(2, 1), (3, 3), (7, 2)]
    PT.leaf) 2663 5 [(2, 1), (11, 3)]
    (PT.node PT.leaf 2671 7 [(2, 1), (3, 1), (5, 1), (89, 1)]
    PT.leaf))))) 2689 19 [(2, 7), (3, 1), (7, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 2699 2 [(2, 1), (19, 1), (71, 1)]
    PT.leaf) 2707 2 [(2, 1), (3, 1), (11, 1), (41, 1)]
    PT.leaf) 2711 7 [(2, 1), (5, 1), (271, 1)]
    (PT.node PT.leaf 2713 5 [(2, 3), (3, 1), (113, 1)]
    PT.leaf)) 2719 3 [(2, 1), (3, 2), (151, 1)]
    (PT.node (PT.node PT.leaf 2741 2 [(2, 2), (5, 1), (137, 1)]
    PT.leaf) 2767 3 [(2, 1), (3, 1), (461, 1)]
    (PT.node PT.leaf 2791 6 [(2, 1), (3, 2), (5, 1), (31, 1)]
    PT.leaf))) 2801 3 [(2, 4), (5, 2), (7, 1)]
    (PT.node (PT.node (PT.node PT.leaf 2803 2 [(2, 1), (3, 1), (467, 1)]
    PT.leaf) 2819 2 [(2, 1), (1409, 1)]
    (PT.node PT.leaf 2843 2 [(2, 1), (7, 2), (29, 1)]
    PT.leaf)) 2851 2 [(2, 1), (3, 1), (5, 2), (19, 1)]
    (PT.node (PT.node PT.leaf 2857 11 [(2, 3), (3, 1), (7, 1), (17, 1)]
    PT.leaf) 2879 7 [(2, 1), (1439, 1)]
    (PT.node PT.leaf 2887 5 [(2, 1), (3, 1), (13, 1), (37, 1)]
    PT.leaf)))) 2897 3 [(2, 4), (181, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 2903 5 [(2, 1), (1451, 1)]
    PT.leaf) 2917 5 [(2, 2), (3, 6)]
    (PT.node PT.leaf 2927 5 [(2, 1), (7, 1), (11, 1), (19, 1)]
    PT.leaf)) 2953 13 [(2, 3), (3, 2), (41, 1)]
    (PT.node (PT.node PT.leaf 3011 2 [(2, 1), (5, 1), (7, 1), (43, 1)]
    PT.leaf) 3019 2 [(2, 1), (3, 1), (503, 1)]
    (PT.node PT.leaf 3049 11 [(2, 3), (3, 1), (127, 1)]
    PT.leaf))) 3061 6 [(2, 2), (3, 2), (5, 1), (17, 1)]
    (PT.node (PT.node (PT.node PT.leaf 3067 2 [(2, 1), (3, 1), (7, 1), (73, 1)]
    PT.leaf) 3079 6 [(2, 1), (3, 4), (19, 1)]
    (PT.node PT.leaf 3089 3 [(2, 4), (193, 1)]
    PT.leaf)) 3109 6 [(2, 2), (3, 1), (7, 1), (37, 1)]
    (PT.node (PT.node PT.leaf 3163 3 [(2, 1), (3, 1), (17, 1), (31, 1)]
    PT.leaf) 3167 5 [(2, 1), (1583, 1)]
    (PT.node PT.leaf 3169 7 [(2, 5), (3, 2), (11, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab7 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 3203 2 [(2, 1), (1601, 1)]
    PT.leaf) 3221 10 [(2, 2), (5, 1), (7, 1), (23, 1)]
    PT.leaf) 3229 6 [(2, 2), (3, 1), (269, 1)]
    (PT.node PT.leaf 3271 3 [(2, 1), (3, 1), (5, 1), (109, 1)]
    PT.leaf)) 3307 2 [(2, 1), (3, 1), (19, 1), (29, 1)]
    (PT.node (PT.node PT.leaf 3329 3 [(2, 8), (13, 1)]
    PT.leaf) 3331 3 [(2, 1), (3, 2), (5, 1), (37, 1)]
    (PT.node PT.leaf 3343 5 [(2, 1), (3, 1), (557, 1)]
    PT.leaf))) 3359 11 [(2, 1), (23, 1), (73, 1)]
    (PT.node (PT.node (PT.node PT.leaf 3371 2 [(2, 1), (5, 1), (337, 1)]
    PT.leaf) 3373 5 [(2, 2), (3, 1), (281, 1)]
    (PT.node PT.leaf 3407 5 [(2, 1), (13, 1), (131, 1)]
    PT.leaf)) 3413 2 [(2, 2), (853, 1)]
    (PT.node (PT.node PT.leaf 3457 7 [(2, 7), (3, 3)]
    PT.leaf) 3461 2 [(2, 2), (5, 1), (173, 1)]
    (PT.node PT.leaf 3467 2 [(2, 1), (1733, 1)]
    PT.leaf)))) 3491 2 [(2, 1), (5, 1), (349, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 3517 2 [(2, 2), (3, 1), (293, 1)]
    PT.leaf) 3541 7 [(2, 2), (3, 1), (5, 1), (59, 1)]
    (PT.node PT.leaf 3581 2 [(2, 2), (5, 1), (179, 1)]
    PT.leaf)) 3583 3 [(2, 1), (3, 2), (199, 1)]
    (PT.node (PT.node PT.leaf 3593 3 [(2, 3), (449, 1)]
    PT.leaf) 3607 5 [(2, 1), (3, 1), (601, 1)]
    (PT.node PT.leaf 3613 2 [(2, 2), (3, 1), (7, 1), (43, 1)]
    PT.leaf))) 3617 3 [(2, 5), (113, 1)]
    (PT.node (PT.node (PT.node PT.leaf 3631 15 [(2, 1), (3, 1), (5, 1), (11, 2)]
    PT.leaf) 3671 13 [(2, 1), (5, 1), (367, 1)]
    (PT.node PT.leaf 3677 2 [(2, 2), (919, 1)]
    PT.leaf)) 3709 2 [(2, 2), (3, 2), (103, 1)]
    (PT.node (PT.node PT.leaf 3761 3 [(2, 4), (5, 1), (47, 1)]
    PT.leaf) 3779 2 [(2, 1), (1889, 1)]
    (PT.node PT.leaf 3793 5 [(2, 4), (3, 1), (79, 1)]
    PT.leaf))))) 3803 2 [(2, 1), (1901, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 3833 3 [(2, 3), (479, 1)]
    PT.leaf) 3847 5 [(2, 1), (3, 1), (641, 1)]
    PT.leaf) 3851 2 [(2, 1), (5, 2), (7, 1), (11, 1)]
    (PT.node PT.leaf 3863 5 [(2, 1), (1931, 1)]
    PT.leaf)) 3889 11 [(2, 4), (3, 5)]
    (PT.node (PT.node PT.leaf 3919 3 [(2, 1), (3, 1), (653, 1)]
    PT.leaf) 3931 2 [(2, 1), (3, 1), (5, 1), (131, 1)]
    (PT.node PT.leaf 3967 6 [(2, 1), (3, 1), (661, 1)]
    PT.leaf))) 4003 2 [(2, 1), (3, 1), (23, 1), (29, 1)]
    (PT.node (PT.node (PT.node PT.leaf 4007 5 [(2, 1), (2003, 1)]
    PT.leaf) 4013 2 [(2, 2), (17, 1), (59, 1)]
    (PT.node PT.leaf 4051 10 [(2, 1), (3, 4), (5, 2)]
    PT.leaf)) 4099 2 [(2, 1), (3, 1), (683, 1)]
    (PT.node (PT.node PT.leaf 4111 12 [(2, 1), (3, 1), (5, 1), (137, 1)]
    PT.leaf) 4129 13 [(2, 5), (3, 1), (43, 1)]
    (PT.node PT.leaf 4153 5 [(2, 3), (3, 1), (173, 1)]
    PT.leaf)))) 4219 2 [(2, 1), (3, 1), (19, 1), (37, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 4229 2 [(2, 2), (7, 1), (151, 1)]
    PT.leaf) 4231 3 [(2, 1), (3, 2), (5, 1), (47, 1)]
    (PT.node PT.leaf 4241 3 [(2, 4), (5, 1), (53, 1)]
    PT.leaf)) 4273 5 [(2, 4), (3, 1), (89, 1)]
    (PT.node (PT.node PT.leaf 4283 2 [(2, 1), (2141, 1)]
    PT.leaf) 4297 5 [(2, 3), (3, 1), (179, 1)]
    (PT.node PT.leaf 4421 3 [(2, 2), (5, 1), (13, 1), (17, 1)]
    PT.leaf))) 4441 21 [(2, 3), (3, 1), (5, 1), (37, 1)]
    (PT.node (PT.node (PT.node PT.leaf 4447 3 [(2, 1), (3, 2), (13, 1), (19, 1)]
    PT.leaf) 4519 3 [(2, 1), (3, 2), (251, 1)]
    (PT.node PT.leaf 4523 5 [(2, 1), (7, 1), (17, 1), (19, 1)]
    PT.leaf)) 4549 6 [(2, 2), (3, 1), (379, 1)]
    (PT.node (PT.node PT.leaf 4583 5 [(2, 1), (29, 1), (79, 1)]
    PT.leaf) 4591 11 [(2, 1), (3, 3), (5, 1), (17, 1)]
    (PT.node PT.leaf 4603 2 [(2, 1), (3, 1), (13, 1), (59, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab8 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 4733 5 [(2, 2), (7, 1), (13, 2)]
    PT.leaf) 4759 3 [(2, 1), (3, 1), (13, 1), (61, 1)]
    PT.leaf) 4783 6 [(2, 1), (3, 1), (797, 1)]
    (PT.node PT.leaf 4793 3 [(2, 3), (599, 1)]
    PT.leaf)) 4909 6 [(2, 2), (3, 1), (409, 1)]
    (PT.node (PT.node PT.leaf 4919 13 [(2, 1), (2459, 1)]
    PT.leaf) 4933 2 [(2, 2), (3, 2), (137, 1)]
    (PT.node PT.leaf 4957 2 [(2, 2), (3, 1), (7, 1), (59, 1)]
    PT.leaf))) 4967 5 [(2, 1), (13, 1), (191, 1)]
    (PT.node (PT.node (PT.node PT.leaf 5003 2 [(2, 1), (41, 1), (61, 1)]
    PT.leaf) 5039 11 [(2, 1), (11, 1), (229, 1)]
    (PT.node PT.leaf 5081 3 [(2, 3), (5, 1), (127, 1)]
    PT.leaf)) 5101 6 [(2, 2), (3, 1), (5, 2), (17, 1)]
    (PT.node (PT.node PT.leaf 5113 19 [(2, 3), (3, 2), (71, 1)]
    PT.leaf) 5119 3 [(2, 1), (3, 1), (853, 1)]
    (PT.node PT.leaf 5171 2 [(2, 1), (5, 1), (11, 1), (47, 1)]
    PT.leaf)))) 5189 2 [(2, 2), (1297, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 5209 17 [(2, 3), (3, 1), (7, 1), (31, 1)]
    PT.leaf) 5233 10 [(2, 4), (3, 1), (109, 1)]
    PT.leaf) 5261 2 [(2, 2), (5, 1), (263, 1)]
    (PT.node PT.leaf 5281 7 [(2, 5), (3, 1), (5, 1), (11, 1)]
    PT.leaf)) 5309 2 [(2, 2), (1327, 1)]
    (PT.node (PT.node PT.leaf 5333 2 [(2, 2), (31, 1), (43, 1)]
    PT.leaf) 5399 7 [(2, 1), (2699, 1)]
    (PT.node PT.leaf 5419 3 [(2, 1), (3, 2), (7, 1), (43, 1)]
    PT.leaf))) 5431 3 [(2, 1), (3, 1), (5, 1), (181, 1)]
    (PT.node (PT.node (PT.node PT.leaf 5437 5 [(2, 2), (3, 2), (151, 1)]
    PT.leaf) 5441 3 [(2, 6), (5, 1), (17, 1)]
    (PT.node PT.leaf 5449 7 [(2, 3), (3, 1), (227, 1)]
    PT.leaf)) 5471 7 [(2, 1), (5, 1), (547, 1)]
    (PT.node (PT.node PT.leaf 5519 13 [(2, 1), (31, 1), (89, 1)]
    PT.leaf) 5581 6 [(2, 2), (3, 2), (5, 1), (31, 1)]
    (PT.node PT.leaf 5639 7 [(2, 1), (2819, 1)]
    PT.leaf))))) 5641 14 [(2, 3), (3, 1), (5, 1), (47, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 5701 2 [(2, 2), (3, 1), (5, 2), (19, 1)]
    PT.leaf) 5741 2 [(2, 2), (5, 1), (7, 1), (41, 1)]
    PT.leaf) 5779 2 [(2, 1), (3, 3), (107, 1)]
    (PT.node PT.leaf 5783 7 [(2, 1), (7, 2), (59, 1)]
    PT.leaf)) 5801 3 [(2, 3), (5, 2), (29, 1)]
    (PT.node (PT.node PT.leaf 5807 5 [(2, 1), (2903, 1)]
    PT.leaf) 5851 2 [(2, 1), (3, 2), (5, 2), (13, 1)]
    (PT.node PT.leaf 5881 31 [(2, 3), (3, 1), (5, 1), (7, 2)]
    PT.leaf))) 5897 3 [(2, 3), (11, 1), (67, 1)]
    (PT.node (PT.node (PT.node PT.leaf 5903 5 [(2, 1), (13, 1), (227, 1)]
    PT.leaf) 6037 5 [(2, 2), (3, 1), (503, 1)]
    (PT.node PT.leaf 6043 5 [(2, 1), (3, 1), (19, 1), (53, 1)]
    PT.leaf)) 6073 10 [(2, 3), (3, 1), (11, 1), (23, 1)]
    (PT.node (PT.node PT.leaf 6089 3 [(2, 3), (761, 1)]
    PT.leaf) 6121 7 [(2, 3), (3, 2), (5, 1), (17, 1)]
    (PT.node PT.leaf 6131 2 [(2, 1), (5, 1), (613, 1)]
    PT.leaf)))) 6151 3 [(2, 1), (3, 1), (5, 2), (41, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 6247 5 [(2, 1), (3, 2), (347, 1)]
    PT.leaf) 6263 5 [(2, 1), (31, 1), (101, 1)]
    (PT.node PT.leaf 6271 11 [(2, 1), (3, 1), (5, 1), (11, 1), (19, 1)]
    PT.leaf)) 6317 2 [(2, 2), (1579, 1)]
    (PT.node (PT.node PT.leaf 6469 2 [(2, 2), (3, 1), (7, 2), (11, 1)]
    PT.leaf) 6569 3 [(2, 3), (821, 1)]
    (PT.node PT.leaf 6577 5 [(2, 4), (3, 1), (137, 1)]
    PT.leaf))) 6581 14 [(2, 2), (5, 1), (7, 1), (47, 1)]
    (PT.node (PT.node (PT.node PT.leaf 6719 11 [(2, 1), (3359, 1)]
    PT.leaf) 6737 3 [(2, 4), (421, 1)]
    (PT.node PT.leaf 6781 2 [(2, 2), (3, 1), (5, 1), (113, 1)]
    PT.leaf)) 6827 2 [(2, 1), (3413, 1)]
    (PT.node (PT.node PT.leaf 6841 22 [(2, 3), (3, 2), (5, 1), (19, 1)]
    PT.leaf) 6869 2 [(2, 2), (17, 1), (101, 1)]
    (PT.node PT.leaf 6907 2 [(2, 1), (3, 1), (1151, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab9 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 6983 5 [(2, 1), (3491, 1)]
    PT.leaf) 6991 6 [(2, 1), (3, 1), (5, 1), (233, 1)]
    PT.leaf) 7039 3 [(2, 1), (3, 2), (17, 1), (23, 1)]
    (PT.node PT.leaf 7109 2 [(2, 2), (1777, 1)]
    PT.leaf)) 7177 10 [(2, 3), (3, 1), (13, 1), (23, 1)]
    (PT.node (PT.node PT.leaf 7207 3 [(2, 1), (3, 1), (1201, 1)]
    PT.leaf) 7283 2 [(2, 1), (11, 1), (331, 1)]
    (PT.node PT.leaf 7321 7 [(2, 3), (3, 1), (5, 1), (61, 1)]
    PT.leaf))) 7411 2 [(2, 1), (3, 1), (5, 1), (13, 1), (19, 1)]
    (PT.node (PT.node (PT.node PT.leaf 7459 2 [(2, 1), (3, 1), (11, 1), (113, 1)]
    PT.leaf) 7489 7 [(2, 6), (3, 2), (13, 1)]
    (PT.node PT.leaf 7541 2 [(2, 2), (5, 1), (13, 1), (29, 1)]
    PT.leaf)) 7583 5 [(2, 1), (17, 1), (223, 1)]
    (PT.node (PT.node PT.leaf 7621 2 [(2, 2), (3, 1), (5, 1), (127, 1)]
    PT.leaf) 7639 7 [(2, 1), (3, 1), (19, 1), (67, 1)]
    (PT.node PT.leaf 7669 2 [(2, 2), (3, 3), (71, 1)]
    PT.leaf)))) 7691 2 [(2, 1), (5, 1), (769, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 7727 5 [(2, 1), (3863, 1)]
    PT.leaf) 7741 7 [(2, 2), (3, 2), (5, 1), (43, 1)]
    (PT.node PT.leaf 7753 10 [(2, 3), (3, 1), (17, 1), (19, 1)]
    PT.leaf)) 7789 2 [(2, 2), (3, 1), (11, 1), (59, 1)]
    (PT.node (PT.node PT.leaf 7867 3 [(2, 1), (3, 2), (19, 1), (23, 1)]
    PT.leaf) 7877 2 [(2, 2), (11, 1), (179, 1)]
    (PT.node PT.leaf 7883 2 [(2, 1), (7, 1), (563, 1)]
    PT.leaf))) 7901 2 [(2, 2), (5, 2), (79, 1)]
    (PT.node (PT.node (PT.node PT.leaf 7933 2 [(2, 2), (3, 1), (661, 1)]
    PT.leaf) 7949 2 [(2, 2), (1987, 1)]
    (PT.node PT.leaf 8009 3 [(2, 3), (7, 1), (11, 1), (13, 1)]
    PT.leaf)) 8017 5 [(2, 4), (3, 1), (167, 1)]
    (PT.node (PT.node PT.leaf 8069 2 [(2, 2), (2017, 1)]
    PT.leaf) 8093 2 [(2, 2), (7, 1), (17, 2)]
    (PT.node PT.leaf 8167 3 [(2, 1), (3, 1), (1361, 1)]
    PT.leaf))))) 8191 17 [(2, 1), (3, 2), (5, 1), (7, 1), (13, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 8233 10 [(2, 3), (3, 1), (7, 3)]
    PT.leaf) 8353 5 [(2, 5), (3, 2), (29, 1)]
    PT.leaf) 8429 2 [(2, 2), (7, 2), (43, 1)]
    (PT.node PT.leaf 8527 5 [(2, 1), (3, 1), (7, 2), (29, 1)]
    PT.leaf)) 8719 3 [(2, 1), (3, 1), (1453, 1)]
    (PT.node (PT.node PT.leaf 8737 5 [(2, 5), (3, 1), (7, 1), (13, 1)]
    PT.leaf) 8831 7 [(2, 1), (5, 1), (883, 1)]
    (PT.node PT.leaf 8849 3 [(2, 4), (7, 1), (79, 1)]
    PT.leaf))) 8971 2 [(2, 1), (3, 1), (5, 1), (13, 1), (23, 1)]
    (PT.node (PT.node (PT.node PT.leaf 9001 7 [(2, 3), (3, 2), (5, 3)]
    PT.leaf) 9103 6 [(2, 1), (3, 1), (37, 1), (41, 1)]
    (PT.node PT.leaf 9151 3 [(2, 1), (3, 1), (5, 2), (61, 1)]
    PT.leaf)) 9181 2 [(2, 2), (3, 3), (5, 1), (17, 1)]
    (PT.node (PT.node PT.leaf 9311 7 [(2, 1), (5, 1), (7, 2), (19, 1)]
    PT.leaf) 9337 5 [(2, 3), (3, 1), (389, 1)]
    (PT.node PT.leaf 9371 2 [(2, 1), (5, 1), (937, 1)]
    PT.leaf)))) 9403 3 [(2, 1), (3, 1), (1567, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 9419 2 [(2, 1), (17, 1), (277, 1)]
    PT.leaf) 9473 3 [(2, 8), (37, 1)]
    (PT.node PT.leaf 9491 2 [(2, 1), (5, 1), (13, 1), (73, 1)]
    PT.leaf)) 9511 3 [(2, 1), (3, 1), (5, 1), (317, 1)]
    (PT.node (PT.node PT.leaf 9613 2 [(2, 2), (3, 3), (89, 1)]
    PT.leaf) 9697 10 [(2, 5), (3, 1), (101, 1)]
    (PT.node PT.leaf 9781 6 [(2, 2), (3, 1), (5, 1), (163, 1)]
    PT.leaf))) 9829 10 [(2, 2), (3, 3), (7, 1), (13, 1)]
    (PT.node (PT.node (PT.node PT.leaf 9931 10 [(2, 1), (3, 1), (5, 1), (331, 1)]
    PT.leaf) 10079 11 [(2, 1), (5039, 1)]
    (PT.node PT.leaf 10091 2 [(2, 1), (5, 1), (1009, 1)]
    PT.leaf)) 10099 2 [(2, 1), (3, 3), (11, 1), (17, 1)]
    (PT.node (PT.node PT.leaf 10133 2 [(2, 2), (17, 1), (149, 1)]
    PT.leaf) 10141 2 [(2, 2), (3, 1), (5, 1), (13, 2)]
    (PT.node PT.leaf 10169 3 [(2, 3), (31, 1), (41, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab10 : PT :=
  PT.node tab6 3187 2 [(2, 1), (3, 3), (59, 1)] tab7

/-- Part of the prime table. -/
def tab11 : PT :=
  PT.node tab8 6917 2 [(2, 2), (7, 1), (13, 1), (19, 1)] tab9

/-- Part of the prime table. -/
def tab12 : PT :=
  PT.node tab4 911 17 [(2, 1), (5, 1), (7, 1), (13, 1)] tab5

/-- Part of the prime table. -/
def tab13 : PT :=
  PT.node tab10 4639 3 [(2, 1), (3, 1), (773, 1)] tab11

/-- Part of the prime table. -/
def tab14 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 10289 3 [(2, 4), (643, 1)]
    PT.leaf) 10303 3 [(2, 1), (3, 1), (17, 1), (101, 1)]
    PT.leaf) 10453 5 [(2, 2), (3, 1), (13, 1), (67, 1)]
    (PT.node PT.leaf 10501 2 [(2, 2), (3, 1), (5, 3), (7, 1)]
    PT.leaf)) 10529 3 [(2, 5), (7, 1), (47, 1)]
    (PT.node (PT.node PT.leaf 10613 2 [(2, 2), (7, 1), (379, 1)]
    PT.leaf) 10739 6 [(2, 1), (7, 1), (13, 1), (59, 1)]
    (PT.node PT.leaf 10753 11 [(2, 9), (3, 1), (7, 1)]
    PT.leaf))) 10853 2 [(2, 2), (2713, 1)]
    (PT.node (PT.node (PT.node PT.leaf 10883 2 [(2, 1), (5441, 1)]
    PT.leaf) 10891 2 [(2, 1), (3, 2), (5, 1), (11, 2)]
    (PT.node PT.leaf 10937 3 [(2, 3), (1367, 1)]
    PT.leaf)) 10993 7 [(2, 4), (3, 1), (229, 1)]
    (PT.node (PT.node PT.leaf 11047 3 [(2, 1), (3, 1), (7, 1), (263, 1)]
    PT.leaf) 11093 2 [(2, 2), (47, 1), (59, 1)]
    (PT.node PT.leaf 11131 2 [(2, 1), (3, 1), (5, 1), (7, 1), (53, 1)]
    PT.leaf)))) 11279 7 [(2, 1), (5639, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 11311 3 [(2, 1), (3, 1), (5, 1), (13, 1), (29, 1)]
    PT.leaf) 11317 2 [(2, 2), (3, 1), (23, 1), (41, 1)]
    PT.leaf) 11437 2 [(2, 2), (3, 1), (953, 1)]
    (PT.node PT.leaf 11447 5 [(2, 1), (59, 1), (97, 1)]
    PT.leaf)) 11483 2 [(2, 1), (5741, 1)]
    (PT.node (PT.node PT.leaf 11503 3 [(2, 1), (3, 4), (71, 1)]
    PT.leaf) 11549 2 [(2, 2), (2887, 1)]
    (PT.node PT.leaf 11777 3 [(2, 9), (23, 1)]
    PT.leaf))) 11801 3 [(2, 3), (5, 2), (59, 1)]
    (PT.node (PT.node (PT.node PT.leaf 11807 5 [(2, 1), (5903, 1)]
    PT.leaf) 11833 5 [(2, 3), (3, 1), (17, 1), (29, 1)]
    (PT.node PT.leaf 11923 5 [(2, 1), (3, 1), (1987, 1)]
    PT.leaf)) 11939 2 [(2, 1), (47, 1), (127, 1)]
    (PT.node (PT.node PT.leaf 12011 2 [(2, 1), (5, 1), (1201, 1)]
    PT.leaf) 12073 7 [(2, 3), (3, 1), (503, 1)]
    (PT.node PT.leaf 12197 2 [(2, 2), (3049, 1)]
    PT.leaf))))) 12263 5 [(2, 1), (6131, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 12277 2 [(2, 2), (3, 2), (11, 1), (31, 1)]
    PT.leaf) 12289 11 [(2, 12), (3, 1)]
    PT.leaf) 12301 2 [(2, 2), (3, 1), (5, 2), (41, 1)]
    (PT.node PT.leaf 12541 14 [(2, 2), (3, 1), (5, 1), (11, 1), (19, 1)]
    PT.leaf)) 12637 2 [(2, 2), (3, 5), (13, 1)]
    (PT.node (PT.node PT.leaf 12653 2 [(2, 2), (3163, 1)]
    PT.leaf) 12757 2 [(2, 2), (3, 1), (1063, 1)]
    (PT.node PT.leaf 12791 7 [(2, 1), (5, 1), (1279, 1)]
    PT.leaf))) 12809 3 [(2, 3), (1601, 1)]
    (PT.node (PT.node (PT.node PT.leaf 12923 2 [(2, 1), (7, 1), (13, 1), (71, 1)]
    PT.leaf) 12953 3 [(2, 3), (1619, 1)]
    (PT.node PT.leaf 12959 7 [(2, 1), (11, 1), (19, 1), (31, 1)]
    PT.leaf)) 12979 2 [(2, 1), (3, 2), (7, 1), (103, 1)]
    (PT.node (PT.node PT.leaf 13001 3 [(2, 3), (5, 3), (13, 1)]
    PT.leaf) 13033 5 [(2, 3), (3, 2), (181, 1)]
    (PT.node PT.leaf 13063 5 [(2, 1), (3, 1), (7, 1), (311, 1)]
    PT.leaf)))) 13163 2 [(2, 1), (6581, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 13171 11 [(2, 1), (3, 1), (5, 1), (439, 1)]
    PT.leaf) 13217 3 [(2, 5), (7, 1), (59, 1)]
    (PT.node PT.leaf 13259 6 [(2, 1), (7, 1), (947, 1)]
    PT.leaf)) 13267 3 [(2, 1), (3, 2), (11, 1), (67, 1)]
    (PT.node (PT.node PT.leaf 13309 6 [(2, 2), (3, 1), (1109, 1)]
    PT.leaf) 13339 2 [(2, 1), (3, 3), (13, 1), (19, 1)]
    (PT.node PT.leaf 13399 3 [(2, 1), (3, 1), (7, 1), (11, 1), (29, 1)]
    PT.leaf))) 13613 2 [(2, 2), (41, 1), (83, 1)]
    (PT.node (PT.node (PT.node PT.leaf 13679 7 [(2, 1), (7, 1), (977, 1)]
    PT.leaf) 13873 5 [(2, 4), (3, 1), (17, 2)]
    (PT.node PT.leaf 13903 3 [(2, 1), (3, 1), (7, 1), (331, 1)]
    PT.leaf)) 13931 2 [(2, 1), (5, 1), (7, 1), (199, 1)]
    (PT.node (PT.node PT.leaf 13967 5 [(2, 1), (6983, 1)]
    PT.leaf) 14009 3 [(2, 3), (17, 1), (103, 1)]
    (PT.node PT.leaf 14083 3 [(2, 1), (3, 1), (2347, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab15 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 14401 11 [(2, 6), (3, 2), (5, 2)]
    PT.leaf) 14537 3 [(2, 3), (23, 1), (79, 1)]
    PT.leaf) 14543 5 [(2, 1), (11, 1), (661, 1)]
    (PT.node PT.leaf 14593 5 [(2, 8), (3, 1), (19, 1)]
    PT.leaf)) 14621 2 [(2, 2), (5, 1), (17, 1), (43, 1)]
    (PT.node (PT.node PT.leaf 14627 2 [(2, 1), (71, 1), (103, 1)]
    PT.leaf) 14633 3 [(2, 3), (31, 1), (59, 1)]
    (PT.node PT.leaf 14657 3 [(2, 6), (229, 1)]
    PT.leaf))) 14713 5 [(2, 3), (3, 1), (613, 1)]
    (PT.node (PT.node (PT.node PT.leaf 14747 2 [(2, 1), (73, 1), (101, 1)]
    PT.leaf) 14947 2 [(2, 1), (3, 1), (47, 1), (53, 1)]
    (PT.node PT.leaf 15061 2 [(2, 2), (3, 1), (5, 1), (251, 1)]
    PT.leaf)) 15173 2 [(2, 2), (3793, 1)]
    (PT.node (PT.node PT.leaf 15277 6 [(2, 2), (3, 1), (19, 1), (67, 1)]
    PT.leaf) 15527 5 [(2, 1), (7, 1), (1109, 1)]
    (PT.node PT.leaf 15559 3 [(2, 1), (3, 1), (2593, 1)]
    PT.leaf)))) 15601 23 [(2, 4), (3, 1), (5, 2), (13, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 15767 5 [(2, 1), (7883, 1)]
    PT.leaf) 15913 5 [(2, 3), (3, 2), (13, 1), (17, 1)]
    PT.leaf) 15923 2 [(2, 1), (19, 1), (419, 1)]
    (PT.node PT.leaf 16127 5 [(2, 1), (11, 1), (733, 1)]
    PT.leaf)) 16189 2 [(2, 2), (3, 1), (19, 1), (71, 1)]
    (PT.node (PT.node PT.leaf 16369 7 [(2, 4), (3, 1), (11, 1), (31, 1)]
    PT.leaf) 16573 2 [(2, 2), (3, 1), (1381, 1)]
    (PT.node PT.leaf 16651 2 [(2, 1), (3, 2), (5, 2), (37, 1)]
    PT.leaf))) 16747 2 [(2, 1), (3, 1), (2791, 1)]
    (PT.node (PT.node (PT.node PT.leaf 16811 7 [(2, 1), (5, 1), (41, 2)]
    PT.leaf) 17033 3 [(2, 3), (2129, 1)]
    (PT.node PT.leaf 17351 11 [(2, 1), (5, 2), (347, 1)]
    PT.leaf)) 17443 2 [(2, 1), (3, 3), (17, 1), (19, 1)]
    (PT.node (PT.node PT.leaf 17569 11 [(2, 5), (3, 2), (61, 1)]
    PT.leaf) 17573 2 [(2, 2), (23, 1), (191, 1)]
    (PT.node PT.leaf 17581 10 [(2, 2), (3, 1), (5, 1), (293, 1)]
    PT.leaf))))) 17707 3 [(2, 1), (3, 1), (13, 1), (227, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 17729 3 [(2, 6), (277, 1)]
    PT.leaf) 17737 7 [(2, 3), (3, 1), (739, 1)]
    PT.leaf) 17791 3 [(2, 1), (3, 1), (5, 1), (593, 1)]
    (PT.node PT.leaf 17851 2 [(2, 1), (3, 1), (5, 2), (7, 1), (17, 1)]
    PT.leaf)) 17911 3 [(2, 1), (3, 2), (5, 1), (199, 1)]
    (PT.node (PT.node PT.leaf 17923 2 [(2, 1), (3, 1), (29, 1), (103, 1)]
    PT.leaf) 17971 3 [(2, 1), (3, 1), (5, 1), (599, 1)]
    (PT.node PT.leaf 17981 2 [(2, 2), (5, 1), (29, 1), (31, 1)]
    PT.leaf))) 18041 3 [(2, 3), (5, 1), (11, 1), (41, 1)]
    (PT.node (PT.node (PT.node PT.leaf 18043 2 [(2, 1), (3, 1), (31, 1), (97, 1)]
    PT.leaf) 18251 2 [(2, 1), (5, 3), (73, 1)]
    (PT.node PT.leaf 18413 2 [(2, 2), (4603, 1)]
    PT.leaf)) 18427 2 [(2, 1), (3, 1), (37, 1), (83, 1)]
    (PT.node (PT.node PT.leaf 18451 3 [(2, 1), (3, 2), (5, 2), (41, 1)]
    PT.leaf) 18671 7 [(2, 1), (5, 1), (1867, 1)]
    (PT.node PT.leaf 18839 7 [(2, 1), (9419, 1)]
    PT.leaf)))) 19073 3 [(2, 7), (149, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 19163 2 [(2, 1), (11, 1), (13, 1), (67, 1)]
    PT.leaf) 19231 6 [(2, 1), (3, 1), (5, 1), (641, 1)]
    (PT.node PT.leaf 19531 13 [(2, 1), (3, 2), (5, 1), (7, 1), (31, 1)]
    PT.leaf)) 19993 10 [(2, 3), (3, 1), (7, 2), (17, 1)]
    (PT.node (PT.node PT.leaf 20023 3 [(2, 1), (3, 1), (47, 1), (71, 1)]
    PT.leaf) 20857 10 [(2, 3), (3, 1), (11, 1), (79, 1)]
    (PT.node PT.leaf 20947 3 [(2, 1), (3, 1), (3491, 1)]
    PT.leaf))) 21407 5 [(2, 1), (7, 1), (11, 1), (139, 1)]
    (PT.node (PT.node (PT.node PT.leaf 21491 2 [(2, 1), (5, 1), (7, 1), (307, 1)]
    PT.leaf) 21589 2 [(2, 2), (3, 1), (7, 1), (257, 1)]
    (PT.node PT.leaf 21787 23 [(2, 1), (3, 1), (3631, 1)]
    PT.leaf)) 21881 3 [(2, 3), (5, 1), (547, 1)]
    (PT.node (PT.node PT.leaf 21929 3 [(2, 3), (2741, 1)]
    PT.leaf) 21997 7 [(2, 2), (3, 2), (13, 1), (47, 1)]
    (PT.node PT.leaf 22027 3 [(2, 1), (3, 1), (3671, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab16 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 22303 6 [(2, 1), (3, 3), (7, 1), (59, 1)]
    PT.leaf) 22391 13 [(2, 1), (5, 1), (2239, 1)]
    PT.leaf) 22433 3 [(2, 5), (701, 1)]
    (PT.node PT.leaf 22691 2 [(2, 1), (5, 1), (2269, 1)]
    PT.leaf)) 23017 5 [(2, 3), (3, 1), (7, 1), (137, 1)]
    (PT.node (PT.node PT.leaf 23269 6 [(2, 2), (3, 1), (7, 1), (277, 1)]
    PT.leaf) 23497 5 [(2, 3), (3, 1), (11, 1), (89, 1)]
    (PT.node PT.leaf 23549 2 [(2, 2), (7, 1), (29, 2)]
    PT.leaf))) 23593 5 [(2, 3), (3, 1), (983, 1)]
    (PT.node (PT.node (PT.node PT.leaf 23603 2 [(2, 1), (11801, 1)]
    PT.leaf) 23743 3 [(2, 1), (3, 2), (1319, 1)]
    (PT.node PT.leaf 23747 2 [(2, 1), (31, 1), (383, 1)]
    PT.leaf)) 23869 2 [(2, 2), (3, 3), (13, 1), (17, 1)]
    (PT.node (PT.node PT.leaf 23879 7 [(2, 1), (11939, 1)]
    PT.leaf) 23909 2 [(2, 2), (43, 1), (139, 1)]
    (PT.node PT.leaf 24023 5 [(2, 1), (12011, 1)]
    PT.leaf)))) 24061 10 [(2, 2), (3, 1), (5, 1), (401, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 24077 2 [(2, 2), (13, 1), (463, 1)]
    PT.leaf) 24379 2 [(2, 1), (3, 1), (17, 1), (239, 1)]
    PT.leaf) 24481 11 [(2, 5), (3, 2), (5, 1), (17, 1)]
    (PT.node PT.leaf 25037 2 [(2, 2), (11, 1), (569, 1)]
    PT.leaf)) 25057 5 [(2, 5), (3, 3), (29, 1)]
    (PT.node (PT.node PT.leaf 25423 3 [(2, 1), (3, 1), (19, 1), (223, 1)]
    PT.leaf) 25913 3 [(2, 3), (41, 1), (79, 1)]
    (PT.node PT.leaf 26209 11 [(2, 5), (3, 2), (7, 1), (13, 1)]
    PT.leaf))) 26497 5 [(2, 7), (3, 2), (23, 1)]
    (PT.node (PT.node (PT.node PT.leaf 26633 3 [(2, 3), (3329, 1)]
    PT.leaf) 27091 2 [(2, 1), (3, 2), (5, 1), (7, 1), (43, 1)]
    (PT.node PT.leaf 27407 5 [(2, 1), (71, 1), (193, 1)]
    PT.leaf)) 27427 5 [(2, 1), (3, 1), (7, 1), (653, 1)]
    (PT.node (PT.node PT.leaf 27883 3 [(2, 1), (3, 2), (1549, 1)]
    PT.leaf) 28099 2 [(2, 1), (3, 2), (7, 1), (223, 1)]
    (PT.node PT.leaf 28349 2 [(2, 2), (19, 1), (373, 1)]
    PT.leaf))))) 28447 3 [(2, 1), (3, 1), (11, 1), (431, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 28541 2 [(2, 2), (5, 1), (1427, 1)]
    PT.leaf) 28729 22 [(2, 3), (3, 3), (7, 1), (19, 1)]
    PT.leaf) 28859 2 [(2, 1), (47, 1), (307, 1)]
    (PT.node PT.leaf 28909 2 [(2, 2), (3, 2), (11, 1), (73, 1)]
    PT.leaf)) 29207 5 [(2, 1), (17, 1), (859, 1)]
    (PT.node (PT.node PT.leaf 29251 2 [(2, 1), (3, 2), (5, 3), (13, 1)]
    PT.leaf) 29363 2 [(2, 1), (53, 1), (277, 1)]
    (PT.node PT.leaf 29989 2 [(2, 2), (3, 2), (7, 2), (17, 1)]
    PT.leaf))) 30169 7 [(2, 3), (3, 2), (419, 1)]
    (PT.node (PT.node (PT.node PT.leaf 30223 3 [(2, 1), (3, 2), (23, 1), (73, 1)]
    PT.leaf) 30347 2 [(2, 1), (15173, 1)]
    (PT.node PT.leaf 30557 2 [(2, 2), (7639, 1)]
    PT.leaf)) 30703 3 [(2, 1), (3, 1), (7, 1), (17, 1), (43, 1)]
    (PT.node (PT.node PT.leaf 30941 2 [(2, 2), (5, 1), (7, 1), (13, 1), (17, 1)]
    PT.leaf) 31013 2 [(2, 2), (7753, 1)]
    (PT.node PT.leaf 31277 2 [(2, 2), (7, 1), (1117, 1)]
    PT.leaf)))) 31319 7 [(2, 1), (7, 1), (2237, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 31391 31 [(2, 1), (5, 1), (43, 1), (73, 1)]
    PT.leaf) 31469 2 [(2, 2), (7867, 1)]
    (PT.node PT.leaf 31477 6 [(2, 2), (3, 1), (43, 1), (61, 1)]
    PT.leaf)) 31847 5 [(2, 1), (15923, 1)]
    (PT.node (PT.node PT.leaf 31859 2 [(2, 1), (17, 1), (937, 1)]
    PT.leaf) 32059 2 [(2, 1), (3, 2), (13, 1), (137, 1)]
    (PT.node PT.leaf 32309 2 [(2, 2), (41, 1), (197, 1)]
    PT.leaf))) 32327 5 [(2, 1), (7, 1), (2309, 1)]
    (PT.node (PT.node (PT.node PT.leaf 32371 2 [(2, 1), (3, 1), (5, 1), (13, 1), (83, 1)]
    PT.leaf) 32441 3 [(2, 3), (5, 1), (811, 1)]
    (PT.node PT.leaf 32491 2 [(2, 1), (3, 2), (5, 1), (19, 2)]
    PT.leaf)) 32647 3 [(2, 1), (3, 1), (5441, 1)]
    (PT.node (PT.node PT.leaf 32713 5 [(2, 3), (3, 1), (29, 1), (47, 1)]
    PT.leaf) 33023 5 [(2, 1), (11, 1), (19, 1), (79, 1)]
    (PT.node PT.leaf 33479 17 [(2, 1), (19, 1), (881, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab17 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 34759 6 [(2, 1), (3, 2), (1931, 1)]
    PT.leaf) 35461 6 [(2, 2), (3, 2), (5, 1), (197, 1)]
    PT.leaf) 36097 5 [(2, 8), (3, 1), (47, 1)]
    (PT.node PT.leaf 36293 2 [(2, 2), (43, 1), (211, 1)]
    PT.leaf)) 36353 3 [(2, 9), (71, 1)]
    (PT.node (PT.node PT.leaf 36389 3 [(2, 2), (11, 1), (827, 1)]
    PT.leaf) 36451 7 [(2, 1), (3, 6), (5, 2)]
    (PT.node PT.leaf 36871 15 [(2, 1), (3, 1), (5, 1), (1229, 1)]
    PT.leaf))) 37379 2 [(2, 1), (11, 1), (1699, 1)]
    (PT.node (PT.node (PT.node PT.leaf 37861 2 [(2, 2), (3, 1), (5, 1), (631, 1)]
    PT.leaf) 38069 2 [(2, 2), (31, 1), (307, 1)]
    (PT.node PT.leaf 38453 2 [(2, 2), (9613, 1)]
    PT.leaf)) 39103 5 [(2, 1), (3, 1), (7, 3), (19, 1)]
    (PT.node (PT.node PT.leaf 39157 6 [(2, 2), (3, 1), (13, 1), (251, 1)]
    PT.leaf) 39227 2 [(2, 1), (11, 1), (1783, 1)]
    (PT.node PT.leaf 39409 7 [(2, 4), (3, 1), (821, 1)]
    PT.leaf)))) 39971 2 [(2, 1), (5, 1), (7, 1), (571, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 40531 2 [(2, 1), (3, 1), (5, 1), (7, 1), (193, 1)]
    PT.leaf) 40897 5 [(2, 6), (3, 2), (71, 1)]
    (PT.node PT.leaf 41017 5 [(2, 3), (3, 1), (1709, 1)]
    PT.leaf)) 41221 2 [(2, 2), (3, 2), (5, 1), (229, 1)]
    (PT.node (PT.node PT.leaf 41231 7 [(2, 1), (5, 1), (7, 1), (19, 1), (31, 1)]
    PT.leaf) 42019 2 [(2, 1), (3, 1), (47, 1), (149, 1)]
    (PT.node PT.leaf 42073 5 [(2, 3), (3, 1), (1753, 1)]
    PT.leaf))) 42407 5 [(2, 1), (7, 1), (13, 1), (233, 1)]
    (PT.node (PT.node (PT.node PT.leaf 42451 3 [(2, 1), (3, 1), (5, 2), (283, 1)]
    PT.leaf) 42899 2 [(2, 1), (89, 1), (241, 1)]
    (PT.node PT.leaf 43051 2 [(2, 1), (3, 1), (5, 2), (7, 1), (41, 1)]
    PT.leaf)) 43573 2 [(2, 2), (3, 1), (3631, 1)]
    (PT.node (PT.node PT.leaf 43609 14 [(2, 3), (3, 1), (23, 1), (79, 1)]
    PT.leaf) 43711 13 [(2, 1), (3, 1), (5, 1), (31, 1), (47, 1)]
    (PT.node PT.leaf 44111 7 [(2, 1), (5, 1), (11, 1), (401, 1)]
    PT.leaf))))) 44579 2 [(2, 1), (31, 1), (719, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 44641 19 [(2, 5), (3, 2), (5, 1), (31, 1)]
    PT.leaf) 44701 2 [(2, 2), (3, 1), (5, 2), (149, 1)]
    PT.leaf) 44851 10 [(2, 1), (3, 1), (5, 2), (13, 1), (23, 1)]
    (PT.node PT.leaf 44909 2 [(2, 2), (103, 1), (109, 1)]
    PT.leaf)) 45319 3 [(2, 1), (3, 1), (7, 1), (13, 1), (83, 1)]
    (PT.node (PT.node PT.leaf 45979 2 [(2, 1), (3, 1), (79, 1), (97, 1)]
    PT.leaf) 46147 2 [(2, 1), (3, 1), (7691, 1)]
    (PT.node PT.leaf 46457 3 [(2, 3), (5807, 1)]
    PT.leaf))) 46807 3 [(2, 1), (3, 1), (29, 1), (269, 1)]
    (PT.node (PT.node (PT.node PT.leaf 47207 5 [(2, 1), (23603, 1)]
    PT.leaf) 47237 2 [(2, 2), (7, 2), (241, 1)]
    (PT.node PT.leaf 47297 3 [(2, 6), (739, 1)]
    PT.leaf)) 47819 2 [(2, 1), (23909, 1)]
    (PT.node (PT.node PT.leaf 47951 7 [(2, 1), (5, 2), (7, 1), (137, 1)]
    PT.leaf) 48247 3 [(2, 1), (3, 1), (11, 1), (17, 1), (43, 1)]
    (PT.node PT.leaf 48413 2 [(2, 2), (7, 2), (13, 1), (19, 1)]
    PT.leaf)))) 48661 2 [(2, 2), (3, 1), (5, 1), (811, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 49843 2 [(2, 1), (3, 3), (13, 1), (71, 1)]
    PT.leaf) 49927 3 [(2, 1), (3, 1), (53, 1), (157, 1)]
    (PT.node PT.leaf 50129 3 [(2, 4), (13, 1), (241, 1)]
    PT.leaf)) 50227 2 [(2, 1), (3, 1), (11, 1), (761, 1)]
    (PT.node (PT.node PT.leaf 50287 3 [(2, 1), (3, 1), (17, 2), (29, 1)]
    PT.leaf) 51199 12 [(2, 1), (3, 1), (7, 1), (23, 1), (53, 1)]
    (PT.node PT.leaf 51481 17 [(2, 3), (3, 2), (5, 1), (11, 1), (13, 1)]
    PT.leaf))) 51539 2 [(2, 1), (73, 1), (353, 1)]
    (PT.node (PT.node (PT.node PT.leaf 51563 2 [(2, 1), (7, 1), (29, 1), (127, 1)]
    PT.leaf) 51827 2 [(2, 1), (25913, 1)]
    (PT.node PT.leaf 51853 11 [(2, 2), (3, 1), (29, 1), (149, 1)]
    PT.leaf)) 52301 2 [(2, 2), (5, 2), (523, 1)]
    (PT.node (PT.node PT.leaf 52369 13 [(2, 4), (3, 1), (1091, 1)]
    PT.leaf) 52553 3 [(2, 3), (6569, 1)]
    (PT.node PT.leaf 52883 2 [(2, 1), (137, 1), (193, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab18 : PT :=
  PT.node tab14 14177 3 [(2, 5), (443, 1)] tab15

/-- Part of the prime table. -/
def tab19 : PT :=
  PT.node tab16 34511 7 [(2, 1), (5, 1), (7, 1), (17, 1), (29, 1)] tab17

/-- Part of the prime table. -/
def tab20 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 53233 5 [(2, 4), (3, 1), (1109, 1)]
    PT.leaf) 53551 3 [(2, 1), (3, 2), (5, 2), (7, 1), (17, 1)]
    PT.leaf) 53951 7 [(2, 1), (5, 2), (13, 1), (83, 1)]
    (PT.node PT.leaf 54001 11 [(2, 4), (3, 3), (5, 3)]
    PT.leaf)) 54311 11 [(2, 1), (5, 1), (5431, 1)]
    (PT.node (PT.node PT.leaf 54767 5 [(2, 1), (139, 1), (197, 1)]
    PT.leaf) 55333 6 [(2, 2), (3, 2), (29, 1), (53, 1)]
    (PT.node PT.leaf 55529 3 [(2, 3), (11, 1), (631, 1)]
    PT.leaf))) 55609 13 [(2, 3), (3, 1), (7, 1), (331, 1)]
    (PT.node (PT.node (PT.node PT.leaf 55633 5 [(2, 4), (3, 1), (19, 1), (61, 1)]
    PT.leaf) 55897 5 [(2, 3), (3, 1), (17, 1), (137, 1)]
    (PT.node PT.leaf 56821 6 [(2, 2), (3, 1), (5, 1), (947, 1)]
    PT.leaf)) 57679 3 [(2, 1), (3, 1), (9613, 1)]
    (PT.node (PT.node PT.leaf 58573 2 [(2, 2), (3, 2), (1627, 1)]
    PT.leaf) 58579 2 [(2, 1), (3, 1), (13, 1), (751, 1)]
    (PT.node PT.leaf 58687 6 [(2, 1), (3, 1), (9781, 1)]
    PT.leaf)))) 58757 2 [(2, 2), (37, 1), (397, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 59351 13 [(2, 1), (5, 2), (1187, 1)]
    PT.leaf) 59453 2 [(2, 2), (89, 1), (167, 1)]
    PT.leaf) 59467 2 [(2, 1), (3, 1), (11, 1), (17, 1), (53, 1)]
    (PT.node PT.leaf 61483 2 [(2, 1), (3, 1), (10247, 1)]
    PT.leaf)) 62233 7 [(2, 3), (3, 1), (2593, 1)]
    (PT.node (PT.node PT.leaf 62939 2 [(2, 1), (31469, 1)]
    PT.leaf) 63473 3 [(2, 4), (3967, 1)]
    (PT.node PT.leaf 63601 7 [(2, 4), (3, 1), (5, 2), (53, 1)]
    PT.leaf))) 63719 13 [(2, 1), (31859, 1)]
    (PT.node (PT.node (PT.node PT.leaf 64171 7 [(2, 1), (3, 2), (5, 1), (23, 1), (31, 1)]
    PT.leaf) 64453 2 [(2, 2), (3, 1), (41, 1), (131, 1)]
    (PT.node PT.leaf 64621 6 [(2, 2), (3, 2), (5, 1), (359, 1)]
    PT.leaf)) 66047 5 [(2, 1), (33023, 1)]
    (PT.node (PT.node PT.leaf 66457 5 [(2, 3), (3, 2), (13, 1), (71, 1)]
    PT.leaf) 66587 2 [(2, 1), (13, 2), (197, 1)]
    (PT.node PT.leaf 66973 2 [(2, 2), (3, 1), (5581, 1)]
    PT.leaf))))) 67021 7 [(2, 2), (3, 1), (5, 1), (1117, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 67231 3 [(2, 1), (3, 4), (5, 1), (83, 1)]
    PT.leaf) 67411 2 [(2, 1), (3, 2), (5, 1), (7, 1), (107, 1)]
    PT.leaf) 67429 2 [(2, 2), (3, 2), (1873, 1)]
    (PT.node PT.leaf 67447 3 [(2, 1), (3, 3), (1249, 1)]
    PT.leaf)) 67733 2 [(2, 2), (7, 1), (41, 1), (59, 1)]
    (PT.node (PT.node PT.leaf 68743 3 [(2, 1), (3, 3), (19, 1), (67, 1)]
    PT.leaf) 69371 2 [(2, 1), (5, 1), (7, 1), (991, 1)]
    (PT.node PT.leaf 70841 3 [(2, 3), (5, 1), (7, 1), (11, 1), (23, 1)]
    PT.leaf))) 71941 2 [(2, 2), (3, 1), (5, 1), (11, 1), (109, 1)]
    (PT.node (PT.node (PT.node PT.leaf 71947 2 [(2, 1), (3, 2), (7, 1), (571, 1)]
    PT.leaf) 72559 3 [(2, 1), (3, 2), (29, 1), (139, 1)]
    (PT.node PT.leaf 72733 2 [(2, 2), (3, 1), (11, 1), (19, 1), (29, 1)]
    PT.leaf)) 73421 2 [(2, 2), (5, 1), (3671, 1)]
    (PT.node (PT.node PT.leaf 73529 3 [(2, 3), (7, 1), (13, 1), (101, 1)]
    PT.leaf) 73547 2 [(2, 1), (11, 1), (3343, 1)]
    (PT.node PT.leaf 74759 11 [(2, 1), (37379, 1)]
    PT.leaf)))) 75617 3 [(2, 5), (17, 1), (139, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 75931 3 [(2, 1), (3, 1), (5, 1), (2531, 1)]
    PT.leaf) 76207 3 [(2, 1), (3, 1), (13, 1), (977, 1)]
    (PT.node PT.leaf 76253 2 [(2, 2), (11, 1), (1733, 1)]
    PT.leaf)) 76561 17 [(2, 4), (3, 1), (5, 1), (11, 1), (29, 1)]
    (PT.node (PT.node PT.leaf 76907 2 [(2, 1), (38453, 1)]
    PT.leaf) 77477 2 [(2, 2), (7, 1), (2767, 1)]
    (PT.node PT.leaf 77689 14 [(2, 3), (3, 2), (13, 1), (83, 1)]
    PT.leaf))) 79411 2 [(2, 1), (3, 1), (5, 1), (2647, 1)]
    (PT.node (PT.node (PT.node PT.leaf 79579 10 [(2, 1), (3, 2), (4421, 1)]
    PT.leaf) 81071 7 [(2, 1), (5, 1), (11, 2), (67, 1)]
    (PT.node PT.leaf 81401 3 [(2, 3), (5, 2), (11, 1), (37, 1)]
    PT.leaf)) 81439 3 [(2, 1), (3, 1), (7, 2), (277, 1)]
    (PT.node (PT.node PT.leaf 84437 2 [(2, 2), (11, 1), (19, 1), (101, 1)]
    PT.leaf) 84449 3 [(2, 5), (7, 1), (13, 1), (29, 1)]
    (PT.node PT.leaf 85297 15 [(2, 4), (3, 1), (1777, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab21 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 86813 2 [(2, 2), (11, 1), (1973, 1)]
    PT.leaf) 87317 2 [(2, 2), (83, 1), (263, 1)]
    PT.leaf) 91381 17 [(2, 2), (3, 1), (5, 1), (1523, 1)]
    (PT.node PT.leaf 91841 3 [(2, 6), (5, 1), (7, 1), (41, 1)]
    PT.leaf)) 92723 2 [(2, 1), (7, 1), (37, 1), (179, 1)]
    (PT.node (PT.node PT.leaf 93077 2 [(2, 2), (23269, 1)]
    PT.leaf) 93097 10 [(2, 3), (3, 3), (431, 1)]
    (PT.node PT.leaf 93169 11 [(2, 4), (3, 2), (647, 1)]
    PT.leaf))) 93371 2 [(2, 1), (5, 1), (9337, 1)]
    (PT.node (PT.node (PT.node PT.leaf 93607 3 [(2, 1), (3, 1), (15601, 1)]
    PT.leaf) 93739 3 [(2, 1), (3, 1), (17, 1), (919, 1)]
    (PT.node PT.leaf 96493 5 [(2, 2), (3, 1), (11, 1), (17, 1), (43, 1)]
    PT.leaf)) 96661 7 [(2, 2), (3, 3), (5, 1), (179, 1)]
    (PT.node (PT.node PT.leaf 96763 5 [(2, 1), (3, 1), (16127, 1)]
    PT.leaf) 97787 2 [(2, 1), (13, 1), (3761, 1)]
    (PT.node PT.leaf 98519 7 [(2, 1), (7, 1), (31, 1), (227, 1)]
    PT.leaf)))) 98731 2 [(2, 1), (3, 2), (5, 1), (1097, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 98809 17 [(2, 3), (3, 1), (23, 1), (179, 1)]
    PT.leaf) 99439 3 [(2, 1), (3, 1), (16573, 1)]
    (PT.node PT.leaf 99907 2 [(2, 1), (3, 1), (16651, 1)]
    PT.leaf)) 101573 2 [(2, 2), (67, 1), (379, 1)]
    (PT.node (PT.node PT.leaf 102673 5 [(2, 4), (3, 2), (23, 1), (31, 1)]
    PT.leaf) 102913 5 [(2, 9), (3, 1), (67, 1)]
    (PT.node PT.leaf 104179 2 [(2, 1), (3, 1), (97, 1), (179, 1)]
    PT.leaf))) 104281 26 [(2, 3), (3, 1), (5, 1), (11, 1), (79, 1)]
    (PT.node (PT.node (PT.node PT.leaf 105733 6 [(2, 2), (3, 3), (11, 1), (89, 1)]
    PT.leaf) 106747 2 [(2, 1), (3, 1), (17791, 1)]
    (PT.node PT.leaf 108541 2 [(2, 2), (3, 4), (5, 1), (67, 1)]
    PT.leaf)) 110563 2 [(2, 1), (3, 1), (18427, 1)]
    (PT.node (PT.node PT.leaf 111919 3 [(2, 1), (3, 1), (23, 1), (811, 1)]
    PT.leaf) 112429 6 [(2, 2), (3, 4), (347, 1)]
    (PT.node PT.leaf 112859 2 [(2, 1), (73, 1), (773, 1)]
    PT.leaf))))) 114161 3 [(2, 4), (5, 1), (1427, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 114769 11 [(2, 4), (3, 2), (797, 1)]
    PT.leaf) 115637 2 [(2, 2), (28909, 1)]
    PT.leaf) 115903 3 [(2, 1), (3, 2), (47, 1), (137, 1)]
    (PT.node PT.leaf 116131 2 [(2, 1), (3, 1), (5, 1), (7, 2), (79, 1)]
    PT.leaf)) 116533 2 [(2, 2), (3, 3), (13, 1), (83, 1)]
    (PT.node (PT.node PT.leaf 118907 2 [(2, 1), (59453, 1)]
    PT.leaf) 119291 2 [(2, 1), (5, 1), (79, 1), (151, 1)]
    (PT.node PT.leaf 120677 2 [(2, 2), (30169, 1)]
    PT.leaf))) 121267 3 [(2, 1), (3, 2), (6737, 1)]
    (PT.node (PT.node (PT.node PT.leaf 122971 7 [(2, 1), (3, 1), (5, 1), (4099, 1)]
    PT.leaf) 123091 2 [(2, 1), (3, 1), (5, 1), (11, 1), (373, 1)]
    (PT.node PT.leaf 124001 3 [(2, 5), (5, 3), (31, 1)]
    PT.leaf)) 125017 5 [(2, 3), (3, 1), (5209, 1)]
    (PT.node (PT.node PT.leaf 125113 5 [(2, 3), (3, 1), (13, 1), (401, 1)]
    PT.leaf) 125683 2 [(2, 1), (3, 1), (20947, 1)]
    (PT.node PT.leaf 126311 23 [(2, 1), (5, 1), (17, 1), (743, 1)]
    PT.leaf)))) 126323 2 [(2, 1), (7, 2), (1289, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 127691 2 [(2, 1), (5, 1), (113, 2)]
    PT.leaf) 127873 15 [(2, 7), (3, 3), (37, 1)]
    (PT.node PT.leaf 128341 2 [(2, 2), (3, 2), (5, 1), (23, 1), (31, 1)]
    PT.leaf)) 130969 13 [(2, 3), (3, 2), (17, 1), (107, 1)]
    (PT.node (PT.node PT.leaf 134507 2 [(2, 1), (109, 1), (617, 1)]
    PT.leaf) 136463 5 [(2, 1), (31, 2), (71, 1)]
    (PT.node PT.leaf 138793 5 [(2, 3), (3, 1), (5783, 1)]
    PT.leaf))) 142969 11 [(2, 3), (3, 1), (7, 1), (23, 1), (37, 1)]
    (PT.node (PT.node (PT.node PT.leaf 144013 2 [(2, 2), (3, 1), (11, 1), (1091, 1)]
    PT.leaf) 145931 2 [(2, 1), (5, 1), (14593, 1)]
    (PT.node PT.leaf 149519 13 [(2, 1), (74759, 1)]
    PT.leaf)) 151169 3 [(2, 7), (1181, 1)]
    (PT.node (PT.node PT.leaf 151273 5 [(2, 3), (3, 2), (11, 1), (191, 1)]
    PT.leaf) 155821 6 [(2, 2), (3, 1), (5, 1), (7, 2), (53, 1)]
    (PT.node PT.leaf 158959 3 [(2, 1), (3, 2), (8831, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab22 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 159799 3 [(2, 1), (3, 1), (26633, 1)]
    PT.leaf) 160081 28 [(2, 4), (3, 1), (5, 1), (23, 1), (29, 1)]
    PT.leaf) 160553 3 [(2, 3), (7, 1), (47, 1), (61, 1)]
    (PT.node PT.leaf 161387 2 [(2, 1), (19, 1), (31, 1), (137, 1)]
    PT.leaf)) 161783 5 [(2, 1), (23, 1), (3517, 1)]
    (PT.node (PT.node PT.leaf 162709 2 [(2, 2), (3, 1), (7, 1), (13, 1), (149, 1)]
    PT.leaf) 162821 11 [(2, 2), (5, 1), (7, 1), (1163, 1)]
    (PT.node PT.leaf 162917 2 [(2, 2), (13, 2), (241, 1)]
    PT.leaf))) 163411 3 [(2, 1), (3, 1), (5, 1), (13, 1), (419, 1)]
    (PT.node (PT.node (PT.node PT.leaf 164443 2 [(2, 1), (3, 1), (27407, 1)]
    PT.leaf) 166027 2 [(2, 1), (3, 1), (7, 1), (59, 1), (67, 1)]
    (PT.node PT.leaf 166393 5 [(2, 3), (3, 2), (2311, 1)]
    PT.leaf)) 167429 2 [(2, 2), (19, 1), (2203, 1)]
    (PT.node (PT.node PT.leaf 167597 2 [(2, 2), (11, 1), (13, 1), (293, 1)]
    PT.leaf) 168719 11 [(2, 1), (11, 1), (7669, 1)]
    (PT.node PT.leaf 171043 2 [(2, 1), (3, 1), (29, 1), (983, 1)]
    PT.leaf)))) 175811 2 [(2, 1), (5, 1), (17581, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 176051 2 [(2, 1), (5, 2), (7, 1), (503, 1)]
    PT.leaf) 179743 3 [(2, 1), (3, 1), (29, 1), (1033, 1)]
    PT.leaf) 179827 2 [(2, 1), (3, 1), (17, 1), (41, 1), (43, 1)]
    (PT.node PT.leaf 181141 6 [(2, 2), (3, 1), (5, 1), (3019, 1)]
    PT.leaf)) 181873 5 [(2, 4), (3, 3), (421, 1)]
    (PT.node (PT.node PT.leaf 183067 5 [(2, 1), (3, 1), (13, 1), (2347, 1)]
    PT.leaf) 183307 2 [(2, 1), (3, 1), (137, 1), (223, 1)]
    (PT.node PT.leaf 183569 3 [(2, 4), (7, 1), (11, 1), (149, 1)]
    PT.leaf))) 183697 5 [(2, 4), (3, 1), (43, 1), (89, 1)]
    (PT.node (PT.node (PT.node PT.leaf 184417 10 [(2, 5), (3, 1), (17, 1), (113, 1)]
    PT.leaf) 184511 13 [(2, 1), (5, 1), (18451, 1)]
    (PT.node PT.leaf 186709 7 [(2, 2), (3, 1), (15559, 1)]
    PT.leaf)) 187393 7 [(2, 10), (3, 1), (61, 1)]
    (PT.node (PT.node PT.leaf 189977 3 [(2, 3), (23747, 1)]
    PT.leaf) 191033 3 [(2, 3), (23879, 1)]
    (PT.node PT.leaf 196039 3 [(2, 1), (3, 2), (10891, 1)]
    PT.leaf))))) 200909 2 [(2, 2), (50227, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 201781 6 [(2, 2), (3, 2), (5, 1), (19, 1), (59, 1)]
    PT.leaf) 203761 11 [(2, 4), (3, 2), (5, 1), (283, 1)]
    PT.leaf) 205463 5 [(2, 1), (17, 1), (6043, 1)]
    (PT.node PT.leaf 207523 2 [(2, 1), (3, 5), (7, 1), (61, 1)]
    PT.leaf)) 208279 11 [(2, 1), (3, 3), (7, 1), (19, 1), (29, 1)]
    (PT.node (PT.node PT.leaf 208519 11 [(2, 1), (3, 1), (23, 1), (1511, 1)]
    PT.leaf) 209719 3 [(2, 1), (3, 2), (61, 1), (191, 1)]
    (PT.node PT.leaf 212677 2 [(2, 2), (3, 1), (37, 1), (479, 1)]
    PT.leaf))) 214891 14 [(2, 1), (3, 1), (5, 1), (13, 1), (19, 1), (29, 1)]
    (PT.node (PT.node (PT.node PT.leaf 215143 5 [(2, 1), (3, 1), (23, 1), (1559, 1)]
    PT.leaf) 216211 10 [(2, 1), (3, 1), (5, 1), (7207, 1)]
    (PT.node PT.leaf 216233 3 [(2, 3), (151, 1), (179, 1)]
    PT.leaf)) 216781 2 [(2, 2), (3, 1), (5, 1), (3613, 1)]
    (PT.node (PT.node PT.leaf 217081 11 [(2, 3), (3, 4), (5, 1), (67, 1)]
    PT.leaf) 222841 13 [(2, 3), (3, 2), (5, 1), (619, 1)]
    (PT.node PT.leaf 223037 2 [(2, 2), (11, 1), (37, 1), (137, 1)]
    PT.leaf)))) 226631 13 [(2, 1), (5, 1), (131, 1), (173, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 226741 2 [(2, 2), (3, 1), (5, 1), (3779, 1)]
    PT.leaf) 228677 2 [(2, 2), (7, 1), (8167, 1)]
    (PT.node PT.leaf 229127 5 [(2, 1), (17, 1), (23, 1), (293, 1)]
    PT.leaf)) 232189 2 [(2, 2), (3, 1), (11, 1), (1759, 1)]
    (PT.node (PT.node PT.leaf 232409 3 [(2, 3), (11, 1), (19, 1), (139, 1)]
    PT.leaf) 234293 2 [(2, 2), (58573, 1)]
    (PT.node PT.leaf 234749 2 [(2, 2), (58687, 1)]
    PT.leaf))) 235003 2 [(2, 1), (3, 1), (53, 1), (739, 1)]
    (PT.node (PT.node (PT.node PT.leaf 236377 10 [(2, 3), (3, 2), (7, 2), (67, 1)]
    PT.leaf) 236737 17 [(2, 6), (3, 3), (137, 1)]
    (PT.node PT.leaf 238019 2 [(2, 1), (11, 1), (31, 1), (349, 1)]
    PT.leaf)) 240059 2 [(2, 1), (7, 1), (13, 1), (1319, 1)]
    (PT.node (PT.node PT.leaf 243577 5 [(2, 3), (3, 2), (17, 1), (199, 1)]
    PT.leaf) 244841 3 [(2, 3), (5, 1), (6121, 1)]
    (PT.node PT.leaf 246247 3 [(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (41, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab23 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 252401 3 [(2, 4), (5, 2), (631, 1)]
    PT.leaf) 257993 3 [(2, 3), (7, 1), (17, 1), (271, 1)]
    PT.leaf) 260023 6 [(2, 1), (3, 1), (7, 1), (41, 1), (151, 1)]
    (PT.node PT.leaf 262049 3 [(2, 5), (19, 1), (431, 1)]
    PT.leaf)) 262321 13 [(2, 4), (3, 1), (5, 1), (1093, 1)]
    (PT.node (PT.node PT.leaf 263591 17 [(2, 1), (5, 1), (43, 1), (613, 1)]
    PT.leaf) 263827 7 [(2, 1), (3, 2), (14657, 1)]
    (PT.node PT.leaf 263899 10 [(2, 1), (3, 6), (181, 1)]
    PT.leaf))) 265717 17 [(2, 2), (3, 2), (11, 2), (61, 1)]
    (PT.node (PT.node (PT.node PT.leaf 268207 5 [(2, 1), (3, 1), (44701, 1)]
    PT.leaf) 268547 2 [(2, 1), (19, 1), (37, 1), (191, 1)]
    (PT.node PT.leaf 271241 3 [(2, 3), (5, 1), (6781, 1)]
    PT.leaf)) 274777 5 [(2, 3), (3, 1), (107, 2)]
    (PT.node (PT.node PT.leaf 278743 3 [(2, 1), (3, 1), (46457, 1)]
    PT.leaf) 280121 3 [(2, 3), (5, 1), (47, 1), (149, 1)]
    (PT.node PT.leaf 281549 2 [(2, 2), (59, 1), (1193, 1)]
    PT.leaf)))) 282091 3 [(2, 1), (3, 1), (5, 1), (9403, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 283807 6 [(2, 1), (3, 2), (15767, 1)]
    PT.leaf) 284731 10 [(2, 1), (3, 1), (5, 1), (9491, 1)]
    (PT.node PT.leaf 290999 7 [(2, 1), (83, 1), (1753, 1)]
    PT.leaf)) 291901 17 [(2, 2), (3, 1), (5, 2), (7, 1), (139, 1)]
    (PT.node (PT.node PT.leaf 292661 2 [(2, 2), (5, 1), (14633, 1)]
    PT.leaf) 293459 2 [(2, 1), (11, 1), (13339, 1)]
    (PT.node PT.leaf 294313 10 [(2, 3), (3, 1), (12263, 1)]
    PT.leaf))) 294649 7 [(2, 3), (3, 1), (12277, 1)]
    (PT.node (PT.node (PT.node PT.leaf 306517 2 [(2, 2), (3, 1), (7, 1), (41, 1), (89, 1)]
    PT.leaf) 318589 2 [(2, 2), (3, 1), (139, 1), (191, 1)]
    (PT.node PT.leaf 326873 3 [(2, 3), (7, 1), (13, 1), (449, 1)]
    PT.leaf)) 331841 6 [(2, 6), (5, 1), (17, 1), (61, 1)]
    (PT.node (PT.node PT.leaf 331999 6 [(2, 1), (3, 1), (55333, 1)]
    PT.leaf) 334507 2 [(2, 1), (3, 1), (197, 1), (283, 1)]
    (PT.node PT.leaf 335609 3 [(2, 3), (7, 1), (13, 1), (461, 1)]
    PT.leaf))))) 337871 14 [(2, 1), (5, 1), (13, 1), (23, 1), (113, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 346309 10 [(2, 2), (3, 1), (28859, 1)]
    PT.leaf) 347227 2 [(2, 1), (3, 1), (11, 1), (5261, 1)]
    PT.leaf) 351397 2 [(2, 2), (3, 2), (43, 1), (227, 1)]
    (PT.node PT.leaf 352201 7 [(2, 3), (3, 1), (5, 2), (587, 1)]
    PT.leaf)) 361679 13 [(2, 1), (139, 1), (1301, 1)]
    (PT.node (PT.node PT.leaf 363889 13 [(2, 4), (3, 2), (7, 1), (19, 2)]
    PT.leaf) 369023 5 [(2, 1), (184511, 1)]
    (PT.node PT.leaf 376627 2 [(2, 1), (3, 1), (41, 1), (1531, 1)]
    PT.leaf))) 381371 2 [(2, 1), (5, 1), (11, 1), (3467, 1)]
    (PT.node (PT.node (PT.node PT.leaf 386719 6 [(2, 1), (3, 1), (64453, 1)]
    PT.leaf) 387727 3 [(2, 1), (3, 1), (64621, 1)]
    (PT.node PT.leaf 391337 3 [(2, 3), (11, 1), (4447, 1)]
    PT.leaf)) 398581 2 [(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (73, 1)]
    (PT.node (PT.node PT.leaf 399403 3 [(2, 1), (3, 2), (22189, 1)]
    PT.leaf) 400607 5 [(2, 1), (29, 1), (6907, 1)]
    (PT.node PT.leaf 400997 2 [(2, 2), (17, 1), (5897, 1)]
    PT.leaf)))) 401173 2 [(2, 2), (3, 1), (101, 1), (331, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 401839 3 [(2, 1), (3, 1), (66973, 1)]
    PT.leaf) 402137 5 [(2, 3), (7, 1), (43, 1), (167, 1)]
    (PT.node PT.leaf 414767 5 [(2, 1), (11, 1), (17, 1), (1109, 1)]
    PT.leaf)) 415409 3 [(2, 4), (7, 1), (3709, 1)]
    (PT.node (PT.node PT.leaf 415669 2 [(2, 2), (3, 1), (11, 1), (47, 1), (67, 1)]
    PT.leaf) 416963 5 [(2, 1), (7, 1), (13, 1), (29, 1), (79, 1)]
    (PT.node PT.leaf 427381 10 [(2, 2), (3, 1), (5, 1), (17, 1), (419, 1)]
    PT.leaf))) 429349 2 [(2, 2), (3, 1), (37, 1), (967, 1)]
    (PT.node (PT.node (PT.node PT.leaf 431521 7 [(2, 5), (3, 1), (5, 1), (29, 1), (31, 1)]
    PT.leaf) 434191 3 [(2, 1), (3, 1), (5, 1), (41, 1), (353, 1)]
    (PT.node PT.leaf 435731 6 [(2, 1), (5, 1), (43573, 1)]
    PT.leaf)) 445157 2 [(2, 2), (109, 1), (1021, 1)]
    (PT.node (PT.node PT.leaf 449131 3 [(2, 1), (3, 1), (5, 1), (11, 1), (1361, 1)]
    PT.leaf) 462643 11 [(2, 1), (3, 1), (83, 1), (929, 1)]
    (PT.node PT.leaf 470201 3 [(2, 3), (5, 2), (2351, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab24 : PT :=
  PT.node tab20 86353 10 [(2, 4), (3, 1), (7, 1), (257, 1)] tab21

/-- Part of the prime table. -/
def tab25 : PT :=
  PT.node tab22 246947 2 [(2, 1), (7, 1), (31, 1), (569, 1)] tab23

/-- Part of the prime table. -/
def tab26 : PT :=
  PT.node tab18 22189 2 [(2, 2), (3, 1), (43, 2)] tab19

/-- Part of the prime table. -/
def tab27 : PT :=
  PT.node tab24 159209 3 [(2, 3), (7, 1), (2843, 1)] tab25

/-- Part of the prime table. -/
def tab28 : PT :=
  PT.node tab12 2131 2 [(2, 1), (3, 1), (5, 1), (71, 1)] tab13

/-- Part of the prime table. -/
def tab29 : PT :=
  PT.node tab26 52951 3 [(2, 1), (3, 1), (5, 2), (353, 1)] tab27

/-- Part of the prime table. -/
def tab30 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 479971 2 [(2, 1), (3, 2), (5, 1), (5333, 1)]
    PT.leaf) 481021 2 [(2, 2), (3, 1), (5, 1), (8017, 1)]
    PT.leaf) 483139 2 [(2, 1), (3, 3), (23, 1), (389, 1)]
    (PT.node PT.leaf 509653 6 [(2, 2), (3, 4), (11, 2), (13, 1)]
    PT.leaf)) 520981 13 [(2, 2), (3, 1), (5, 1), (19, 1), (457, 1)]
    (PT.node (PT.node PT.leaf 524099 2 [(2, 1), (262049, 1)]
    PT.leaf) 536621 2 [(2, 2), (5, 1), (7, 1), (3833, 1)]
    (PT.node PT.leaf 538651 3 [(2, 1), (3, 4), (5, 2), (7, 1), (19, 1)]
    PT.leaf))) 548557 5 [(2, 2), (3, 1), (17, 1), (2689, 1)]
    (PT.node (PT.node (PT.node PT.leaf 562399 3 [(2, 1), (3, 1), (67, 1), (1399, 1)]
    PT.leaf) 563099 2 [(2, 1), (281549, 1)]
    (PT.node PT.leaf 565013 2 [(2, 2), (7, 1), (17, 1), (1187, 1)]
    PT.leaf)) 570821 2 [(2, 2), (5, 1), (28541, 1)]
    (PT.node (PT.node PT.leaf 576031 15 [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (211, 1)]
    PT.leaf) 576151 3 [(2, 1), (3, 1), (5, 2), (23, 1), (167, 1)]
    (PT.node PT.leaf 576469 6 [(2, 2), (3, 2), (67, 1), (239, 1)]
    PT.leaf)))) 576791 13 [(2, 1), (5, 1), (57679, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 590077 6 [(2, 2), (3, 2), (37, 1), (443, 1)]
    PT.leaf) 598963 7 [(2, 1), (3, 1), (7, 1), (13, 1), (1097, 1)]
    PT.leaf) 603937 5 [(2, 5), (3, 4), (233, 1)]
    (PT.node PT.leaf 604441 7 [(2, 3), (3, 2), (5, 1), (23, 1), (73, 1)]
    PT.leaf)) 612067 2 [(2, 1), (3, 1), (7, 1), (13, 1), (19, 1), (59, 1)]
    (PT.node (PT.node PT.leaf 613169 3 [(2, 4), (19, 1), (2017, 1)]
    PT.leaf) 613279 3 [(2, 1), (3, 3), (41, 1), (277, 1)]
    (PT.node PT.leaf 617341 6 [(2, 2), (3, 1), (5, 1), (10289, 1)]
    PT.leaf))) 628561 7 [(2, 4), (3, 4), (5, 1), (97, 1)]
    (PT.node (PT.node (PT.node PT.leaf 635837 2 [(2, 2), (158959, 1)]
    PT.leaf) 637073 3 [(2, 4), (29, 1), (1373, 1)]
    (PT.node PT.leaf 637841 21 [(2, 4), (5, 1), (7, 1), (17, 1), (67, 1)]
    PT.leaf)) 638147 5 [(2, 1), (17, 1), (137, 2)]
    (PT.node (PT.node PT.leaf 638233 11 [(2, 3), (3, 1), (7, 1), (29, 1), (131, 1)]
    PT.leaf) 644353 5 [(2, 8), (3, 1), (839, 1)]
    (PT.node PT.leaf 656371 2 [(2, 1), (3, 3), (5, 1), (11, 1), (13, 1), (17, 1)]
    PT.leaf))))) 656737 5 [(2, 5), (3, 1), (6841, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 671219 2 [(2, 1), (335609, 1)]
    PT.leaf) 672901 2 [(2, 2), (3, 1), (5, 2), (2243, 1)]
    PT.leaf) 680657 3 [(2, 4), (19, 1), (2239, 1)]
    (PT.node PT.leaf 680749 2 [(2, 2), (3, 1), (17, 1), (47, 1), (71, 1)]
    PT.leaf)) 684869 3 [(2, 2), (131, 1), (1307, 1)]
    (PT.node (PT.node PT.leaf 723917 2 [(2, 2), (71, 1), (2549, 1)]
    PT.leaf) 731363 2 [(2, 1), (503, 1), (727, 1)]
    (PT.node PT.leaf 734941 2 [(2, 2), (3, 3), (5, 1), (1361, 1)]
    PT.leaf))) 752449 7 [(2, 6), (3, 1), (3919, 1)]
    (PT.node (PT.node (PT.node PT.leaf 788261 2 [(2, 2), (5, 1), (11, 1), (3583, 1)]
    PT.leaf) 797161 17 [(2, 3), (3, 1), (5, 1), (7, 1), (13, 1), (73, 1)]
    (PT.node PT.leaf 799873 10 [(2, 7), (3, 1), (2083, 1)]
    PT.leaf)) 800281 21 [(2, 3), (3, 4), (5, 1), (13, 1), (19, 1)]
    (PT.node (PT.node PT.leaf 810091 3 [(2, 1), (3, 2), (5, 1), (9001, 1)]
    PT.leaf) 813097 7 [(2, 3), (3, 2), (23, 1), (491, 1)]
    (PT.node PT.leaf 822599 7 [(2, 1), (7, 1), (58757, 1)]
    PT.leaf)))) 822761 3 [(2, 3), (5, 1), (67, 1), (307, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 827023 3 [(2, 1), (3, 1), (7, 2), (29, 1), (97, 1)]
    PT.leaf) 830833 15 [(2, 4), (3, 1), (19, 1), (911, 1)]
    (PT.node PT.leaf 833117 2 [(2, 2), (208279, 1)]
    PT.leaf)) 849349 2 [(2, 2), (3, 2), (23593, 1)]
    (PT.node (PT.node PT.leaf 861001 13 [(2, 3), (3, 1), (5, 3), (7, 1), (41, 1)]
    PT.leaf) 864079 3 [(2, 1), (3, 1), (144013, 1)]
    (PT.node PT.leaf 866329 11 [(2, 3), (3, 1), (36097, 1)]
    PT.leaf))) 868381 2 [(2, 2), (3, 1), (5, 1), (41, 1), (353, 1)]
    (PT.node (PT.node (PT.node PT.leaf 871463 5 [(2, 1), (435731, 1)]
    PT.leaf) 879881 6 [(2, 3), (5, 1), (21997, 1)]
    (PT.node PT.leaf 918469 6 [(2, 2), (3, 2), (31, 1), (823, 1)]
    PT.leaf)) 924751 6 [(2, 1), (3, 3), (5, 3), (137, 1)]
    (PT.node (PT.node PT.leaf 926659 2 [(2, 1), (3, 2), (51481, 1)]
    PT.leaf) 926977 5 [(2, 8), (3, 1), (17, 1), (71, 1)]
    (PT.node PT.leaf 940403 2 [(2, 1), (470201, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab31 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 1009153 5 [(2, 9), (3, 3), (73, 1)]
    PT.leaf) 1028263 3 [(2, 1), (3, 1), (17, 2), (593, 1)]
    PT.leaf) 1041757 2 [(2, 2), (3, 1), (86813, 1)]
    (PT.node PT.leaf 1058821 2 [(2, 2), (3, 1), (5, 1), (7, 1), (2521, 1)]
    PT.leaf)) 1063831 3 [(2, 1), (3, 1), (5, 1), (35461, 1)]
    (PT.node (PT.node PT.leaf 1072829 2 [(2, 2), (268207, 1)]
    PT.leaf) 1073243 2 [(2, 1), (536621, 1)]
    (PT.node PT.leaf 1076057 3 [(2, 3), (134507, 1)]
    PT.leaf))) 1077301 10 [(2, 2), (3, 4), (5, 2), (7, 1), (19, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1081291 2 [(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (271, 1)]
    PT.leaf) 1088053 2 [(2, 2), (3, 1), (7, 1), (12953, 1)]
    (PT.node PT.leaf 1097113 5 [(2, 3), (3, 1), (17, 1), (2689, 1)]
    PT.leaf)) 1104113 3 [(2, 4), (151, 1), (457, 1)]
    (PT.node (PT.node PT.leaf 1127809 17 [(2, 7), (3, 2), (11, 1), (89, 1)]
    PT.leaf) 1141081 11 [(2, 3), (3, 1), (5, 1), (37, 1), (257, 1)]
    (PT.node PT.leaf 1156013 2 [(2, 2), (11, 1), (13, 1), (43, 1), (47, 1)]
    PT.leaf)))) 1160839 3 [(2, 1), (3, 3), (7, 1), (37, 1), (83, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 1167449 3 [(2, 3), (145931, 1)]
    PT.leaf) 1171579 2 [(2, 1), (3, 1), (19, 1), (43, 1), (239, 1)]
    PT.leaf) 1180159 3 [(2, 1), (3, 1), (7, 1), (28099, 1)]
    (PT.node PT.leaf 1192753 5 [(2, 4), (3, 3), (11, 1), (251, 1)]
    PT.leaf)) 1198661 2 [(2, 2), (5, 1), (73, 1), (821, 1)]
    (PT.node (PT.node PT.leaf 1222567 3 [(2, 1), (3, 1), (203761, 1)]
    PT.leaf) 1250413 2 [(2, 2), (3, 1), (79, 1), (1319, 1)]
    (PT.node PT.leaf 1269193 10 [(2, 3), (3, 1), (52883, 1)]
    PT.leaf))) 1275683 2 [(2, 1), (637841, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1366861 6 [(2, 2), (3, 1), (5, 1), (11, 1), (19, 1), (109, 1)]
    PT.leaf) 1377757 5 [(2, 2), (3, 3), (12757, 1)]
    (PT.node PT.leaf 1380277 6 [(2, 2), (3, 2), (23, 1), (1667, 1)]
    PT.leaf)) 1387961 15 [(2, 3), (5, 1), (7, 1), (4957, 1)]
    (PT.node (PT.node PT.leaf 1391323 2 [(2, 1), (3, 1), (67, 1), (3461, 1)]
    PT.leaf) 1400507 2 [(2, 1), (47, 2), (317, 1)]
    (PT.node PT.leaf 1469341 10 [(2, 2), (3, 4), (5, 1), (907, 1)]
    PT.leaf))))) 1477807 3 [(2, 1), (3, 1), (11, 1), (22391, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 1513921 21 [(2, 6), (3, 1), (5, 1), (19, 1), (83, 1)]
    PT.leaf) 1535837 2 [(2, 2), (599, 1), (641, 1)]
    PT.leaf) 1539917 2 [(2, 2), (7, 1), (43, 1), (1279, 1)]
    (PT.node PT.leaf 1580653 5 [(2, 2), (3, 2), (23, 2), (83, 1)]
    PT.leaf)) 1599181 6 [(2, 2), (3, 1), (5, 1), (11, 1), (2423, 1)]
    (PT.node (PT.node PT.leaf 1600033 5 [(2, 5), (3, 1), (7, 1), (2381, 1)]
    PT.leaf) 1607357 2 [(2, 2), (401839, 1)]
    (PT.node PT.leaf 1664101 11 [(2, 2), (3, 2), (5, 2), (43, 2)]
    PT.leaf))) 1674289 26 [(2, 4), (3, 2), (7, 1), (11, 1), (151, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1759763 2 [(2, 1), (879881, 1)]
    PT.leaf) 1768423 3 [(2, 1), (3, 1), (47, 1), (6271, 1)]
    (PT.node PT.leaf 1772893 17 [(2, 2), (3, 2), (11, 3), (37, 1)]
    PT.leaf)) 1784611 2 [(2, 1), (3, 2), (5, 1), (79, 1), (251, 1)]
    (PT.node (PT.node PT.leaf 1794041 3 [(2, 3), (5, 1), (44851, 1)]
    PT.leaf) 1803647 5 [(2, 1), (13, 1), (69371, 1)]
    (PT.node PT.leaf 1806113 3 [(2, 5), (7, 1), (11, 1), (733, 1)]
    PT.leaf)))) 1814809 7 [(2, 3), (3, 1), (75617, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 1825297 7 [(2, 4), (3, 1), (11, 1), (3457, 1)]
    PT.leaf) 1826389 2 [(2, 2), (3, 5), (1879, 1)]
    (PT.node PT.leaf 1850573 2 [(2, 2), (462643, 1)]
    PT.leaf)) 1867421 2 [(2, 2), (5, 1), (93371, 1)]
    (PT.node (PT.node PT.leaf 1880807 5 [(2, 1), (940403, 1)]
    PT.leaf) 1888171 33 [(2, 1), (3, 1), (5, 1), (62939, 1)]
    (PT.node PT.leaf 1937959 6 [(2, 1), (3, 1), (11, 1), (29363, 1)]
    PT.leaf))) 1940443 2 [(2, 1), (3, 1), (7, 1), (47, 1), (983, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1944053 2 [(2, 2), (11, 1), (17, 1), (23, 1), (113, 1)]
    PT.leaf) 1963057 5 [(2, 4), (3, 1), (40897, 1)]
    (PT.node PT.leaf 1988689 11 [(2, 4), (3, 1), (13, 1), (3187, 1)]
    PT.leaf)) 2045761 19 [(2, 6), (3, 1), (5, 1), (2131, 1)]
    (PT.node (PT.node PT.leaf 2132771 2 [(2, 1), (5, 1), (271, 1), (787, 1)]
    PT.leaf) 2133031 15 [(2, 1), (3, 1), (5, 1), (97, 1), (733, 1)]
    (PT.node PT.leaf 2164387 3 [(2, 1), (3, 1), (7, 1), (29, 1), (1777, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab32 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 2180921 3 [(2, 3), (5, 1), (7, 1), (7789, 1)]
    PT.leaf) 2197469 2 [(2, 2), (7, 1), (13, 1), (6037, 1)]
    PT.leaf) 2267143 5 [(2, 1), (3, 1), (79, 1), (4783, 1)]
    (PT.node PT.leaf 2289401 3 [(2, 3), (5, 2), (11447, 1)]
    PT.leaf)) 2297881 19 [(2, 3), (3, 2), (5, 1), (13, 1), (491, 1)]
    (PT.node (PT.node PT.leaf 2303293 2 [(2, 2), (3, 1), (367, 1), (523, 1)]
    PT.leaf) 2312027 2 [(2, 1), (1156013, 1)]
    (PT.node PT.leaf 2380141 2 [(2, 2), (3, 2), (5, 1), (7, 1), (1889, 1)]
    PT.leaf))) 2390909 2 [(2, 2), (13, 1), (45979, 1)]
    (PT.node (PT.node (PT.node PT.leaf 2409829 6 [(2, 2), (3, 1), (409, 1), (491, 1)]
    PT.leaf) 2426789 2 [(2, 2), (7, 1), (13, 1), (59, 1), (113, 1)]
    (PT.node PT.leaf 2454637 5 [(2, 2), (3, 1), (59, 1), (3467, 1)]
    PT.leaf)) 2460181 2 [(2, 2), (3, 1), (5, 1), (131, 1), (313, 1)]
    (PT.node (PT.node PT.leaf 2481971 2 [(2, 1), (5, 1), (19, 1), (13063, 1)]
    PT.leaf) 2487697 5 [(2, 4), (3, 1), (51827, 1)]
    (PT.node PT.leaf 2499121 23 [(2, 4), (3, 3), (5, 1), (13, 1), (89, 1)]
    PT.leaf)))) 2554039 3 [(2, 1), (3, 3), (47297, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 2573621 2 [(2, 2), (5, 1), (7, 1), (31, 1), (593, 1)]
    PT.leaf) 2614303 5 [(2, 1), (3, 3), (48413, 1)]
    PT.leaf) 2635909 6 [(2, 2), (3, 1), (11, 1), (19, 1), (1051, 1)]
    (PT.node PT.leaf 2645171 2 [(2, 1), (5, 1), (11, 1), (139, 1), (173, 1)]
    PT.leaf)) 2653727 5 [(2, 1), (97, 1), (13679, 1)]
    (PT.node (PT.node PT.leaf 2677709 2 [(2, 2), (11, 1), (19, 1), (3203, 1)]
    PT.leaf) 2695351 3 [(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (151, 1)]
    (PT.node PT.leaf 2715931 3 [(2, 1), (3, 4), (5, 1), (7, 1), (479, 1)]
    PT.leaf))) 2726089 13 [(2, 3), (3, 1), (97, 1), (1171, 1)]
    (PT.node (PT.node (PT.node PT.leaf 2740249 11 [(2, 3), (3, 2), (7, 1), (5437, 1)]
    PT.leaf) 2780923 2 [(2, 1), (3, 1), (269, 1), (1723, 1)]
    (PT.node PT.leaf 2828219 2 [(2, 1), (23, 1), (61483, 1)]
    PT.leaf)) 2864867 2 [(2, 1), (127, 1), (11279, 1)]
    (PT.node (PT.node PT.leaf 2876483 2 [(2, 1), (7, 1), (205463, 1)]
    PT.leaf) 2905319 7 [(2, 1), (13, 1), (131, 1), (853, 1)]
    (PT.node PT.leaf 2934467 2 [(2, 1), (61, 1), (67, 1), (359, 1)]
    PT.leaf))))) 2961121 13 [(2, 5), (3, 1), (5, 1), (31, 1), (199, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 2972701 26 [(2, 2), (3, 4), (5, 2), (367, 1)]
    PT.leaf) 2993311 15 [(2, 1), (3, 2), (5, 1), (79, 1), (421, 1)]
    PT.leaf) 3034859 2 [(2, 1), (269, 1), (5641, 1)]
    (PT.node PT.leaf 3065147 2 [(2, 1), (7, 2), (31277, 1)]
    PT.leaf)) 3074581 6 [(2, 2), (3, 2), (5, 1), (19, 1), (29, 1), (31, 1)]
    (PT.node (PT.node PT.leaf 3238099 2 [(2, 1), (3, 1), (41, 1), (13163, 1)]
    PT.leaf) 3298481 3 [(2, 4), (5, 1), (41231, 1)]
    (PT.node PT.leaf 3299797 2 [(2, 2), (3, 2), (71, 1), (1291, 1)]
    PT.leaf))) 3318409 7 [(2, 3), (3, 6), (569, 1)]
    (PT.node (PT.node (PT.node PT.leaf 3325937 3 [(2, 4), (97, 1), (2143, 1)]
    PT.leaf) 3331033 7 [(2, 3), (3, 1), (138793, 1)]
    (PT.node PT.leaf 3348577 13 [(2, 5), (3, 2), (7, 1), (11, 1), (151, 1)]
    PT.leaf)) 3362279 7 [(2, 1), (19, 1), (23, 1), (3847, 1)]
    (PT.node (PT.node PT.leaf 3365591 23 [(2, 1), (5, 1), (23, 1), (14633, 1)]
    PT.leaf) 3397663 3 [(2, 1), (3, 2), (31, 1), (6089, 1)]
    (PT.node PT.leaf 3409261 6 [(2, 2), (3, 1), (5, 1), (56821, 1)]
    PT.leaf)))) 3420493 5 [(2, 2), (3, 1), (29, 1), (9829, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 3516001 14 [(2, 5), (3, 1), (5, 3), (293, 1)]
    PT.leaf) 3541249 7 [(2, 8), (3, 2), (29, 1), (53, 1)]
    (PT.node PT.leaf 3557299 11 [(2, 1), (3, 1), (67, 1), (8849, 1)]
    PT.leaf)) 3715757 2 [(2, 2), (11, 1), (84449, 1)]
    (PT.node (PT.node PT.leaf 3758281 11 [(2, 3), (3, 1), (5, 1), (31319, 1)]
    PT.leaf) 3831043 5 [(2, 1), (3, 1), (31, 1), (43, 1), (479, 1)]
    (PT.node PT.leaf 3842677 2 [(2, 2), (3, 2), (173, 1), (617, 1)]
    PT.leaf))) 3852677 3 [(2, 2), (17, 1), (53, 1), (1069, 1)]
    (PT.node (PT.node (PT.node PT.leaf 3855937 10 [(2, 6), (3, 1), (7, 1), (19, 1), (151, 1)]
    PT.leaf) 3950117 2 [(2, 2), (61, 1), (16189, 1)]
    (PT.node PT.leaf 3961333 2 [(2, 2), (3, 3), (43, 1), (853, 1)]
    PT.leaf)) 3981071 17 [(2, 1), (5, 1), (19, 1), (23, 1), (911, 1)]
    (PT.node (PT.node PT.leaf 3989437 2 [(2, 2), (3, 1), (11, 1), (30223, 1)]
    PT.leaf) 4222747 3 [(2, 1), (3, 3), (11, 1), (7109, 1)]
    (PT.node PT.leaf 4252519 3 [(2, 1), (3, 2), (31, 1), (7621, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab33 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 4404047 5 [(2, 1), (31, 1), (251, 1), (283, 1)]
    PT.leaf) 4437733 2 [(2, 2), (3, 1), (13, 1), (28447, 1)]
    PT.leaf) 4533059 2 [(2, 1), (19, 1), (119291, 1)]
    (PT.node PT.leaf 4576433 5 [(2, 4), (7, 1), (29, 1), (1409, 1)]
    PT.leaf)) 4609393 5 [(2, 4), (3, 1), (109, 1), (881, 1)]
    (PT.node (PT.node PT.leaf 4697003 2 [(2, 1), (37, 1), (63473, 1)]
    PT.leaf) 4720637 2 [(2, 2), (1180159, 1)]
    (PT.node PT.leaf 4732369 7 [(2, 4), (3, 1), (19, 1), (5189, 1)]
    PT.leaf))) 4760281 23 [(2, 3), (3, 2), (5, 1), (7, 1), (1889, 1)]
    (PT.node (PT.node (PT.node PT.leaf 4772771 6 [(2, 1), (5, 1), (477277, 1)]
    PT.leaf) 4810493 2 [(2, 2), (53, 1), (22691, 1)]
    (PT.node PT.leaf 4822039 3 [(2, 1), (3, 3), (13, 1), (6869, 1)]
    PT.leaf)) 4849081 11 [(2, 3), (3, 1), (5, 1), (17, 1), (2377, 1)]
    (PT.node (PT.node PT.leaf 5078863 3 [(2, 1), (3, 4), (107, 1), (293, 1)]
    PT.leaf) 5104249 7 [(2, 3), (3, 1), (212677, 1)]
    (PT.node PT.leaf 5132597 2 [(2, 2), (7, 1), (183307, 1)]
    PT.leaf)))) 5141369 3 [(2, 3), (239, 1), (2689, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 5229043 26 [(2, 1), (3, 1), (7, 1), (13, 1), (61, 1), (157, 1)]
    PT.leaf) 5234081 6 [(2, 5), (5, 1), (32713, 1)]
    (PT.node PT.leaf 5308447 6 [(2, 1), (3, 1), (11, 1), (13, 1), (23, 1), (269, 1)]
    PT.leaf)) 5369753 3 [(2, 3), (671219, 1)]
    (PT.node (PT.node PT.leaf 5390701 6 [(2, 2), (3, 1), (5, 2), (7, 1), (17, 1), (151, 1)]
    PT.leaf) 5417851 15 [(2, 1), (3, 1), (5, 2), (19, 1), (1901, 1)]
    (PT.node PT.leaf 5463181 2 [(2, 2), (3, 3), (5, 1), (67, 1), (151, 1)]
    PT.leaf))) 5591899 2 [(2, 1), (3, 2), (13, 1), (23, 1), (1039, 1)]
    (PT.node (PT.node (PT.node PT.leaf 5699873 3 [(2, 5), (59, 1), (3019, 1)]
    PT.leaf) 5700731 2 [(2, 1), (5, 1), (7, 1), (81439, 1)]
    (PT.node PT.leaf 5774023 5 [(2, 1), (3, 2), (97, 1), (3307, 1)]
    PT.leaf)) 5791337 3 [(2, 3), (723917, 1)]
    (PT.node (PT.node PT.leaf 5834947 3 [(2, 1), (3, 1), (13, 1), (239, 1), (313, 1)]
    PT.leaf) 5835173 2 [(2, 2), (7, 1), (271, 1), (769, 1)]
    (PT.node PT.leaf 5874179 2 [(2, 1), (61, 1), (89, 1), (541, 1)]
    PT.leaf))))) 5926729 11 [(2, 3), (3, 1), (246947, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 6232199 14 [(2, 1), (7, 1), (445157, 1)]
    PT.leaf) 6294091 10 [(2, 1), (3, 1), (5, 1), (11, 1), (19073, 1)]
    PT.leaf) 6304673 3 [(2, 5), (11, 1), (17911, 1)]
    (PT.node PT.leaf 6348263 5 [(2, 1), (43, 1), (97, 1), (761, 1)]
    PT.leaf)) 6578839 6 [(2, 1), (3, 2), (7, 2), (7459, 1)]
    (PT.node (PT.node PT.leaf 6579439 3 [(2, 1), (3, 1), (839, 1), (1307, 1)]
    PT.leaf) 6619231 6 [(2, 1), (3, 2), (5, 1), (73547, 1)]
    (PT.node PT.leaf 6662063 5 [(2, 1), (11, 1), (17, 1), (47, 1), (379, 1)]
    PT.leaf))) 6731183 5 [(2, 1), (3365591, 1)]
    (PT.node (PT.node (PT.node PT.leaf 6811369 13 [(2, 3), (3, 1), (283807, 1)]
    PT.leaf) 6935543 5 [(2, 1), (1567, 1), (2213, 1)]
    (PT.node PT.leaf 7038247 3 [(2, 1), (3, 1), (19, 1), (107, 1), (577, 1)]
    PT.leaf)) 7063513 5 [(2, 3), (3, 1), (294313, 1)]
    (PT.node (PT.node PT.leaf 7247629 2 [(2, 2), (3, 2), (109, 1), (1847, 1)]
    PT.leaf) 7440061 6 [(2, 2), (3, 1), (5, 1), (124001, 1)]
    (PT.node PT.leaf 7449133 5 [(2, 2), (3, 1), (151, 1), (4111, 1)]
    PT.leaf)))) 7477117 5 [(2, 2), (3, 1), (23, 1), (27091, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 7596203 2 [(2, 1), (29, 1), (130969, 1)]
    PT.leaf) 7638073 5 [(2, 3), (3, 1), (13, 1), (24481, 1)]
    (PT.node PT.leaf 7670501 2 [(2, 2), (5, 3), (23, 2), (29, 1)]
    PT.leaf)) 7698853 2 [(2, 2), (3, 2), (7, 1), (137, 1), (223, 1)]
    (PT.node (PT.node PT.leaf 7761773 2 [(2, 2), (1940443, 1)]
    PT.leaf) 7908811 2 [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (2897, 1)]
    (PT.node PT.leaf 7947361 13 [(2, 5), (3, 2), (5, 1), (5519, 1)]
    PT.leaf))) 8127961 17 [(2, 3), (3, 1), (5, 1), (67733, 1)]
    (PT.node (PT.node (PT.node PT.leaf 8393057 3 [(2, 5), (7, 1), (89, 1), (421, 1)]
    PT.leaf) 8401397 2 [(2, 2), (1307, 1), (1607, 1)]
    (PT.node PT.leaf 8465381 2 [(2, 2), (5, 1), (7, 1), (11, 1), (23, 1), (239, 1)]
    PT.leaf)) 8708069 2 [(2, 2), (269, 1), (8093, 1)]
    (PT.node (PT.node PT.leaf 8715961 17 [(2, 3), (3, 2), (5, 1), (11, 1), (31, 1), (71, 1)]
    PT.leaf) 8943553 5 [(2, 6), (3, 2), (15527, 1)]
    (PT.node PT.leaf 8970971 2 [(2, 1), (5, 1), (73, 1), (12289, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab34 : PT :=
  PT.node tab30 1000921 7 [(2, 3), (3, 1), (5, 1), (19, 1), (439, 1)] tab31

/-- Part of the prime table. -/
def tab35 : PT :=
  PT.node tab32 4353691 2 [(2, 1), (3, 1), (5, 1), (11, 1), (79, 1), (167, 1)] tab33

/-- Part of the prime table. -/
def tab36 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 9187351 3 [(2, 1), (3, 1), (5, 2), (23, 1), (2663, 1)]
    PT.leaf) 9589289 3 [(2, 3), (1198661, 1)]
    PT.leaf) 9967721 3 [(2, 3), (5, 1), (7, 1), (97, 1), (367, 1)]
    (PT.node PT.leaf 10018067 2 [(2, 1), (17, 1), (294649, 1)]
    PT.leaf)) 10113553 5 [(2, 4), (3, 3), (41, 1), (571, 1)]
    (PT.node (PT.node PT.leaf 10256527 3 [(2, 1), (3, 2), (7, 1), (81401, 1)]
    PT.leaf) 10319761 71 [(2, 4), (3, 2), (5, 1), (11, 1), (1303, 1)]
    (PT.node PT.leaf 10378063 11 [(2, 1), (3, 2), (179, 1), (3221, 1)]
    PT.leaf))) 10510459 3 [(2, 1), (3, 1), (7, 1), (19, 1), (13171, 1)]
    (PT.node (PT.node (PT.node PT.leaf 10835701 6 [(2, 2), (3, 1), (5, 2), (19, 1), (1901, 1)]
    PT.leaf) 10952281 11 [(2, 3), (3, 3), (5, 1), (10141, 1)]
    (PT.node PT.leaf 10965013 2 [(2, 2), (3, 1), (491, 1), (1861, 1)]
    PT.leaf)) 11413351 6 [(2, 1), (3, 2), (5, 2), (13, 1), (1951, 1)]
    (PT.node (PT.node PT.leaf 11490289 7 [(2, 4), (3, 1), (19, 1), (43, 1), (293, 1)]
    PT.leaf) 11562701 2 [(2, 2), (5, 2), (43, 1), (2689, 1)]
    (PT.node PT.leaf 11631811 2 [(2, 1), (3, 1), (5, 1), (387727, 1)]
    PT.leaf)))) 11667673 10 [(2, 3), (3, 3), (19, 1), (2843, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 11677891 2 [(2, 1), (3, 1), (5, 1), (7, 1), (55609, 1)]
    PT.leaf) 11721217 11 [(2, 9), (3, 1), (13, 1), (587, 1)]
    PT.leaf) 12207031 6 [(2, 1), (3, 1), (5, 1), (11, 1), (71, 1), (521, 1)]
    (PT.node PT.leaf 12263431 11 [(2, 1), (3, 1), (5, 1), (337, 1), (1213, 1)]
    PT.leaf)) 12833941 11 [(2, 2), (3, 1), (5, 1), (7, 1), (30557, 1)]
    (PT.node (PT.node PT.leaf 12865927 5 [(2, 1), (3, 1), (19, 1), (112859, 1)]
    PT.leaf) 13444007 5 [(2, 1), (23, 2), (97, 1), (131, 1)]
    (PT.node PT.leaf 13948027 3 [(2, 1), (3, 1), (647, 1), (3593, 1)]
    PT.leaf))) 14346613 6 [(2, 2), (3, 3), (7, 2), (2711, 1)]
    (PT.node (PT.node (PT.node PT.leaf 14751887 5 [(2, 1), (17, 1), (137, 1), (3167, 1)]
    PT.leaf) 14819927 5 [(2, 1), (11, 1), (79, 1), (8527, 1)]
    (PT.node PT.leaf 15503233 5 [(2, 7), (3, 1), (47, 1), (859, 1)]
    PT.leaf)) 15527627 2 [(2, 1), (107, 1), (72559, 1)]
    (PT.node (PT.node PT.leaf 16293691 12 [(2, 1), (3, 3), (5, 1), (7, 1), (37, 1), (233, 1)]
    PT.leaf) 16591823 5 [(2, 1), (13, 1), (638147, 1)]
    (PT.node PT.leaf 16787009 3 [(2, 6), (7, 2), (53, 1), (101, 1)]
    PT.leaf))))) 16876357 5 [(2, 2), (3, 1), (7, 1), (200909, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 16880011 2 [(2, 1), (3, 1), (5, 1), (7, 2), (11483, 1)]
    PT.leaf) 17154559 3 [(2, 1), (3, 3), (491, 1), (647, 1)]
    PT.leaf) 17163827 2 [(2, 1), (821, 1), (10453, 1)]
    (PT.node PT.leaf 17198267 2 [(2, 1), (37, 1), (232409, 1)]
    PT.leaf)) 17396887 6 [(2, 1), (3, 1), (13, 1), (223037, 1)]
    (PT.node (PT.node PT.leaf 17634931 2 [(2, 1), (3, 1), (5, 1), (139, 1), (4229, 1)]
    PT.leaf) 17884211 2 [(2, 1), (5, 1), (31, 2), (1861, 1)]
    (PT.node PT.leaf 17950001 3 [(2, 4), (5, 5), (359, 1)]
    PT.leaf))) 18451151 11 [(2, 1), (5, 2), (369023, 1)]
    (PT.node (PT.node (PT.node PT.leaf 19218301 2 [(2, 2), (3, 1), (5, 2), (29, 1), (47, 2)]
    PT.leaf) 19622651 2 [(2, 1), (5, 2), (601, 1), (653, 1)]
    (PT.node PT.leaf 20018081 3 [(2, 5), (5, 1), (125113, 1)]
    PT.leaf)) 20241187 2 [(2, 1), (3, 1), (7, 1), (17, 1), (28349, 1)]
    (PT.node (PT.node PT.leaf 20381027 2 [(2, 1), (29, 1), (351397, 1)]
    PT.leaf) 20386337 3 [(2, 5), (637073, 1)]
    (PT.node PT.leaf 20525431 3 [(2, 1), (3, 1), (5, 1), (23, 1), (151, 1), (197, 1)]
    PT.leaf)))) 20853377 3 [(2, 7), (162917, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 21020917 2 [(2, 2), (3, 1), (7, 1), (19, 1), (13171, 1)]
    PT.leaf) 21627173 2 [(2, 2), (7, 1), (41, 1), (18839, 1)]
    (PT.node PT.leaf 21869777 3 [(2, 4), (1366861, 1)]
    PT.leaf)) 22149217 10 [(2, 5), (3, 2), (76907, 1)]
    (PT.node (PT.node PT.leaf 22406023 5 [(2, 1), (3, 2), (263, 1), (4733, 1)]
    PT.leaf) 22996651 2 [(2, 1), (3, 1), (5, 2), (19, 1), (8069, 1)]
    (PT.node PT.leaf 23468881 11 [(2, 4), (3, 1), (5, 1), (97787, 1)]
    PT.leaf))) 23560631 19 [(2, 1), (5, 1), (47, 1), (50129, 1)]
    (PT.node (PT.node (PT.node PT.leaf 24079801 26 [(2, 3), (3, 1), (5, 2), (67, 1), (599, 1)]
    PT.leaf) 24239419 7 [(2, 1), (3, 1), (7, 2), (29, 1), (2843, 1)]
    (PT.node PT.leaf 24578551 6 [(2, 1), (3, 2), (5, 2), (193, 1), (283, 1)]
    PT.leaf)) 25633813 6 [(2, 2), (3, 1), (19, 1), (112429, 1)]
    (PT.node (PT.node PT.leaf 25654001 6 [(2, 4), (5, 3), (101, 1), (127, 1)]
    PT.leaf) 26010319 3 [(2, 1), (3, 1), (41, 1), (105733, 1)]
    (PT.node PT.leaf 26234909 2 [(2, 2), (7, 1), (29, 1), (32309, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab37 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 26884777 5 [(2, 3), (3, 1), (211, 1), (5309, 1)]
    PT.leaf) 27595297 5 [(2, 5), (3, 3), (19, 1), (41, 2)]
    PT.leaf) 27656359 3 [(2, 1), (3, 1), (4609393, 1)]
    (PT.node PT.leaf 27706387 2 [(2, 1), (3, 1), (53, 1), (151, 1), (577, 1)]
    PT.leaf)) 28294769 3 [(2, 4), (1768423, 1)]
    (PT.node (PT.node PT.leaf 30514801 17 [(2, 4), (3, 1), (5, 2), (59, 1), (431, 1)]
    PT.leaf) 30557921 6 [(2, 5), (5, 1), (331, 1), (577, 1)]
    (PT.node PT.leaf 30652009 13 [(2, 3), (3, 1), (23, 1), (55529, 1)]
    PT.leaf))) 30867523 2 [(2, 1), (3, 1), (7, 1), (734941, 1)]
    (PT.node (PT.node (PT.node PT.leaf 31012561 7 [(2, 4), (3, 2), (5, 1), (19, 1), (2267, 1)]
    PT.leaf) 32009891 2 [(2, 1), (5, 1), (11, 1), (290999, 1)]
    (PT.node PT.leaf 32292739 2 [(2, 1), (3, 2), (1794041, 1)]
    PT.leaf)) 32668561 19 [(2, 4), (3, 2), (5, 1), (17, 2), (157, 1)]
    (PT.node (PT.node PT.leaf 33544781 2 [(2, 2), (5, 1), (211, 1), (7949, 1)]
    PT.leaf) 33999967 7 [(2, 1), (3, 3), (7, 1), (11, 1), (13, 1), (17, 1), (37, 1)]
    (PT.node PT.leaf 34199239 15 [(2, 1), (3, 1), (5699873, 1)]
    PT.leaf)))) 34354087 3 [(2, 1), (3, 1), (13, 1), (47, 1), (9371, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 34540591 6 [(2, 1), (3, 1), (5, 1), (7, 2), (23497, 1)]
    PT.leaf) 38109329 3 [(2, 4), (997, 1), (2389, 1)]
    (PT.node PT.leaf 38211023 5 [(2, 1), (997, 1), (19163, 1)]
    PT.leaf)) 38220251 2 [(2, 1), (5, 3), (17, 2), (23, 2)]
    (PT.node (PT.node PT.leaf 38358737 3 [(2, 4), (13, 1), (184417, 1)]
    PT.leaf) 38533987 3 [(2, 1), (3, 2), (431, 1), (4967, 1)]
    (PT.node PT.leaf 40497241 13 [(2, 3), (3, 1), (5, 1), (7, 1), (37, 1), (1303, 1)]
    PT.leaf))) 41213191 13 [(2, 1), (3, 1), (5, 1), (37, 1), (107, 1), (347, 1)]
    (PT.node (PT.node (PT.node PT.leaf 41233879 7 [(2, 1), (3, 2), (7, 1), (89, 1), (3677, 1)]
    PT.leaf) 42695269 2 [(2, 2), (3, 1), (7, 3), (11, 1), (23, 1), (41, 1)]
    (PT.node PT.leaf 43785151 3 [(2, 1), (3, 1), (5, 2), (291901, 1)]
    PT.leaf)) 44988319 3 [(2, 1), (3, 3), (833117, 1)]
    (PT.node (PT.node PT.leaf 45169853 2 [(2, 2), (7, 1), (13, 1), (31, 1), (4003, 1)]
    PT.leaf) 46406281 14 [(2, 3), (3, 1), (5, 1), (386719, 1)]
    (PT.node PT.leaf 46499389 2 [(2, 2), (3, 1), (13, 1), (347, 1), (859, 1)]
    PT.leaf))))) 46873051 2 [(2, 1), (3, 1), (5, 2), (7, 1), (44641, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 48071041 11 [(2, 7), (3, 1), (5, 1), (25037, 1)]
    PT.leaf) 48552947 2 [(2, 1), (13, 1), (1867421, 1)]
    PT.leaf) 48767767 5 [(2, 1), (3, 1), (8127961, 1)]
    (PT.node PT.leaf 49103233 5 [(2, 7), (3, 1), (127873, 1)]
    PT.leaf)) 49627843 2 [(2, 1), (3, 1), (11, 1), (389, 1), (1933, 1)]
    (PT.node (PT.node PT.leaf 50408381 2 [(2, 2), (5, 1), (11, 1), (29, 1), (7901, 1)]
    PT.leaf) 51354301 10 [(2, 2), (3, 1), (5, 2), (71, 1), (2411, 1)]
    (PT.node PT.leaf 53306107 3 [(2, 1), (3, 1), (7, 1), (1269193, 1)]
    PT.leaf))) 54375301 2 [(2, 2), (3, 4), (5, 2), (7, 2), (137, 1)]
    (PT.node (PT.node (PT.node PT.leaf 55918991 7 [(2, 1), (5, 1), (5591899, 1)]
    PT.leaf) 56788429 6 [(2, 2), (3, 1), (4732369, 1)]
    (PT.node PT.leaf 57386453 2 [(2, 2), (14346613, 1)]
    PT.leaf)) 60228893 3 [(2, 2), (17, 1), (463, 1), (1913, 1)]
    (PT.node (PT.node PT.leaf 61585361 3 [(2, 4), (5, 1), (251, 1), (3067, 1)]
    PT.leaf) 62060021 2 [(2, 2), (5, 1), (11, 1), (282091, 1)]
    (PT.node PT.leaf 67496441 3 [(2, 3), (5, 1), (11, 1), (131, 1), (1171, 1)]
    PT.leaf)))) 69424153 10 [(2, 3), (3, 1), (7, 1), (41, 1), (10079, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 69617111 11 [(2, 1), (5, 1), (29, 1), (240059, 1)]
    PT.leaf) 69655517 2 [(2, 2), (7, 1), (2487697, 1)]
    (PT.node PT.leaf 71556577 17 [(2, 5), (3, 1), (7, 1), (13, 1), (8191, 1)]
    PT.leaf)) 72577051 2 [(2, 1), (3, 1), (5, 2), (7, 1), (13, 2), (409, 1)]
    (PT.node (PT.node PT.leaf 73782517 2 [(2, 2), (3, 1), (17, 1), (361679, 1)]
    PT.leaf) 75210413 2 [(2, 2), (2251, 1), (8353, 1)]
    (PT.node PT.leaf 77053541 2 [(2, 2), (5, 1), (3852677, 1)]
    PT.leaf))) 77619973 2 [(2, 2), (3, 1), (641, 1), (10091, 1)]
    (PT.node (PT.node (PT.node PT.leaf 77724067 7 [(2, 1), (3, 1), (7, 1), (1850573, 1)]
    PT.leaf) 78149713 5 [(2, 4), (3, 1), (73, 1), (22303, 1)]
    (PT.node PT.leaf 83437259 2 [(2, 1), (17, 1), (1381, 1), (1777, 1)]
    PT.leaf)) 85375177 5 [(2, 3), (3, 1), (3557299, 1)]
    (PT.node (PT.node PT.leaf 87683177 3 [(2, 3), (7, 1), (19, 1), (23, 1), (3583, 1)]
    PT.leaf) 89589673 5 [(2, 3), (3, 3), (414767, 1)]
    (PT.node PT.leaf 89913157 6 [(2, 2), (3, 1), (149, 1), (50287, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab38 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 90339707 2 [(2, 1), (45169853, 1)]
    PT.leaf) 91605427 2 [(2, 1), (3, 1), (11, 1), (1387961, 1)]
    PT.leaf) 91724627 2 [(2, 1), (7, 1), (41, 1), (159799, 1)]
    (PT.node PT.leaf 92204351 7 [(2, 1), (5, 2), (7, 1), (131, 1), (2011, 1)]
    PT.leaf)) 92687027 2 [(2, 1), (17, 1), (2726089, 1)]
    (PT.node (PT.node PT.leaf 93775673 5 [(2, 3), (17, 1), (101, 1), (6827, 1)]
    PT.leaf) 93853931 2 [(2, 1), (5, 1), (181, 1), (51853, 1)]
    (PT.node PT.leaf 94783189 6 [(2, 2), (3, 1), (167, 1), (47297, 1)]
    PT.leaf))) 96052211 2 [(2, 1), (5, 1), (17, 1), (565013, 1)]
    (PT.node (PT.node (PT.node PT.leaf 96656723 2 [(2, 1), (47, 1), (1028263, 1)]
    PT.leaf) 97292389 2 [(2, 2), (3, 1), (19, 2), (37, 1), (607, 1)]
    (PT.node PT.leaf 97940629 2 [(2, 2), (3, 2), (37, 1), (73529, 1)]
    PT.leaf)) 103692397 2 [(2, 2), (3, 1), (31, 1), (278743, 1)]
    (PT.node (PT.node PT.leaf 104670301 11 [(2, 2), (3, 1), (5, 2), (7, 1), (49843, 1)]
    PT.leaf) 108365261 2 [(2, 2), (5, 1), (227, 1), (23869, 1)]
    (PT.node PT.leaf 108866969 3 [(2, 3), (7, 1), (1944053, 1)]
    PT.leaf)))) 112660001 3 [(2, 5), (5, 4), (43, 1), (131, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 114481561 7 [(2, 3), (3, 1), (5, 1), (29, 1), (67, 1), (491, 1)]
    PT.leaf) 120457787 2 [(2, 1), (60228893, 1)]
    PT.leaf) 121590431 7 [(2, 1), (5, 1), (13, 2), (71947, 1)]
    (PT.node PT.leaf 123037769 3 [(2, 3), (7, 1), (19, 1), (115637, 1)]
    PT.leaf)) 123152587 2 [(2, 1), (3, 1), (20525431, 1)]
    (PT.node (PT.node PT.leaf 123182329 11 [(2, 3), (3, 1), (5132597, 1)]
    PT.leaf) 124701767 7 [(2, 1), (7, 3), (17, 3), (37, 1)]
    (PT.node PT.leaf 126373609 11 [(2, 3), (3, 7), (31, 1), (233, 1)]
    PT.leaf))) 127159831 6 [(2, 1), (3, 2), (5, 1), (7, 1), (17, 1), (31, 1), (383, 1)]
    (PT.node (PT.node (PT.node PT.leaf 127176431 7 [(2, 1), (5, 1), (23, 1), (433, 1), (1277, 1)]
    PT.leaf) 127389817 5 [(2, 3), (3, 2), (37, 1), (47819, 1)]
    (PT.node PT.leaf 127473943 5 [(2, 1), (3, 1), (317, 1), (67021, 1)]
    PT.leaf)) 127806197 2 [(2, 2), (7, 1), (127, 2), (283, 1)]
    (PT.node (PT.node PT.leaf 130949933 2 [(2, 2), (157, 1), (208519, 1)]
    PT.leaf) 131500009 19 [(2, 3), (3, 2), (1826389, 1)]
    (PT.node PT.leaf 132241619 2 [(2, 1), (71, 1), (131, 1), (7109, 1)]
    PT.leaf))))) 133338869 2 [(2, 2), (13, 1), (29, 2), (3049, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 136191721 17 [(2, 3), (3, 1), (5, 1), (7, 1), (73, 1), (2221, 1)]
    PT.leaf) 139017523 5 [(2, 1), (3, 1), (7, 1), (797, 1), (4153, 1)]
    PT.leaf) 141914947 2 [(2, 1), (3, 1), (17, 1), (1391323, 1)]
    (PT.node PT.leaf 142439873 3 [(2, 6), (17, 1), (89, 1), (1471, 1)]
    PT.leaf)) 146491361 3 [(2, 5), (5, 1), (41, 1), (137, 1), (163, 1)]
    (PT.node (PT.node PT.leaf 147996911 17 [(2, 1), (5, 1), (127, 1), (116533, 1)]
    PT.leaf) 150332843 2 [(2, 1), (11, 1), (73, 1), (93607, 1)]
    (PT.node PT.leaf 162915967 3 [(2, 1), (3, 2), (2803, 1), (3229, 1)]
    PT.leaf))) 163350799 3 [(2, 1), (3, 1), (13, 1), (1237, 1), (1693, 1)]
    (PT.node (PT.node (PT.node PT.leaf 165651347 6 [(2, 1), (7, 1), (149, 1), (79411, 1)]
    PT.leaf) 166484861 3 [(2, 2), (5, 1), (61, 1), (136463, 1)]
    (PT.node PT.leaf 171001547 2 [(2, 1), (6469, 1), (13217, 1)]
    PT.leaf)) 176158223 5 [(2, 1), (41, 1), (103, 1), (20857, 1)]
    (PT.node (PT.node PT.leaf 176524207 3 [(2, 1), (3, 1), (157, 1), (187393, 1)]
    PT.leaf) 180055529 3 [(2, 3), (101, 1), (222841, 1)]
    (PT.node PT.leaf 185419219 2 [(2, 1), (3, 1), (89, 1), (347227, 1)]
    PT.leaf)))) 186991531 11 [(2, 1), (3, 1), (5, 1), (11, 1), (83, 1), (6827, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 187551347 2 [(2, 1), (93775673, 1)]
    PT.leaf) 192750517 2 [(2, 2), (3, 6), (7, 2), (19, 1), (71, 1)]
    (PT.node PT.leaf 193311109 2 [(2, 2), (3, 2), (5369753, 1)]
    PT.leaf)) 194086693 13 [(2, 2), (3, 4), (43, 1), (13931, 1)]
    (PT.node (PT.node PT.leaf 195894929 3 [(2, 4), (43, 1), (284731, 1)]
    PT.leaf) 196412933 2 [(2, 2), (49103233, 1)]
    (PT.node PT.leaf 208097431 6 [(2, 1), (3, 1), (5, 1), (131, 1), (52951, 1)]
    PT.leaf))) 208124989 2 [(2, 2), (3, 1), (43, 1), (149, 1), (2707, 1)]
    (PT.node (PT.node (PT.node PT.leaf 220194563 2 [(2, 1), (7, 1), (67, 1), (234749, 1)]
    PT.leaf) 221110919 17 [(2, 1), (7, 1), (97, 1), (162821, 1)]
    (PT.node PT.leaf 228979297 11 [(2, 5), (3, 2), (7, 1), (13, 1), (8737, 1)]
    PT.leaf)) 230329301 3 [(2, 2), (5, 2), (2303293, 1)]
    (PT.node (PT.node PT.leaf 232285523 2 [(2, 1), (7, 1), (16591823, 1)]
    PT.leaf) 236022613 2 [(2, 2), (3, 1), (7, 2), (79, 1), (5081, 1)]
    (PT.node PT.leaf 237048061 2 [(2, 2), (3, 1), (5, 1), (41, 1), (173, 1), (557, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab39 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 259161187 3 [(2, 1), (3, 1), (2953, 1), (14627, 1)]
    PT.leaf) 262209281 3 [(2, 8), (5, 1), (127, 1), (1613, 1)]
    PT.leaf) 268628879 7 [(2, 1), (7, 2), (19, 1), (89, 1), (1621, 1)]
    (PT.node PT.leaf 268982321 3 [(2, 4), (5, 1), (3362279, 1)]
    PT.leaf)) 276763169 6 [(2, 5), (11, 1), (83, 1), (9473, 1)]
    (PT.node (PT.node PT.leaf 278218153 15 [(2, 3), (3, 4), (429349, 1)]
    PT.leaf) 279599737 5 [(2, 3), (3, 1), (13, 1), (197, 1), (4549, 1)]
    (PT.node PT.leaf 280257881 6 [(2, 3), (5, 1), (7, 1), (1000921, 1)]
    PT.leaf))) 305175781 6 [(2, 2), (3, 2), (5, 1), (7, 1), (13, 1), (31, 1), (601, 1)]
    (PT.node (PT.node (PT.node PT.leaf 306012541 2 [(2, 2), (3, 1), (5, 1), (1259, 1), (4051, 1)]
    PT.leaf) 310641311 13 [(2, 1), (5, 1), (7, 1), (4437733, 1)]
    (PT.node PT.leaf 310897033 5 [(2, 3), (3, 1), (977, 1), (13259, 1)]
    PT.leaf)) 312410911 7 [(2, 1), (3, 1), (5, 1), (7, 1), (29, 1), (43, 1), (1193, 1)]
    (PT.node (PT.node PT.leaf 316264843 2 [(2, 1), (3, 2), (19, 1), (924751, 1)]
    PT.leaf) 316950847 3 [(2, 1), (3, 1), (4919, 1), (10739, 1)]
    (PT.node PT.leaf 320852267 2 [(2, 1), (7, 1), (59, 1), (71, 1), (5471, 1)]
    PT.leaf)))) 323683781 2 [(2, 2), (5, 1), (7, 1), (2312027, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 327728087 5 [(2, 1), (7, 1), (47, 1), (173, 1), (2879, 1)]
    PT.leaf) 328845079 3 [(2, 1), (3, 2), (2917, 1), (6263, 1)]
    (PT.node PT.leaf 329422297 5 [(2, 3), (3, 1), (7, 2), (280121, 1)]
    PT.leaf)) 343540871 7 [(2, 1), (5, 1), (34354087, 1)]
    (PT.node (PT.node PT.leaf 350947567 3 [(2, 1), (3, 4), (1451, 1), (1493, 1)]
    PT.leaf) 351597737 3 [(2, 3), (7, 2), (19, 1), (47207, 1)]
    (PT.node PT.leaf 363858181 6 [(2, 2), (3, 1), (5, 1), (7, 1), (866329, 1)]
    PT.leaf))) 369023021 3 [(2, 2), (5, 1), (18451151, 1)]
    (PT.node (PT.node (PT.node PT.leaf 391789859 2 [(2, 1), (195894929, 1)]
    PT.leaf) 401936329 13 [(2, 3), (3, 2), (31, 2), (37, 1), (157, 1)]
    (PT.node PT.leaf 405784411 2 [(2, 1), (3, 1), (5, 1), (137, 1), (98731, 1)]
    PT.leaf)) 412450637 2 [(2, 2), (13, 1), (163, 1), (48661, 1)]
    (PT.node (PT.node PT.leaf 414810691 11 [(2, 1), (3, 1), (5, 1), (7, 1), (31, 1), (63719, 1)]
    PT.leaf) 451209307 2 [(2, 1), (3, 1), (47, 1), (1600033, 1)]
    (PT.node PT.leaf 459355339 10 [(2, 1), (3, 2), (13, 1), (1963057, 1)]
    PT.leaf))))) 466344409 7 [(2, 3), (3, 1), (17, 1), (31, 1), (36871, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 474694483 2 [(2, 1), (3, 1), (131, 1), (603937, 1)]
    PT.leaf) 477307001 3 [(2, 3), (5, 3), (31, 1), (89, 1), (173, 1)]
    PT.leaf) 493121947 3 [(2, 1), (3, 1), (883, 1), (93077, 1)]
    (PT.node PT.leaf 504656641 7 [(2, 8), (3, 2), (5, 1), (71, 1), (617, 1)]
    PT.leaf)) 514173859 2 [(2, 1), (3, 1), (11, 1), (19, 1), (521, 1), (787, 1)]
    (PT.node (PT.node PT.leaf 527135461 6 [(2, 2), (3, 1), (5, 1), (103, 1), (85297, 1)]
    PT.leaf) 552284737 5 [(2, 6), (3, 1), (2876483, 1)]
    (PT.node PT.leaf 565364923 2 [(2, 1), (3, 1), (79, 1), (1192753, 1)]
    PT.leaf))) 568614203 2 [(2, 1), (13, 1), (21869777, 1)]
    (PT.node (PT.node (PT.node PT.leaf 581024467 17 [(2, 1), (3, 2), (11, 1), (2934467, 1)]
    PT.leaf) 596514349 2 [(2, 2), (3, 3), (19, 1), (149, 1), (1951, 1)]
    (PT.node PT.leaf 604842197 2 [(2, 2), (7, 1), (131, 1), (269, 1), (613, 1)]
    PT.leaf)) 606538249 13 [(2, 3), (3, 1), (29, 1), (871463, 1)]
    (PT.node (PT.node PT.leaf 612928711 13 [(2, 1), (3, 2), (5, 1), (17, 1), (400607, 1)]
    PT.leaf) 628086659 2 [(2, 1), (17, 1), (509, 1), (36293, 1)]
    (PT.node PT.leaf 633929497 5 [(2, 3), (3, 1), (23, 1), (79, 1), (14537, 1)]
    PT.leaf)))) 690456227 2 [(2, 1), (47, 1), (1741, 1), (4219, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 693016607 5 [(2, 1), (3581, 1), (96763, 1)]
    PT.leaf) 707425387 2 [(2, 1), (3, 1), (17, 1), (6935543, 1)]
    (PT.node PT.leaf 730314019 2 [(2, 1), (3, 2), (7, 1), (29, 1), (269, 1), (743, 1)]
    PT.leaf)) 763058587 2 [(2, 1), (3, 1), (127176431, 1)]
    (PT.node (PT.node PT.leaf 764583683 2 [(2, 1), (97, 1), (271, 1), (14543, 1)]
    PT.leaf) 775940419 7 [(2, 1), (3, 3), (11, 1), (17, 1), (43, 1), (1787, 1)]
    (PT.node PT.leaf 785699599 19 [(2, 1), (3, 1), (130949933, 1)]
    PT.leaf))) 800198983 3 [(2, 1), (3, 2), (11, 1), (53, 1), (76253, 1)]
    (PT.node (PT.node (PT.node PT.leaf 826632619 3 [(2, 1), (3, 1), (7, 1), (1523, 1), (12923, 1)]
    PT.leaf) 829621381 2 [(2, 2), (3, 1), (5, 1), (7, 1), (31, 1), (63719, 1)]
    (PT.node PT.leaf 843714919 3 [(2, 1), (3, 2), (46873051, 1)]
    PT.leaf)) 853390763 5 [(2, 1), (7, 2), (8708069, 1)]
    (PT.node (PT.node PT.leaf 864840203 2 [(2, 1), (521, 1), (601, 1), (1381, 1)]
    PT.leaf) 875335231 7 [(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (126311, 1)]
    (PT.node PT.leaf 902418613 5 [(2, 2), (3, 1), (47, 1), (1600033, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab40 : PT :=
  PT.node tab36 26287991 7 [(2, 1), (5, 1), (1063, 1), (2473, 1)] tab37

/-- Part of the prime table. -/
def tab41 : PT :=
  PT.node tab38 239371661 2 [(2, 2), (5, 1), (11, 1), (1088053, 1)] tab39

/-- Part of the prime table. -/
def tab42 : PT :=
  PT.node tab34 2167621 2 [(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (397, 1)] tab35

/-- Part of the prime table. -/
def tab43 : PT :=
  PT.node tab40 89968357 7 [(2, 2), (3, 2), (2499121, 1)] tab41

/-- Part of the prime table. -/
def tab44 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 925685143 3 [(2, 1), (3, 1), (2857, 1), (54001, 1)]
    PT.leaf) 932227613 2 [(2, 2), (59, 1), (3950117, 1)]
    PT.leaf) 944601841 11 [(2, 4), (3, 2), (5, 1), (7, 1), (13, 2), (1109, 1)]
    (PT.node PT.leaf 955921051 3 [(2, 1), (3, 2), (5, 2), (7, 1), (17, 1), (17851, 1)]
    PT.leaf)) 963689941 2 [(2, 2), (3, 3), (5, 1), (1784611, 1)]
    (PT.node (PT.node PT.leaf 978594469 2 [(2, 2), (3, 1), (19, 2), (223, 1), (1013, 1)]
    PT.leaf) 1000527599 7 [(2, 1), (7, 1), (71, 2), (14177, 1)]
    (PT.node PT.leaf 1001523179 2 [(2, 1), (23, 1), (29, 1), (37, 1), (103, 1), (197, 1)]
    PT.leaf))) 1011185971 2 [(2, 1), (3, 1), (5, 1), (1039, 1), (32441, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1024823381 2 [(2, 2), (5, 1), (7, 1), (163, 1), (44909, 1)]
    PT.leaf) 1056949339 2 [(2, 1), (3, 1), (176158223, 1)]
    (PT.node PT.leaf 1121351701 6 [(2, 2), (3, 1), (5, 2), (7, 1), (29, 1), (18413, 1)]
    PT.leaf)) 1143852607 5 [(2, 1), (3, 2), (13, 1), (23, 1), (283, 1), (751, 1)]
    (PT.node (PT.node PT.leaf 1222417697 3 [(2, 5), (59, 1), (691, 1), (937, 1)]
    PT.leaf) 1243466999 11 [(2, 1), (7669, 1), (81071, 1)]
    (PT.node PT.leaf 1292236823 5 [(2, 1), (3593, 1), (179827, 1)]
    PT.leaf)))) 1361917211 2 [(2, 1), (5, 1), (136191721, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 1365378737 3 [(2, 4), (37, 1), (461, 1), (5003, 1)]
    PT.leaf) 1378436737 5 [(2, 7), (3, 1), (23, 1), (97, 1), (1609, 1)]
    PT.leaf) 1394714501 2 [(2, 2), (5, 3), (97, 1), (149, 1), (193, 1)]
    (PT.node PT.leaf 1430126501 3 [(2, 2), (5, 3), (11, 1), (260023, 1)]
    PT.leaf)) 1433991301 10 [(2, 2), (3, 1), (5, 2), (7, 1), (331, 1), (2063, 1)]
    (PT.node (PT.node PT.leaf 1478526139 2 [(2, 1), (3, 2), (419, 1), (196039, 1)]
    PT.leaf) 1514770111 6 [(2, 1), (3, 2), (5, 1), (7, 1), (23, 1), (107, 1), (977, 1)]
    (PT.node PT.leaf 1575222931 7 [(2, 1), (3, 3), (5, 1), (19, 1), (67, 1), (4583, 1)]
    PT.leaf))) 1579264051 2 [(2, 1), (3, 1), (5, 2), (7, 1), (13, 1), (127, 1), (911, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1600591819 2 [(2, 1), (3, 1), (7, 1), (38109329, 1)]
    PT.leaf) 1606238987 2 [(2, 1), (11, 1), (19, 1), (3842677, 1)]
    (PT.node PT.leaf 1667228851 2 [(2, 1), (3, 2), (5, 2), (7, 1), (29, 1), (18251, 1)]
    PT.leaf)) 1668745181 2 [(2, 2), (5, 1), (83437259, 1)]
    (PT.node (PT.node PT.leaf 1727870509 2 [(2, 2), (3, 3), (7, 1), (13, 1), (175811, 1)]
    PT.leaf) 1803301831 3 [(2, 1), (3, 2), (5, 1), (11, 1), (173, 1), (10529, 1)]
    (PT.node PT.leaf 1856918071 6 [(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (53, 1), (2927, 1)]
    PT.leaf))))) 1890771811 2 [(2, 1), (3, 1), (5, 1), (23, 1), (2740249, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 2002734973 5 [(2, 2), (3, 2), (7, 1), (7947361, 1)]
    PT.leaf) 2055731473 7 [(2, 4), (3, 2), (41, 1), (191, 1), (1823, 1)]
    PT.leaf) 2226067273 5 [(2, 3), (3, 4), (11, 1), (13, 1), (24023, 1)]
    (PT.node PT.leaf 2235195191 11 [(2, 1), (5, 1), (17, 1), (79, 1), (149, 1), (1117, 1)]
    PT.leaf)) 2262697039 11 [(2, 1), (3, 3), (7, 1), (37, 1), (161783, 1)]
    (PT.node (PT.node PT.leaf 2263148233 7 [(2, 3), (3, 1), (227, 1), (415409, 1)]
    PT.leaf) 2300511547 2 [(2, 1), (3, 2), (127806197, 1)]
    (PT.node PT.leaf 2309087647 3 [(2, 1), (3, 2), (8719, 1), (14713, 1)]
    PT.leaf))) 2343849413 2 [(2, 2), (97, 1), (967, 1), (6247, 1)]
    (PT.node (PT.node (PT.node PT.leaf 2453987681 3 [(2, 5), (5, 1), (3581, 1), (4283, 1)]
    PT.leaf) 2485642321 11 [(2, 4), (3, 2), (5, 1), (7, 1), (19, 1), (101, 1), (257, 1)]
    (PT.node PT.leaf 2496170221 7 [(2, 2), (3, 1), (5, 1), (19, 1), (23, 1), (31, 1), (37, 1), (83, 1)]
    PT.leaf)) 2569610653 2 [(2, 2), (3, 1), (7, 1), (1429, 1), (21407, 1)]
    (PT.node (PT.node PT.leaf 2592135487 6 [(2, 1), (3, 3), (17, 1), (523, 1), (5399, 1)]
    PT.leaf) 2610804127 3 [(2, 1), (3, 1), (7, 1), (1187, 1), (52369, 1)]
    (PT.node PT.leaf 2662289521 21 [(2, 4), (3, 1), (5, 1), (11, 1), (197, 1), (5119, 1)]
    PT.leaf)))) 2663944399 6 [(2, 1), (3, 2), (147996911, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 2664097031 7 [(2, 1), (5, 1), (7, 1), (17, 1), (521, 1), (4297, 1)]
    PT.leaf) 2723834423 5 [(2, 1), (1361917211, 1)]
    (PT.node PT.leaf 2745256771 3 [(2, 1), (3, 2), (5, 1), (23, 1), (31, 1), (179, 1), (239, 1)]
    PT.leaf)) 2767631689 29 [(2, 3), (3, 2), (17, 1), (71, 1), (31847, 1)]
    (PT.node (PT.node PT.leaf 2787186403 2 [(2, 1), (3, 3), (7, 1), (11, 1), (13, 1), (51563, 1)]
    PT.leaf) 2848487797 14 [(2, 2), (3, 5), (7, 2), (11, 1), (5437, 1)]
    (PT.node PT.leaf 2879800139 2 [(2, 1), (181, 1), (733, 1), (10853, 1)]
    PT.leaf))) 2886653113 13 [(2, 3), (3, 1), (7, 2), (2454637, 1)]
    (PT.node (PT.node (PT.node PT.leaf 2937190033 13 [(2, 4), (3, 3), (7, 1), (503, 1), (1931, 1)]
    PT.leaf) 2938723001 3 [(2, 3), (5, 3), (131, 1), (22433, 1)]
    (PT.node PT.leaf 3158528101 2 [(2, 2), (3, 1), (5, 2), (7, 1), (13, 1), (127, 1), (911, 1)]
    PT.leaf)) 3202878953 3 [(2, 3), (7, 1), (13, 1), (37, 1), (118907, 1)]
    (PT.node (PT.node PT.leaf 3265059751 13 [(2, 1), (3, 1), (5, 3), (19, 1), (229127, 1)]
    PT.leaf) 3314521417 5 [(2, 3), (3, 1), (17, 1), (739, 1), (10993, 1)]
    (PT.node PT.leaf 3353767033 13 [(2, 3), (3, 1), (7, 1), (11, 1), (1814809, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab45 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 3401979949 2 [(2, 2), (3, 2), (37, 1), (2554039, 1)]
    PT.leaf) 3927085741 13 [(2, 2), (3, 4), (5, 1), (67, 1), (97, 1), (373, 1)]
    PT.leaf) 4189129561 13 [(2, 3), (3, 2), (5, 1), (7, 2), (11, 1), (21589, 1)]
    (PT.node PT.leaf 4338835663 7 [(2, 1), (3, 1), (7, 1), (107, 1), (263, 1), (3671, 1)]
    PT.leaf)) 4472754901 2 [(2, 2), (3, 1), (5, 2), (373, 1), (39971, 1)]
    (PT.node (PT.node PT.leaf 4493160547 2 [(2, 1), (3, 1), (7, 2), (19, 1), (223, 1), (3607, 1)]
    PT.leaf) 4802611441 29 [(2, 4), (3, 1), (5, 1), (11, 1), (263, 1), (6917, 1)]
    (PT.node PT.leaf 5422626589 6 [(2, 2), (3, 1), (73, 1), (349, 1), (17737, 1)]
    PT.leaf))) 5490513541 6 [(2, 2), (3, 2), (5, 1), (23, 1), (31, 1), (179, 1), (239, 1)]
    (PT.node (PT.node (PT.node PT.leaf 5513746949 2 [(2, 2), (1378436737, 1)]
    PT.leaf) 5646638993 3 [(2, 4), (1063, 1), (331999, 1)]
    (PT.node PT.leaf 5718469541 2 [(2, 2), (5, 1), (7, 2), (5835173, 1)]
    PT.leaf)) 5759600279 11 [(2, 1), (2879800139, 1)]
    (PT.node (PT.node PT.leaf 5960866633 5 [(2, 3), (3, 1), (7, 1), (79, 1), (449131, 1)]
    PT.leaf) 6170086309 2 [(2, 2), (3, 1), (514173859, 1)]
    (PT.node PT.leaf 6259457419 2 [(2, 1), (3, 1), (9001, 1), (115903, 1)]
    PT.leaf)))) 6562429921 26 [(2, 5), (3, 3), (5, 1), (23, 1), (66047, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 6583580711 7 [(2, 1), (5, 1), (7, 2), (139, 1), (96661, 1)]
    PT.leaf) 7462037027 2 [(2, 1), (173, 1), (283, 1), (76207, 1)]
    PT.leaf) 7853576701 2 [(2, 2), (3, 1), (5, 2), (17, 1), (1539917, 1)]
    (PT.node PT.leaf 7960598843 2 [(2, 1), (7, 1), (568614203, 1)]
    PT.leaf)) 8341832431 3 [(2, 1), (3, 2), (5, 1), (92687027, 1)]
    (PT.node (PT.node PT.leaf 8580759007 3 [(2, 1), (3, 1), (1430126501, 1)]
    PT.leaf) 8597647453 5 [(2, 2), (3, 1), (7727, 1), (92723, 1)]
    (PT.node PT.leaf 8824793797 2 [(2, 2), (3, 2), (7, 1), (13, 1), (101, 1), (149, 1), (179, 1)]
    PT.leaf))) 9228932281 11 [(2, 3), (3, 2), (5, 1), (2311, 1), (11093, 1)]
    (PT.node (PT.node (PT.node PT.leaf 9295132387 3 [(2, 1), (3, 1), (19, 1), (41, 1), (1988689, 1)]
    PT.leaf) 9545601493 5 [(2, 2), (3, 4), (7, 1), (353, 1), (11923, 1)]
    (PT.node PT.leaf 9818036359 6 [(2, 1), (3, 1), (13, 1), (23, 1), (37, 1), (211, 1), (701, 1)]
    PT.leaf)) 9993477157 7 [(2, 2), (3, 1), (13, 1), (263, 1), (243577, 1)]
    (PT.node (PT.node PT.leaf 10012471081 11 [(2, 3), (3, 1), (5, 1), (83437259, 1)]
    PT.leaf) 10077550361 3 [(2, 3), (5, 1), (17, 1), (14819927, 1)]
    (PT.node PT.leaf 10177286401 29 [(2, 8), (3, 2), (5, 2), (109, 1), (1621, 1)]
    PT.leaf))))) 10569493391 7 [(2, 1), (5, 1), (1056949339, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 11018941331 2 [(2, 1), (5, 1), (79, 1), (13948027, 1)]
    PT.leaf) 12340172617 5 [(2, 3), (3, 1), (514173859, 1)]
    PT.leaf) 12346432697 6 [(2, 3), (13, 1), (61, 1), (1123, 1), (1733, 1)]
    (PT.node PT.leaf 12368890003 3 [(2, 1), (3, 1), (7, 1), (173, 1), (491, 1), (3467, 1)]
    PT.leaf)) 12897251893 5 [(2, 2), (3, 4), (7, 1), (17, 1), (334507, 1)]
    (PT.node (PT.node PT.leaf 13080080081 3 [(2, 4), (5, 1), (71, 1), (1433, 1), (1607, 1)]
    PT.leaf) 13624382047 5 [(2, 1), (3, 1), (11, 1), (17, 1), (691, 1), (17573, 1)]
    (PT.node PT.leaf 13739597803 2 [(2, 1), (3, 2), (7, 1), (71, 1), (1535837, 1)]
    PT.leaf))) 15100497917 2 [(2, 2), (7, 1), (31, 1), (17396887, 1)]
    (PT.node (PT.node (PT.node PT.leaf 15428908531 2 [(2, 1), (3, 2), (5, 1), (7, 1), (23, 1), (683, 1), (1559, 1)]
    PT.leaf) 15441801523 2 [(2, 1), (3, 1), (7, 1), (17, 1), (21627173, 1)]
    (PT.node PT.leaf 16017362827 5 [(2, 1), (3, 1), (37, 1), (41, 1), (1759763, 1)]
    PT.leaf)) 16148168401 22 [(2, 4), (3, 1), (5, 2), (7, 1), (13, 1), (19, 1), (43, 1), (181, 1)]
    (PT.node (PT.node PT.leaf 17189128703 5 [(2, 1), (37, 1), (232285523, 1)]
    PT.leaf) 19350342553 7 [(2, 3), (3, 1), (47, 1), (17154559, 1)]
    (PT.node PT.leaf 19663685221 2 [(2, 2), (3, 1), (5, 1), (327728087, 1)]
    PT.leaf)))) 19937168287 6 [(2, 1), (3, 1), (7, 1), (474694483, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 20236908217 5 [(2, 3), (3, 1), (7, 1), (120457787, 1)]
    PT.leaf) 22216443433 5 [(2, 3), (3, 1), (925685143, 1)]
    (PT.node PT.leaf 23415976777 5 [(2, 3), (3, 1), (607, 1), (1607357, 1)]
    PT.leaf)) 25085030513 3 [(2, 4), (1229, 1), (1275683, 1)]
    (PT.node (PT.node PT.leaf 25813566589 2 [(2, 2), (3, 1), (4129, 1), (520981, 1)]
    PT.leaf) 26677735199 11 [(2, 1), (349, 1), (38220251, 1)]
    (PT.node PT.leaf 27532181491 3 [(2, 1), (3, 1), (5, 1), (11, 2), (83, 1), (91381, 1)]
    PT.leaf))) 31831146251 2 [(2, 1), (5, 4), (37, 1), (521, 1), (1321, 1)]
    (PT.node (PT.node (PT.node PT.leaf 33608357287 3 [(2, 1), (3, 1), (7, 1), (800198983, 1)]
    PT.leaf) 35761058621 2 [(2, 2), (5, 1), (7, 1), (19, 1), (13444007, 1)]
    (PT.node PT.leaf 35785493279 7 [(2, 1), (37, 1), (47, 1), (1297, 1), (7933, 1)]
    PT.leaf)) 38568967187 2 [(2, 1), (53, 1), (363858181, 1)]
    (PT.node (PT.node PT.leaf 39168525373 11 [(2, 2), (3, 1), (23, 1), (141914947, 1)]
    PT.leaf) 45758859173 2 [(2, 2), (13, 1), (797, 1), (1104113, 1)]
    (PT.node PT.leaf 46685826619 2 [(2, 1), (3, 1), (41, 1), (127, 1), (1009, 1), (1481, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab46 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 49099377809 3 [(2, 4), (13, 1), (2389, 1), (98809, 1)]
    PT.leaf) 52379047267 2 [(2, 1), (3, 1), (7, 1), (13, 1), (31, 1), (61, 1), (97, 1), (523, 1)]
    PT.leaf) 55479494963 2 [(2, 1), (367, 1), (823, 1), (91841, 1)]
    (PT.node PT.leaf 56422630543 3 [(2, 1), (3, 1), (10883, 1), (864079, 1)]
    PT.leaf)) 60907449611 2 [(2, 1), (5, 1), (7, 1), (283, 1), (3074581, 1)]
    (PT.node (PT.node PT.leaf 64704045557 2 [(2, 2), (23, 1), (31, 1), (37, 1), (613169, 1)]
    PT.leaf) 65522613283 2 [(2, 1), (3, 1), (7, 1), (29, 1), (89, 1), (604441, 1)]
    (PT.node PT.leaf 66027296779 2 [(2, 1), (3, 1), (17, 1), (193, 1), (331, 1), (10133, 1)]
    PT.leaf))) 75137056459 11 [(2, 1), (3, 1), (43, 1), (73, 1), (3989437, 1)]
    (PT.node (PT.node (PT.node PT.leaf 76461209273 3 [(2, 3), (7, 1), (1365378737, 1)]
    PT.leaf) 77443438027 3 [(2, 1), (3, 1), (3671, 1), (3516001, 1)]
    (PT.node PT.leaf 78785754721 19 [(2, 5), (3, 1), (5, 1), (17, 1), (103, 1), (93739, 1)]
    PT.leaf)) 78851328029 3 [(2, 2), (11, 2), (162915967, 1)]
    (PT.node (PT.node PT.leaf 82191045331 2 [(2, 1), (3, 3), (5, 1), (23, 1), (223, 1), (59351, 1)]
    PT.leaf) 82233985061 2 [(2, 2), (5, 1), (149, 1), (27595297, 1)]
    (PT.node PT.leaf 83988573481 11 [(2, 3), (3, 2), (5, 1), (7, 2), (431, 1), (11047, 1)]
    PT.leaf)))) 85650753583 13 [(2, 1), (3, 2), (71, 1), (229, 1), (292661, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 86950696619 2 [(2, 1), (41, 2), (167, 1), (251, 1), (617, 1)]
    PT.leaf) 89295617581 6 [(2, 2), (3, 1), (5, 1), (13, 1), (114481561, 1)]
    PT.leaf) 89451727381 6 [(2, 2), (3, 3), (5, 1), (165651347, 1)]
    (PT.node PT.leaf 93801799907 2 [(2, 1), (647, 1), (1303, 1), (55633, 1)]
    PT.leaf)) 104940138847 3 [(2, 1), (3, 1), (233, 1), (7741, 1), (9697, 1)]
    (PT.node (PT.node PT.leaf 116720967413 2 [(2, 2), (7, 1), (53, 1), (7411, 1), (10613, 1)]
    PT.leaf) 125642407351 6 [(2, 1), (3, 1), (5, 2), (43, 1), (97, 1), (409, 1), (491, 1)]
    (PT.node PT.leaf 135676061629 2 [(2, 2), (3, 1), (12197, 1), (926977, 1)]
    PT.leaf))) 138333204689 3 [(2, 4), (7, 1), (13267, 1), (93097, 1)]
    (PT.node (PT.node (PT.node PT.leaf 140073863861 2 [(2, 2), (5, 1), (7, 1), (1000527599, 1)]
    PT.leaf) 141102648931 10 [(2, 1), (3, 1), (5, 1), (101, 1), (401, 1), (116131, 1)]
    (PT.node PT.leaf 145159381141 2 [(2, 2), (3, 1), (5, 1), (103, 1), (617, 1), (38069, 1)]
    PT.leaf)) 148012666057 5 [(2, 3), (3, 2), (2055731473, 1)]
    (PT.node (PT.node PT.leaf 168247348891 3 [(2, 1), (3, 1), (5, 1), (39227, 1), (142969, 1)]
    PT.leaf) 171686630257 5 [(2, 4), (3, 1), (373, 1), (9589289, 1)]
    (PT.node PT.leaf 172919530897 5 [(2, 4), (3, 1), (7, 1), (227, 1), (2267143, 1)]
    PT.leaf))))) 186707169083 2 [(2, 1), (7, 1), (347, 1), (937, 1), (41017, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 216671449993 5 [(2, 3), (3, 1), (41, 1), (220194563, 1)]
    PT.leaf) 221388064231 19 [(2, 1), (3, 1), (5, 1), (23, 1), (320852267, 1)]
    PT.leaf) 239337374873 3 [(2, 3), (107, 1), (279599737, 1)]
    (PT.node PT.leaf 247174661801 3 [(2, 3), (5, 2), (11, 2), (29, 1), (352201, 1)]
    PT.leaf)) 274223552137 5 [(2, 3), (3, 1), (127, 1), (89968357, 1)]
    (PT.node (PT.node PT.leaf 278331379369 11 [(2, 3), (3, 1), (7, 2), (43, 1), (151, 1), (36451, 1)]
    PT.leaf) 293906280391 6 [(2, 1), (3, 1), (5, 1), (23, 1), (73, 1), (5834947, 1)]
    (PT.node PT.leaf 303833702891 2 [(2, 1), (5, 1), (31, 1), (47, 1), (20853377, 1)]
    PT.leaf))) 310107024037 2 [(2, 2), (3, 2), (47, 1), (2099, 1), (87317, 1)]
    (PT.node (PT.node (PT.node PT.leaf 332207361361 13 [(2, 4), (3, 2), (5, 1), (7, 1), (23, 1), (293, 1), (9781, 1)]
    PT.leaf) 372649725281 3 [(2, 5), (5, 1), (7, 1), (31, 1), (71, 1), (151169, 1)]
    (PT.node PT.leaf 374857981681 11 [(2, 4), (3, 1), (5, 1), (7, 1), (13, 1), (17163827, 1)]
    PT.leaf)) 382199718569 3 [(2, 3), (47774964821, 1)]
    (PT.node (PT.node PT.leaf 395950646197 2 [(2, 2), (3, 3), (7, 1), (2311, 1), (226631, 1)]
    PT.leaf) 396162689311 3 [(2, 1), (3, 2), (5, 1), (29, 1), (139, 1), (1039, 1), (1051, 1)]
    (PT.node PT.leaf 416450882401 41 [(2, 5), (3, 1), (5, 2), (7, 2), (3541249, 1)]
    PT.leaf)))) 441019876741 2 [(2, 2), (3, 1), (5, 1), (19, 1), (67, 1), (5774023, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 456085740811 2 [(2, 1), (3, 1), (5, 1), (7, 1), (653, 1), (3325937, 1)]
    PT.leaf) 465900166691 2 [(2, 1), (5, 1), (7, 1), (1123, 1), (5926729, 1)]
    (PT.node PT.leaf 480771505499 2 [(2, 1), (17, 1), (43, 1), (328845079, 1)]
    PT.leaf)) 491037786697 5 [(2, 3), (3, 1), (17, 1), (83, 1), (233, 1), (62233, 1)]
    (PT.node (PT.node PT.leaf 516879573103 3 [(2, 1), (3, 2), (19, 1), (9103, 1), (166027, 1)]
    PT.leaf) 544590336119 7 [(2, 1), (17, 1), (16017362827, 1)]
    (PT.node PT.leaf 562731116179 3 [(2, 1), (3, 1), (7, 1), (11, 1), (83, 1), (1193, 1), (12301, 1)]
    PT.leaf))) 602912599837 5 [(2, 2), (3, 1), (43, 1), (4909, 1), (238019, 1)]
    (PT.node (PT.node (PT.node PT.leaf 623689190653 2 [(2, 2), (3, 1), (11, 1), (919, 1), (5141369, 1)]
    PT.leaf) 655718413087 3 [(2, 1), (3, 2), (11, 1), (17, 1), (11437, 1), (17033, 1)]
    (PT.node PT.leaf 657871880489 3 [(2, 3), (82233985061, 1)]
    PT.leaf)) 677199970831 6 [(2, 1), (3, 1), (5, 1), (107, 1), (499, 1), (619, 1), (683, 1)]
    (PT.node (PT.node PT.leaf 687262545131 2 [(2, 1), (5, 1), (7, 1), (9818036359, 1)]
    PT.leaf) 693696942149 2 [(2, 2), (7, 2), (29, 1), (37, 1), (3298481, 1)]
    (PT.node PT.leaf 705670360649 3 [(2, 3), (11, 1), (29, 1), (61, 1), (4533059, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab47 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 790579404481 17 [(2, 6), (3, 1), (5, 1), (521, 1), (1580653, 1)]
    PT.leaf) 836561914831 6 [(2, 1), (3, 2), (5, 1), (9295132387, 1)]
    PT.leaf) 852460489981 6 [(2, 2), (3, 5), (5, 1), (11, 1), (2423, 1), (6581, 1)]
    (PT.node PT.leaf 865622988431 11 [(2, 1), (5, 1), (32327, 1), (2677709, 1)]
    PT.leaf)) 934415109937 15 [(2, 4), (3, 2), (7, 1), (11, 1), (43, 1), (151, 1), (12979, 1)]
    (PT.node (PT.node PT.leaf 959453441717 5 [(2, 2), (7, 2), (11, 1), (17, 1), (19, 1), (1377757, 1)]
    PT.leaf) 991247891059 2 [(2, 1), (3, 3), (17, 1), (557, 1), (569, 1), (3407, 1)]
    (PT.node PT.leaf 1037517185381 11 [(2, 2), (5, 1), (13, 1), (101, 1), (1009, 1), (39157, 1)]
    PT.leaf))) 1049590933663 3 [(2, 1), (3, 1), (89, 1), (607, 1), (3238099, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1208179545301 2 [(2, 2), (3, 2), (5, 2), (7, 1), (13, 1), (14751887, 1)]
    PT.leaf) 1219148483701 2 [(2, 2), (3, 1), (5, 2), (7, 2), (7583, 1), (10937, 1)]
    (PT.node PT.leaf 1224695996347 2 [(2, 1), (3, 1), (54311, 1), (3758281, 1)]
    PT.leaf)) 1235534918771 2 [(2, 1), (5, 1), (3221, 1), (38358737, 1)]
    (PT.node (PT.node PT.leaf 1268339206921 7 [(2, 3), (3, 1), (5, 1), (10569493391, 1)]
    PT.leaf) 1335495402823 6 [(2, 1), (3, 1), (7, 1), (23, 1), (13903, 1), (99439, 1)]
    (PT.node PT.leaf 1344338283767 5 [(2, 1), (19, 1), (24077, 1), (1469341, 1)]
    PT.leaf)))) 1394813567261 2 [(2, 2), (5, 1), (37, 1), (43, 1), (79, 1), (229, 1), (2423, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 1499167462211 2 [(2, 1), (5, 1), (11, 1), (20023, 1), (680657, 1)]
    PT.leaf) 1516607793331 3 [(2, 1), (3, 1), (5, 1), (7, 1), (97, 1), (733, 1), (101573, 1)]
    (PT.node PT.leaf 1572132928211 2 [(2, 1), (5, 1), (13, 1), (157, 1), (167, 1), (379, 1), (1217, 1)]
    PT.leaf)) 1653850268201 3 [(2, 3), (5, 2), (13, 1), (23, 1), (27656359, 1)]
    (PT.node (PT.node PT.leaf 1696964587657 10 [(2, 3), (3, 1), (13, 1), (29, 1), (187551347, 1)]
    PT.leaf) 1900421426047 3 [(2, 1), (3, 1), (11, 1), (13, 1), (5881, 1), (376627, 1)]
    (PT.node PT.leaf 1957650063931 2 [(2, 1), (3, 2), (5, 1), (11, 1), (107, 1), (1129, 1), (16369, 1)]
    PT.leaf))) 2033125998091 3 [(2, 1), (3, 1), (5, 1), (11, 1), (1459, 1), (4222747, 1)]
    (PT.node (PT.node (PT.node PT.leaf 2049790620979 2 [(2, 1), (3, 2), (43051, 1), (2645171, 1)]
    PT.leaf) 2202194614231 6 [(2, 1), (3, 4), (5, 1), (13, 1), (73, 1), (2864867, 1)]
    (PT.node PT.leaf 2223673948273 5 [(2, 4), (3, 1), (7, 1), (1409, 1), (4697003, 1)]
    PT.leaf)) 2351635987027 2 [(2, 1), (3, 1), (4273, 1), (91724627, 1)]
    (PT.node (PT.node PT.leaf 2357622555649 23 [(2, 10), (3, 1), (17, 1), (71, 1), (635837, 1)]
    PT.leaf) 2501339684251 2 [(2, 1), (3, 1), (5, 3), (11, 1), (37, 1), (251, 1), (32647, 1)]
    (PT.node PT.leaf 2585122674619 3 [(2, 1), (3, 1), (11, 1), (39168525373, 1)]
    PT.leaf))))) 2790506402989 2 [(2, 2), (3, 1), (19, 1), (5119, 1), (2390909, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 2884629032993 3 [(2, 5), (7, 1), (479, 1), (26884777, 1)]
    PT.leaf) 2891083442729 3 [(2, 3), (13, 1), (37, 1), (251, 1), (2993311, 1)]
    PT.leaf) 3320489854057 17 [(2, 3), (3, 1), (41, 1), (8093, 1), (416963, 1)]
    (PT.node PT.leaf 3381457093727 5 [(2, 1), (317, 1), (1019, 1), (5234081, 1)]
    PT.leaf)) 3447899565839 7 [(2, 1), (7, 2), (13, 1), (19, 1), (142439873, 1)]
    (PT.node (PT.node PT.leaf 3617523089023 5 [(2, 1), (3, 1), (207523, 1), (2905319, 1)]
    PT.leaf) 3646526369051 6 [(2, 1), (5, 2), (181873, 1), (400997, 1)]
    (PT.node PT.leaf 3737657091169 37 [(2, 5), (3, 2), (7, 1), (11, 1), (13, 1), (19, 1), (151, 1), (4519, 1)]
    PT.leaf))) 3740221981231 13 [(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (47, 1), (1399, 1), (11777, 1)]
    (PT.node (PT.node (PT.node PT.leaf 3778501876319 7 [(2, 1), (13, 1), (17, 1), (89, 1), (96052211, 1)]
    PT.leaf) 3867675755483 2 [(2, 1), (7, 1), (11, 2), (31391, 1), (72733, 1)]
    (PT.node PT.leaf 3949510875139 2 [(2, 1), (3, 2), (197, 1), (367, 1), (3034859, 1)]
    PT.leaf)) 4099581241957 2 [(2, 2), (3, 2), (43051, 1), (2645171, 1)]
    (PT.node (PT.node PT.leaf 4242586390571 6 [(2, 1), (5, 1), (11, 1), (38568967187, 1)]
    PT.leaf) 4296301150081 7 [(2, 7), (3, 1), (5, 1), (29, 1), (31, 1), (113, 1), (22027, 1)]
    (PT.node PT.leaf 4330075325201 3 [(2, 4), (5, 2), (31, 1), (443, 1), (788261, 1)]
    PT.leaf)))) 4342701505151 7 [(2, 1), (5, 2), (37, 1), (12959, 1), (181141, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 4513076485163 2 [(2, 1), (7, 2), (167597, 1), (274777, 1)]
    PT.leaf) 4534166740403 2 [(2, 1), (13, 1), (19, 1), (15913, 1), (576791, 1)]
    (PT.node PT.leaf 4721697244987 2 [(2, 1), (3, 1), (67447, 1), (11667673, 1)]
    PT.leaf)) 4803254465101 2 [(2, 2), (3, 1), (5, 2), (7, 1), (13, 1), (17, 1), (127, 1), (227, 1), (359, 1)]
    (PT.node (PT.node PT.leaf 4811739025283 5 [(2, 1), (7, 2), (49099377809, 1)]
    PT.leaf) 4968278946539 2 [(2, 1), (73, 1), (199, 1), (171001547, 1)]
    (PT.node PT.leaf 5196608121641 6 [(2, 3), (5, 1), (13, 1), (9993477157, 1)]
    PT.leaf))) 5524111988167 3 [(2, 1), (3, 1), (787, 1), (17569, 1), (66587, 1)]
    (PT.node (PT.node (PT.node PT.leaf 5889307277311 3 [(2, 1), (3, 1), (5, 1), (41, 1), (1973, 1), (2426789, 1)]
    PT.leaf) 5926311255103 5 [(2, 1), (3, 1), (7, 1), (141102648931, 1)]
    (PT.node PT.leaf 5968930061879 7 [(2, 1), (7, 2), (60907449611, 1)]
    PT.leaf)) 6340441439719 6 [(2, 1), (3, 3), (101, 1), (349, 1), (3331033, 1)]
    (PT.node (PT.node PT.leaf 7130928407599 3 [(2, 1), (3, 2), (396162689311, 1)]
    PT.leaf) 7492751023103 5 [(2, 1), (73, 1), (6719, 1), (7638073, 1)]
    (PT.node PT.leaf 7746000794761 13 [(2, 3), (3, 1), (5, 1), (157, 1), (3407, 1), (120677, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab48 : PT :=
  PT.node tab44 3362180467 2 [(2, 1), (3, 1), (67, 1), (661, 1), (12653, 1)] tab45

/-- Part of the prime table. -/
def tab49 : PT :=
  PT.node tab46 731048936627 2 [(2, 1), (1861, 1), (196412933, 1)] tab47

/-- Part of the prime table. -/
def tab50 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 8316340970029 2 [(2, 2), (3, 1), (7, 1), (13, 1), (107, 1), (127, 1), (337, 1), (1663, 1)]
    PT.leaf) 8737481256739 2 [(2, 1), (3, 1), (13, 1), (37, 1), (107, 1), (28294769, 1)]
    PT.leaf) 9108709959749 3 [(2, 2), (7, 1), (59, 1), (5513746949, 1)]
    (PT.node PT.leaf 9291185416529 3 [(2, 4), (467, 1), (1243466999, 1)]
    PT.leaf)) 9468940004449 22 [(2, 5), (3, 1), (19, 1), (4603, 1), (1127809, 1)]
    (PT.node (PT.node PT.leaf 9784371625351 7 [(2, 1), (3, 1), (5, 2), (7, 1), (19, 1), (1901, 1), (257993, 1)]
    PT.leaf) 10464092501131 2 [(2, 1), (3, 2), (5, 1), (163, 1), (1361, 1), (524099, 1)]
    (PT.node PT.leaf 10654978292191 6 [(2, 1), (3, 2), (5, 1), (59, 1), (26209, 1), (76561, 1)]
    PT.leaf))) 10731999191101 6 [(2, 2), (3, 1), (5, 2), (11, 1), (1061, 1), (3065147, 1)]
    (PT.node (PT.node (PT.node PT.leaf 10768274427527 5 [(2, 1), (7, 1), (11, 1), (42019, 1), (1664101, 1)]
    PT.leaf) 11445249950263 5 [(2, 1), (3, 5), (73, 1), (83, 1), (1153, 1), (3371, 1)]
    (PT.node PT.leaf 11709700117279 3 [(2, 1), (3, 1), (8233, 1), (237048061, 1)]
    PT.leaf)) 12400411646533 2 [(2, 2), (3, 1), (7, 1), (13, 1), (113, 1), (787, 1), (127691, 1)]
    (PT.node (PT.node PT.leaf 12560063349523 2 [(2, 1), (3, 1), (13, 1), (89, 1), (149, 1), (3089, 1), (3931, 1)]
    PT.leaf) 13205195936791 6 [(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (19073, 1), (161387, 1)]
    (PT.node PT.leaf 14861111488247 5 [(2, 1), (73, 1), (3331, 1), (30557921, 1)]
    PT.leaf)))) 15464918155177 5 [(2, 3), (3, 4), (7, 1), (41, 1), (293, 1), (283807, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 15683402202973 5 [(2, 2), (3, 1), (7, 1), (186707169083, 1)]
    PT.leaf) 15798461357509 6 [(2, 2), (3, 1), (17, 1), (77443438027, 1)]
    PT.leaf) 16079046319741 6 [(2, 2), (3, 1), (5, 1), (31, 1), (359, 1), (24079801, 1)]
    (PT.node PT.leaf 16761187781959 6 [(2, 1), (3, 1), (21929, 1), (127389817, 1)]
    PT.leaf)) 17177163455369 3 [(2, 3), (7, 2), (643, 1), (1303, 1), (52301, 1)]
    (PT.node (PT.node PT.leaf 17748600316039 6 [(2, 1), (3, 2), (53, 1), (127, 1), (146491361, 1)]
    PT.leaf) 18145704541823 5 [(2, 1), (11, 1), (13, 1), (29, 1), (12791, 1), (171043, 1)]
    (PT.node PT.leaf 22125996444329 3 [(2, 3), (7, 1), (29, 1), (13624382047, 1)]
    PT.leaf))) 22351248070103 5 [(2, 1), (7, 2), (199, 1), (9311, 1), (123091, 1)]
    (PT.node (PT.node (PT.node PT.leaf 27511055689331 6 [(2, 1), (5, 1), (17, 1), (691, 1), (1471, 1), (159209, 1)]
    PT.leaf) 28641763802723 5 [(2, 1), (7, 1), (71, 1), (1223, 1), (23560631, 1)]
    (PT.node PT.leaf 29854145014147 2 [(2, 1), (3, 3), (1181, 1), (10501, 1), (44579, 1)]
    PT.leaf)) 31479823396757 2 [(2, 2), (7, 2), (23, 1), (1811, 1), (3855937, 1)]
    (PT.node (PT.node PT.leaf 32261046755681 3 [(2, 5), (5, 1), (149, 1), (157, 1), (2383, 1), (3617, 1)]
    PT.leaf) 32341769617307 2 [(2, 1), (59, 1), (61, 1), (4493160547, 1)]
    (PT.node PT.leaf 32488790012831 11 [(2, 1), (5, 1), (71, 1), (45758859173, 1)]
    PT.leaf))))) 32528030679467 2 [(2, 1), (7, 1), (853, 1), (2723834423, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 33061343925391 11 [(2, 1), (3, 1), (5, 1), (11, 1), (13399, 1), (7477117, 1)]
    PT.leaf) 36825984292217 3 [(2, 3), (7, 1), (1759, 1), (11549, 1), (32371, 1)]
    PT.leaf) 36887518522451 2 [(2, 1), (5, 2), (23, 1), (523, 1), (3803, 1), (16127, 1)]
    (PT.node PT.leaf 40018405658657 3 [(2, 5), (479, 1), (2610804127, 1)]
    PT.leaf)) 41284013010997 15 [(2, 2), (3, 1), (7, 1), (17, 1), (211, 1), (5171, 1), (26497, 1)]
    (PT.node (PT.node PT.leaf 42272797713043 2 [(2, 1), (3, 1), (13, 1), (23, 1), (373, 1), (4523, 1), (13967, 1)]
    PT.leaf) 42674719959097 10 [(2, 3), (3, 1), (19, 1), (149, 1), (628086659, 1)]
    (PT.node PT.leaf 45692145853819 2 [(2, 1), (3, 1), (37, 1), (53, 1), (23017, 1), (168719, 1)]
    PT.leaf))) 46848518953531 3 [(2, 1), (3, 1), (5, 1), (7, 1), (19, 2), (73, 1), (8465381, 1)]
    (PT.node (PT.node (PT.node PT.leaf 46922470889141 2 [(2, 2), (5, 1), (7, 1), (11, 1), (17, 1), (2617, 1), (684869, 1)]
    PT.leaf) 49312005546883 2 [(2, 1), (3, 1), (13, 1), (101, 1), (6259457419, 1)]
    (PT.node PT.leaf 49851598189501 6 [(2, 2), (3, 4), (5, 3), (359, 1), (521, 1), (6581, 1)]
    PT.leaf)) 50368674550301 10 [(2, 2), (5, 2), (7039, 1), (71556577, 1)]
    (PT.node (PT.node PT.leaf 59376284620771 2 [(2, 1), (3, 1), (5, 1), (13, 1), (37, 1), (43, 1), (163, 1), (379, 1), (1549, 1)]
    PT.leaf) 63573002031499 2 [(2, 1), (3, 1), (17, 1), (19, 1), (54767, 1), (598963, 1)]
    (PT.node PT.leaf 68077641271019 2 [(2, 1), (23, 1), (149, 1), (5281, 1), (1880807, 1)]
    PT.leaf)))) 68917740951781 2 [(2, 2), (3, 3), (5, 1), (7, 3), (7877, 1), (47237, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 69710210289691 2 [(2, 1), (3, 1), (5, 1), (73, 1), (31831146251, 1)]
    PT.leaf) 71316922984999 3 [(2, 1), (3, 1), (29, 1), (179, 1), (691, 1), (983, 1), (3371, 1)]
    (PT.node PT.leaf 77230798373051 6 [(2, 1), (5, 2), (7, 1), (31, 1), (2081, 1), (3420493, 1)]
    PT.leaf)) 85584439140289 7 [(2, 6), (3, 1), (11, 1), (53, 1), (764583683, 1)]
    (PT.node (PT.node PT.leaf 96173433314953 13 [(2, 3), (3, 1), (7, 1), (443, 1), (1292236823, 1)]
    PT.leaf) 99244068137581 6 [(2, 2), (3, 1), (5, 1), (719, 1), (2300511547, 1)]
    (PT.node PT.leaf 99995282631947 2 [(2, 1), (13, 1), (17, 1), (4639, 1), (48767767, 1)]
    PT.leaf))) 102057353159483 2 [(2, 1), (7, 1), (1291, 1), (5646638993, 1)]
    (PT.node (PT.node (PT.node PT.leaf 104264348523151 11 [(2, 1), (3, 1), (5, 2), (17, 1), (59, 1), (693016607, 1)]
    PT.leaf) 115512048133057 5 [(2, 6), (3, 3), (17, 1), (233, 1), (16876357, 1)]
    (PT.node PT.leaf 120683554562401 7 [(2, 5), (3, 1), (5, 2), (19, 1), (4591, 1), (576469, 1)]
    PT.leaf)) 127875805844851 3 [(2, 1), (3, 2), (5, 2), (7, 1), (49927, 1), (813097, 1)]
    (PT.node (PT.node PT.leaf 132197305635599 7 [(2, 1), (7, 1), (937, 1), (10077550361, 1)]
    PT.leaf) 138161295607249 7 [(2, 4), (3, 2), (959453441717, 1)]
    (PT.node PT.leaf 143665652631953 3 [(2, 4), (11, 1), (17, 1), (4793, 1), (10018067, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab51 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 170558863220351 7 [(2, 1), (5, 2), (11, 1), (310107024037, 1)]
    PT.leaf) 181345750520141 2 [(2, 2), (5, 1), (17, 1), (31013, 1), (17198267, 1)]
    PT.leaf) 189361597248713 5 [(2, 3), (7, 1), (3381457093727, 1)]
    (PT.node PT.leaf 199592183280697 5 [(2, 3), (3, 1), (8316340970029, 1)]
    PT.leaf)) 230512752775793 3 [(2, 4), (31, 1), (106747, 1), (4353691, 1)]
    (PT.node (PT.node PT.leaf 234895531489741 2 [(2, 2), (3, 3), (5, 1), (11, 1), (97, 1), (14621, 1), (27883, 1)]
    PT.leaf) 237899493854161 11 [(2, 4), (3, 1), (5, 1), (991247891059, 1)]
    (PT.node PT.leaf 257418443803231 3 [(2, 1), (3, 2), (5, 1), (17, 1), (168247348891, 1)]
    PT.leaf))) 272518951775491 10 [(2, 1), (3, 2), (5, 1), (7, 1), (51539, 1), (8393057, 1)]
    (PT.node (PT.node (PT.node PT.leaf 282097794109643 2 [(2, 1), (7, 1), (37, 1), (544590336119, 1)]
    PT.leaf) 285996443195311 6 [(2, 1), (3, 1), (5, 1), (227, 1), (467, 1), (3079, 1), (29207, 1)]
    (PT.node PT.leaf 292479061755151 3 [(2, 1), (3, 2), (5, 2), (257, 1), (953, 1), (2653727, 1)]
    PT.leaf)) 347568611538691 2 [(2, 1), (3, 3), (5, 1), (59, 1), (571, 1), (38211023, 1)]
    (PT.node (PT.node PT.leaf 398633408201869 2 [(2, 2), (3, 1), (7, 1), (1321, 1), (13613, 1), (263899, 1)]
    PT.leaf) 402546032623057 13 [(2, 4), (3, 1), (7, 1), (167, 1), (1811, 1), (3961333, 1)]
    (PT.node PT.leaf 417335431509277 2 [(2, 2), (3, 1), (7, 1), (4968278946539, 1)]
    PT.leaf)))) 419460012167869 2 [(2, 2), (3, 2), (7, 1), (859, 1), (5081, 1), (381371, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 419740263829463 5 [(2, 1), (347, 1), (13033, 1), (46406281, 1)]
    PT.leaf) 436305197351477 2 [(2, 2), (359, 1), (303833702891, 1)]
    (PT.node PT.leaf 445455365264339 2 [(2, 1), (11, 1), (13, 1), (27427, 1), (56788429, 1)]
    PT.leaf)) 470380031133611 2 [(2, 1), (5, 1), (13, 2), (278331379369, 1)]
    (PT.node (PT.node PT.leaf 475384700124973 2 [(2, 2), (3, 2), (11, 1), (31, 1), (67, 1), (271, 1), (2132771, 1)]
    PT.leaf) 564833623891391 14 [(2, 1), (5, 1), (7, 2), (53, 1), (379, 1), (57386453, 1)]
    (PT.node PT.leaf 646835392346141 2 [(2, 2), (5, 1), (32341769617307, 1)]
    PT.leaf))) 719272201686877 5 [(2, 2), (3, 3), (71, 1), (93801799907, 1)]
    (PT.node (PT.node (PT.node PT.leaf 829007553280001 3 [(2, 11), (5, 4), (229, 1), (2828219, 1)]
    PT.leaf) 895380004183111 6 [(2, 1), (3, 1), (5, 1), (59, 1), (71, 1), (14747, 1), (483139, 1)]
    (PT.node PT.leaf 973116649840171 7 [(2, 1), (3, 1), (5, 1), (11, 1), (644353, 1), (4576433, 1)]
    PT.leaf)) 1163018639068051 2 [(2, 1), (3, 1), (5, 2), (17, 1), (456085740811, 1)]
    (PT.node (PT.node PT.leaf 1183576566098753 5 [(2, 6), (7, 1), (29, 1), (31, 1), (2938723001, 1)]
    PT.leaf) 1200552169759711 6 [(2, 1), (3, 1), (5, 1), (40018405658657, 1)]
    (PT.node PT.leaf 1225397542878343 3 [(2, 1), (3, 2), (68077641271019, 1)]
    PT.leaf))))) 1331399425301563 2 [(2, 1), (3, 1), (337, 1), (541, 1), (1907, 1), (638233, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 1437263292796553 3 [(2, 3), (13, 1), (53, 1), (25423, 1), (10256527, 1)]
    PT.leaf) 1648012040336791 3 [(2, 1), (3, 2), (5, 1), (283, 1), (64704045557, 1)]
    PT.leaf) 2014250546320891 2 [(2, 1), (3, 1), (5, 1), (17, 1), (3949510875139, 1)]
    (PT.node PT.leaf 2155876969481479 6 [(2, 1), (3, 2), (541, 1), (221388064231, 1)]
    PT.leaf)) 2249049650927341 6 [(2, 2), (3, 1), (5, 1), (173, 1), (216671449993, 1)]
    (PT.node (PT.node PT.leaf 2622789666510241 22 [(2, 5), (3, 1), (5, 1), (30347, 1), (180055529, 1)]
    PT.leaf) 2703853428809791 3 [(2, 1), (3, 1), (5, 1), (137, 1), (657871880489, 1)]
    (PT.node PT.leaf 2824638746642753 3 [(2, 6), (13, 1), (71, 1), (149, 1), (1747, 1), (183697, 1)]
    PT.leaf))) 2866633219854799 6 [(2, 1), (3, 1), (67, 1), (7130928407599, 1)]
    (PT.node (PT.node (PT.node PT.leaf 3276169443857161 7 [(2, 3), (3, 2), (5, 1), (23, 1), (151, 1), (1871, 1), (1400507, 1)]
    PT.leaf) 3571279638916061 2 [(2, 2), (5, 1), (19, 1), (5851, 1), (1606238987, 1)]
    (PT.node PT.leaf 3734409164527273 5 [(2, 3), (3, 1), (7, 2), (11, 1), (37, 1), (59, 1), (132241619, 1)]
    PT.leaf)) 3760772209395037 2 [(2, 2), (3, 1), (11, 2), (19, 1), (733, 1), (5801, 1), (32059, 1)]
    (PT.node (PT.node PT.leaf 3815387864419363 7 [(2, 1), (3, 1), (7, 2), (11, 1), (43, 1), (353, 1), (77724067, 1)]
    PT.leaf) 3943521108237341 2 [(2, 2), (5, 1), (7, 1), (23, 1), (1224695996347, 1)]
    (PT.node PT.leaf 4228269369065659 3 [(2, 1), (3, 5), (7, 1), (13873, 1), (89589673, 1)]
    PT.leaf)))) 4805923863681403 2 [(2, 1), (3, 1), (7, 1), (11, 1), (29, 1), (34759, 1), (10319761, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 5144408211938741 2 [(2, 2), (5, 1), (673, 1), (382199718569, 1)]
    PT.leaf) 5522944621250897 3 [(2, 4), (7, 1), (49312005546883, 1)]
    (PT.node PT.leaf 5580127603378541 2 [(2, 2), (5, 1), (47, 1), (107, 1), (55479494963, 1)]
    PT.leaf)) 7105848287681981 3 [(2, 2), (5, 1), (107, 1), (3320489854057, 1)]
    (PT.node (PT.node PT.leaf 8224356155341457 3 [(2, 4), (13, 1), (5874179, 1), (6731183, 1)]
    PT.leaf) 9460375336977361 14 [(2, 4), (3, 1), (5, 1), (73, 1), (24379, 1), (22149217, 1)]
    (PT.node PT.leaf 10926617075177803 5 [(2, 1), (3, 1), (61, 1), (29854145014147, 1)]
    PT.leaf))) 11627796440687491 10 [(2, 1), (3, 3), (5, 1), (7, 1), (2719, 1), (2262697039, 1)]
    (PT.node (PT.node (PT.node PT.leaf 13370848663151621 2 [(2, 2), (5, 1), (19, 1), (283, 1), (10753, 1), (11562701, 1)]
    PT.leaf) 14421466756460791 6 [(2, 1), (3, 2), (5, 1), (13, 1), (47, 1), (2903, 1), (90339707, 1)]
    (PT.node PT.leaf 15615240677173831 3 [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (23, 1), (293906280391, 1)]
    PT.leaf)) 16443420968455561 7 [(2, 3), (3, 3), (5, 1), (29, 1), (656371, 1), (799873, 1)]
    (PT.node (PT.node PT.leaf 16665215705306549 2 [(2, 2), (29, 1), (143665652631953, 1)]
    PT.leaf) 16842464147039939 2 [(2, 1), (11, 2), (268547, 1), (259161187, 1)]
    (PT.node PT.leaf 21261152595806269 2 [(2, 2), (3, 1), (1249, 1), (1511, 1), (4007, 1), (234293, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab52 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 27145365052629449 3 [(2, 3), (47, 1), (53, 1), (107, 1), (113, 1), (112660001, 1)]
    PT.leaf) 27935336611728311 17 [(2, 1), (5, 1), (19, 1), (71, 1), (16811, 1), (123182329, 1)]
    PT.leaf) 29320017968958271 3 [(2, 1), (3, 1), (5, 1), (727, 1), (1344338283767, 1)]
    (PT.node PT.leaf 33579221106357041 3 [(2, 4), (5, 1), (419740263829463, 1)]
    PT.leaf)) 38697691152119723 2 [(2, 1), (71, 1), (272518951775491, 1)]
    (PT.node (PT.node PT.leaf 38833995162778271 7 [(2, 1), (5, 1), (7, 1), (13, 1), (42674719959097, 1)]
    PT.leaf) 43755700778249029 7 [(2, 2), (3, 1), (37, 1), (113, 1), (31477, 1), (27706387, 1)]
    (PT.node PT.leaf 50544702849929377 5 [(2, 5), (3, 1), (11, 1), (17, 1), (61, 1), (7321, 1), (6304673, 1)]
    PT.leaf))) 55439996877924151 3 [(2, 1), (3, 1), (5, 2), (37, 1), (103, 1), (15277, 1), (6348263, 1)]
    (PT.node (PT.node (PT.node PT.leaf 59097442119890627 2 [(2, 1), (1073243, 1), (27532181491, 1)]
    PT.leaf) 60082728190583743 3 [(2, 1), (3, 2), (7, 1), (281, 1), (1696964587657, 1)]
    (PT.node PT.leaf 78690566287141541 2 [(2, 2), (5, 1), (31, 1), (151, 1), (25057, 1), (33544781, 1)]
    PT.leaf)) 80037421623539251 3 [(2, 1), (3, 1), (5, 3), (13, 1), (31, 1), (199, 1), (509, 1), (2614303, 1)]
    (PT.node (PT.node PT.leaf 81750272028928231 7 [(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (4013, 1), (7462037027, 1)]
    PT.leaf) 85274310200918999 17 [(2, 1), (101, 1), (709, 1), (3373, 1), (176524207, 1)]
    (PT.node PT.leaf 98311534883794601 3 [(2, 3), (5, 2), (19, 1), (29, 1), (233, 1), (17707, 1), (216233, 1)]
    PT.leaf)))) 101575310611951327 3 [(2, 1), (3, 1), (29, 1), (7761773, 1), (75210413, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 104771190406139743 3 [(2, 1), (3, 1), (337, 1), (160081, 1), (323683781, 1)]
    PT.leaf) 134501009594864791 6 [(2, 1), (3, 1), (5, 1), (43, 1), (104264348523151, 1)]
    PT.leaf) 143554218709131407 5 [(2, 1), (11, 1), (2557, 1), (23549, 1), (108365261, 1)]
    (PT.node PT.leaf 145171177264407947 2 [(2, 1), (79, 1), (15061, 1), (52553, 1), (1160839, 1)]
    PT.leaf)) 163330228644304489 7 [(2, 3), (3, 1), (13, 1), (209719, 1), (2496170221, 1)]
    (PT.node (PT.node PT.leaf 165049085515149863 5 [(2, 1), (13, 1), (17, 1), (29, 1), (31, 1), (4241, 1), (97940629, 1)]
    PT.leaf) 169310154773889599 7 [(2, 1), (7, 1), (30867523, 1), (391789859, 1)]
    (PT.node PT.leaf 200741603328100897 10 [(2, 5), (3, 1), (23, 1), (1153, 1), (78851328029, 1)]
    PT.leaf))) 216770511782448821 2 [(2, 2), (5, 1), (7, 4), (8429, 1), (17443, 1), (30703, 1)]
    (PT.node (PT.node (PT.node PT.leaf 248366755289421259 7 [(2, 1), (3, 1), (7, 3), (120683554562401, 1)]
    PT.leaf) 280441731546402949 6 [(2, 2), (3, 6), (96173433314953, 1)]
    (PT.node PT.leaf 284860058207025151 6 [(2, 1), (3, 2), (5, 2), (17, 1), (487, 1), (76461209273, 1)]
    PT.leaf)) 285472521588928549 2 [(2, 2), (3, 1), (7, 1), (5449, 1), (623689190653, 1)]
    (PT.node (PT.node PT.leaf 354584652719343763 2 [(2, 1), (3, 1), (59097442119890627, 1)]
    PT.leaf) 365834083876629007 3 [(2, 1), (3, 1), (1373, 1), (73421, 1), (604842197, 1)]
    (PT.node PT.leaf 380808546861411923 2 [(2, 1), (11, 1), (43, 1), (402546032623057, 1)]
    PT.leaf))))) 425557298187947929 7 [(2, 3), (3, 1), (59, 1), (83, 1), (283, 1), (2053, 1), (6232199, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 484563667343825089 7 [(2, 6), (3, 3), (17, 1), (1013, 1), (17729, 1), (918469, 1)]
    PT.leaf) 489769993189671059 2 [(2, 1), (59, 1), (181, 1), (3847, 1), (5960866633, 1)]
    PT.leaf) 625552508473588471 3 [(2, 1), (3, 1), (5, 1), (31, 1), (67, 1), (391337, 1), (25654001, 1)]
    (PT.node PT.leaf 807006057569188747 3 [(2, 1), (3, 1), (134501009594864791, 1)]
    PT.leaf)) 837197335075000483 3 [(2, 1), (3, 2), (11, 1), (4228269369065659, 1)]
    (PT.node (PT.node PT.leaf 1121659287043817009 3 [(2, 4), (19, 1), (173, 1), (346309, 1), (61585361, 1)]
    PT.leaf) 1357455621951689179 2 [(2, 1), (3, 1), (67, 1), (139, 1), (419, 1), (1129, 1), (51354301, 1)]
    (PT.node PT.leaf 1435511378542612963 2 [(2, 1), (3, 1), (29, 1), (37, 1), (1289, 1), (1531, 1), (2741, 1), (41221, 1)]
    PT.leaf))) 1453121857811448551 11 [(2, 1), (5, 2), (11, 1), (41, 2), (139, 1), (431, 1), (26234909, 1)]
    (PT.node (PT.node (PT.node PT.leaf 2192537062271178641 3 [(2, 4), (5, 1), (43, 1), (228677, 1), (2787186403, 1)]
    PT.leaf) 2226081858886600201 13 [(2, 3), (3, 2), (5, 2), (1657, 1), (3061, 1), (7283, 1), (33479, 1)]
    (PT.node PT.leaf 2615418118891695851 2 [(2, 1), (5, 2), (37, 1), (11490289, 1), (123037769, 1)]
    PT.leaf)) 2871392081815431791 7 [(2, 1), (5, 1), (7, 1), (11, 1), (5101, 1), (731048936627, 1)]
    (PT.node (PT.node PT.leaf 3124914562747294549 2 [(2, 2), (3, 1), (7, 1), (11, 1), (1171579, 1), (2886653113, 1)]
    PT.leaf) 3325433255988398101 2 [(2, 2), (3, 2), (5, 2), (7, 1), (13, 1), (127, 1), (911, 1), (350947567, 1)]
    (PT.node PT.leaf 3440498852589004771 3 [(2, 1), (3, 1), (5, 1), (3109, 1), (36887518522451, 1)]
    PT.leaf)))) 3693170746409441903 5 [(2, 1), (11, 1), (73, 1), (402137, 1), (5718469541, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 3747607031112307667 2 [(2, 1), (53, 1), (252401, 1), (140073863861, 1)]
    PT.leaf) 3999088279399464409 17 [(2, 3), (3, 1), (31, 1), (563099, 1), (9545601493, 1)]
    (PT.node PT.leaf 4750445693592883451 2 [(2, 1), (5, 2), (29, 1), (3276169443857161, 1)]
    PT.leaf)) 4773789388470179983 3 [(2, 1), (3, 1), (101, 1), (4720637, 1), (1668745181, 1)]
    (PT.node (PT.node PT.leaf 4840424302613898067 2 [(2, 1), (3, 1), (17, 1), (53, 1), (895380004183111, 1)]
    PT.leaf) 5079304643216687969 3 [(2, 5), (7, 2), (41, 2), (114161, 1), (16880011, 1)]
    (PT.node PT.leaf 5244722549705267119 3 [(2, 1), (3, 2), (7, 1), (103, 1), (823, 1), (491037786697, 1)]
    PT.leaf))) 5649279695306924197 2 [(2, 2), (3, 1), (13, 1), (83, 1), (436305197351477, 1)]
    (PT.node (PT.node (PT.node PT.leaf 5959385178992891363 2 [(2, 1), (19231, 1), (576031, 1), (268982321, 1)]
    PT.leaf) 6115909044841454629 14 [(2, 2), (3, 3), (7, 1), (11, 1), (19, 1), (37, 1), (590077, 1), (1772893, 1)]
    (PT.node PT.leaf 6193396676178514477 2 [(2, 2), (3, 2), (47, 1), (163, 1), (9151, 1), (2453987681, 1)]
    PT.leaf)) 6254429058851062673 3 [(2, 4), (11, 1), (29, 1), (1225397542878343, 1)]
    (PT.node (PT.node PT.leaf 7176374761323733117 2 [(2, 2), (3, 1), (23, 1), (409, 1), (63573002031499, 1)]
    PT.leaf) 9700639967080761011 2 [(2, 1), (5, 1), (13, 1), (23, 1), (433, 1), (7492751023103, 1)]
    (PT.node PT.leaf 9875322243666178231 3 [(2, 1), (3, 1), (5, 1), (71, 1), (499, 1), (9291185416529, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab53 : PT :=
  (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 15782029270873877411 2 [(2, 1), (5, 1), (7, 1), (37, 1), (281, 1), (53951, 1), (401936329, 1)]
    PT.leaf) 19566123517737808021 6 [(2, 2), (3, 2), (5, 1), (17, 1), (179, 1), (191033, 1), (186991531, 1)]
    PT.leaf) 24727552016409065771 2 [(2, 1), (5, 1), (227, 1), (733, 1), (14861111488247, 1)]
    (PT.node PT.leaf 28769600332597803883 2 [(2, 1), (3, 1), (7, 1), (31, 1), (43785151, 1), (504656641, 1)]
    PT.leaf)) 32147832919817717593 22 [(2, 3), (3, 1), (7, 2), (61, 1), (223, 1), (829, 1), (1063, 1), (1279, 1), (1783, 1)]
    (PT.node (PT.node PT.leaf 32607907713428723311 11 [(2, 1), (3, 1), (5, 1), (223, 1), (397, 1), (731363, 1), (16787009, 1)]
    PT.leaf) 47834644354838156839 3 [(2, 1), (3, 1), (11, 1), (739, 1), (8527, 1), (98519, 1), (1167449, 1)]
    (PT.node PT.leaf 52198426022458982993 3 [(2, 4), (11, 1), (17, 1), (232189, 1), (75137056459, 1)]
    PT.leaf))) 88770666332610762169 11 [(2, 3), (3, 1), (19, 1), (73, 1), (139, 1), (3331, 1), (5759600279, 1)]
    (PT.node (PT.node (PT.node PT.leaf 94597128022319068199 7 [(2, 1), (13, 1), (233, 1), (15615240677173831, 1)]
    PT.leaf) 96038174442851039533 2 [(2, 2), (3, 1), (7, 2), (163330228644304489, 1)]
    (PT.node PT.leaf 128020985937141860471 17 [(2, 1), (5, 1), (1861, 1), (13309, 1), (516879573103, 1)]
    PT.leaf)) 142543030393176192727 3 [(2, 1), (3, 1), (67, 1), (354584652719343763, 1)]
    (PT.node (PT.node PT.leaf 149431854123332538041 3 [(2, 3), (5, 1), (131, 1), (211, 1), (110563, 1), (1222417697, 1)]
    PT.leaf) 157571957584602258799 3 [(2, 1), (3, 1), (17, 1), (19, 1), (31, 1), (2622789666510241, 1)]
    (PT.node PT.leaf 172827552198815888791 6 [(2, 1), (3, 1), (5, 1), (13, 2), (43, 1), (810091, 1), (978594469, 1)]
    PT.leaf)))) 228025037356421836807 5 [(2, 1), (3, 2), (11, 1), (6317, 1), (12073, 1), (15100497917, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 434995922491317607327 5 [(2, 1), (3, 1), (977, 1), (3011, 1), (14947, 1), (37379, 1), (44111, 1)]
    PT.leaf) 496865249166620100967 3 [(2, 1), (3, 1), (176051, 1), (470380031133611, 1)]
    (PT.node PT.leaf 506710914239632419773 2 [(2, 2), (7, 1), (13, 1), (353, 1), (3943521108237341, 1)]
    PT.leaf)) 539093310059453790343 3 [(2, 1), (3, 1), (13, 1), (2411, 1), (2866633219854799, 1)]
    (PT.node (PT.node PT.leaf 700888562389531127981 10 [(2, 2), (5, 1), (53, 1), (307, 1), (1777, 1), (162709, 1), (7449133, 1)]
    PT.leaf) 703207451121161180833 10 [(2, 5), (3, 2), (11, 1), (71, 1), (97, 1), (1373, 1), (21881, 1), (1072829, 1)]
    (PT.node PT.leaf 846041103974872866961 7 [(2, 4), (3, 2), (5, 1), (29, 1), (37, 1), (244841, 1), (4472754901, 1)]
    PT.leaf))) 1606424290213518947263 7 [(2, 1), (3, 1), (7, 1), (13, 1), (864840203, 1), (3401979949, 1)]
    (PT.node (PT.node (PT.node PT.leaf 1622337552083173402331 2 [(2, 1), (5, 1), (7, 1), (1583, 1), (67429, 1), (201781, 1), (1076057, 1)]
    PT.leaf) 1807475964966137691443 2 [(2, 1), (7, 1), (61, 1), (127, 1), (16665215705306549, 1)]
    (PT.node PT.leaf 2519545342349331183143 5 [(2, 1), (23, 1), (42899, 1), (2197469, 1), (581024467, 1)]
    PT.leaf)) 5378193516362980863601 19 [(2, 4), (3, 2), (5, 2), (17, 1), (29, 1), (1063831, 1), (2848487797, 1)]
    (PT.node (PT.node PT.leaf 5742692449452968574979 2 [(2, 1), (3, 3), (7, 1), (47, 1), (241, 1), (7109, 1), (7177, 1), (26287991, 1)]
    PT.leaf) 7560423642616328727781 7 [(2, 2), (3, 1), (5, 1), (17, 1), (139, 1), (613279, 1), (86950696619, 1)]
    (PT.node PT.leaf 9630092768572369626677 2 [(2, 2), (11, 1), (13, 1), (19, 1), (149519, 1), (5926311255103, 1)]
    PT.leaf))))) 11388947865738759181153 5 [(2, 5), (3, 2), (7, 1), (5649279695306924197, 1)]
    (PT.node (PT.node (PT.node (PT.node (PT.node (PT.node PT.leaf 12567292335484050831661 13 [(2, 2), (3, 2), (5, 1), (7, 1), (347, 1), (12263431, 1), (2343849413, 1)]
    PT.leaf) 31810898376456201755581 2 [(2, 2), (3, 1), (5, 1), (37, 1), (14329233502908198989, 1)]
    PT.leaf) 47009039042447030231489 6 [(2, 6), (13, 1), (83, 1), (241, 1), (2824638746642753, 1)]
    (PT.node PT.leaf 63681511996418550459487 5 [(2, 1), (3, 1), (47, 1), (97, 1), (367, 1), (9187351, 1), (690456227, 1)]
    PT.leaf)) 97199158345481611029493 6 [(2, 2), (3, 2), (7, 1), (19, 2), (647, 1), (46147, 1), (35785493279, 1)]
    (PT.node (PT.node PT.leaf 98811777493935291929249 3 [(2, 5), (7, 2), (739, 1), (85274310200918999, 1)]
    PT.leaf) 105293313660391861035901 10 [(2, 2), (3, 1), (5, 2), (11, 1), (29, 1), (43, 1), (61, 1), (419460012167869, 1)]
    (PT.node PT.leaf 109912203092239643840221 10 [(2, 2), (3, 2), (5, 1), (7, 3), (19, 1), (127, 1), (199, 1), (523, 1), (29989, 1), (236377, 1)]
    PT.leaf))) 751670559138758105956097 3 [(2, 8), (13, 1), (17, 1), (31, 1), (37, 1), (409, 1), (1129, 1), (25085030513, 1)]
    (PT.node (PT.node (PT.node PT.leaf 950996059627210897943351 7 [(2, 1), (5, 2), (37, 1), (83, 1), (6193396676178514477, 1)]
    PT.leaf) 2768733893059808474864941 6 [(2, 2), (3, 1), (5, 1), (1091, 1), (1093, 1), (38697691152119723, 1)]
    (PT.node PT.leaf 4362139336229068656094783 6 [(2, 1), (3, 1), (41, 1), (3299797, 1), (7596203, 1), (707425387, 1)]
    PT.leaf)) 4805345109492315767981401 11 [(2, 3), (3, 1), (5, 2), (37, 1), (2131, 1), (101575310611951327, 1)]
    (PT.node (PT.node PT.leaf 7801927585025353459681093 5 [(2, 2), (3, 1), (7, 1), (13, 1), (349, 1), (503, 1), (4591, 1), (14083, 1), (14401, 1), (43711, 1)]
    PT.leaf) 7858179685661558917710821 10 [(2, 2), (5, 1), (197, 1), (349, 1), (167429, 1), (1674289, 1), (20386337, 1)]
    (PT.node PT.leaf 10866472977391930428570371 2 [(2, 1), (5, 1), (11, 1), (61, 1), (1193, 1), (1357455621951689179, 1)]
    PT.leaf)))) 14724111939861108567410951 7 [(2, 1), (5, 2), (7, 1), (1129, 1), (4810493, 1), (7746000794761, 1)]
    (PT.node (PT.node (PT.node (PT.node PT.leaf 30824387179353424155370957 2 [(2, 2), (3, 1), (7, 2), (19, 1), (31, 1), (233, 1), (17707, 1), (2133031, 1), (10113553, 1)]
    PT.leaf) 33899939683211028917156831 13 [(2, 1), (5, 1), (641, 1), (983, 1), (2671, 1), (2014250546320891, 1)]
    (PT.node PT.leaf 83197127088240304524014197 2 [(2, 2), (3, 2), (7, 1), (17, 1), (269, 1), (932227613, 1), (77443438027, 1)]
    PT.leaf)) 303309617049998388989376043 3 [(2, 1), (3, 1), (7, 1), (29, 1), (1747, 1), (142543030393176192727, 1)]
    (PT.node (PT.node PT.leaf 315163118203085670683224621 2 [(2, 2), (3, 1), (5, 1), (11, 1), (10169, 1), (160553, 1), (292479061755151, 1)]
    PT.leaf) 362759437743508955104646759 19 [(2, 1), (17, 1), (3715757, 1), (2871392081815431791, 1)]
    (PT.node PT.leaf 494424256962371823779424877 2 [(2, 2), (3, 2), (11, 1), (13, 1), (31, 1), (41, 1), (467, 1), (1931, 1), (3409261, 1), (24578551, 1)]
    PT.leaf))) 1539295634290340976189184549 2 [(2, 2), (3, 4), (7, 1), (37, 1), (191, 1), (96038174442851039533, 1)]
    (PT.node (PT.node (PT.node PT.leaf 8170509011431363408568150369 6 [(2, 5), (13, 1), (31, 1), (4759, 1), (126323, 1), (11721217, 1), (89913157, 1)]
    PT.leaf) 172545754771028210096747645881 7 [(2, 3), (3, 1), (5, 1), (17, 1), (41, 1), (8017, 1), (99907, 1), (20381027, 1), (126373609, 1)]
    (PT.node PT.leaf 607127818287731321660577427051 3 [(2, 1), (3, 1), (5, 2), (11, 1), (19, 1), (151273, 1), (128020985937141860471, 1)]
    PT.leaf)) 62065212901958868055012327674641 3 [(2, 4), (5, 1), (7, 2), (17, 1), (97, 1), (233, 1), (941, 1), (189977, 1), (230512752775793, 1)]
    (PT.node (PT.node PT.leaf 177635683940025046467781066894531 3 [(2, 1), (3, 1), (5, 1), (47, 1), (8971, 1), (332207361361, 1), (42272797713043, 1)]
    PT.leaf) 3754733257489862401973357979128773 5 [(2, 2), (3, 1), (11, 2), (61, 1), (71, 1), (547, 1), (1093, 1), (2664097031, 1), (374857981681, 1)]
    (PT.node PT.leaf 243270318891483838103593381595151809701 6 [(2, 2), (3, 1), (5, 2), (7, 3), (11, 1), (19, 1), (31, 1), (61, 1), (127, 1), (151, 1), (211, 1), (271, 1), (911, 1), (2251, 1), (1081291, 1), (2460181, 1)]
    PT.leaf))))))

/-- Part of the prime table. -/
def tab54 : PT :=
  PT.node tab50 169299992707751 11 [(2, 1), (5, 3), (677199970831, 1)] tab51

/-- Part of the prime table. -/
def tab55 : PT :=
  PT.node tab52 14329233502908198989 2 [(2, 2), (5463181, 1), (655718413087, 1)] tab53

/-- Part of the prime table. -/
def tab56 : PT :=
  PT.node tab48 47774964821 2 [(2, 2), (5, 1), (11, 2), (29, 1), (680749, 1)] tab49

/-- Part of the prime table. -/
def tab57 : PT :=
  PT.node tab54 23971944503021153 3 [(2, 5), (11, 1), (17, 1), (71, 1), (56422630543, 1)] tab55

/-- Part of the prime table. -/
def tab58 : PT :=
  PT.node tab42 9170881 19 [(2, 6), (3, 1), (5, 1), (41, 1), (233, 1)] tab43

/-- Part of the prime table. -/
def tab59 : PT :=
  PT.node tab56 8079064749671 11 [(2, 1), (5, 1), (1429, 1), (565364923, 1)] tab57

/-- Part of the prime table. -/
def tab60 : PT :=
  PT.node tab28 10247 5 [(2, 1), (47, 1), (109, 1)] tab29

/-- Part of the prime table. -/
def tab61 : PT :=
  PT.node tab58 917087137 5 [(2, 5), (3, 1), (7, 2), (19, 1), (31, 1), (331, 1)] tab59

/-- The prime table. -/
def table : PT :=
  PT.node tab60 477277 2 [(2, 2), (3, 1), (31, 1), (1283, 1)] tab61

/-- The prime table is valid. -/
theorem table_ok : table.allOK table = true := by
  decide +kernel

/-- Every key of the prime table is prime. -/
theorem table_prime : ∀ x, table.mem x = true → x.Prime :=
  PT.prime_of_mem table_ok

/-- Instructions, part 0. -/
def tree3_0 : List Ins := [
  .up 3 1,
  .rs 3 1 167,
  .parS 3,
  .force 13 1 [(3, 2)],
  .rs 13 1 72,
  .force 7 1 [(3, 2), (13, 1)],
  .up 7 1,
  .rs 7 1 93,
  .par2 13 7,
  .force 19 1 [(3, 2), (7, 2), (13, 1)],
  .up 19 1,
  .rs 19 1 60,
  .par2 13 19,
  .force 127 1 [(3, 2), (7, 2), (13, 1), (19, 2)],
  .up 127 1,
  .rs 127 1 36,
  .par2 13 127,
  .force 5419 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2)],
  .up 5419 1,
  .rs 5419 1 20,
  .par2 13 5419,
  .force 1009 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 2)],
  .up 1009 1,
  .rs 1009 1 20,
  .par2 13 1009,
  .force 9181 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (5419, 2)],
  .up 9181 1,
  .rs 9181 1 14,
  .par2 13 9181,
  .force 1423 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 2)],
  .up 1423 1,
  .rs 1423 1 13,
  .par2 13 1423,
  .force 96493 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2)],
  .up 96493 1,
  .rs 96493 1 7,
  .par2 13 96493,
  .force 163350799 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 2)],
  .up 163350799 1,
  .rs 163350799 1 4,
  .par2 13 163350799,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 2), (163350799, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2)],
  .force 40497241 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2)],
  .up 40497241 1,
  .rs 40497241 1 4,
  .par2 13 40497241,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2), (40497241, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (1423, 6), (5419, 2), (9181, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (1423, 10), (5419, 2), (9181, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 2)],
  .force 125642407351 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 4)],
  .up 125642407351 1,
  .rs 125642407351 1 4,
  .par2 13 125642407351,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 4), (125642407351, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 4)],
  .force 19937168287 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 6)],
  .up 19937168287 1,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 6)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 10)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 12)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 2), (5419, 2)],
  .force 1037517185381 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 4), (5419, 2)],
  .up 1037517185381 1,
  .rs 1037517185381 1 5,
  .par2 13 1037517185381,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 4), (5419, 2), (1037517185381, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 4), (5419, 2)],
  .force 1024823381 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 6), (5419, 2)],
  .up 1024823381 1,
  .rs 1024823381 1 5,
  .par2 13 1024823381,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 6), (5419, 2), (1024823381, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 6), (5419, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 10), (5419, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 12), (5419, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 16), (5419, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (1009, 18), (5419, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 2)],
  .force 836561914831 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 4)],
  .up 836561914831 1,
  .rs 836561914831 1 6,
  .par2 13 836561914831,
  .force 347568611538691 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 4), (836561914831, 2)],
  .up 347568611538691 1,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 4), (836561914831, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 4), (836561914831, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 4)],
  .force 829621381 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 6)],
  .up 829621381 1,
  .rs 829621381 1 5,
  .par2 13 829621381,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 6), (829621381, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 6)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 10)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 12)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 16)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2), (5419, 18)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 2)],
  .force 262209281 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 4)],
  .up 262209281 1,
  .rs 262209281 1 9,
  .par2 13 262209281,
  .force 4296301150081 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 4), (262209281, 2)],
  .up 4296301150081 1,
  .rs 4296301150081 1 5,
  .par2 13 4296301150081,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 4), (262209281, 2), (4296301150081, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 4), (262209281, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 4), (262209281, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 4), (262209281, 6)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 4)],
  .force 162709 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 6)],
  .up 162709 1,
  .rs 162709 1 12,
  .par2 13 162709,
  .force 8824793797 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 6), (162709, 2)],
  .up 8824793797 1,
  .rs 8824793797 1 6,
  .par2 13 8824793797,
  .force 425557298187947929 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 6), (162709, 2), (8824793797, 2)],
  .up 425557298187947929 1,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 6), (162709, 2), (8824793797, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 6), (162709, 2), (8824793797, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 6), (162709, 2)],
  .force 700888562389531127981 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 6), (162709, 4)],
  .up 700888562389531127981 1,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 6), (162709, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 6), (162709, 6)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 6), (162709, 10)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 6)],
  .force 47834644354838156839 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 10)],
  .up 47834644354838156839 1,
  .rs 47834644354838156839 1 4,
  .par2 13 47834644354838156839,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 10), (47834644354838156839, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 10)],
  .force 1437263292796553 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 12)],
  .up 1437263292796553 1,
  .rs 1437263292796553 1 4,
  .par2 13 1437263292796553,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 12), (1437263292796553, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 12)],
  .force 115512048133057 1 [(3, 2), (7, 2), (13, 1), (19, 2), (127, 16)],
  .up 115512048133057 1,
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 16)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 18)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 22)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 28)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2), (127, 30)],
  .big [(3, 2), (7, 2), (13, 1), (19, 2)],
  .force 911 1 [(3, 2), (7, 2), (13, 1), (19, 4)],
  .up 911 1,
  .rs 911 1 24,
  .par2 13 911,
  .force 830833 1 [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2)],
  .up 830833 1,
  .rs 830833 1 12,
  .par2 13 830833,
  .force 861001 1 [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (830833, 2)],
  .up 861001 1,
  .rs 861001 1 9,
  .par2 13 861001,
  .force 217081 1 [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (830833, 2), (861001, 2)],
  .up 217081 1,
  .rs 217081 1 6,
  .par2 13 217081,
  .force 1077301 1 [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (217081, 2), (830833, 2), (861001, 2)],
  .up 1077301 1,
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (217081, 2), (830833, 2), (861001, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (217081, 4), (830833, 2), (861001, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (830833, 2), (861001, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (830833, 2), (861001, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (830833, 2), (861001, 6)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (830833, 2)],
  .force 2249049650927341 1 [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (830833, 4)],
  .up 2249049650927341 1,
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (830833, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (830833, 6)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2), (830833, 10)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 2)],
  .force 17884211 1 [(3, 2), (7, 2), (13, 1), (19, 4), (911, 4)],
  .up 17884211 1,
  .rs 17884211 1 9,
  .par2 13 17884211,
  .force 45692145853819 1 [(3, 2), (7, 2), (13, 1), (19, 4), (911, 4), (17884211, 2)],
  .up 45692145853819 1,
  .rs 45692145853819 1 4,
  .par2 13 45692145853819,
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 4), (17884211, 2), (45692145853819, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 4), (17884211, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 4), (17884211, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 4), (17884211, 6)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 4)],
  .force 81750272028928231 1 [(3, 2), (7, 2), (13, 1), (19, 4), (911, 6)],
  .up 81750272028928231 1,
  .rs 81750272028928231 1 4,
  .par2 13 81750272028928231,
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 6), (81750272028928231, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 6)],
  .force 247174661801 1 [(3, 2), (7, 2), (13, 1), (19, 4), (911, 10)],
  .up 247174661801 1,
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 10)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 12)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 16)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 18)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4), (911, 22)],
  .big [(3, 2), (7, 2), (13, 1), (19, 4)],
  .force 70841 1 [(3, 2), (7, 2), (13, 1), (19, 6)],
  .up 70841 1,
  .rs 70841 1 15,
  .par2 13 70841,
  .force 128341 1 [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 2)],
  .up 128341 1,
  .rs 128341 1 11,
  .par2 13 128341,
  .force 5490513541 1 [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 2), (128341, 2)],
  .up 5490513541 1,
  .rs 5490513541 1 6,
  .par2 13 5490513541,
  .force 1435511378542612963 1 [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 2), (128341, 2), (5490513541, 2)],
  .up 1435511378542612963 1,
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 2), (128341, 2), (5490513541, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 2), (128341, 2), (5490513541, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 2), (128341, 2)],
  .force 12833941 1 [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 2), (128341, 4)],
  .up 12833941 1,
  .rs 12833941 1 4,
  .par2 13 12833941,
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 2), (128341, 4), (12833941, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 2), (128341, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 2), (128341, 6)],
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 2)],
  .force 1163018639068051 1 [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 4)],
  .up 1163018639068051 1,
  .rs 1163018639068051 1 4,
  .par2 13 1163018639068051,
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 4), (1163018639068051, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 4)],
  .force 98811777493935291929249 1 [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 6)],
  .up 98811777493935291929249 1,
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 6)],
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 10)],
  .big [(3, 2), (7, 2), (13, 1), (19, 6), (70841, 12)],
  .big [(3, 2), (7, 2), (13, 1), (19, 6)],
  .force 62060021 1 [(3, 2), (7, 2), (13, 1), (19, 10)],
  .up 62060021 1,
  .rs 62060021 1 9,
  .par2 13 62060021,
  .force 17748600316039 1 [(3, 2), (7, 2), (13, 1), (19, 10), (62060021, 2)],
  .up 17748600316039 1,
  .rs 17748600316039 1 5,
  .par2 13 17748600316039,
  .big [(3, 2), (7, 2), (13, 1), (19, 10), (62060021, 2), (17748600316039, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 10), (62060021, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 10), (62060021, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 10), (62060021, 6)],
  .big [(3, 2), (7, 2), (13, 1), (19, 10)],
  .force 133338869 1 [(3, 2), (7, 2), (13, 1), (19, 12)],
  .up 133338869 1,
  .rs 133338869 1 8,
  .par2 13 133338869,
  .force 316950847 1 [(3, 2), (7, 2), (13, 1), (19, 12), (133338869, 2)],
  .up 316950847 1,
  .rs 316950847 1 5,
  .par2 13 316950847,
  .big [(3, 2), (7, 2), (13, 1), (19, 12), (133338869, 2), (316950847, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 12), (133338869, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 12), (133338869, 4)],
  .big [(3, 2), (7, 2), (13, 1), (19, 12), (133338869, 6)],
  .big [(3, 2), (7, 2), (13, 1), (19, 12)],
  .force 99995282631947 1 [(3, 2), (7, 2), (13, 1), (19, 16)],
  .up 99995282631947 1,
  .rs 99995282631947 1 5,
  .par2 13 99995282631947,
  .big [(3, 2), (7, 2), (13, 1), (19, 16), (99995282631947, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 16)],
  .force 109912203092239643840221 1 [(3, 2), (7, 2), (13, 1), (19, 18)],
  .up 109912203092239643840221 1,
  .rs 109912203092239643840221 1 4,
  .par2 13 109912203092239643840221,
  .big [(3, 2), (7, 2), (13, 1), (19, 18), (109912203092239643840221, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 18)],
  .force 1335495402823 1 [(3, 2), (7, 2), (13, 1), (19, 22)],
  .up 1335495402823 1,
  .rs 1335495402823 1 4,
  .par2 13 1335495402823,
  .big [(3, 2), (7, 2), (13, 1), (19, 22), (1335495402823, 2)],
  .big [(3, 2), (7, 2), (13, 1), (19, 22)],
  .force 165049085515149863 1 [(3, 2), (7, 2), (13, 1), (19, 28)],
  .up 165049085515149863 1,
  .big [(3, 2), (7, 2), (13, 1), (19, 28)],
  .big [(3, 2), (7, 2), (13, 1), (19, 30)],
  .big [(3, 2), (7, 2), (13, 1), (19, 36)],
  .big [(3, 2), (7, 2), (13, 1), (19, 40)],
  .big [(3, 2), (7, 2), (13, 1), (19, 42)],
  .big [(3, 2), (7, 2), (13, 1), (19, 46)],
  .big [(3, 2), (7, 2), (13, 1), (19, 52)],
  .big [(3, 2), (7, 2), (13, 1), (19, 58)],
  .big [(3, 2), (7, 2), (13, 1)],
  .force 2801 1 [(3, 2), (7, 4), (13, 1)],
  .up 2801 1,
  .rs 2801 1 23,
  .par2 13 2801,
  .force 4933 1 [(3, 2), (7, 4), (13, 1), (2801, 2)],
  .up 4933 1,
  .rs 4933 1 19,
  .par2 13 4933,
  .force 331 1 [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 2)],
  .up 331 1,
  .rs 331 1 22,
  .par2 13 331,
  .force 5233 1 [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2)],
  .up 5233 1,
  .rs 5233 1 14,
  .par2 13 5233,
  .force 42073 1 [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2)],
  .up 42073 1,
  .rs 42073 1 10,
  .par2 13 42073,
  .force 75931 1 [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2)],
  .up 75931 1,
  .rs 75931 1 6,
  .par2 13 75931,
  .force 787 1 [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2), (75931, 2)],
  .up 787 1,
  .rs 787 1 4,
  .par2 13 787,
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (787, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2), (75931, 4)],
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2)],
  .force 284860058207025151 1 [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 4)],
  .up 284860058207025151 1,
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 4)],
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 6)],
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2)],
  .force 41213191 1 [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 4)],
  .up 41213191 1,
  .rs 41213191 1 5,
  .par2 13 41213191,
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 4), (41213191, 2)],
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 4)],
  .force 5522944621250897 1 [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 6)],
  .up 5522944621250897 1,
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 6)],
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 10)],
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2), (5233, 12)],
  .big [(3, 2), (7, 4), (13, 1), (331, 2), (2801, 2), (4933, 2)],
  .force 63601 1 [(3, 2), (7, 4), (13, 1), (331, 4), (2801, 2), (4933, 2)],
  .up 63601 1,
  .rs 63601 1 9,
  .par2 13 63601,
  .force 612067 1 [(3, 2), (7, 4), (13, 1), (331, 4), (2801, 2), (4933, 2), (63601, 2)],
  .up 612067 1,
  .rs 612067 1 6,
  .par2 13 612067,
  .force 26010319 1 [(3, 2), (7, 4), (13, 1), (331, 4), (2801, 2), (4933, 2), (63601, 2), (612067, 2)],
  .up 26010319 1,
  .big [(3, 2), (7, 4), (13, 1), (331, 4), (2801, 2), (4933, 2), (63601, 2), (612067, 2)],
  .big [(3, 2), (7, 4), (13, 1), (331, 4), (2801, 2), (4933, 2), (63601, 2), (612067, 4)],
  .big [(3, 2), (7, 4), (13, 1), (331, 4), (2801, 2), (4933, 2), (63601, 2)],
  .big [(3, 2), (7, 4), (13, 1), (331, 4), (2801, 2), (4933, 2), (63601, 4)],
  .big [(3, 2), (7, 4), (13, 1), (331, 4), (2801, 2), (4933, 2), (63601, 6)],
  .big [(3, 2), (7, 4), (13, 1), (331, 4), (2801, 2), (4933, 2)],
  .force 604842197 1 [(3, 2), (7, 4), (13, 1), (331, 6), (2801, 2), (4933, 2)],
  .up 604842197 1,
  .rs 604842197 1 5,
  .par2 13 604842197,
  .big [(3, 2), (7, 4), (13, 1), (331, 6), (2801, 2), (4933, 2), (604842197, 2)],
  .big [(3, 2), (7, 4), (13, 1), (331, 6), (2801, 2), (4933, 2)],
  .force 703207451121161180833 1 [(3, 2), (7, 4), (13, 1), (331, 10), (2801, 2), (4933, 2)],
  .up 703207451121161180833 1,
  .big [(3, 2), (7, 4), (13, 1), (331, 10), (2801, 2), (4933, 2)],
  .big [(3, 2), (7, 4), (13, 1), (331, 12), (2801, 2), (4933, 2)],
  .big [(3, 2), (7, 4), (13, 1), (331, 16), (2801, 2), (4933, 2)],
  .big [(3, 2), (7, 4), (13, 1), (331, 18), (2801, 2), (4933, 2)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 2)],
  .force 230329301 1 [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 4)],
  .up 230329301 1,
  .rs 230329301 1 7,
  .par2 13 230329301,
  .force 237899493854161 1 [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 4), (230329301, 2)],
  .up 237899493854161 1,
  .big [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 4), (230329301, 2)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 4), (230329301, 4)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 4)],
  .force 12400411646533 1 [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 6)],
  .up 12400411646533 1,
  .rs 12400411646533 1 4,
  .par2 13 12400411646533,
  .big [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 6), (12400411646533, 2)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 6)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 10)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 12)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 2), (4933, 16)]]

/-- Instructions, part 1. -/
def tree3_1 : List Ins := [
  .big [(3, 2), (7, 4), (13, 1), (2801, 2)],
  .force 6294091 1 [(3, 2), (7, 4), (13, 1), (2801, 4)],
  .up 6294091 1,
  .rs 6294091 1 9,
  .par2 13 6294091,
  .force 13205195936791 1 [(3, 2), (7, 4), (13, 1), (2801, 4), (6294091, 2)],
  .up 13205195936791 1,
  .rs 13205195936791 1 4,
  .par2 13 13205195936791,
  .big [(3, 2), (7, 4), (13, 1), (2801, 4), (6294091, 2), (13205195936791, 2)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 4), (6294091, 2)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 4), (6294091, 4)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 4), (6294091, 6)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 4)],
  .force 2884629032993 1 [(3, 2), (7, 4), (13, 1), (2801, 6)],
  .up 2884629032993 1,
  .rs 2884629032993 1 5,
  .par2 13 2884629032993,
  .big [(3, 2), (7, 4), (13, 1), (2801, 6), (2884629032993, 2)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 6)],
  .force 2033125998091 1 [(3, 2), (7, 4), (13, 1), (2801, 10)],
  .up 2033125998091 1,
  .big [(3, 2), (7, 4), (13, 1), (2801, 10)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 12)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 16)],
  .big [(3, 2), (7, 4), (13, 1), (2801, 18)],
  .big [(3, 2), (7, 4), (13, 1)],
  .force 4733 1 [(3, 2), (7, 6), (13, 1)],
  .up 4733 1,
  .rs 4733 1 21,
  .par2 13 4733,
  .force 22406023 1 [(3, 2), (7, 6), (13, 1), (4733, 2)],
  .up 22406023 1,
  .rs 22406023 1 10,
  .par2 13 22406023,
  .force 606538249 1 [(3, 2), (7, 6), (13, 1), (4733, 2), (22406023, 2)],
  .up 606538249 1,
  .rs 606538249 1 6,
  .par2 13 606538249,
  .force 2635909 1 [(3, 2), (7, 6), (13, 1), (4733, 2), (22406023, 2), (606538249, 2)],
  .up 2635909 1,
  .rs 2635909 1 4,
  .par2 13 2635909,
  .big [(3, 2), (7, 6), (13, 1), (4733, 2), (2635909, 2), (22406023, 2), (606538249, 2)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 2), (22406023, 2), (606538249, 2)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 2), (22406023, 2), (606538249, 4)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 2), (22406023, 2)],
  .force 829007553280001 1 [(3, 2), (7, 6), (13, 1), (4733, 2), (22406023, 4)],
  .up 829007553280001 1,
  .big [(3, 2), (7, 6), (13, 1), (4733, 2), (22406023, 4)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 2), (22406023, 6)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 2)],
  .force 11018941331 1 [(3, 2), (7, 6), (13, 1), (4733, 4)],
  .up 11018941331 1,
  .rs 11018941331 1 7,
  .par2 13 11018941331,
  .force 8580759007 1 [(3, 2), (7, 6), (13, 1), (4733, 4), (11018941331, 2)],
  .up 8580759007 1,
  .rs 8580759007 1 4,
  .par2 13 8580759007,
  .big [(3, 2), (7, 6), (13, 1), (4733, 4), (8580759007, 2), (11018941331, 2)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 4), (11018941331, 2)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 4), (11018941331, 4)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 4)],
  .force 329422297 1 [(3, 2), (7, 6), (13, 1), (4733, 6)],
  .up 329422297 1,
  .rs 329422297 1 6,
  .par2 13 329422297,
  .force 69655517 1 [(3, 2), (7, 6), (13, 1), (4733, 6), (329422297, 2)],
  .up 69655517 1,
  .big [(3, 2), (7, 6), (13, 1), (4733, 6), (329422297, 2)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 6), (329422297, 4)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 6)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 10)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 12)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 16)],
  .big [(3, 2), (7, 6), (13, 1), (4733, 18)],
  .big [(3, 2), (7, 6), (13, 1)],
  .force 293459 1 [(3, 2), (7, 10), (13, 1)],
  .up 293459 1,
  .rs 293459 1 13,
  .par2 13 293459,
  .force 310897033 1 [(3, 2), (7, 10), (13, 1), (293459, 2)],
  .up 310897033 1,
  .rs 310897033 1 8,
  .par2 13 310897033,
  .force 139017523 1 [(3, 2), (7, 10), (13, 1), (293459, 2), (310897033, 2)],
  .up 139017523 1,
  .rs 139017523 1 5,
  .par2 13 139017523,
  .big [(3, 2), (7, 10), (13, 1), (293459, 2), (139017523, 2), (310897033, 2)],
  .big [(3, 2), (7, 10), (13, 1), (293459, 2), (310897033, 2)],
  .big [(3, 2), (7, 10), (13, 1), (293459, 2), (310897033, 4)],
  .big [(3, 2), (7, 10), (13, 1), (293459, 2), (310897033, 6)],
  .big [(3, 2), (7, 10), (13, 1), (293459, 2)],
  .force 9875322243666178231 1 [(3, 2), (7, 10), (13, 1), (293459, 4)],
  .up 9875322243666178231 1,
  .rs 9875322243666178231 1 4,
  .par2 13 9875322243666178231,
  .big [(3, 2), (7, 10), (13, 1), (293459, 4), (9875322243666178231, 2)],
  .big [(3, 2), (7, 10), (13, 1), (293459, 4)],
  .big [(3, 2), (7, 10), (13, 1), (293459, 6)],
  .big [(3, 2), (7, 10), (13, 1), (293459, 10)],
  .big [(3, 2), (7, 10), (13, 1)],
  .force 16148168401 1 [(3, 2), (7, 12), (13, 1)],
  .up 16148168401 1,
  .rs 16148168401 1 8,
  .par2 13 16148168401,
  .force 200741603328100897 1 [(3, 2), (7, 12), (13, 1), (16148168401, 2)],
  .up 200741603328100897 1,
  .rs 200741603328100897 1 4,
  .par2 13 200741603328100897,
  .big [(3, 2), (7, 12), (13, 1), (16148168401, 2), (200741603328100897, 2)],
  .big [(3, 2), (7, 12), (13, 1), (16148168401, 2)],
  .big [(3, 2), (7, 12), (13, 1), (16148168401, 4)],
  .big [(3, 2), (7, 12), (13, 1), (16148168401, 6)],
  .big [(3, 2), (7, 12), (13, 1)],
  .force 2767631689 1 [(3, 2), (7, 16), (13, 1)],
  .up 2767631689 1,
  .rs 2767631689 1 8,
  .par2 13 2767631689,
  .force 34199239 1 [(3, 2), (7, 16), (13, 1), (2767631689, 2)],
  .up 34199239 1,
  .rs 34199239 1 6,
  .par2 13 34199239,
  .force 14009 1 [(3, 2), (7, 16), (13, 1), (34199239, 2), (2767631689, 2)],
  .up 14009 1,
  .big [(3, 2), (7, 16), (13, 1), (34199239, 2), (2767631689, 2)],
  .big [(3, 2), (7, 16), (13, 1), (34199239, 4), (2767631689, 2)],
  .big [(3, 2), (7, 16), (13, 1), (2767631689, 2)],
  .big [(3, 2), (7, 16), (13, 1), (2767631689, 4)],
  .big [(3, 2), (7, 16), (13, 1), (2767631689, 6)],
  .big [(3, 2), (7, 16), (13, 1)],
  .force 4534166740403 1 [(3, 2), (7, 18), (13, 1)],
  .up 4534166740403 1,
  .rs 4534166740403 1 6,
  .par2 13 4534166740403,
  .force 4721697244987 1 [(3, 2), (7, 18), (13, 1), (4534166740403, 2)],
  .up 4721697244987 1,
  .big [(3, 2), (7, 18), (13, 1), (4534166740403, 2)],
  .big [(3, 2), (7, 18), (13, 1), (4534166740403, 4)],
  .big [(3, 2), (7, 18), (13, 1)],
  .force 31479823396757 1 [(3, 2), (7, 22), (13, 1)],
  .up 31479823396757 1,
  .rs 31479823396757 1 5,
  .par2 13 31479823396757,
  .big [(3, 2), (7, 22), (13, 1), (31479823396757, 2)],
  .big [(3, 2), (7, 22), (13, 1)],
  .force 71316922984999 1 [(3, 2), (7, 28), (13, 1)],
  .up 71316922984999 1,
  .rs 71316922984999 1 5,
  .par2 13 71316922984999,
  .big [(3, 2), (7, 28), (13, 1), (71316922984999, 2)],
  .big [(3, 2), (7, 28), (13, 1)],
  .force 3999088279399464409 1 [(3, 2), (7, 30), (13, 1)],
  .up 3999088279399464409 1,
  .rs 3999088279399464409 1 4,
  .par2 13 3999088279399464409,
  .big [(3, 2), (7, 30), (13, 1), (3999088279399464409, 2)],
  .big [(3, 2), (7, 30), (13, 1)],
  .force 4805345109492315767981401 1 [(3, 2), (7, 36), (13, 1)],
  .up 4805345109492315767981401 1,
  .big [(3, 2), (7, 36), (13, 1)],
  .force 4362139336229068656094783 1 [(3, 2), (7, 40), (13, 1)],
  .up 4362139336229068656094783 1,
  .big [(3, 2), (7, 40), (13, 1)],
  .force 2192537062271178641 1 [(3, 2), (7, 42), (13, 1)],
  .up 2192537062271178641 1,
  .big [(3, 2), (7, 42), (13, 1)],
  .big [(3, 2), (7, 46), (13, 1)],
  .big [(3, 2), (7, 52), (13, 1)],
  .big [(3, 2), (7, 58), (13, 1)],
  .big [(3, 2), (7, 60), (13, 1)],
  .big [(3, 2), (7, 66), (13, 1)],
  .big [(3, 2), (7, 70), (13, 1)],
  .big [(3, 2), (7, 72), (13, 1)],
  .big [(3, 2), (7, 78), (13, 1)],
  .big [(3, 2), (7, 82), (13, 1)],
  .big [(3, 2), (7, 88), (13, 1)],
  .big [(3, 2), (13, 1)],
  .force 61 1 [(3, 2), (13, 2)],
  .rs 61 1 44,
  .force 31 1 [(3, 2), (13, 2), (61, 1)],
  .up 31 1,
  .rs 31 1 51,
  .par2 61 31,
  .force 331 1 [(3, 2), (13, 2), (31, 2), (61, 1)],
  .up 331 1,
  .rs 331 1 30,
  .par2 61 331,
  .force 5233 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2)],
  .up 5233 1,
  .rs 5233 1 19,
  .par2 61 5233,
  .force 42073 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2)],
  .up 42073 1,
  .rs 42073 1 14,
  .par2 61 42073,
  .force 75931 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 2)],
  .up 75931 1,
  .rs 75931 1 10,
  .par2 61 75931,
  .force 787 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 2), (75931, 2)],
  .up 787 1,
  .rs 787 1 10,
  .par2 61 787,
  .force 409 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .up 409 1,
  .rs 409 1 8,
  .par2 61 409,
  .force 55897 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (409, 2), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .up 55897 1,
  .rs 55897 1 4,
  .par2 61 55897,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (409, 2), (787, 2), (5233, 2), (42073, 2), (55897, 2), (75931, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (409, 2), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (409, 4), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (409, 6), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .force 672901 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (787, 4), (5233, 2), (42073, 2), (75931, 2)],
  .up 672901 1,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (787, 4), (5233, 2), (42073, 2), (75931, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (787, 6), (5233, 2), (42073, 2), (75931, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 2), (75931, 2)],
  .force 687262545131 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 2), (75931, 4)],
  .up 687262545131 1,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 2), (75931, 4)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 2), (75931, 6)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 2)],
  .force 284860058207025151 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 4)],
  .up 284860058207025151 1,
  .rs 284860058207025151 1 4,
  .par2 61 284860058207025151,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 4), (284860058207025151, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 4)],
  .force 248366755289421259 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 6)],
  .up 248366755289421259 1,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 6)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 10)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2), (42073, 12)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 2)],
  .force 41213191 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 4)],
  .up 41213191 1,
  .rs 41213191 1 7,
  .par2 61 41213191,
  .force 183067 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 4), (41213191, 2)],
  .up 183067 1,
  .rs 183067 1 5,
  .par2 61 183067,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 4), (183067, 2), (41213191, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 4), (41213191, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 4), (41213191, 4)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 4)],
  .force 5522944621250897 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 6)],
  .up 5522944621250897 1,
  .rs 5522944621250897 1 4,
  .par2 61 5522944621250897,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 6), (5522944621250897, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 6)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 10)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 12)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2), (5233, 16)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 2)],
  .force 63601 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4)],
  .up 63601 1,
  .rs 63601 1 13,
  .par2 61 63601,
  .force 612067 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 2)],
  .up 612067 1,
  .rs 612067 1 9,
  .par2 61 612067,
  .force 26010319 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 2), (612067, 2)],
  .up 26010319 1,
  .rs 26010319 1 5,
  .par2 61 26010319,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 2), (612067, 2), (26010319, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 2), (612067, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 2), (612067, 4)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 2), (612067, 6)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 2)],
  .force 50408381 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 4)],
  .up 50408381 1,
  .rs 50408381 1 5,
  .par2 61 50408381,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 4), (50408381, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 4)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 6)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4), (63601, 10)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 4)],
  .force 604842197 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 6)],
  .up 604842197 1,
  .rs 604842197 1 7,
  .par2 61 604842197,
  .force 365834083876629007 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 6), (604842197, 2)],
  .up 365834083876629007 1,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 6), (604842197, 2)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 6), (604842197, 4)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 6)],
  .force 703207451121161180833 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 10)],
  .up 703207451121161180833 1,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 10)],
  .force 80037421623539251 1 [(3, 2), (13, 2), (31, 2), (61, 1), (331, 12)],
  .up 80037421623539251 1,
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 12)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 16)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 18)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 22)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1), (331, 28)],
  .big [(3, 2), (13, 2), (31, 2), (61, 1)],
  .force 17351 1 [(3, 2), (13, 2), (31, 4), (61, 1)],
  .up 17351 1,
  .rs 17351 1 17,
  .par2 61 17351,
  .force 21787 1 [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2)],
  .up 21787 1,
  .rs 21787 1 14,
  .par2 61 21787,
  .force 5104249 1 [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 2)],
  .up 5104249 1,
  .rs 5104249 1 8,
  .par2 61 5104249,
  .force 656737 1 [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 2), (5104249, 2)],
  .up 656737 1,
  .rs 656737 1 6,
  .par2 61 656737,
  .force 216781 1 [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 2), (656737, 2), (5104249, 2)],
  .up 216781 1,
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 2), (656737, 2), (5104249, 2)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 2), (656737, 4), (5104249, 2)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 2), (5104249, 2)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 2), (5104249, 4)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 2), (5104249, 6)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 2)],
  .force 166484861 1 [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 4)],
  .up 166484861 1,
  .rs 166484861 1 5,
  .par2 61 166484861,
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 4), (166484861, 2)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 4)],
  .force 1622337552083173402331 1 [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 6)],
  .up 1622337552083173402331 1,
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 6)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 10)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2), (21787, 12)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 2)],
  .force 1648012040336791 1 [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 4)],
  .up 1648012040336791 1,
  .rs 1648012040336791 1 5,
  .par2 61 1648012040336791,
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 4), (1648012040336791, 2)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 4)],
  .force 68917740951781 1 [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 6)],
  .up 68917740951781 1,
  .rs 68917740951781 1 4,
  .par2 61 68917740951781,
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 6), (68917740951781, 2)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 6)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 10)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1), (17351, 12)],
  .big [(3, 2), (13, 2), (31, 4), (61, 1)],
  .force 917087137 1 [(3, 2), (13, 2), (31, 6), (61, 1)],
  .up 917087137 1,
  .rs 917087137 1 9,
  .par2 61 917087137,
  .force 38533987 1 [(3, 2), (13, 2), (31, 6), (61, 1), (917087137, 2)],
  .up 38533987 1,
  .rs 38533987 1 6,
  .par2 61 38533987,
  .force 15441801523 1 [(3, 2), (13, 2), (31, 6), (61, 1), (38533987, 2), (917087137, 2)],
  .up 15441801523 1,
  .big [(3, 2), (13, 2), (31, 6), (61, 1), (38533987, 2), (917087137, 2)],
  .big [(3, 2), (13, 2), (31, 6), (61, 1), (38533987, 4), (917087137, 2)],
  .big [(3, 2), (13, 2), (31, 6), (61, 1), (917087137, 2)],
  .big [(3, 2), (13, 2), (31, 6), (61, 1), (917087137, 4)],
  .big [(3, 2), (13, 2), (31, 6), (61, 1), (917087137, 6)],
  .big [(3, 2), (13, 2), (31, 6), (61, 1)],
  .force 150332843 1 [(3, 2), (13, 2), (31, 10), (61, 1)],
  .up 150332843 1,
  .rs 150332843 1 8,
  .par2 61 150332843,
  .force 127473943 1 [(3, 2), (13, 2), (31, 10), (61, 1), (150332843, 2)],
  .up 127473943 1,
  .rs 127473943 1 5,
  .par2 61 127473943,
  .big [(3, 2), (13, 2), (31, 10), (61, 1), (127473943, 2), (150332843, 2)],
  .big [(3, 2), (13, 2), (31, 10), (61, 1), (150332843, 2)],
  .big [(3, 2), (13, 2), (31, 10), (61, 1), (150332843, 4)],
  .big [(3, 2), (13, 2), (31, 10), (61, 1), (150332843, 6)],
  .big [(3, 2), (13, 2), (31, 10), (61, 1)],
  .force 7908811 1 [(3, 2), (13, 2), (31, 12), (61, 1)],
  .up 7908811 1,
  .rs 7908811 1 8,
  .par2 61 7908811,
  .force 2426789 1 [(3, 2), (13, 2), (31, 12), (61, 1), (7908811, 2)],
  .up 2426789 1,
  .rs 2426789 1 5,
  .par2 61 2426789,
  .big [(3, 2), (13, 2), (31, 12), (61, 1), (2426789, 2), (7908811, 2)],
  .big [(3, 2), (13, 2), (31, 12), (61, 1), (7908811, 2)],
  .big [(3, 2), (13, 2), (31, 12), (61, 1), (7908811, 4)]]

/-- Instructions, part 2. -/
def tree3_2 : List Ins := [
  .big [(3, 2), (13, 2), (31, 12), (61, 1), (7908811, 6)],
  .big [(3, 2), (13, 2), (31, 12), (61, 1)],
  .force 751670559138758105956097 1 [(3, 2), (13, 2), (31, 16), (61, 1)],
  .up 751670559138758105956097 1,
  .rs 751670559138758105956097 1 4,
  .par2 61 751670559138758105956097,
  .big [(3, 2), (13, 2), (31, 16), (61, 1), (751670559138758105956097, 2)],
  .big [(3, 2), (13, 2), (31, 16), (61, 1)],
  .force 88770666332610762169 1 [(3, 2), (13, 2), (31, 18), (61, 1)],
  .up 88770666332610762169 1,
  .rs 88770666332610762169 1 4,
  .par2 61 88770666332610762169,
  .big [(3, 2), (13, 2), (31, 18), (61, 1), (88770666332610762169, 2)],
  .big [(3, 2), (13, 2), (31, 18), (61, 1)],
  .force 7176374761323733117 1 [(3, 2), (13, 2), (31, 22), (61, 1)],
  .up 7176374761323733117 1,
  .big [(3, 2), (13, 2), (31, 22), (61, 1)],
  .big [(3, 2), (13, 2), (31, 28), (61, 1)],
  .big [(3, 2), (13, 2), (31, 30), (61, 1)],
  .big [(3, 2), (13, 2), (31, 36), (61, 1)],
  .big [(3, 2), (13, 2), (31, 40), (61, 1)],
  .big [(3, 2), (13, 2), (31, 42), (61, 1)],
  .big [(3, 2), (13, 2), (31, 46), (61, 1)],
  .big [(3, 2), (13, 2), (61, 1)],
  .force 97 1 [(3, 2), (13, 2), (61, 2)],
  .rs 97 1 38,
  .force 7 2 [(3, 2), (13, 2), (61, 2), (97, 1)],
  .rs 7 1 85,
  .par2 97 7,
  .force 19 1 [(3, 2), (7, 2), (13, 2), (61, 2), (97, 1)],
  .up 19 1,
  .rs 19 1 55,
  .par2 97 19,
  .force 127 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1)],
  .up 127 1,
  .rs 127 1 32,
  .par2 97 127,
  .force 5419 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2)],
  .up 5419 1,
  .rs 5419 1 18,
  .par2 97 5419,
  .force 1009 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (5419, 2)],
  .up 1009 1,
  .rs 1009 1 18,
  .par2 97 1009,
  .force 9181 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (5419, 2)],
  .up 9181 1,
  .rs 9181 1 12,
  .par2 97 9181,
  .force 1423 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (5419, 2), (9181, 2)],
  .up 1423 1,
  .rs 1423 1 10,
  .par2 97 1423,
  .force 96493 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2)],
  .up 96493 1,
  .rs 96493 1 6,
  .par2 97 96493,
  .force 163350799 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 2)],
  .up 163350799 1,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 4)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2)],
  .force 40497241 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2)],
  .up 40497241 1,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (1423, 6), (5419, 2), (9181, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (5419, 2), (9181, 2)],
  .force 125642407351 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (5419, 2), (9181, 4)],
  .up 125642407351 1,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (5419, 2), (9181, 4)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (5419, 2), (9181, 6)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (5419, 2), (9181, 10)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 2), (5419, 2)],
  .force 1037517185381 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 4), (5419, 2)],
  .up 1037517185381 1,
  .rs 1037517185381 1 5,
  .par2 97 1037517185381,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 4), (5419, 2), (1037517185381, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 4), (5419, 2)],
  .force 1024823381 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 6), (5419, 2)],
  .up 1024823381 1,
  .rs 1024823381 1 4,
  .par2 97 1024823381,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 6), (5419, 2), (1024823381, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 6), (5419, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 10), (5419, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 12), (5419, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (1009, 16), (5419, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (5419, 2)],
  .force 836561914831 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (5419, 4)],
  .up 836561914831 1,
  .rs 836561914831 1 5,
  .par2 97 836561914831,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (5419, 4), (836561914831, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (5419, 4)],
  .force 829621381 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (5419, 6)],
  .up 829621381 1,
  .rs 829621381 1 4,
  .par2 97 829621381,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (5419, 6), (829621381, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (5419, 6)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (5419, 10)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (5419, 12)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2), (5419, 16)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 2)],
  .force 262209281 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 4)],
  .up 262209281 1,
  .rs 262209281 1 8,
  .par2 97 262209281,
  .force 4296301150081 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 4), (262209281, 2)],
  .up 4296301150081 1,
  .rs 4296301150081 1 4,
  .par2 97 4296301150081,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 4), (262209281, 2), (4296301150081, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 4), (262209281, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 4), (262209281, 4)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 4), (262209281, 6)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 4)],
  .force 162709 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 6)],
  .up 162709 1,
  .rs 162709 1 10,
  .par2 97 162709,
  .force 8824793797 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 6), (162709, 2)],
  .up 8824793797 1,
  .rs 8824793797 1 5,
  .par2 97 8824793797,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 6), (162709, 2), (8824793797, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 6), (162709, 2)],
  .force 700888562389531127981 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 6), (162709, 4)],
  .up 700888562389531127981 1,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 6), (162709, 4)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 6), (162709, 6)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 6)],
  .force 47834644354838156839 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 10)],
  .up 47834644354838156839 1,
  .rs 47834644354838156839 1 4,
  .par2 97 47834644354838156839,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 10), (47834644354838156839, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 10)],
  .force 1437263292796553 1 [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 12)],
  .up 1437263292796553 1,
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 12)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 16)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 18)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 22)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 28)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1), (127, 30)],
  .big [(3, 2), (7, 2), (13, 2), (19, 2), (61, 2), (97, 1)],
  .force 911 1 [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1)],
  .up 911 1,
  .rs 911 1 22,
  .par2 97 911,
  .force 830833 1 [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2)],
  .up 830833 1,
  .rs 830833 1 11,
  .par2 97 830833,
  .force 861001 1 [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2), (830833, 2)],
  .up 861001 1,
  .rs 861001 1 8,
  .par2 97 861001,
  .force 217081 1 [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2), (830833, 2), (861001, 2)],
  .up 217081 1,
  .rs 217081 1 5,
  .par2 97 217081,
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2), (217081, 2), (830833, 2), (861001, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2), (830833, 2), (861001, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2), (830833, 2), (861001, 4)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2), (830833, 2), (861001, 6)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2), (830833, 2)],
  .force 2249049650927341 1 [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2), (830833, 4)],
  .up 2249049650927341 1,
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2), (830833, 4)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2), (830833, 6)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 2)],
  .force 17884211 1 [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 4)],
  .up 17884211 1,
  .rs 17884211 1 8,
  .par2 97 17884211,
  .force 45692145853819 1 [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 4), (17884211, 2)],
  .up 45692145853819 1,
  .rs 45692145853819 1 4,
  .par2 97 45692145853819,
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 4), (17884211, 2), (45692145853819, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 4), (17884211, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 4), (17884211, 4)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 4), (17884211, 6)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 4)],
  .force 81750272028928231 1 [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 6)],
  .up 81750272028928231 1,
  .rs 81750272028928231 1 4,
  .par2 97 81750272028928231,
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 6), (81750272028928231, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 6)],
  .force 247174661801 1 [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 10)],
  .up 247174661801 1,
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 10)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 12)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 16)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1), (911, 18)],
  .big [(3, 2), (7, 2), (13, 2), (19, 4), (61, 2), (97, 1)],
  .force 70841 1 [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1)],
  .up 70841 1,
  .rs 70841 1 13,
  .par2 97 70841,
  .force 128341 1 [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 2)],
  .up 128341 1,
  .rs 128341 1 10,
  .par2 97 128341,
  .force 5490513541 1 [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 2), (128341, 2)],
  .up 5490513541 1,
  .rs 5490513541 1 5,
  .par2 97 5490513541,
  .big [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 2), (128341, 2), (5490513541, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 2), (128341, 2)],
  .force 12833941 1 [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 2), (128341, 4)],
  .up 12833941 1,
  .big [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 2), (128341, 4)],
  .big [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 2), (128341, 6)],
  .big [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 2)],
  .force 1163018639068051 1 [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 4)],
  .up 1163018639068051 1,
  .rs 1163018639068051 1 4,
  .par2 97 1163018639068051,
  .big [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 4), (1163018639068051, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 4)],
  .big [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 6)],
  .big [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1), (70841, 10)],
  .big [(3, 2), (7, 2), (13, 2), (19, 6), (61, 2), (97, 1)],
  .force 62060021 1 [(3, 2), (7, 2), (13, 2), (19, 10), (61, 2), (97, 1)],
  .up 62060021 1,
  .rs 62060021 1 8,
  .par2 97 62060021,
  .force 17748600316039 1 [(3, 2), (7, 2), (13, 2), (19, 10), (61, 2), (97, 1), (62060021, 2)],
  .up 17748600316039 1,
  .rs 17748600316039 1 4,
  .par2 97 17748600316039,
  .big [(3, 2), (7, 2), (13, 2), (19, 10), (61, 2), (97, 1), (62060021, 2), (17748600316039, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 10), (61, 2), (97, 1), (62060021, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 10), (61, 2), (97, 1), (62060021, 4)],
  .big [(3, 2), (7, 2), (13, 2), (19, 10), (61, 2), (97, 1), (62060021, 6)],
  .big [(3, 2), (7, 2), (13, 2), (19, 10), (61, 2), (97, 1)],
  .force 133338869 1 [(3, 2), (7, 2), (13, 2), (19, 12), (61, 2), (97, 1)],
  .up 133338869 1,
  .rs 133338869 1 7,
  .par2 97 133338869,
  .force 316950847 1 [(3, 2), (7, 2), (13, 2), (19, 12), (61, 2), (97, 1), (133338869, 2)],
  .up 316950847 1,
  .rs 316950847 1 4,
  .par2 97 316950847,
  .big [(3, 2), (7, 2), (13, 2), (19, 12), (61, 2), (97, 1), (133338869, 2), (316950847, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 12), (61, 2), (97, 1), (133338869, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 12), (61, 2), (97, 1), (133338869, 4)],
  .big [(3, 2), (7, 2), (13, 2), (19, 12), (61, 2), (97, 1)],
  .force 99995282631947 1 [(3, 2), (7, 2), (13, 2), (19, 16), (61, 2), (97, 1)],
  .up 99995282631947 1,
  .rs 99995282631947 1 4,
  .par2 97 99995282631947,
  .big [(3, 2), (7, 2), (13, 2), (19, 16), (61, 2), (97, 1), (99995282631947, 2)],
  .big [(3, 2), (7, 2), (13, 2), (19, 16), (61, 2), (97, 1)],
  .force 109912203092239643840221 1 [(3, 2), (7, 2), (13, 2), (19, 18), (61, 2), (97, 1)],
  .up 109912203092239643840221 1,
  .big [(3, 2), (7, 2), (13, 2), (19, 18), (61, 2), (97, 1)],
  .force 1335495402823 1 [(3, 2), (7, 2), (13, 2), (19, 22), (61, 2), (97, 1)],
  .up 1335495402823 1,
  .big [(3, 2), (7, 2), (13, 2), (19, 22), (61, 2), (97, 1)],
  .big [(3, 2), (7, 2), (13, 2), (19, 28), (61, 2), (97, 1)],
  .big [(3, 2), (7, 2), (13, 2), (19, 30), (61, 2), (97, 1)],
  .big [(3, 2), (7, 2), (13, 2), (19, 36), (61, 2), (97, 1)],
  .big [(3, 2), (7, 2), (13, 2), (19, 40), (61, 2), (97, 1)],
  .big [(3, 2), (7, 2), (13, 2), (19, 42), (61, 2), (97, 1)],
  .big [(3, 2), (7, 2), (13, 2), (19, 46), (61, 2), (97, 1)],
  .big [(3, 2), (7, 2), (13, 2), (19, 52), (61, 2), (97, 1)],
  .big [(3, 2), (7, 2), (13, 2), (61, 2), (97, 1)],
  .force 2801 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1)],
  .up 2801 1,
  .rs 2801 1 21,
  .par2 97 2801,
  .force 4933 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2)],
  .up 4933 1,
  .rs 4933 1 17,
  .par2 97 4933,
  .force 331 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2), (4933, 2)],
  .up 331 1,
  .rs 331 1 19,
  .par2 97 331,
  .force 5233 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2)],
  .up 5233 1,
  .rs 5233 1 12,
  .par2 97 5233,
  .force 42073 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2)],
  .up 42073 1,
  .rs 42073 1 8,
  .par2 97 42073,
  .force 75931 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2)],
  .up 75931 1,
  .rs 75931 1 5,
  .par2 97 75931,
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 4)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 6)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 2)],
  .force 41213191 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 4)],
  .up 41213191 1,
  .rs 41213191 1 4,
  .par2 97 41213191,
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 4), (41213191, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 4)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 6)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2), (5233, 10)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 2), (2801, 2), (4933, 2)],
  .force 63601 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 4), (2801, 2), (4933, 2)],
  .up 63601 1,
  .rs 63601 1 8,
  .par2 97 63601,
  .force 612067 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 4), (2801, 2), (4933, 2), (63601, 2)],
  .up 612067 1,
  .rs 612067 1 4,
  .par2 97 612067,
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 4), (2801, 2), (4933, 2), (63601, 2), (612067, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 4), (2801, 2), (4933, 2), (63601, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 4), (2801, 2), (4933, 2), (63601, 4)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 4), (2801, 2), (4933, 2), (63601, 6)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 4), (2801, 2), (4933, 2)],
  .force 604842197 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 6), (2801, 2), (4933, 2)],
  .up 604842197 1,
  .rs 604842197 1 4,
  .par2 97 604842197,
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 6), (2801, 2), (4933, 2), (604842197, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 6), (2801, 2), (4933, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 10), (2801, 2), (4933, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 12), (2801, 2), (4933, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (331, 16), (2801, 2), (4933, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2), (4933, 2)],
  .force 230329301 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2), (4933, 4)],
  .up 230329301 1,
  .rs 230329301 1 6,
  .par2 97 230329301,
  .force 237899493854161 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2), (4933, 4), (230329301, 2)],
  .up 237899493854161 1,
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2), (4933, 4), (230329301, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2), (4933, 4), (230329301, 4)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2), (4933, 4)],
  .force 12400411646533 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2), (4933, 6)],
  .up 12400411646533 1,
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2), (4933, 6)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2), (4933, 10)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2), (4933, 12)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 2)],
  .force 6294091 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 4)],
  .up 6294091 1,
  .rs 6294091 1 8,
  .par2 97 6294091,
  .force 13205195936791 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 4), (6294091, 2)],
  .up 13205195936791 1,
  .rs 13205195936791 1 4,
  .par2 97 13205195936791,
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 4), (6294091, 2), (13205195936791, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 4), (6294091, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 4), (6294091, 4)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 4), (6294091, 6)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 4)],
  .force 2884629032993 1 [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 6)],
  .up 2884629032993 1,
  .rs 2884629032993 1 5,
  .par2 97 2884629032993,
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 6), (2884629032993, 2)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 6)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 10)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 12)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 16)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1), (2801, 18)],
  .big [(3, 2), (7, 4), (13, 2), (61, 2), (97, 1)],
  .force 4733 1 [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1)],
  .up 4733 1,
  .rs 4733 1 19,
  .par2 97 4733,
  .force 22406023 1 [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 2)],
  .up 22406023 1,
  .rs 22406023 1 9,
  .par2 97 22406023,
  .force 606538249 1 [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 2), (22406023, 2)],
  .up 606538249 1,
  .rs 606538249 1 6,
  .par2 97 606538249,
  .force 2635909 1 [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 2), (22406023, 2), (606538249, 2)],
  .up 2635909 1,
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 2), (22406023, 2), (606538249, 2)],
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 2), (22406023, 2), (606538249, 4)],
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 2), (22406023, 2)],
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 2), (22406023, 4)],
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 2), (22406023, 6)],
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 2)],
  .force 11018941331 1 [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 4)],
  .up 11018941331 1,
  .rs 11018941331 1 6,
  .par2 97 11018941331,
  .force 8580759007 1 [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 4), (11018941331, 2)],
  .up 8580759007 1,
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 4), (11018941331, 2)]]

/-- Instructions, part 3. -/
def tree3_3 : List Ins := [
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 4), (11018941331, 4)],
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 4)],
  .force 329422297 1 [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 6)],
  .up 329422297 1,
  .rs 329422297 1 5,
  .par2 97 329422297,
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 6), (329422297, 2)],
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 6)],
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 10)],
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 12)],
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1), (4733, 16)],
  .big [(3, 2), (7, 6), (13, 2), (61, 2), (97, 1)],
  .force 293459 1 [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1)],
  .up 293459 1,
  .rs 293459 1 12,
  .par2 97 293459,
  .force 310897033 1 [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1), (293459, 2)],
  .up 310897033 1,
  .rs 310897033 1 7,
  .par2 97 310897033,
  .force 139017523 1 [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1), (293459, 2), (310897033, 2)],
  .up 139017523 1,
  .rs 139017523 1 4,
  .par2 97 139017523,
  .big [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1), (293459, 2), (139017523, 2), (310897033, 2)],
  .big [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1), (293459, 2), (310897033, 2)],
  .big [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1), (293459, 2), (310897033, 4)],
  .big [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1), (293459, 2)],
  .force 9875322243666178231 1 [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1), (293459, 4)],
  .up 9875322243666178231 1,
  .big [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1), (293459, 4)],
  .big [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1), (293459, 6)],
  .big [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1), (293459, 10)],
  .big [(3, 2), (7, 10), (13, 2), (61, 2), (97, 1)],
  .force 16148168401 1 [(3, 2), (7, 12), (13, 2), (61, 2), (97, 1)],
  .up 16148168401 1,
  .rs 16148168401 1 7,
  .par2 97 16148168401,
  .force 200741603328100897 1 [(3, 2), (7, 12), (13, 2), (61, 2), (97, 1), (16148168401, 2)],
  .up 200741603328100897 1,
  .rs 200741603328100897 1 4,
  .par2 97 200741603328100897,
  .big [(3, 2), (7, 12), (13, 2), (61, 2), (97, 1), (16148168401, 2), (200741603328100897, 2)],
  .big [(3, 2), (7, 12), (13, 2), (61, 2), (97, 1), (16148168401, 2)],
  .big [(3, 2), (7, 12), (13, 2), (61, 2), (97, 1), (16148168401, 4)],
  .big [(3, 2), (7, 12), (13, 2), (61, 2), (97, 1)],
  .force 2767631689 1 [(3, 2), (7, 16), (13, 2), (61, 2), (97, 1)],
  .up 2767631689 1,
  .rs 2767631689 1 7,
  .par2 97 2767631689,
  .force 34199239 1 [(3, 2), (7, 16), (13, 2), (61, 2), (97, 1), (2767631689, 2)],
  .up 34199239 1,
  .rs 34199239 1 5,
  .par2 97 34199239,
  .big [(3, 2), (7, 16), (13, 2), (61, 2), (97, 1), (34199239, 2), (2767631689, 2)],
  .big [(3, 2), (7, 16), (13, 2), (61, 2), (97, 1), (2767631689, 2)],
  .big [(3, 2), (7, 16), (13, 2), (61, 2), (97, 1), (2767631689, 4)],
  .big [(3, 2), (7, 16), (13, 2), (61, 2), (97, 1)],
  .force 4534166740403 1 [(3, 2), (7, 18), (13, 2), (61, 2), (97, 1)],
  .up 4534166740403 1,
  .rs 4534166740403 1 6,
  .par2 97 4534166740403,
  .force 4721697244987 1 [(3, 2), (7, 18), (13, 2), (61, 2), (97, 1), (4534166740403, 2)],
  .up 4721697244987 1,
  .big [(3, 2), (7, 18), (13, 2), (61, 2), (97, 1), (4534166740403, 2)],
  .big [(3, 2), (7, 18), (13, 2), (61, 2), (97, 1), (4534166740403, 4)],
  .big [(3, 2), (7, 18), (13, 2), (61, 2), (97, 1)],
  .force 31479823396757 1 [(3, 2), (7, 22), (13, 2), (61, 2), (97, 1)],
  .up 31479823396757 1,
  .rs 31479823396757 1 5,
  .par2 97 31479823396757,
  .big [(3, 2), (7, 22), (13, 2), (61, 2), (97, 1), (31479823396757, 2)],
  .big [(3, 2), (7, 22), (13, 2), (61, 2), (97, 1)],
  .force 71316922984999 1 [(3, 2), (7, 28), (13, 2), (61, 2), (97, 1)],
  .up 71316922984999 1,
  .rs 71316922984999 1 4,
  .par2 97 71316922984999,
  .big [(3, 2), (7, 28), (13, 2), (61, 2), (97, 1), (71316922984999, 2)],
  .big [(3, 2), (7, 28), (13, 2), (61, 2), (97, 1)],
  .force 3999088279399464409 1 [(3, 2), (7, 30), (13, 2), (61, 2), (97, 1)],
  .up 3999088279399464409 1,
  .rs 3999088279399464409 1 4,
  .par2 97 3999088279399464409,
  .big [(3, 2), (7, 30), (13, 2), (61, 2), (97, 1), (3999088279399464409, 2)],
  .big [(3, 2), (7, 30), (13, 2), (61, 2), (97, 1)],
  .force 4805345109492315767981401 1 [(3, 2), (7, 36), (13, 2), (61, 2), (97, 1)],
  .up 4805345109492315767981401 1,
  .big [(3, 2), (7, 36), (13, 2), (61, 2), (97, 1)],
  .force 4362139336229068656094783 1 [(3, 2), (7, 40), (13, 2), (61, 2), (97, 1)],
  .up 4362139336229068656094783 1,
  .big [(3, 2), (7, 40), (13, 2), (61, 2), (97, 1)],
  .big [(3, 2), (7, 42), (13, 2), (61, 2), (97, 1)],
  .big [(3, 2), (7, 46), (13, 2), (61, 2), (97, 1)],
  .big [(3, 2), (7, 52), (13, 2), (61, 2), (97, 1)],
  .big [(3, 2), (7, 58), (13, 2), (61, 2), (97, 1)],
  .big [(3, 2), (7, 60), (13, 2), (61, 2), (97, 1)],
  .big [(3, 2), (7, 66), (13, 2), (61, 2), (97, 1)],
  .big [(3, 2), (7, 70), (13, 2), (61, 2), (97, 1)],
  .big [(3, 2), (7, 72), (13, 2), (61, 2), (97, 1)],
  .big [(3, 2), (7, 78), (13, 2), (61, 2), (97, 1)],
  .big [(3, 2), (7, 82), (13, 2), (61, 2), (97, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 1)],
  .force 3169 1 [(3, 2), (13, 2), (61, 2), (97, 2)],
  .rs 3169 1 21,
  .force 317 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 1)],
  .up 317 1,
  .rs 317 1 27,
  .par2 3169 317,
  .force 14401 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1)],
  .up 14401 1,
  .rs 14401 1 15,
  .par2 3169 14401,
  .force 125017 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 2)],
  .up 125017 1,
  .rs 125017 1 11,
  .par2 3169 125017,
  .force 263827 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 2), (125017, 2)],
  .up 263827 1,
  .rs 263827 1 7,
  .par2 3169 263827,
  .force 3314521417 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 2), (125017, 2), (263827, 2)],
  .up 3314521417 1,
  .rs 3314521417 1 4,
  .par2 3169 3314521417,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 2), (125017, 2), (263827, 2), (3314521417, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 2), (125017, 2), (263827, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 2), (125017, 2), (263827, 4)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 2), (125017, 2)],
  .force 3440498852589004771 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 2), (125017, 4)],
  .up 3440498852589004771 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 2), (125017, 4)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 2), (125017, 6)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 2)],
  .force 2235195191 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 4)],
  .up 2235195191 1,
  .rs 2235195191 1 5,
  .par2 3169 2235195191,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 4), (2235195191, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 4)],
  .force 853390763 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 6)],
  .up 853390763 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 6)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 10)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1), (14401, 12)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 2), (3169, 1)],
  .force 2961121 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 4), (3169, 1)],
  .up 2961121 1,
  .rs 2961121 1 9,
  .par2 3169 2961121,
  .force 73782517 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 4), (3169, 1), (2961121, 2)],
  .up 73782517 1,
  .rs 73782517 1 6,
  .par2 3169 73782517,
  .force 2715931 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 4), (3169, 1), (2961121, 2), (73782517, 2)],
  .up 2715931 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 4), (3169, 1), (2961121, 2), (73782517, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 4), (3169, 1), (2961121, 2), (73782517, 4)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 4), (3169, 1), (2961121, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 4), (3169, 1), (2961121, 4)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 4), (3169, 1), (2961121, 6)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 4), (3169, 1)],
  .force 13739597803 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 6), (3169, 1)],
  .up 13739597803 1,
  .rs 13739597803 1 6,
  .par2 3169 13739597803,
  .force 4840424302613898067 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 6), (3169, 1), (13739597803, 2)],
  .up 4840424302613898067 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 6), (3169, 1), (13739597803, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 6), (3169, 1), (13739597803, 4)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 6), (3169, 1)],
  .force 705670360649 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 10), (3169, 1)],
  .up 705670360649 1,
  .rs 705670360649 1 4,
  .par2 3169 705670360649,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 10), (3169, 1), (705670360649, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 10), (3169, 1)],
  .force 506710914239632419773 1 [(3, 2), (13, 2), (61, 2), (97, 2), (317, 12), (3169, 1)],
  .up 506710914239632419773 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 12), (3169, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 16), (3169, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 18), (3169, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (317, 22), (3169, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 1)],
  .force 3348577 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2)],
  .rs 3348577 1 11,
  .force 1674289 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (3348577, 1)],
  .up 1674289 1,
  .rs 1674289 1 10,
  .par2 3348577 1674289,
  .force 934415109937 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (1674289, 2), (3348577, 1)],
  .up 934415109937 1,
  .rs 934415109937 1 5,
  .par2 3348577 934415109937,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (1674289, 2), (3348577, 1), (934415109937, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (1674289, 2), (3348577, 1)],
  .force 7858179685661558917710821 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (1674289, 4), (3348577, 1)],
  .up 7858179685661558917710821 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (1674289, 4), (3348577, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (1674289, 6), (3348577, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (3348577, 1)],
  .force 3737657091169 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (3348577, 2)],
  .rs 3737657091169 1 5,
  .force 843714919 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (3348577, 2), (3737657091169, 1)],
  .up 843714919 1,
  .rs 843714919 1 5,
  .par2 3737657091169 843714919,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (3348577, 2), (843714919, 2), (3737657091169, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (3348577, 2), (3737657091169, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (3348577, 2), (3737657091169, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (3348577, 2)],
  .force 1453121857811448551 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (3348577, 4)],
  .up 1453121857811448551 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (3348577, 4)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2), (3348577, 6)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 2)],
  .force 1653850268201 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 4)],
  .rs 1653850268201 1 6,
  .force 2039 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 4), (1653850268201, 1)],
  .up 2039 1,
  .rs 2039 1 11,
  .par2 1653850268201 2039,
  .force 577 1 [(3, 2), (13, 2), (61, 2), (97, 2), (2039, 2), (3169, 4), (1653850268201, 1)],
  .up 577 1,
  .rs 577 1 10,
  .par2 1653850268201 577,
  .force 5851 1 [(3, 2), (13, 2), (61, 2), (97, 2), (577, 2), (2039, 2), (3169, 4), (1653850268201, 1)],
  .up 5851 1,
  .rs 5851 1 6,
  .par2 1653850268201 5851,
  .force 11413351 1 [(3, 2), (13, 2), (61, 2), (97, 2), (577, 2), (2039, 2), (3169, 4), (5851, 2), (1653850268201, 1)],
  .up 11413351 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (577, 2), (2039, 2), (3169, 4), (5851, 2), (1653850268201, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (577, 2), (2039, 2), (3169, 4), (5851, 4), (1653850268201, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (577, 2), (2039, 2), (3169, 4), (1653850268201, 1)],
  .force 77053541 1 [(3, 2), (13, 2), (61, 2), (97, 2), (577, 4), (2039, 2), (3169, 4), (1653850268201, 1)],
  .up 77053541 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (577, 4), (2039, 2), (3169, 4), (1653850268201, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (577, 6), (2039, 2), (3169, 4), (1653850268201, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (2039, 2), (3169, 4), (1653850268201, 1)],
  .force 1572132928211 1 [(3, 2), (13, 2), (61, 2), (97, 2), (2039, 4), (3169, 4), (1653850268201, 1)],
  .up 1572132928211 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (2039, 4), (3169, 4), (1653850268201, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (2039, 6), (3169, 4), (1653850268201, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 4), (1653850268201, 1)],
  .force 22216443433 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 4), (1653850268201, 2)],
  .rs 22216443433 1 3,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 4), (22216443433, 1), (1653850268201, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 4), (1653850268201, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 4), (1653850268201, 4)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 4)],
  .force 3447899565839 1 [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 6)],
  .up 3447899565839 1,
  .rs 3447899565839 1 5,
  .parS 3447899565839,
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 6), (3447899565839, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 6)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 10)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 12)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 16)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2), (3169, 18)],
  .big [(3, 2), (13, 2), (61, 2), (97, 2)],
  .force 262321 1 [(3, 2), (13, 2), (61, 2), (97, 4)],
  .rs 262321 1 13,
  .force 4231 1 [(3, 2), (13, 2), (61, 2), (97, 4), (262321, 1)],
  .up 4231 1,
  .rs 4231 1 17,
  .par2 262321 4231,
  .force 9931 1 [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (262321, 1)],
  .up 9931 1,
  .rs 9931 1 13,
  .par2 262321 9931,
  .force 155821 1 [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (9931, 2), (262321, 1)],
  .up 155821 1,
  .rs 155821 1 8,
  .par2 262321 155821,
  .force 849349 1 [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (9931, 2), (155821, 2), (262321, 1)],
  .up 849349 1,
  .rs 849349 1 5,
  .par2 262321 849349,
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (9931, 2), (155821, 2), (262321, 1), (849349, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (9931, 2), (155821, 2), (262321, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (9931, 2), (155821, 4), (262321, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (9931, 2), (155821, 6), (262321, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (9931, 2), (262321, 1)],
  .force 16079046319741 1 [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (9931, 4), (262321, 1)],
  .up 16079046319741 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (9931, 4), (262321, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (9931, 6), (262321, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (9931, 10), (262321, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 2), (262321, 1)],
  .force 216211 1 [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 4), (262321, 1)],
  .up 216211 1,
  .rs 216211 1 7,
  .par2 262321 216211,
  .force 2226067273 1 [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 4), (216211, 2), (262321, 1)],
  .up 2226067273 1,
  .rs 2226067273 1 4,
  .par2 262321 2226067273,
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 4), (216211, 2), (262321, 1), (2226067273, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 4), (216211, 2), (262321, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 4), (216211, 4), (262321, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 4), (262321, 1)],
  .force 2569610653 1 [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 6), (262321, 1)],
  .up 2569610653 1,
  .rs 2569610653 1 4,
  .par2 262321 2569610653,
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 6), (262321, 1), (2569610653, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 6), (262321, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 10), (262321, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (4231, 12), (262321, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (262321, 1)],
  .force 5701 1 [(3, 2), (13, 2), (61, 2), (97, 4), (262321, 2)],
  .rs 5701 1 13,
  .force 2851 1 [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 1), (262321, 2)],
  .up 2851 1,
  .rs 2851 1 13,
  .par2 5701 2851,
  .force 5779 1 [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 2), (5701, 1), (262321, 2)],
  .up 5779 1,
  .rs 5779 1 9,
  .par2 5701 5779,
  .force 3889 1 [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 2), (5701, 1), (5779, 2), (262321, 2)],
  .up 3889 1,
  .rs 3889 1 7,
  .par2 5701 3889,
  .force 102913 1 [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 2), (3889, 2), (5701, 1), (5779, 2), (262321, 2)],
  .up 102913 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 2), (3889, 2), (5701, 1), (5779, 2), (262321, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 2), (3889, 4), (5701, 1), (5779, 2), (262321, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 2), (5701, 1), (5779, 2), (262321, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 2), (5701, 1), (5779, 4), (262321, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 2), (5701, 1), (5779, 6), (262321, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 2), (5701, 1), (262321, 2)],
  .force 23468881 1 [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 4), (5701, 1), (262321, 2)],
  .up 23468881 1,
  .rs 23468881 1 4,
  .par2 5701 23468881,
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 4), (5701, 1), (262321, 2), (23468881, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 4), (5701, 1), (262321, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 6), (5701, 1), (262321, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (2851, 10), (5701, 1), (262321, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 1), (262321, 2)],
  .force 10835701 1 [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 2), (262321, 2)],
  .rs 10835701 1 7,
  .force 5417851 1 [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 2), (262321, 2), (10835701, 1)],
  .up 5417851 1,
  .rs 5417851 1 6,
  .par2 10835701 5417851,
  .force 9784371625351 1 [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 2), (262321, 2), (5417851, 2), (10835701, 1)],
  .up 9784371625351 1,
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 2), (262321, 2), (5417851, 2), (10835701, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 2), (262321, 2), (5417851, 4), (10835701, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 2), (262321, 2), (10835701, 1)],
  .force 32292739 1 [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 2), (262321, 2), (10835701, 2)],
  .up 32292739 1,
  .rs 32292739 1 4,
  .parS 32292739,
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 2), (262321, 2), (10835701, 2), (32292739, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 2), (262321, 2), (10835701, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 2), (262321, 2), (10835701, 4)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 2), (262321, 2)],
  .force 20018081 1 [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 4), (262321, 2)],
  .rs 20018081 1 4,
  .force 3541 1 [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 4), (262321, 2), (20018081, 1)],
  .up 3541 1,
  .rs 3541 1 4,
  .par2 20018081 3541,
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (3541, 2), (5701, 4), (262321, 2), (20018081, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 4), (262321, 2), (20018081, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 4), (262321, 2), (20018081, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 4), (262321, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 6), (262321, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (5701, 10), (262321, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (262321, 2)],
  .force 1856918071 1 [(3, 2), (13, 2), (61, 2), (97, 4), (262321, 4)],
  .up 1856918071 1,
  .rs 1856918071 1 4,
  .parS 1856918071,
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (262321, 4), (1856918071, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (262321, 4)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (262321, 6)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4), (262321, 10)],
  .big [(3, 2), (13, 2), (61, 2), (97, 4)],
  .force 20241187 1 [(3, 2), (13, 2), (61, 2), (97, 6)],
  .up 20241187 1,
  .rs 20241187 1 9,
  .parS 20241187,
  .force 1890771811 1 [(3, 2), (13, 2), (61, 2), (97, 6), (20241187, 2)],
  .up 1890771811 1,
  .rs 1890771811 1 5,
  .parS 1890771811,
  .big [(3, 2), (13, 2), (61, 2), (97, 6), (20241187, 2), (1890771811, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 6), (20241187, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 6), (20241187, 4)],
  .big [(3, 2), (13, 2), (61, 2), (97, 6), (20241187, 6)],
  .big [(3, 2), (13, 2), (61, 2), (97, 6)],
  .force 837197335075000483 1 [(3, 2), (13, 2), (61, 2), (97, 10)],
  .up 837197335075000483 1,
  .rs 837197335075000483 1 4,
  .parS 837197335075000483]

/-- Instructions, part 4. -/
def tree3_4 : List Ins := [
  .big [(3, 2), (13, 2), (61, 2), (97, 10), (837197335075000483, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 10)],
  .force 8224356155341457 1 [(3, 2), (13, 2), (61, 2), (97, 12)],
  .rs 8224356155341457 1 4,
  .force 67496441 1 [(3, 2), (13, 2), (61, 2), (97, 12), (8224356155341457, 1)],
  .up 67496441 1,
  .rs 67496441 1 4,
  .par2 8224356155341457 67496441,
  .big [(3, 2), (13, 2), (61, 2), (97, 12), (67496441, 2), (8224356155341457, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 12), (8224356155341457, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 12), (8224356155341457, 2)],
  .big [(3, 2), (13, 2), (61, 2), (97, 12)],
  .force 62065212901958868055012327674641 1 [(3, 2), (13, 2), (61, 2), (97, 16)],
  .rs 62065212901958868055012327674641 1 3,
  .big [(3, 2), (13, 2), (61, 2), (97, 16), (62065212901958868055012327674641, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 16)],
  .force 97199158345481611029493 1 [(3, 2), (13, 2), (61, 2), (97, 18)],
  .rs 97199158345481611029493 1 3,
  .big [(3, 2), (13, 2), (61, 2), (97, 18), (97199158345481611029493, 1)],
  .big [(3, 2), (13, 2), (61, 2), (97, 18)],
  .big [(3, 2), (13, 2), (61, 2), (97, 22)],
  .big [(3, 2), (13, 2), (61, 2), (97, 28)],
  .big [(3, 2), (13, 2), (61, 2), (97, 30)],
  .big [(3, 2), (13, 2), (61, 2), (97, 36)],
  .big [(3, 2), (13, 2), (61, 2)],
  .force 21491 1 [(3, 2), (13, 2), (61, 4)],
  .up 21491 1,
  .rs 21491 1 17,
  .parS 21491,
  .force 1097113 1 [(3, 2), (13, 2), (61, 4), (21491, 2)],
  .rs 1097113 1 11,
  .force 548557 1 [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 1)],
  .up 548557 1,
  .rs 548557 1 10,
  .par2 1097113 548557,
  .force 25633813 1 [(3, 2), (13, 2), (61, 4), (21491, 2), (548557, 2), (1097113, 1)],
  .up 25633813 1,
  .rs 25633813 1 6,
  .par2 1097113 25633813,
  .force 103692397 1 [(3, 2), (13, 2), (61, 4), (21491, 2), (548557, 2), (1097113, 1), (25633813, 2)],
  .up 103692397 1,
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (548557, 2), (1097113, 1), (25633813, 2)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (548557, 2), (1097113, 1), (25633813, 4)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (548557, 2), (1097113, 1)],
  .force 121590431 1 [(3, 2), (13, 2), (61, 4), (21491, 2), (548557, 4), (1097113, 1)],
  .up 121590431 1,
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (548557, 4), (1097113, 1)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (548557, 6), (1097113, 1)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 1)],
  .force 1888171 1 [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 2)],
  .up 1888171 1,
  .rs 1888171 1 7,
  .parS 1888171,
  .force 91605427 1 [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 2), (1888171, 2)],
  .up 91605427 1,
  .rs 91605427 1 4,
  .parS 91605427,
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 2), (1888171, 2), (91605427, 2)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 2), (1888171, 2)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 2), (1888171, 4)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 2)],
  .force 234895531489741 1 [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 4)],
  .rs 234895531489741 1 3,
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 4), (234895531489741, 1)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 4)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 2), (1097113, 6)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 2)],
  .force 1011185971 1 [(3, 2), (13, 2), (61, 4), (21491, 4)],
  .up 1011185971 1,
  .rs 1011185971 1 6,
  .parS 1011185971,
  .force 5422626589 1 [(3, 2), (13, 2), (61, 4), (21491, 4), (1011185971, 2)],
  .rs 5422626589 1 3,
  .big [(3, 2), (13, 2), (61, 4), (21491, 4), (1011185971, 2), (5422626589, 1)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 4), (1011185971, 2)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 4), (1011185971, 4)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 4)],
  .force 124701767 1 [(3, 2), (13, 2), (61, 4), (21491, 6)],
  .up 124701767 1,
  .rs 124701767 1 4,
  .parS 124701767,
  .big [(3, 2), (13, 2), (61, 4), (21491, 6), (124701767, 2)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 6)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 10)],
  .big [(3, 2), (13, 2), (61, 4), (21491, 12)],
  .big [(3, 2), (13, 2), (61, 4)],
  .force 52379047267 1 [(3, 2), (13, 2), (61, 6)],
  .up 52379047267 1,
  .rs 52379047267 1 8,
  .parS 52379047267,
  .force 138161295607249 1 [(3, 2), (13, 2), (61, 6), (52379047267, 2)],
  .rs 138161295607249 1 4,
  .force 6619231 1 [(3, 2), (13, 2), (61, 6), (52379047267, 2), (138161295607249, 1)],
  .up 6619231 1,
  .rs 6619231 1 4,
  .par2 138161295607249 6619231,
  .big [(3, 2), (13, 2), (61, 6), (6619231, 2), (52379047267, 2), (138161295607249, 1)],
  .big [(3, 2), (13, 2), (61, 6), (52379047267, 2), (138161295607249, 1)],
  .big [(3, 2), (13, 2), (61, 6), (52379047267, 2), (138161295607249, 2)],
  .big [(3, 2), (13, 2), (61, 6), (52379047267, 2)],
  .big [(3, 2), (13, 2), (61, 6), (52379047267, 4)],
  .big [(3, 2), (13, 2), (61, 6), (52379047267, 6)],
  .big [(3, 2), (13, 2), (61, 6)],
  .force 4242586390571 1 [(3, 2), (13, 2), (61, 10)],
  .up 4242586390571 1,
  .rs 4242586390571 1 6,
  .parS 4242586390571,
  .force 963689941 1 [(3, 2), (13, 2), (61, 10), (4242586390571, 2)],
  .rs 963689941 1 3,
  .big [(3, 2), (13, 2), (61, 10), (963689941, 1), (4242586390571, 2)],
  .big [(3, 2), (13, 2), (61, 10), (4242586390571, 2)],
  .big [(3, 2), (13, 2), (61, 10), (4242586390571, 4)],
  .big [(3, 2), (13, 2), (61, 10)],
  .force 14421466756460791 1 [(3, 2), (13, 2), (61, 12)],
  .up 14421466756460791 1,
  .rs 14421466756460791 1 5,
  .parS 14421466756460791,
  .big [(3, 2), (13, 2), (61, 12), (14421466756460791, 2)],
  .big [(3, 2), (13, 2), (61, 12)],
  .force 362759437743508955104646759 1 [(3, 2), (13, 2), (61, 16)],
  .up 362759437743508955104646759 1,
  .big [(3, 2), (13, 2), (61, 16)],
  .force 607127818287731321660577427051 1 [(3, 2), (13, 2), (61, 18)],
  .up 607127818287731321660577427051 1,
  .big [(3, 2), (13, 2), (61, 18)],
  .big [(3, 2), (13, 2), (61, 22)],
  .big [(3, 2), (13, 2), (61, 28)],
  .big [(3, 2), (13, 2), (61, 30)],
  .big [(3, 2), (13, 2), (61, 36)],
  .big [(3, 2), (13, 2), (61, 40)],
  .big [(3, 2), (13, 2), (61, 42)],
  .big [(3, 2), (13, 2)],
  .force 30941 1 [(3, 2), (13, 4)],
  .rs 30941 1 18,
  .force 191 1 [(3, 2), (13, 4), (30941, 1)],
  .up 191 1,
  .rs 191 1 31,
  .par2 30941 191,
  .force 31 1 [(3, 2), (13, 4), (191, 2), (30941, 1)],
  .up 31 1,
  .rs 31 1 44,
  .par2 30941 31,
  .force 331 1 [(3, 2), (13, 4), (31, 2), (191, 2), (30941, 1)],
  .up 331 1,
  .rs 331 1 25,
  .par2 30941 331,
  .force 5233 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (30941, 1)],
  .up 5233 1,
  .rs 5233 1 16,
  .par2 30941 5233,
  .force 42073 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 2), (30941, 1)],
  .up 42073 1,
  .rs 42073 1 11,
  .par2 30941 42073,
  .force 75931 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 2), (30941, 1), (42073, 2)],
  .up 75931 1,
  .rs 75931 1 8,
  .par2 30941 75931,
  .force 787 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 2), (30941, 1), (42073, 2), (75931, 2)],
  .up 787 1,
  .rs 787 1 6,
  .par2 30941 787,
  .force 409 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (787, 2), (5233, 2), (30941, 1), (42073, 2), (75931, 2)],
  .up 409 1,
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (787, 2), (5233, 2), (30941, 1), (42073, 2), (75931, 2)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (787, 4), (5233, 2), (30941, 1), (42073, 2), (75931, 2)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 2), (30941, 1), (42073, 2), (75931, 2)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 2), (30941, 1), (42073, 2), (75931, 4)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 2), (30941, 1), (42073, 2), (75931, 6)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 2), (30941, 1), (42073, 2)],
  .force 284860058207025151 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 2), (30941, 1), (42073, 4)],
  .up 284860058207025151 1,
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 2), (30941, 1), (42073, 4)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 2), (30941, 1), (42073, 6)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 2), (30941, 1)],
  .force 41213191 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 4), (30941, 1)],
  .up 41213191 1,
  .rs 41213191 1 6,
  .par2 30941 41213191,
  .force 183067 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 4), (30941, 1), (41213191, 2)],
  .up 183067 1,
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 4), (30941, 1), (41213191, 2)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 4), (30941, 1), (41213191, 4)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 4), (30941, 1)],
  .force 5522944621250897 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 6), (30941, 1)],
  .up 5522944621250897 1,
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 6), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 10), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (5233, 12), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 2), (30941, 1)],
  .force 63601 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 4), (30941, 1)],
  .up 63601 1,
  .rs 63601 1 11,
  .par2 30941 63601,
  .force 612067 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 4), (30941, 1), (63601, 2)],
  .up 612067 1,
  .rs 612067 1 7,
  .par2 30941 612067,
  .force 26010319 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 4), (30941, 1), (63601, 2), (612067, 2)],
  .up 26010319 1,
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 4), (30941, 1), (63601, 2), (612067, 2)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 4), (30941, 1), (63601, 2), (612067, 4)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 4), (30941, 1), (63601, 2)],
  .force 50408381 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 4), (30941, 1), (63601, 4)],
  .up 50408381 1,
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 4), (30941, 1), (63601, 4)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 4), (30941, 1), (63601, 6)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 4), (30941, 1)],
  .force 604842197 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 6), (30941, 1)],
  .up 604842197 1,
  .rs 604842197 1 6,
  .par2 30941 604842197,
  .force 365834083876629007 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 6), (30941, 1), (604842197, 2)],
  .up 365834083876629007 1,
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 6), (30941, 1), (604842197, 2)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 6), (30941, 1), (604842197, 4)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 6), (30941, 1)],
  .force 703207451121161180833 1 [(3, 2), (13, 4), (31, 2), (191, 2), (331, 10), (30941, 1)],
  .up 703207451121161180833 1,
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 10), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 12), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 16), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 18), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (331, 22), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 2), (191, 2), (30941, 1)],
  .force 17351 1 [(3, 2), (13, 4), (31, 4), (191, 2), (30941, 1)],
  .up 17351 1,
  .rs 17351 1 14,
  .par2 30941 17351,
  .force 21787 1 [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (30941, 1)],
  .up 21787 1,
  .rs 21787 1 12,
  .par2 30941 21787,
  .force 5104249 1 [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (21787, 2), (30941, 1)],
  .up 5104249 1,
  .rs 5104249 1 7,
  .par2 30941 5104249,
  .force 656737 1 [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (21787, 2), (30941, 1), (5104249, 2)],
  .up 656737 1,
  .rs 656737 1 4,
  .par2 30941 656737,
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (21787, 2), (30941, 1), (656737, 2), (5104249, 2)],
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (21787, 2), (30941, 1), (5104249, 2)],
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (21787, 2), (30941, 1), (5104249, 4)],
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (21787, 2), (30941, 1)],
  .force 166484861 1 [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (21787, 4), (30941, 1)],
  .up 166484861 1,
  .rs 166484861 1 4,
  .par2 30941 166484861,
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (21787, 4), (30941, 1), (166484861, 2)],
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (21787, 4), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (21787, 6), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (21787, 10), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 2), (30941, 1)],
  .force 1648012040336791 1 [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 4), (30941, 1)],
  .up 1648012040336791 1,
  .rs 1648012040336791 1 4,
  .par2 30941 1648012040336791,
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 4), (30941, 1), (1648012040336791, 2)],
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 4), (30941, 1)],
  .force 68917740951781 1 [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 6), (30941, 1)],
  .up 68917740951781 1,
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 6), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 10), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (17351, 12), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 4), (191, 2), (30941, 1)],
  .force 917087137 1 [(3, 2), (13, 4), (31, 6), (191, 2), (30941, 1)],
  .up 917087137 1,
  .rs 917087137 1 8,
  .par2 30941 917087137,
  .force 38533987 1 [(3, 2), (13, 4), (31, 6), (191, 2), (30941, 1), (917087137, 2)],
  .up 38533987 1,
  .rs 38533987 1 5,
  .par2 30941 38533987,
  .big [(3, 2), (13, 4), (31, 6), (191, 2), (30941, 1), (38533987, 2), (917087137, 2)],
  .big [(3, 2), (13, 4), (31, 6), (191, 2), (30941, 1), (917087137, 2)],
  .big [(3, 2), (13, 4), (31, 6), (191, 2), (30941, 1), (917087137, 4)],
  .big [(3, 2), (13, 4), (31, 6), (191, 2), (30941, 1), (917087137, 6)],
  .big [(3, 2), (13, 4), (31, 6), (191, 2), (30941, 1)],
  .force 150332843 1 [(3, 2), (13, 4), (31, 10), (191, 2), (30941, 1)],
  .up 150332843 1,
  .rs 150332843 1 7,
  .par2 30941 150332843,
  .force 127473943 1 [(3, 2), (13, 4), (31, 10), (191, 2), (30941, 1), (150332843, 2)],
  .up 127473943 1,
  .rs 127473943 1 4,
  .par2 30941 127473943,
  .big [(3, 2), (13, 4), (31, 10), (191, 2), (30941, 1), (127473943, 2), (150332843, 2)],
  .big [(3, 2), (13, 4), (31, 10), (191, 2), (30941, 1), (150332843, 2)],
  .big [(3, 2), (13, 4), (31, 10), (191, 2), (30941, 1), (150332843, 4)],
  .big [(3, 2), (13, 4), (31, 10), (191, 2), (30941, 1)],
  .force 7908811 1 [(3, 2), (13, 4), (31, 12), (191, 2), (30941, 1)],
  .up 7908811 1,
  .rs 7908811 1 6,
  .par2 30941 7908811,
  .force 2426789 1 [(3, 2), (13, 4), (31, 12), (191, 2), (30941, 1), (7908811, 2)],
  .up 2426789 1,
  .big [(3, 2), (13, 4), (31, 12), (191, 2), (30941, 1), (7908811, 2)],
  .big [(3, 2), (13, 4), (31, 12), (191, 2), (30941, 1), (7908811, 4)],
  .big [(3, 2), (13, 4), (31, 12), (191, 2), (30941, 1)],
  .force 751670559138758105956097 1 [(3, 2), (13, 4), (31, 16), (191, 2), (30941, 1)],
  .up 751670559138758105956097 1,
  .big [(3, 2), (13, 4), (31, 16), (191, 2), (30941, 1)],
  .force 88770666332610762169 1 [(3, 2), (13, 4), (31, 18), (191, 2), (30941, 1)],
  .up 88770666332610762169 1,
  .big [(3, 2), (13, 4), (31, 18), (191, 2), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 22), (191, 2), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 28), (191, 2), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 30), (191, 2), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 36), (191, 2), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 40), (191, 2), (30941, 1)],
  .big [(3, 2), (13, 4), (31, 42), (191, 2), (30941, 1)],
  .big [(3, 2), (13, 4), (191, 2), (30941, 1)],
  .force 13001 1 [(3, 2), (13, 4), (191, 4), (30941, 1)],
  .up 13001 1,
  .rs 13001 1 15,
  .par2 30941 13001,
  .force 9511 1 [(3, 2), (13, 4), (191, 4), (13001, 2), (30941, 1)],
  .up 9511 1,
  .rs 9511 1 12,
  .par2 30941 9511,
  .force 51199 1 [(3, 2), (13, 4), (191, 4), (9511, 2), (13001, 2), (30941, 1)],
  .up 51199 1,
  .rs 51199 1 8,
  .par2 30941 51199,
  .force 236737 1 [(3, 2), (13, 4), (191, 4), (9511, 2), (13001, 2), (30941, 1), (51199, 2)],
  .up 236737 1,
  .rs 236737 1 5,
  .par2 30941 236737,
  .big [(3, 2), (13, 4), (191, 4), (9511, 2), (13001, 2), (30941, 1), (51199, 2), (236737, 2)],
  .big [(3, 2), (13, 4), (191, 4), (9511, 2), (13001, 2), (30941, 1), (51199, 2)],
  .big [(3, 2), (13, 4), (191, 4), (9511, 2), (13001, 2), (30941, 1), (51199, 4)],
  .big [(3, 2), (13, 4), (191, 4), (9511, 2), (13001, 2), (30941, 1), (51199, 6)],
  .big [(3, 2), (13, 4), (191, 4), (9511, 2), (13001, 2), (30941, 1)],
  .force 2481971 1 [(3, 2), (13, 4), (191, 4), (9511, 4), (13001, 2), (30941, 1)],
  .up 2481971 1,
  .rs 2481971 1 4,
  .par2 30941 2481971,
  .big [(3, 2), (13, 4), (191, 4), (9511, 4), (13001, 2), (30941, 1), (2481971, 2)],
  .big [(3, 2), (13, 4), (191, 4), (9511, 4), (13001, 2), (30941, 1)],
  .big [(3, 2), (13, 4), (191, 4), (9511, 6), (13001, 2), (30941, 1)],
  .big [(3, 2), (13, 4), (191, 4), (9511, 10), (13001, 2), (30941, 1)],
  .big [(3, 2), (13, 4), (191, 4), (13001, 2), (30941, 1)],
  .force 32491 1 [(3, 2), (13, 4), (191, 4), (13001, 4), (30941, 1)],
  .up 32491 1,
  .rs 32491 1 7,
  .par2 30941 32491,
  .force 17981 1 [(3, 2), (13, 4), (191, 4), (13001, 4), (30941, 1), (32491, 2)],
  .up 17981 1,
  .rs 17981 1 4,
  .par2 30941 17981,
  .big [(3, 2), (13, 4), (191, 4), (13001, 4), (17981, 2), (30941, 1), (32491, 2)],
  .big [(3, 2), (13, 4), (191, 4), (13001, 4), (30941, 1), (32491, 2)],
  .big [(3, 2), (13, 4), (191, 4), (13001, 4), (30941, 1), (32491, 4)],
  .big [(3, 2), (13, 4), (191, 4), (13001, 4), (30941, 1)],
  .force 310641311 1 [(3, 2), (13, 4), (191, 4), (13001, 6), (30941, 1)],
  .up 310641311 1,
  .big [(3, 2), (13, 4), (191, 4), (13001, 6), (30941, 1)],
  .big [(3, 2), (13, 4), (191, 4), (13001, 10), (30941, 1)],
  .big [(3, 2), (13, 4), (191, 4), (13001, 12), (30941, 1)],
  .big [(3, 2), (13, 4), (191, 4), (30941, 1)],
  .force 183569 1 [(3, 2), (13, 4), (191, 6), (30941, 1)],
  .up 183569 1,
  .rs 183569 1 10,
  .par2 30941 183569,
  .force 2592135487 1 [(3, 2), (13, 4), (191, 6), (30941, 1), (183569, 2)],
  .up 2592135487 1,
  .rs 2592135487 1 5,
  .par2 30941 2592135487,
  .big [(3, 2), (13, 4), (191, 6), (30941, 1), (183569, 2), (2592135487, 2)],
  .big [(3, 2), (13, 4), (191, 6), (30941, 1), (183569, 2)],
  .force 477307001 1 [(3, 2), (13, 4), (191, 6), (30941, 1), (183569, 4)],
  .up 477307001 1,
  .big [(3, 2), (13, 4), (191, 6), (30941, 1), (183569, 4)],
  .big [(3, 2), (13, 4), (191, 6), (30941, 1), (183569, 6)],
  .big [(3, 2), (13, 4), (191, 6), (30941, 1)],
  .force 1900421426047 1 [(3, 2), (13, 4), (191, 10), (30941, 1)],
  .up 1900421426047 1,
  .rs 1900421426047 1 4,
  .par2 30941 1900421426047,
  .big [(3, 2), (13, 4), (191, 10), (30941, 1), (1900421426047, 2)],
  .big [(3, 2), (13, 4), (191, 10), (30941, 1)],
  .force 48552947 1 [(3, 2), (13, 4), (191, 12), (30941, 1)],
  .up 48552947 1,
  .rs 48552947 1 4,
  .par2 30941 48552947,
  .big [(3, 2), (13, 4), (191, 12), (30941, 1), (48552947, 2)],
  .big [(3, 2), (13, 4), (191, 12), (30941, 1)],
  .big [(3, 2), (13, 4), (191, 16), (30941, 1)],
  .big [(3, 2), (13, 4), (191, 18), (30941, 1)],
  .big [(3, 2), (13, 4), (191, 22), (30941, 1)],
  .big [(3, 2), (13, 4), (191, 28), (30941, 1)],
  .big [(3, 2), (13, 4), (30941, 1)],
  .force 14083 1 [(3, 2), (13, 4), (30941, 2)],
  .up 14083 1,
  .rs 14083 1 16,
  .parS 14083,
  .force 14401 1 [(3, 2), (13, 4), (14083, 2), (30941, 2)],
  .rs 14401 1 13,
  .force 4591 1 [(3, 2), (13, 4), (14083, 2), (14401, 1), (30941, 2)]]

/-- Instructions, part 5. -/
def tree3_5 : List Ins := [
  .up 4591 1,
  .rs 4591 1 13,
  .par2 14401 4591,
  .force 55333 1 [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 1), (30941, 2)],
  .up 55333 1,
  .rs 55333 1 9,
  .par2 14401 55333,
  .force 2780923 1 [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 1), (30941, 2), (55333, 2)],
  .up 2780923 1,
  .rs 2780923 1 5,
  .par2 14401 2780923,
  .big [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 1), (30941, 2), (55333, 2), (2780923, 2)],
  .big [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 1), (30941, 2), (55333, 2)],
  .big [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 1), (30941, 2), (55333, 4)],
  .big [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 1), (30941, 2), (55333, 6)],
  .big [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 1), (30941, 2)],
  .force 8079064749671 1 [(3, 2), (13, 4), (4591, 4), (14083, 2), (14401, 1), (30941, 2)],
  .up 8079064749671 1,
  .rs 8079064749671 1 4,
  .par2 14401 8079064749671,
  .big [(3, 2), (13, 4), (4591, 4), (14083, 2), (14401, 1), (30941, 2), (8079064749671, 2)],
  .big [(3, 2), (13, 4), (4591, 4), (14083, 2), (14401, 1), (30941, 2)],
  .big [(3, 2), (13, 4), (4591, 6), (14083, 2), (14401, 1), (30941, 2)],
  .big [(3, 2), (13, 4), (4591, 10), (14083, 2), (14401, 1), (30941, 2)],
  .big [(3, 2), (13, 4), (14083, 2), (14401, 1), (30941, 2)],
  .force 125017 1 [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2)],
  .rs 125017 1 9,
  .force 4591 1 [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 1)],
  .up 4591 1,
  .rs 4591 1 10,
  .par2 125017 4591,
  .force 55333 1 [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 2), (30941, 2), (125017, 1)],
  .up 55333 1,
  .rs 55333 1 6,
  .par2 125017 55333,
  .force 2780923 1 [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 2), (30941, 2), (55333, 2), (125017, 1)],
  .up 2780923 1,
  .big [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 2), (30941, 2), (55333, 2), (125017, 1)],
  .big [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 2), (30941, 2), (55333, 4), (125017, 1)],
  .big [(3, 2), (13, 4), (4591, 2), (14083, 2), (14401, 2), (30941, 2), (125017, 1)],
  .force 8079064749671 1 [(3, 2), (13, 4), (4591, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 1)],
  .up 8079064749671 1,
  .big [(3, 2), (13, 4), (4591, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 1)],
  .big [(3, 2), (13, 4), (4591, 6), (14083, 2), (14401, 2), (30941, 2), (125017, 1)],
  .big [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 1)],
  .force 263827 1 [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 2)],
  .up 263827 1,
  .rs 263827 1 6,
  .parS 263827,
  .force 3314521417 1 [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 2), (263827, 2)],
  .rs 3314521417 1 3,
  .big [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 2), (263827, 2), (3314521417, 1)],
  .big [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 2), (263827, 2)],
  .big [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 2), (263827, 4)],
  .big [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 2)],
  .big [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 4)],
  .big [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2), (125017, 6)],
  .big [(3, 2), (13, 4), (14083, 2), (14401, 2), (30941, 2)],
  .force 2235195191 1 [(3, 2), (13, 4), (14083, 2), (14401, 4), (30941, 2)],
  .up 2235195191 1,
  .rs 2235195191 1 4,
  .parS 2235195191,
  .big [(3, 2), (13, 4), (14083, 2), (14401, 4), (30941, 2), (2235195191, 2)],
  .big [(3, 2), (13, 4), (14083, 2), (14401, 4), (30941, 2)],
  .big [(3, 2), (13, 4), (14083, 2), (14401, 6), (30941, 2)],
  .big [(3, 2), (13, 4), (14083, 2), (14401, 10), (30941, 2)],
  .big [(3, 2), (13, 4), (14083, 2), (30941, 2)],
  .force 50368674550301 1 [(3, 2), (13, 4), (14083, 4), (30941, 2)],
  .rs 50368674550301 1 4,
  .force 1937959 1 [(3, 2), (13, 4), (14083, 4), (30941, 2), (50368674550301, 1)],
  .up 1937959 1,
  .rs 1937959 1 5,
  .par2 50368674550301 1937959,
  .big [(3, 2), (13, 4), (14083, 4), (30941, 2), (1937959, 2), (50368674550301, 1)],
  .big [(3, 2), (13, 4), (14083, 4), (30941, 2), (50368674550301, 1)],
  .big [(3, 2), (13, 4), (14083, 4), (30941, 2), (50368674550301, 2)],
  .big [(3, 2), (13, 4), (14083, 4), (30941, 2)],
  .force 7801927585025353459681093 1 [(3, 2), (13, 4), (14083, 6), (30941, 2)],
  .rs 7801927585025353459681093 1 3,
  .big [(3, 2), (13, 4), (14083, 6), (30941, 2), (7801927585025353459681093, 1)],
  .big [(3, 2), (13, 4), (14083, 6), (30941, 2)],
  .big [(3, 2), (13, 4), (14083, 10), (30941, 2)],
  .big [(3, 2), (13, 4), (14083, 12), (30941, 2)],
  .big [(3, 2), (13, 4), (30941, 2)],
  .force 239371661 1 [(3, 2), (13, 4), (30941, 4)],
  .rs 239371661 1 7,
  .force 69617111 1 [(3, 2), (13, 4), (30941, 4), (239371661, 1)],
  .up 69617111 1,
  .rs 69617111 1 6,
  .par2 239371661 69617111,
  .force 12897251893 1 [(3, 2), (13, 4), (30941, 4), (69617111, 2), (239371661, 1)],
  .up 12897251893 1,
  .big [(3, 2), (13, 4), (30941, 4), (69617111, 2), (239371661, 1)],
  .big [(3, 2), (13, 4), (30941, 4), (69617111, 4), (239371661, 1)],
  .big [(3, 2), (13, 4), (30941, 4), (239371661, 1)],
  .force 493121947 1 [(3, 2), (13, 4), (30941, 4), (239371661, 2)],
  .up 493121947 1,
  .rs 493121947 1 4,
  .parS 493121947,
  .big [(3, 2), (13, 4), (30941, 4), (239371661, 2), (493121947, 2)],
  .big [(3, 2), (13, 4), (30941, 4), (239371661, 2)],
  .big [(3, 2), (13, 4), (30941, 4), (239371661, 4)],
  .big [(3, 2), (13, 4), (30941, 4)],
  .force 17177163455369 1 [(3, 2), (13, 4), (30941, 6)],
  .rs 17177163455369 1 4,
  .force 5791337 1 [(3, 2), (13, 4), (30941, 6), (17177163455369, 1)],
  .up 5791337 1,
  .rs 5791337 1 4,
  .par2 17177163455369 5791337,
  .big [(3, 2), (13, 4), (30941, 6), (5791337, 2), (17177163455369, 1)],
  .big [(3, 2), (13, 4), (30941, 6), (17177163455369, 1)],
  .big [(3, 2), (13, 4), (30941, 6), (17177163455369, 2)],
  .big [(3, 2), (13, 4), (30941, 6)],
  .big [(3, 2), (13, 4), (30941, 10)],
  .big [(3, 2), (13, 4), (30941, 12)],
  .big [(3, 2), (13, 4), (30941, 16)],
  .big [(3, 2), (13, 4)],
  .force 5229043 1 [(3, 2), (13, 6)],
  .up 5229043 1,
  .rs 5229043 1 12,
  .parS 5229043,
  .force 72577051 1 [(3, 2), (13, 6), (5229043, 2)],
  .up 72577051 1,
  .rs 72577051 1 8,
  .parS 72577051,
  .force 65522613283 1 [(3, 2), (13, 6), (5229043, 2), (72577051, 2)],
  .up 65522613283 1,
  .rs 65522613283 1 5,
  .parS 65522613283,
  .big [(3, 2), (13, 6), (5229043, 2), (72577051, 2), (65522613283, 2)],
  .big [(3, 2), (13, 6), (5229043, 2), (72577051, 2)],
  .big [(3, 2), (13, 6), (5229043, 2), (72577051, 4)],
  .big [(3, 2), (13, 6), (5229043, 2), (72577051, 6)],
  .big [(3, 2), (13, 6), (5229043, 2)],
  .force 32607907713428723311 1 [(3, 2), (13, 6), (5229043, 4)],
  .up 32607907713428723311 1,
  .big [(3, 2), (13, 6), (5229043, 4)],
  .big [(3, 2), (13, 6), (5229043, 6)],
  .big [(3, 2), (13, 6), (5229043, 10)],
  .big [(3, 2), (13, 6)],
  .force 18041 1 [(3, 2), (13, 10)],
  .rs 18041 1 16,
  .force 859 1 [(3, 2), (13, 10), (18041, 1)],
  .up 859 1,
  .rs 859 1 20,
  .par2 18041 859,
  .force 246247 1 [(3, 2), (13, 10), (859, 2), (18041, 1)],
  .up 246247 1,
  .rs 246247 1 11,
  .par2 18041 246247,
  .force 6151 1 [(3, 2), (13, 10), (859, 2), (18041, 1), (246247, 2)],
  .up 6151 1,
  .rs 6151 1 10,
  .par2 18041 6151,
  .force 10099 1 [(3, 2), (13, 10), (859, 2), (6151, 2), (18041, 1), (246247, 2)],
  .up 10099 1,
  .rs 10099 1 7,
  .par2 18041 10099,
  .force 33999967 1 [(3, 2), (13, 10), (859, 2), (6151, 2), (10099, 2), (18041, 1), (246247, 2)],
  .up 33999967 1,
  .big [(3, 2), (13, 10), (859, 2), (6151, 2), (10099, 2), (18041, 1), (246247, 2)],
  .big [(3, 2), (13, 10), (859, 2), (6151, 2), (10099, 4), (18041, 1), (246247, 2)],
  .big [(3, 2), (13, 10), (859, 2), (6151, 2), (18041, 1), (246247, 2)],
  .force 1499167462211 1 [(3, 2), (13, 10), (859, 2), (6151, 4), (18041, 1), (246247, 2)],
  .up 1499167462211 1,
  .big [(3, 2), (13, 10), (859, 2), (6151, 4), (18041, 1), (246247, 2)],
  .big [(3, 2), (13, 10), (859, 2), (6151, 6), (18041, 1), (246247, 2)],
  .big [(3, 2), (13, 10), (859, 2), (18041, 1), (246247, 2)],
  .force 1268339206921 1 [(3, 2), (13, 10), (859, 2), (18041, 1), (246247, 4)],
  .up 1268339206921 1,
  .big [(3, 2), (13, 10), (859, 2), (18041, 1), (246247, 4)],
  .big [(3, 2), (13, 10), (859, 2), (18041, 1), (246247, 6)],
  .big [(3, 2), (13, 10), (859, 2), (18041, 1)],
  .force 4772771 1 [(3, 2), (13, 10), (859, 4), (18041, 1)],
  .up 4772771 1,
  .rs 4772771 1 7,
  .par2 18041 4772771,
  .force 1667228851 1 [(3, 2), (13, 10), (859, 4), (18041, 1), (4772771, 2)],
  .up 1667228851 1,
  .rs 1667228851 1 4,
  .par2 18041 1667228851,
  .big [(3, 2), (13, 10), (859, 4), (18041, 1), (4772771, 2), (1667228851, 2)],
  .big [(3, 2), (13, 10), (859, 4), (18041, 1), (4772771, 2)],
  .big [(3, 2), (13, 10), (859, 4), (18041, 1), (4772771, 4)],
  .big [(3, 2), (13, 10), (859, 4), (18041, 1)],
  .force 398633408201869 1 [(3, 2), (13, 10), (859, 6), (18041, 1)],
  .up 398633408201869 1,
  .rs 398633408201869 1 4,
  .par2 18041 398633408201869,
  .big [(3, 2), (13, 10), (859, 6), (18041, 1), (398633408201869, 2)],
  .big [(3, 2), (13, 10), (859, 6), (18041, 1)],
  .big [(3, 2), (13, 10), (859, 10), (18041, 1)],
  .big [(3, 2), (13, 10), (859, 12), (18041, 1)],
  .big [(3, 2), (13, 10), (859, 16), (18041, 1)],
  .big [(3, 2), (13, 10), (859, 18), (18041, 1)],
  .big [(3, 2), (13, 10), (18041, 1)],
  .force 46499389 1 [(3, 2), (13, 10), (18041, 2)],
  .rs 46499389 1 8,
  .force 6577 1 [(3, 2), (13, 10), (18041, 2), (46499389, 1)],
  .up 6577 1,
  .rs 6577 1 12,
  .par2 46499389 6577,
  .force 66457 1 [(3, 2), (13, 10), (6577, 2), (18041, 2), (46499389, 1)],
  .up 66457 1,
  .rs 66457 1 8,
  .par2 46499389 66457,
  .force 318589 1 [(3, 2), (13, 10), (6577, 2), (18041, 2), (66457, 2), (46499389, 1)],
  .up 318589 1,
  .rs 318589 1 4,
  .par2 46499389 318589,
  .big [(3, 2), (13, 10), (6577, 2), (18041, 2), (66457, 2), (318589, 2), (46499389, 1)],
  .big [(3, 2), (13, 10), (6577, 2), (18041, 2), (66457, 2), (46499389, 1)],
  .big [(3, 2), (13, 10), (6577, 2), (18041, 2), (66457, 4), (46499389, 1)],
  .big [(3, 2), (13, 10), (6577, 2), (18041, 2), (66457, 6), (46499389, 1)],
  .big [(3, 2), (13, 10), (6577, 2), (18041, 2), (46499389, 1)],
  .force 2297881 1 [(3, 2), (13, 10), (6577, 4), (18041, 2), (46499389, 1)],
  .up 2297881 1,
  .rs 2297881 1 4,
  .par2 46499389 2297881,
  .big [(3, 2), (13, 10), (6577, 4), (18041, 2), (2297881, 2), (46499389, 1)],
  .big [(3, 2), (13, 10), (6577, 4), (18041, 2), (46499389, 1)],
  .big [(3, 2), (13, 10), (6577, 6), (18041, 2), (46499389, 1)],
  .big [(3, 2), (13, 10), (6577, 10), (18041, 2), (46499389, 1)],
  .big [(3, 2), (13, 10), (18041, 2), (46499389, 1)],
  .force 16761187781959 1 [(3, 2), (13, 10), (18041, 2), (46499389, 2)],
  .up 16761187781959 1,
  .rs 16761187781959 1 4,
  .parS 16761187781959,
  .big [(3, 2), (13, 10), (18041, 2), (46499389, 2), (16761187781959, 2)],
  .big [(3, 2), (13, 10), (18041, 2), (46499389, 2)],
  .big [(3, 2), (13, 10), (18041, 2), (46499389, 4)],
  .big [(3, 2), (13, 10), (18041, 2), (46499389, 6)],
  .big [(3, 2), (13, 10), (18041, 2)],
  .force 790579404481 1 [(3, 2), (13, 10), (18041, 4)],
  .rs 790579404481 1 5,
  .force 827023 1 [(3, 2), (13, 10), (18041, 4), (790579404481, 1)],
  .up 827023 1,
  .rs 827023 1 5,
  .par2 790579404481 827023,
  .big [(3, 2), (13, 10), (18041, 4), (827023, 2), (790579404481, 1)],
  .big [(3, 2), (13, 10), (18041, 4), (790579404481, 1)],
  .big [(3, 2), (13, 10), (18041, 4), (790579404481, 2)],
  .big [(3, 2), (13, 10), (18041, 4)],
  .force 9108709959749 1 [(3, 2), (13, 10), (18041, 6)],
  .rs 9108709959749 1 3,
  .big [(3, 2), (13, 10), (18041, 6), (9108709959749, 1)],
  .big [(3, 2), (13, 10), (18041, 6)],
  .big [(3, 2), (13, 10), (18041, 10)],
  .big [(3, 2), (13, 10), (18041, 12)],
  .big [(3, 2), (13, 10)],
  .force 1803647 1 [(3, 2), (13, 12)],
  .up 1803647 1,
  .rs 1803647 1 11,
  .parS 1803647,
  .force 104940138847 1 [(3, 2), (13, 12), (1803647, 2)],
  .up 104940138847 1,
  .rs 104940138847 1 5,
  .parS 104940138847,
  .big [(3, 2), (13, 12), (1803647, 2), (104940138847, 2)],
  .big [(3, 2), (13, 12), (1803647, 2)],
  .force 4803254465101 1 [(3, 2), (13, 12), (1803647, 4)],
  .rs 4803254465101 1 3,
  .big [(3, 2), (13, 12), (1803647, 4), (4803254465101, 1)],
  .big [(3, 2), (13, 12), (1803647, 4)],
  .big [(3, 2), (13, 12), (1803647, 6)],
  .big [(3, 2), (13, 12)],
  .force 15798461357509 1 [(3, 2), (13, 16)],
  .rs 15798461357509 1 6,
  .force 77477 1 [(3, 2), (13, 16), (15798461357509, 1)],
  .up 77477 1,
  .rs 77477 1 9,
  .par2 15798461357509 77477,
  .force 114769 1 [(3, 2), (13, 16), (77477, 2), (15798461357509, 1)],
  .up 114769 1,
  .rs 114769 1 6,
  .par2 15798461357509 114769,
  .force 2972701 1 [(3, 2), (13, 16), (77477, 2), (114769, 2), (15798461357509, 1)],
  .up 2972701 1,
  .big [(3, 2), (13, 16), (77477, 2), (114769, 2), (15798461357509, 1)],
  .big [(3, 2), (13, 16), (77477, 2), (114769, 4), (15798461357509, 1)],
  .big [(3, 2), (13, 16), (77477, 2), (15798461357509, 1)],
  .big [(3, 2), (13, 16), (77477, 4), (15798461357509, 1)],
  .big [(3, 2), (13, 16), (77477, 6), (15798461357509, 1)],
  .big [(3, 2), (13, 16), (15798461357509, 1)],
  .force 83197127088240304524014197 1 [(3, 2), (13, 16), (15798461357509, 2)],
  .rs 83197127088240304524014197 1 3,
  .big [(3, 2), (13, 16), (15798461357509, 2), (83197127088240304524014197, 1)],
  .big [(3, 2), (13, 16), (15798461357509, 2)],
  .big [(3, 2), (13, 16), (15798461357509, 4)],
  .big [(3, 2), (13, 16)],
  .force 9468940004449 1 [(3, 2), (13, 18)],
  .rs 9468940004449 1 5,
  .force 12865927 1 [(3, 2), (13, 18), (9468940004449, 1)],
  .up 12865927 1,
  .rs 12865927 1 6,
  .par2 9468940004449 12865927,
  .force 1250413 1 [(3, 2), (13, 18), (12865927, 2), (9468940004449, 1)],
  .up 1250413 1,
  .big [(3, 2), (13, 18), (12865927, 2), (9468940004449, 1)],
  .big [(3, 2), (13, 18), (12865927, 4), (9468940004449, 1)],
  .big [(3, 2), (13, 18), (9468940004449, 1)],
  .force 496865249166620100967 1 [(3, 2), (13, 18), (9468940004449, 2)],
  .up 496865249166620100967 1,
  .big [(3, 2), (13, 18), (9468940004449, 2)],
  .big [(3, 2), (13, 18)],
  .force 2519545342349331183143 1 [(3, 2), (13, 22)],
  .up 2519545342349331183143 1,
  .rs 2519545342349331183143 1 4,
  .parS 2519545342349331183143,
  .big [(3, 2), (13, 22), (2519545342349331183143, 2)],
  .big [(3, 2), (13, 22)],
  .force 846041103974872866961 1 [(3, 2), (13, 28)],
  .rs 846041103974872866961 1 3,
  .big [(3, 2), (13, 28), (846041103974872866961, 1)],
  .big [(3, 2), (13, 28)],
  .force 8170509011431363408568150369 1 [(3, 2), (13, 30)],
  .rs 8170509011431363408568150369 1 3,
  .big [(3, 2), (13, 30), (8170509011431363408568150369, 1)],
  .big [(3, 2), (13, 30)],
  .big [(3, 2), (13, 36)],
  .big [(3, 2), (13, 40)],
  .big [(3, 2), (13, 42)],
  .big [(3, 2), (13, 46)],
  .big [(3, 2), (13, 52)],
  .big [(3, 2), (13, 58)],
  .big [(3, 2), (13, 60)],
  .big [(3, 2), (13, 66)],
  .big [(3, 2), (13, 70)],
  .big [(3, 2)],
  .force 11 2 [(3, 4)],
  .rs 11 1 76,
  .parS 11,
  .force 19 1 [(3, 4), (11, 2)],
  .up 19 1,
  .rs 19 1 59,
  .parS 19,
  .force 127 1 [(3, 4), (11, 2), (19, 2)],
  .up 127 1,
  .rs 127 1 36,
  .parS 127,
  .force 5419 1 [(3, 4), (11, 2), (19, 2), (127, 2)],
  .up 5419 1,
  .rs 5419 1 20,
  .parS 5419,
  .force 1009 1 [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 2)],
  .rs 1009 1 20,
  .force 313 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 1), (5419, 2)],
  .up 313 1,
  .rs 313 1 23,
  .par2 1009 313,
  .force 181 2 [(3, 4), (11, 2), (19, 2), (127, 2), (313, 2), (1009, 1), (5419, 2)],
  .rs 181 1 23,
  .par2 1009 181,
  .force 139 1 [(3, 4), (11, 2), (19, 2), (127, 2), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .up 139 1,
  .rs 139 1 21,
  .par2 1009 139,
  .force 499 1 [(3, 4), (11, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .up 499 1,
  .rs 499 1 14,
  .par2 1009 499,
  .force 109 2 [(3, 4), (11, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .rs 109 1 15,
  .par2 1009 109,
  .force 571 1 [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .up 571 1,
  .rs 571 1 10,
  .par2 1009 571,
  .force 151 1 [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .up 151 1,
  .rs 151 1 8,
  .par2 1009 151,
  .force 1093 1 [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (151, 2), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .up 1093 1,
  .rs 1093 1 4,
  .par2 1009 1093,
  .big [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (151, 2), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (1093, 2), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (151, 2), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (151, 4), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (151, 6), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .force 11631811 1 [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (571, 4), (1009, 1), (5419, 2)],
  .up 11631811 1,
  .big [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (571, 4), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (571, 6), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .force 24061 1 [(3, 4), (11, 2), (19, 2), (109, 4), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .up 24061 1,
  .rs 24061 1 5,
  .par2 1009 24061,
  .force 46807 1 [(3, 4), (11, 2), (19, 2), (109, 4), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2), (24061, 2)],
  .up 46807 1,
  .big [(3, 4), (11, 2), (19, 2), (109, 4), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2), (24061, 2)],
  .big [(3, 4), (11, 2), (19, 2), (109, 4), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .force 53306107 1 [(3, 4), (11, 2), (19, 2), (109, 6), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .up 53306107 1,
  .big [(3, 4), (11, 2), (19, 2), (109, 6), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (109, 10), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (109, 12), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)]]

/-- Instructions, part 6. -/
def tree3_6 : List Ins := [
  .force 55918991 1 [(3, 4), (11, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 4), (1009, 1), (5419, 2)],
  .up 55918991 1,
  .rs 55918991 1 4,
  .par2 1009 55918991,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 4), (1009, 1), (5419, 2), (55918991, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 4), (1009, 1), (5419, 2)],
  .force 236022613 1 [(3, 4), (11, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 6), (1009, 1), (5419, 2)],
  .up 236022613 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 6), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 10), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 12), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .force 9170881 1 [(3, 4), (11, 2), (19, 2), (127, 2), (139, 4), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .up 9170881 1,
  .rs 9170881 1 6,
  .par2 1009 9170881,
  .force 752449 1 [(3, 4), (11, 2), (19, 2), (127, 2), (139, 4), (181, 2), (313, 2), (1009, 1), (5419, 2), (9170881, 2)],
  .up 752449 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 4), (181, 2), (313, 2), (1009, 1), (5419, 2), (9170881, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 4), (181, 2), (313, 2), (1009, 1), (5419, 2), (9170881, 4)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 4), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .force 87683177 1 [(3, 4), (11, 2), (19, 2), (127, 2), (139, 6), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .up 87683177 1,
  .rs 87683177 1 4,
  .par2 1009 87683177,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 6), (181, 2), (313, 2), (1009, 1), (5419, 2), (87683177, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 6), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 10), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 12), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 16), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (139, 18), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .force 19622651 1 [(3, 4), (11, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2)],
  .up 19622651 1,
  .rs 19622651 1 7,
  .par2 1009 19622651,
  .force 479971 1 [(3, 4), (11, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2), (19622651, 2)],
  .up 479971 1,
  .rs 479971 1 4,
  .par2 1009 479971,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2), (479971, 2), (19622651, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2), (19622651, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2), (19622651, 4)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2)],
  .force 4338835663 1 [(3, 4), (11, 2), (19, 2), (127, 2), (181, 6), (313, 2), (1009, 1), (5419, 2)],
  .up 4338835663 1,
  .rs 4338835663 1 5,
  .par2 1009 4338835663,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (181, 6), (313, 2), (1009, 1), (5419, 2), (4338835663, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (181, 6), (313, 2), (1009, 1), (5419, 2)],
  .force 52198426022458982993 1 [(3, 4), (11, 2), (19, 2), (127, 2), (181, 10), (313, 2), (1009, 1), (5419, 2)],
  .up 52198426022458982993 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (181, 10), (313, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (181, 12), (313, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (181, 16), (313, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (181, 18), (313, 2), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (313, 2), (1009, 1), (5419, 2)],
  .force 875335231 1 [(3, 4), (11, 2), (19, 2), (127, 2), (313, 4), (1009, 1), (5419, 2)],
  .up 875335231 1,
  .rs 875335231 1 6,
  .par2 1009 875335231,
  .force 405784411 1 [(3, 4), (11, 2), (19, 2), (127, 2), (313, 4), (1009, 1), (5419, 2), (875335231, 2)],
  .up 405784411 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (313, 4), (1009, 1), (5419, 2), (875335231, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (313, 4), (1009, 1), (5419, 2), (875335231, 4)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (313, 4), (1009, 1), (5419, 2)],
  .force 32528030679467 1 [(3, 4), (11, 2), (19, 2), (127, 2), (313, 6), (1009, 1), (5419, 2)],
  .up 32528030679467 1,
  .rs 32528030679467 1 4,
  .par2 1009 32528030679467,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (313, 6), (1009, 1), (5419, 2), (32528030679467, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (313, 6), (1009, 1), (5419, 2)],
  .force 4805923863681403 1 [(3, 4), (11, 2), (19, 2), (127, 2), (313, 10), (1009, 1), (5419, 2)],
  .up 4805923863681403 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (313, 10), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (313, 12), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (313, 16), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (313, 18), (1009, 1), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 1), (5419, 2)],
  .force 9181 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2)],
  .rs 9181 1 14,
  .force 4591 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 1)],
  .up 4591 1,
  .rs 4591 1 14,
  .par2 9181 4591,
  .force 55333 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1)],
  .up 55333 1,
  .rs 55333 1 9,
  .par2 9181 55333,
  .force 2780923 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1), (55333, 2)],
  .up 2780923 1,
  .rs 2780923 1 5,
  .par2 9181 2780923,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1), (55333, 2), (2780923, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1), (55333, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1), (55333, 4)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1), (55333, 6)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1)],
  .force 8079064749671 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 4), (5419, 2), (9181, 1)],
  .up 8079064749671 1,
  .rs 8079064749671 1 4,
  .par2 9181 8079064749671,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 4), (5419, 2), (9181, 1), (8079064749671, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 4), (5419, 2), (9181, 1)],
  .force 36825984292217 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 6), (5419, 2), (9181, 1)],
  .up 36825984292217 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 6), (5419, 2), (9181, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 10), (5419, 2), (9181, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (4591, 12), (5419, 2), (9181, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 1)],
  .force 1423 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 2)],
  .up 1423 1,
  .rs 1423 1 13,
  .parS 1423,
  .force 96493 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2)],
  .rs 96493 1 7,
  .force 48247 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 1)],
  .up 48247 1,
  .rs 48247 1 6,
  .par2 96493 48247,
  .force 775940419 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (48247, 2), (96493, 1)],
  .up 775940419 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (48247, 2), (96493, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (48247, 4), (96493, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 1)],
  .force 163350799 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 2)],
  .up 163350799 1,
  .rs 163350799 1 4,
  .parS 163350799,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 2), (163350799, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 4)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2)],
  .force 40497241 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2)],
  .rs 40497241 1 4,
  .force 36353 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2), (40497241, 1)],
  .up 36353 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2), (40497241, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2), (40497241, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 6), (5419, 2), (9181, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (1423, 10), (5419, 2), (9181, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 2)],
  .force 125642407351 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 4)],
  .up 125642407351 1,
  .rs 125642407351 1 4,
  .parS 125642407351,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 4), (125642407351, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 4)],
  .force 19937168287 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 6)],
  .up 19937168287 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 6)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 10)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 12)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 2), (5419, 2)],
  .force 1037517185381 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 4), (5419, 2)],
  .rs 1037517185381 1 5,
  .force 172919530897 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 4), (5419, 2), (1037517185381, 1)],
  .up 172919530897 1,
  .rs 172919530897 1 4,
  .par2 1037517185381 172919530897,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 4), (5419, 2), (172919530897, 2), (1037517185381, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 4), (5419, 2), (1037517185381, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 4), (5419, 2), (1037517185381, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 4), (5419, 2)],
  .force 1024823381 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 6), (5419, 2)],
  .rs 1024823381 1 5,
  .force 15527627 1 [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 6), (5419, 2), (1024823381, 1)],
  .up 15527627 1,
  .rs 15527627 1 4,
  .par2 1024823381 15527627,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 6), (5419, 2), (15527627, 2), (1024823381, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 6), (5419, 2), (1024823381, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 6), (5419, 2), (1024823381, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 6), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 10), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 12), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 16), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (1009, 18), (5419, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 2)],
  .force 836561914831 1 [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 4)],
  .up 836561914831 1,
  .rs 836561914831 1 6,
  .parS 836561914831,
  .force 347568611538691 1 [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 4), (836561914831, 2)],
  .up 347568611538691 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 4), (836561914831, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 4), (836561914831, 4)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 4)],
  .force 829621381 1 [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 6)],
  .rs 829621381 1 5,
  .force 414810691 1 [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 6), (829621381, 1)],
  .up 414810691 1,
  .rs 414810691 1 4,
  .par2 829621381 414810691,
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 6), (414810691, 2), (829621381, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 6), (829621381, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 6), (829621381, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 6)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 10)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 12)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 16)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2), (5419, 18)],
  .big [(3, 4), (11, 2), (19, 2), (127, 2)],
  .force 262209281 1 [(3, 4), (11, 2), (19, 2), (127, 4)],
  .rs 262209281 1 9,
  .force 13931 1 [(3, 4), (11, 2), (19, 2), (127, 4), (262209281, 1)],
  .up 13931 1,
  .rs 13931 1 14,
  .par2 262209281 13931,
  .force 194086693 1 [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 2), (262209281, 1)],
  .up 194086693 1,
  .rs 194086693 1 7,
  .par2 262209281 194086693,
  .force 1380277 1 [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 2), (194086693, 2), (262209281, 1)],
  .up 1380277 1,
  .rs 1380277 1 4,
  .par2 262209281 1380277,
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 2), (1380277, 2), (194086693, 2), (262209281, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 2), (194086693, 2), (262209281, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 2), (194086693, 4), (262209281, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 2), (262209281, 1)],
  .force 1394813567261 1 [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 4), (262209281, 1)],
  .up 1394813567261 1,
  .rs 1394813567261 1 4,
  .par2 262209281 1394813567261,
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 4), (262209281, 1), (1394813567261, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 4), (262209281, 1)],
  .force 285472521588928549 1 [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 6), (262209281, 1)],
  .up 285472521588928549 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 6), (262209281, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 10), (262209281, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (13931, 12), (262209281, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (262209281, 1)],
  .force 4296301150081 1 [(3, 4), (11, 2), (19, 2), (127, 4), (262209281, 2)],
  .rs 4296301150081 1 5,
  .force 123152587 1 [(3, 4), (11, 2), (19, 2), (127, 4), (262209281, 2), (4296301150081, 1)],
  .up 123152587 1,
  .rs 123152587 1 5,
  .par2 4296301150081 123152587,
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (123152587, 2), (262209281, 2), (4296301150081, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (262209281, 2), (4296301150081, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (262209281, 2), (4296301150081, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (262209281, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (262209281, 4)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4), (262209281, 6)],
  .big [(3, 4), (11, 2), (19, 2), (127, 4)],
  .force 162709 1 [(3, 4), (11, 2), (19, 2), (127, 6)],
  .rs 162709 1 11,
  .force 86353 1 [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 1)],
  .up 86353 1,
  .rs 86353 1 11,
  .par2 162709 86353,
  .force 2485642321 1 [(3, 4), (11, 2), (19, 2), (127, 6), (86353, 2), (162709, 1)],
  .up 2485642321 1,
  .rs 2485642321 1 5,
  .par2 162709 2485642321,
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (86353, 2), (162709, 1), (2485642321, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (86353, 2), (162709, 1)],
  .force 8970971 1 [(3, 4), (11, 2), (19, 2), (127, 6), (86353, 4), (162709, 1)],
  .up 8970971 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (86353, 4), (162709, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (86353, 6), (162709, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 1)],
  .force 8824793797 1 [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 2)],
  .rs 8824793797 1 6,
  .force 2409829 1 [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 1)],
  .up 2409829 1,
  .rs 2409829 1 6,
  .par2 8824793797 2409829,
  .force 4252519 1 [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 2), (2409829, 2), (8824793797, 1)],
  .up 4252519 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 2), (2409829, 2), (8824793797, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 2), (2409829, 4), (8824793797, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 1)],
  .force 425557298187947929 1 [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 2)],
  .rs 425557298187947929 1 3,
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 2), (425557298187947929, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 4)],
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 2)],
  .force 700888562389531127981 1 [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 4)],
  .rs 700888562389531127981 1 3,
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 4), (700888562389531127981, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 4)],
  .big [(3, 4), (11, 2), (19, 2), (127, 6), (162709, 6)],
  .big [(3, 4), (11, 2), (19, 2), (127, 6)],
  .force 47834644354838156839 1 [(3, 4), (11, 2), (19, 2), (127, 10)],
  .up 47834644354838156839 1,
  .rs 47834644354838156839 1 4,
  .parS 47834644354838156839,
  .big [(3, 4), (11, 2), (19, 2), (127, 10), (47834644354838156839, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 10)],
  .force 1437263292796553 1 [(3, 4), (11, 2), (19, 2), (127, 12)],
  .rs 1437263292796553 1 4,
  .force 12346432697 1 [(3, 4), (11, 2), (19, 2), (127, 12), (1437263292796553, 1)],
  .up 12346432697 1,
  .big [(3, 4), (11, 2), (19, 2), (127, 12), (1437263292796553, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 12), (1437263292796553, 2)],
  .big [(3, 4), (11, 2), (19, 2), (127, 12)],
  .force 115512048133057 1 [(3, 4), (11, 2), (19, 2), (127, 16)],
  .rs 115512048133057 1 3,
  .big [(3, 4), (11, 2), (19, 2), (127, 16), (115512048133057, 1)],
  .big [(3, 4), (11, 2), (19, 2), (127, 16)],
  .big [(3, 4), (11, 2), (19, 2), (127, 18)],
  .big [(3, 4), (11, 2), (19, 2), (127, 22)],
  .big [(3, 4), (11, 2), (19, 2), (127, 28)],
  .big [(3, 4), (11, 2), (19, 2), (127, 30)],
  .big [(3, 4), (11, 2), (19, 2)],
  .force 911 1 [(3, 4), (11, 2), (19, 4)],
  .up 911 1,
  .rs 911 1 24,
  .parS 911,
  .force 830833 1 [(3, 4), (11, 2), (19, 4), (911, 2)],
  .rs 830833 1 12,
  .force 3271 1 [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 1)],
  .up 3271 1,
  .rs 3271 1 17,
  .par2 830833 3271,
  .force 509653 1 [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 2), (830833, 1)],
  .up 509653 1,
  .rs 509653 1 9,
  .par2 830833 509653,
  .force 12368890003 1 [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 2), (509653, 2), (830833, 1)],
  .up 12368890003 1,
  .rs 12368890003 1 5,
  .par2 830833 12368890003,
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 2), (509653, 2), (830833, 1), (12368890003, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 2), (509653, 2), (830833, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 2), (509653, 4), (830833, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 2), (509653, 6), (830833, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 2), (830833, 1)],
  .force 30514801 1 [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 4), (830833, 1)],
  .up 30514801 1,
  .rs 30514801 1 6,
  .par2 830833 30514801,
  .force 8943553 1 [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 4), (830833, 1), (30514801, 2)],
  .up 8943553 1,
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 4), (830833, 1), (30514801, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 4), (830833, 1), (30514801, 4)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 4), (830833, 1)],
  .force 2002734973 1 [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 6), (830833, 1)],
  .up 2002734973 1,
  .rs 2002734973 1 4,
  .par2 830833 2002734973,
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 6), (830833, 1), (2002734973, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 6), (830833, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 10), (830833, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (3271, 12), (830833, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 1)],
  .force 861001 1 [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 2)],
  .rs 861001 1 9,
  .force 2851 1 [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 2), (861001, 1)],
  .up 2851 1,
  .rs 2851 1 12,
  .par2 861001 2851,
  .force 5779 1 [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 2), (830833, 2), (861001, 1)],
  .up 5779 1,
  .rs 5779 1 8,
  .par2 861001 5779,
  .force 3889 1 [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 2), (5779, 2), (830833, 2), (861001, 1)],
  .up 3889 1,
  .rs 3889 1 6,
  .par2 861001 3889,
  .force 102913 1 [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 2), (3889, 2), (5779, 2), (830833, 2), (861001, 1)],
  .up 102913 1,
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 2), (3889, 2), (5779, 2), (830833, 2), (861001, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 2), (3889, 4), (5779, 2), (830833, 2), (861001, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 2), (5779, 2), (830833, 2), (861001, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 2), (5779, 4), (830833, 2), (861001, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 2), (5779, 6), (830833, 2), (861001, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 2), (830833, 2), (861001, 1)],
  .force 23468881 1 [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 4), (830833, 2), (861001, 1)],
  .up 23468881 1,
  .rs 23468881 1 4,
  .par2 861001 23468881,
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 4), (830833, 2), (861001, 1), (23468881, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 4), (830833, 2), (861001, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 6), (830833, 2), (861001, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (2851, 10), (830833, 2), (861001, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 2), (861001, 1)],
  .force 217081 1 [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 2), (861001, 2)],
  .rs 217081 1 6,
  .force 108541 1 [(3, 4), (11, 2), (19, 4), (911, 2), (217081, 1), (830833, 2), (861001, 2)],
  .up 108541 1,
  .rs 108541 1 6,
  .par2 217081 108541,
  .force 3927085741 1 [(3, 4), (11, 2), (19, 4), (911, 2), (108541, 2), (217081, 1), (830833, 2), (861001, 2)],
  .up 3927085741 1,
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (108541, 2), (217081, 1), (830833, 2), (861001, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (108541, 4), (217081, 1), (830833, 2), (861001, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (217081, 1), (830833, 2), (861001, 2)],
  .force 1077301 1 [(3, 4), (11, 2), (19, 4), (911, 2), (217081, 2), (830833, 2), (861001, 2)],
  .rs 1077301 1 3,
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (217081, 2), (830833, 2), (861001, 2), (1077301, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (217081, 2), (830833, 2), (861001, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (217081, 4), (830833, 2), (861001, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 2), (861001, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 2), (861001, 4)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 2), (861001, 6)]]

/-- Instructions, part 7. -/
def tree3_7 : List Ins := [
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 2)],
  .force 2249049650927341 1 [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 4)],
  .rs 2249049650927341 1 3,
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 4), (2249049650927341, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 4)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 6)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2), (830833, 10)],
  .big [(3, 4), (11, 2), (19, 4), (911, 2)],
  .force 17884211 1 [(3, 4), (11, 2), (19, 4), (911, 4)],
  .up 17884211 1,
  .rs 17884211 1 8,
  .parS 17884211,
  .force 45692145853819 1 [(3, 4), (11, 2), (19, 4), (911, 4), (17884211, 2)],
  .up 45692145853819 1,
  .rs 45692145853819 1 4,
  .parS 45692145853819,
  .big [(3, 4), (11, 2), (19, 4), (911, 4), (17884211, 2), (45692145853819, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 4), (17884211, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 4), (17884211, 4)],
  .big [(3, 4), (11, 2), (19, 4), (911, 4), (17884211, 6)],
  .big [(3, 4), (11, 2), (19, 4), (911, 4)],
  .force 81750272028928231 1 [(3, 4), (11, 2), (19, 4), (911, 6)],
  .up 81750272028928231 1,
  .rs 81750272028928231 1 4,
  .parS 81750272028928231,
  .big [(3, 4), (11, 2), (19, 4), (911, 6), (81750272028928231, 2)],
  .big [(3, 4), (11, 2), (19, 4), (911, 6)],
  .force 247174661801 1 [(3, 4), (11, 2), (19, 4), (911, 10)],
  .rs 247174661801 1 3,
  .big [(3, 4), (11, 2), (19, 4), (911, 10), (247174661801, 1)],
  .big [(3, 4), (11, 2), (19, 4), (911, 10)],
  .big [(3, 4), (11, 2), (19, 4), (911, 12)],
  .big [(3, 4), (11, 2), (19, 4), (911, 16)],
  .big [(3, 4), (11, 2), (19, 4), (911, 18)],
  .big [(3, 4), (11, 2), (19, 4), (911, 22)],
  .big [(3, 4), (11, 2), (19, 4)],
  .force 70841 1 [(3, 4), (11, 2), (19, 6)],
  .rs 70841 1 15,
  .force 11807 1 [(3, 4), (11, 2), (19, 6), (70841, 1)],
  .up 11807 1,
  .rs 11807 1 16,
  .par2 70841 11807,
  .force 2017 1 [(3, 4), (11, 2), (19, 6), (11807, 2), (70841, 1)],
  .up 2017 1,
  .rs 2017 1 15,
  .par2 70841 2017,
  .force 4099 1 [(3, 4), (11, 2), (19, 6), (2017, 2), (11807, 2), (70841, 1)],
  .up 4099 1,
  .rs 4099 1 12,
  .par2 70841 4099,
  .force 800281 1 [(3, 4), (11, 2), (19, 6), (2017, 2), (4099, 2), (11807, 2), (70841, 1)],
  .up 800281 1,
  .rs 800281 1 6,
  .par2 70841 800281,
  .force 48071041 1 [(3, 4), (11, 2), (19, 6), (2017, 2), (4099, 2), (11807, 2), (70841, 1), (800281, 2)],
  .up 48071041 1,
  .big [(3, 4), (11, 2), (19, 6), (2017, 2), (4099, 2), (11807, 2), (70841, 1), (800281, 2)],
  .big [(3, 4), (11, 2), (19, 6), (2017, 2), (4099, 2), (11807, 2), (70841, 1), (800281, 4)],
  .big [(3, 4), (11, 2), (19, 6), (2017, 2), (4099, 2), (11807, 2), (70841, 1)],
  .force 369023021 1 [(3, 4), (11, 2), (19, 6), (2017, 2), (4099, 4), (11807, 2), (70841, 1)],
  .up 369023021 1,
  .big [(3, 4), (11, 2), (19, 6), (2017, 2), (4099, 4), (11807, 2), (70841, 1)],
  .big [(3, 4), (11, 2), (19, 6), (2017, 2), (4099, 6), (11807, 2), (70841, 1)],
  .big [(3, 4), (11, 2), (19, 6), (2017, 2), (4099, 10), (11807, 2), (70841, 1)],
  .big [(3, 4), (11, 2), (19, 6), (2017, 2), (11807, 2), (70841, 1)],
  .force 617341 1 [(3, 4), (11, 2), (19, 6), (2017, 4), (11807, 2), (70841, 1)],
  .up 617341 1,
  .rs 617341 1 6,
  .par2 70841 617341,
  .force 39409 1 [(3, 4), (11, 2), (19, 6), (2017, 4), (11807, 2), (70841, 1), (617341, 2)],
  .up 39409 1,
  .big [(3, 4), (11, 2), (19, 6), (2017, 4), (11807, 2), (70841, 1), (617341, 2)],
  .big [(3, 4), (11, 2), (19, 6), (2017, 4), (11807, 2), (70841, 1), (617341, 4)],
  .big [(3, 4), (11, 2), (19, 6), (2017, 4), (11807, 2), (70841, 1)],
  .force 1727870509 1 [(3, 4), (11, 2), (19, 6), (2017, 6), (11807, 2), (70841, 1)],
  .up 1727870509 1,
  .big [(3, 4), (11, 2), (19, 6), (2017, 6), (11807, 2), (70841, 1)],
  .big [(3, 4), (11, 2), (19, 6), (2017, 10), (11807, 2), (70841, 1)],
  .big [(3, 4), (11, 2), (19, 6), (2017, 12), (11807, 2), (70841, 1)],
  .big [(3, 4), (11, 2), (19, 6), (11807, 2), (70841, 1)],
  .force 280257881 1 [(3, 4), (11, 2), (19, 6), (11807, 4), (70841, 1)],
  .up 280257881 1,
  .rs 280257881 1 6,
  .par2 70841 280257881,
  .force 596514349 1 [(3, 4), (11, 2), (19, 6), (11807, 4), (70841, 1), (280257881, 2)],
  .up 596514349 1,
  .big [(3, 4), (11, 2), (19, 6), (11807, 4), (70841, 1), (280257881, 2)],
  .big [(3, 4), (11, 2), (19, 6), (11807, 4), (70841, 1), (280257881, 4)],
  .big [(3, 4), (11, 2), (19, 6), (11807, 4), (70841, 1)],
  .force 1807475964966137691443 1 [(3, 4), (11, 2), (19, 6), (11807, 6), (70841, 1)],
  .up 1807475964966137691443 1,
  .big [(3, 4), (11, 2), (19, 6), (11807, 6), (70841, 1)],
  .big [(3, 4), (11, 2), (19, 6), (11807, 10), (70841, 1)],
  .big [(3, 4), (11, 2), (19, 6), (11807, 12), (70841, 1)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 1)],
  .force 128341 1 [(3, 4), (11, 2), (19, 6), (70841, 2)],
  .rs 128341 1 11,
  .force 64171 1 [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 1)],
  .up 64171 1,
  .rs 64171 1 11,
  .par2 128341 64171,
  .force 39103 1 [(3, 4), (11, 2), (19, 6), (64171, 2), (70841, 2), (128341, 1)],
  .up 39103 1,
  .rs 39103 1 8,
  .par2 128341 39103,
  .force 67411 1 [(3, 4), (11, 2), (19, 6), (39103, 2), (64171, 2), (70841, 2), (128341, 1)],
  .up 67411 1,
  .rs 67411 1 5,
  .par2 128341 67411,
  .big [(3, 4), (11, 2), (19, 6), (39103, 2), (64171, 2), (67411, 2), (70841, 2), (128341, 1)],
  .big [(3, 4), (11, 2), (19, 6), (39103, 2), (64171, 2), (70841, 2), (128341, 1)],
  .big [(3, 4), (11, 2), (19, 6), (39103, 4), (64171, 2), (70841, 2), (128341, 1)],
  .big [(3, 4), (11, 2), (19, 6), (39103, 6), (64171, 2), (70841, 2), (128341, 1)],
  .big [(3, 4), (11, 2), (19, 6), (64171, 2), (70841, 2), (128341, 1)],
  .force 33579221106357041 1 [(3, 4), (11, 2), (19, 6), (64171, 4), (70841, 2), (128341, 1)],
  .up 33579221106357041 1,
  .big [(3, 4), (11, 2), (19, 6), (64171, 4), (70841, 2), (128341, 1)],
  .big [(3, 4), (11, 2), (19, 6), (64171, 6), (70841, 2), (128341, 1)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 1)],
  .force 5490513541 1 [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 2)],
  .rs 5490513541 1 6,
  .force 2745256771 1 [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 2), (5490513541, 1)],
  .up 2745256771 1,
  .rs 2745256771 1 5,
  .par2 5490513541 2745256771,
  .big [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 2), (2745256771, 2), (5490513541, 1)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 2), (5490513541, 1)],
  .force 1435511378542612963 1 [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 2), (5490513541, 2)],
  .up 1435511378542612963 1,
  .big [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 2), (5490513541, 2)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 2), (5490513541, 4)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 2)],
  .force 12833941 1 [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 4)],
  .rs 12833941 1 4,
  .force 1058821 1 [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 4), (12833941, 1)],
  .up 1058821 1,
  .big [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 4), (12833941, 1)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 4), (12833941, 2)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 4)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 2), (128341, 6)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 2)],
  .force 1163018639068051 1 [(3, 4), (11, 2), (19, 6), (70841, 4)],
  .up 1163018639068051 1,
  .rs 1163018639068051 1 4,
  .parS 1163018639068051,
  .big [(3, 4), (11, 2), (19, 6), (70841, 4), (1163018639068051, 2)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 4)],
  .force 98811777493935291929249 1 [(3, 4), (11, 2), (19, 6), (70841, 6)],
  .rs 98811777493935291929249 1 3,
  .big [(3, 4), (11, 2), (19, 6), (70841, 6), (98811777493935291929249, 1)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 6)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 10)],
  .big [(3, 4), (11, 2), (19, 6), (70841, 12)],
  .big [(3, 4), (11, 2), (19, 6)],
  .force 62060021 1 [(3, 4), (11, 2), (19, 10)],
  .rs 62060021 1 9,
  .force 104281 1 [(3, 4), (11, 2), (19, 10), (62060021, 1)],
  .up 104281 1,
  .rs 104281 1 11,
  .par2 62060021 104281,
  .force 179743 1 [(3, 4), (11, 2), (19, 10), (104281, 2), (62060021, 1)],
  .up 179743 1,
  .rs 179743 1 8,
  .par2 62060021 179743,
  .force 49627843 1 [(3, 4), (11, 2), (19, 10), (104281, 2), (179743, 2), (62060021, 1)],
  .up 49627843 1,
  .rs 49627843 1 4,
  .par2 62060021 49627843,
  .big [(3, 4), (11, 2), (19, 10), (104281, 2), (179743, 2), (49627843, 2), (62060021, 1)],
  .big [(3, 4), (11, 2), (19, 10), (104281, 2), (179743, 2), (62060021, 1)],
  .big [(3, 4), (11, 2), (19, 10), (104281, 2), (179743, 4), (62060021, 1)],
  .big [(3, 4), (11, 2), (19, 10), (104281, 2), (179743, 6), (62060021, 1)],
  .big [(3, 4), (11, 2), (19, 10), (104281, 2), (62060021, 1)],
  .force 181345750520141 1 [(3, 4), (11, 2), (19, 10), (104281, 4), (62060021, 1)],
  .up 181345750520141 1,
  .big [(3, 4), (11, 2), (19, 10), (104281, 4), (62060021, 1)],
  .big [(3, 4), (11, 2), (19, 10), (104281, 6), (62060021, 1)],
  .big [(3, 4), (11, 2), (19, 10), (62060021, 1)],
  .force 17748600316039 1 [(3, 4), (11, 2), (19, 10), (62060021, 2)],
  .up 17748600316039 1,
  .rs 17748600316039 1 4,
  .parS 17748600316039,
  .big [(3, 4), (11, 2), (19, 10), (62060021, 2), (17748600316039, 2)],
  .big [(3, 4), (11, 2), (19, 10), (62060021, 2)],
  .big [(3, 4), (11, 2), (19, 10), (62060021, 4)],
  .big [(3, 4), (11, 2), (19, 10), (62060021, 6)],
  .big [(3, 4), (11, 2), (19, 10)],
  .force 133338869 1 [(3, 4), (11, 2), (19, 12)],
  .rs 133338869 1 8,
  .force 29251 1 [(3, 4), (11, 2), (19, 12), (133338869, 1)],
  .up 29251 1,
  .rs 29251 1 11,
  .par2 133338869 29251,
  .force 1477807 1 [(3, 4), (11, 2), (19, 12), (29251, 2), (133338869, 1)],
  .up 1477807 1,
  .rs 1477807 1 6,
  .par2 133338869 1477807,
  .force 2167621 1 [(3, 4), (11, 2), (19, 12), (29251, 2), (1477807, 2), (133338869, 1)],
  .up 2167621 1,
  .big [(3, 4), (11, 2), (19, 12), (29251, 2), (1477807, 2), (133338869, 1)],
  .big [(3, 4), (11, 2), (19, 12), (29251, 2), (1477807, 4), (133338869, 1)],
  .big [(3, 4), (11, 2), (19, 12), (29251, 2), (133338869, 1)],
  .force 3571279638916061 1 [(3, 4), (11, 2), (19, 12), (29251, 4), (133338869, 1)],
  .up 3571279638916061 1,
  .big [(3, 4), (11, 2), (19, 12), (29251, 4), (133338869, 1)],
  .big [(3, 4), (11, 2), (19, 12), (29251, 6), (133338869, 1)],
  .big [(3, 4), (11, 2), (19, 12), (133338869, 1)],
  .force 316950847 1 [(3, 4), (11, 2), (19, 12), (133338869, 2)],
  .up 316950847 1,
  .rs 316950847 1 5,
  .parS 316950847,
  .big [(3, 4), (11, 2), (19, 12), (133338869, 2), (316950847, 2)],
  .big [(3, 4), (11, 2), (19, 12), (133338869, 2)],
  .big [(3, 4), (11, 2), (19, 12), (133338869, 4)],
  .big [(3, 4), (11, 2), (19, 12), (133338869, 6)],
  .big [(3, 4), (11, 2), (19, 12)],
  .force 99995282631947 1 [(3, 4), (11, 2), (19, 16)],
  .up 99995282631947 1,
  .rs 99995282631947 1 5,
  .parS 99995282631947,
  .big [(3, 4), (11, 2), (19, 16), (99995282631947, 2)],
  .big [(3, 4), (11, 2), (19, 16)],
  .force 109912203092239643840221 1 [(3, 4), (11, 2), (19, 18)],
  .rs 109912203092239643840221 1 4,
  .force 16842464147039939 1 [(3, 4), (11, 2), (19, 18), (109912203092239643840221, 1)],
  .up 16842464147039939 1,
  .big [(3, 4), (11, 2), (19, 18), (109912203092239643840221, 1)],
  .big [(3, 4), (11, 2), (19, 18), (109912203092239643840221, 2)],
  .big [(3, 4), (11, 2), (19, 18)],
  .force 1335495402823 1 [(3, 4), (11, 2), (19, 22)],
  .up 1335495402823 1,
  .rs 1335495402823 1 4,
  .parS 1335495402823,
  .big [(3, 4), (11, 2), (19, 22), (1335495402823, 2)],
  .big [(3, 4), (11, 2), (19, 22)],
  .force 165049085515149863 1 [(3, 4), (11, 2), (19, 28)],
  .up 165049085515149863 1,
  .big [(3, 4), (11, 2), (19, 28)],
  .big [(3, 4), (11, 2), (19, 30)],
  .big [(3, 4), (11, 2), (19, 36)],
  .big [(3, 4), (11, 2), (19, 40)],
  .big [(3, 4), (11, 2), (19, 42)],
  .big [(3, 4), (11, 2), (19, 46)],
  .big [(3, 4), (11, 2), (19, 52)],
  .big [(3, 4), (11, 2)],
  .force 3221 1 [(3, 4), (11, 4)],
  .rs 3221 1 22,
  .force 179 1 [(3, 4), (11, 4), (3221, 1)],
  .up 179 1,
  .rs 179 1 32,
  .par2 3221 179,
  .force 4603 1 [(3, 4), (11, 4), (179, 2), (3221, 1)],
  .up 4603 1,
  .rs 4603 1 19,
  .par2 3221 4603,
  .force 1009153 1 [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 2)],
  .up 1009153 1,
  .rs 1009153 1 11,
  .par2 3221 1009153,
  .force 459355339 1 [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 2), (1009153, 2)],
  .up 459355339 1,
  .rs 459355339 1 6,
  .par2 3221 459355339,
  .force 66027296779 1 [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 2), (1009153, 2), (459355339, 2)],
  .up 66027296779 1,
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 2), (1009153, 2), (459355339, 2)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 2), (1009153, 2), (459355339, 4)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 2), (1009153, 2)],
  .force 82191045331 1 [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 2), (1009153, 4)],
  .up 82191045331 1,
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 2), (1009153, 4)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 2), (1009153, 6)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 2)],
  .force 214891 1 [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 4)],
  .up 214891 1,
  .rs 214891 1 9,
  .par2 3221 214891,
  .force 431521 1 [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 4), (214891, 2)],
  .up 431521 1,
  .rs 431521 1 6,
  .par2 3221 431521,
  .force 785699599 1 [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 4), (214891, 2), (431521, 2)],
  .up 785699599 1,
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 4), (214891, 2), (431521, 2)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 4), (214891, 2), (431521, 4)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 4), (214891, 2)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 4), (214891, 4)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 4), (214891, 6)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 4)],
  .force 693696942149 1 [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 6)],
  .up 693696942149 1,
  .rs 693696942149 1 4,
  .par2 3221 693696942149,
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 6), (693696942149, 2)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 6)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 10)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 12)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1), (4603, 16)],
  .big [(3, 4), (11, 4), (179, 2), (3221, 1)],
  .force 93853931 1 [(3, 4), (11, 4), (179, 4), (3221, 1)],
  .up 93853931 1,
  .rs 93853931 1 9,
  .par2 3221 93853931,
  .force 628561 1 [(3, 4), (11, 4), (179, 4), (3221, 1), (93853931, 2)],
  .up 628561 1,
  .rs 628561 1 7,
  .par2 3221 628561,
  .force 7440061 1 [(3, 4), (11, 4), (179, 4), (3221, 1), (628561, 2), (93853931, 2)],
  .up 7440061 1,
  .rs 7440061 1 4,
  .par2 3221 7440061,
  .big [(3, 4), (11, 4), (179, 4), (3221, 1), (628561, 2), (7440061, 2), (93853931, 2)],
  .big [(3, 4), (11, 4), (179, 4), (3221, 1), (628561, 2), (93853931, 2)],
  .big [(3, 4), (11, 4), (179, 4), (3221, 1), (628561, 4), (93853931, 2)],
  .big [(3, 4), (11, 4), (179, 4), (3221, 1), (93853931, 2)],
  .big [(3, 4), (11, 4), (179, 4), (3221, 1), (93853931, 4)],
  .big [(3, 4), (11, 4), (179, 4), (3221, 1), (93853931, 6)],
  .big [(3, 4), (11, 4), (179, 4), (3221, 1)],
  .force 465900166691 1 [(3, 4), (11, 4), (179, 6), (3221, 1)],
  .up 465900166691 1,
  .rs 465900166691 1 6,
  .par2 3221 465900166691,
  .force 434995922491317607327 1 [(3, 4), (11, 4), (179, 6), (3221, 1), (465900166691, 2)],
  .up 434995922491317607327 1,
  .big [(3, 4), (11, 4), (179, 6), (3221, 1), (465900166691, 2)],
  .big [(3, 4), (11, 4), (179, 6), (3221, 1), (465900166691, 4)],
  .big [(3, 4), (11, 4), (179, 6), (3221, 1)],
  .force 973116649840171 1 [(3, 4), (11, 4), (179, 10), (3221, 1)],
  .up 973116649840171 1,
  .rs 973116649840171 1 4,
  .par2 3221 973116649840171,
  .big [(3, 4), (11, 4), (179, 10), (3221, 1), (973116649840171, 2)],
  .big [(3, 4), (11, 4), (179, 10), (3221, 1)],
  .force 94597128022319068199 1 [(3, 4), (11, 4), (179, 12), (3221, 1)],
  .up 94597128022319068199 1,
  .big [(3, 4), (11, 4), (179, 12), (3221, 1)],
  .big [(3, 4), (11, 4), (179, 16), (3221, 1)],
  .big [(3, 4), (11, 4), (179, 18), (3221, 1)],
  .big [(3, 4), (11, 4), (179, 22), (3221, 1)],
  .big [(3, 4), (11, 4), (179, 28), (3221, 1)],
  .big [(3, 4), (11, 4), (179, 30), (3221, 1)],
  .big [(3, 4), (11, 4), (3221, 1)],
  .force 10378063 1 [(3, 4), (11, 4), (3221, 2)],
  .up 10378063 1,
  .rs 10378063 1 11,
  .parS 10378063,
  .force 46685826619 1 [(3, 4), (11, 4), (3221, 2), (10378063, 2)],
  .up 46685826619 1,
  .rs 46685826619 1 6,
  .parS 46685826619,
  .force 399403 1 [(3, 4), (11, 4), (3221, 2), (10378063, 2), (46685826619, 2)],
  .up 399403 1,
  .rs 399403 1 4,
  .parS 399403,
  .big [(3, 4), (11, 4), (3221, 2), (399403, 2), (10378063, 2), (46685826619, 2)],
  .big [(3, 4), (11, 4), (3221, 2), (10378063, 2), (46685826619, 2)],
  .big [(3, 4), (11, 4), (3221, 2), (10378063, 2), (46685826619, 4)],
  .big [(3, 4), (11, 4), (3221, 2), (10378063, 2)],
  .force 31810898376456201755581 1 [(3, 4), (11, 4), (3221, 2), (10378063, 4)],
  .rs 31810898376456201755581 1 3,
  .big [(3, 4), (11, 4), (3221, 2), (10378063, 4), (31810898376456201755581, 1)],
  .big [(3, 4), (11, 4), (3221, 2), (10378063, 4)],
  .big [(3, 4), (11, 4), (3221, 2), (10378063, 6)],
  .big [(3, 4), (11, 4), (3221, 2)],
  .force 1957650063931 1 [(3, 4), (11, 4), (3221, 4)],
  .up 1957650063931 1,
  .rs 1957650063931 1 6,
  .parS 1957650063931,
  .force 15683402202973 1 [(3, 4), (11, 4), (3221, 4), (1957650063931, 2)],
  .rs 15683402202973 1 3,
  .big [(3, 4), (11, 4), (3221, 4), (1957650063931, 2), (15683402202973, 1)],
  .big [(3, 4), (11, 4), (3221, 4), (1957650063931, 2)],
  .big [(3, 4), (11, 4), (3221, 4), (1957650063931, 4)],
  .big [(3, 4), (11, 4), (3221, 4)],
  .force 92204351 1 [(3, 4), (11, 4), (3221, 6)],
  .up 92204351 1,
  .rs 92204351 1 6,
  .parS 92204351,
  .force 7698853 1 [(3, 4), (11, 4), (3221, 6), (92204351, 2)],
  .rs 7698853 1 3,
  .big [(3, 4), (11, 4), (3221, 6), (7698853, 1), (92204351, 2)],
  .big [(3, 4), (11, 4), (3221, 6), (92204351, 2)],
  .big [(3, 4), (11, 4), (3221, 6), (92204351, 4)],
  .big [(3, 4), (11, 4), (3221, 6)],
  .force 315163118203085670683224621 1 [(3, 4), (11, 4), (3221, 10)],
  .rs 315163118203085670683224621 1 3,
  .big [(3, 4), (11, 4), (3221, 10), (315163118203085670683224621, 1)],
  .big [(3, 4), (11, 4), (3221, 10)],
  .big [(3, 4), (11, 4), (3221, 12)],
  .big [(3, 4), (11, 4), (3221, 16)],
  .big [(3, 4), (11, 4), (3221, 18)],
  .big [(3, 4), (11, 4)],
  .force 45319 1 [(3, 4), (11, 6)],
  .up 45319 1,
  .rs 45319 1 16,
  .parS 45319,
  .force 5390701 1 [(3, 4), (11, 6), (45319, 2)],
  .rs 5390701 1 10,
  .force 2695351 1 [(3, 4), (11, 6), (45319, 2), (5390701, 1)],
  .up 2695351 1]

/-- Instructions, part 8. -/
def tree3_8 : List Ins := [
  .rs 2695351 1 9,
  .par2 5390701 2695351,
  .force 316264843 1 [(3, 4), (11, 6), (45319, 2), (2695351, 2), (5390701, 1)],
  .up 316264843 1,
  .rs 316264843 1 6,
  .par2 5390701 316264843,
  .force 10965013 1 [(3, 4), (11, 6), (45319, 2), (2695351, 2), (5390701, 1), (316264843, 2)],
  .up 10965013 1,
  .big [(3, 4), (11, 6), (45319, 2), (2695351, 2), (5390701, 1), (316264843, 2)],
  .big [(3, 4), (11, 6), (45319, 2), (2695351, 2), (5390701, 1), (316264843, 4)],
  .big [(3, 4), (11, 6), (45319, 2), (2695351, 2), (5390701, 1)],
  .big [(3, 4), (11, 6), (45319, 2), (2695351, 4), (5390701, 1)],
  .big [(3, 4), (11, 6), (45319, 2), (2695351, 6), (5390701, 1)],
  .big [(3, 4), (11, 6), (45319, 2), (5390701, 1)],
  .force 186709 1 [(3, 4), (11, 6), (45319, 2), (5390701, 2)],
  .rs 186709 1 8,
  .force 18671 1 [(3, 4), (11, 6), (45319, 2), (186709, 1), (5390701, 2)],
  .up 18671 1,
  .rs 18671 1 9,
  .par2 186709 18671,
  .force 3831043 1 [(3, 4), (11, 6), (18671, 2), (45319, 2), (186709, 1), (5390701, 2)],
  .up 3831043 1,
  .rs 3831043 1 5,
  .par2 186709 3831043,
  .big [(3, 4), (11, 6), (18671, 2), (45319, 2), (186709, 1), (3831043, 2), (5390701, 2)],
  .big [(3, 4), (11, 6), (18671, 2), (45319, 2), (186709, 1), (5390701, 2)],
  .big [(3, 4), (11, 6), (18671, 4), (45319, 2), (186709, 1), (5390701, 2)],
  .big [(3, 4), (11, 6), (18671, 6), (45319, 2), (186709, 1), (5390701, 2)],
  .big [(3, 4), (11, 6), (45319, 2), (186709, 1), (5390701, 2)],
  .force 7038247 1 [(3, 4), (11, 6), (45319, 2), (186709, 2), (5390701, 2)],
  .up 7038247 1,
  .rs 7038247 1 5,
  .parS 7038247,
  .big [(3, 4), (11, 6), (45319, 2), (186709, 2), (5390701, 2), (7038247, 2)],
  .big [(3, 4), (11, 6), (45319, 2), (186709, 2), (5390701, 2)],
  .big [(3, 4), (11, 6), (45319, 2), (186709, 4), (5390701, 2)],
  .big [(3, 4), (11, 6), (45319, 2), (186709, 6), (5390701, 2)],
  .big [(3, 4), (11, 6), (45319, 2), (5390701, 2)],
  .force 2768733893059808474864941 1 [(3, 4), (11, 6), (45319, 2), (5390701, 4)],
  .rs 2768733893059808474864941 1 3,
  .big [(3, 4), (11, 6), (45319, 2), (5390701, 4), (2768733893059808474864941, 1)],
  .big [(3, 4), (11, 6), (45319, 2), (5390701, 4)],
  .big [(3, 4), (11, 6), (45319, 2), (5390701, 6)],
  .big [(3, 4), (11, 6), (45319, 2)],
  .force 27935336611728311 1 [(3, 4), (11, 6), (45319, 4)],
  .up 27935336611728311 1,
  .rs 27935336611728311 1 4,
  .parS 27935336611728311,
  .big [(3, 4), (11, 6), (45319, 4), (27935336611728311, 2)],
  .big [(3, 4), (11, 6), (45319, 4)],
  .force 351597737 1 [(3, 4), (11, 6), (45319, 6)],
  .rs 351597737 1 4,
  .force 108866969 1 [(3, 4), (11, 6), (45319, 6), (351597737, 1)],
  .up 108866969 1,
  .big [(3, 4), (11, 6), (45319, 6), (351597737, 1)],
  .big [(3, 4), (11, 6), (45319, 6), (351597737, 2)],
  .big [(3, 4), (11, 6), (45319, 6)],
  .big [(3, 4), (11, 6), (45319, 10)],
  .big [(3, 4), (11, 6), (45319, 12)],
  .big [(3, 4), (11, 6)],
  .force 1806113 1 [(3, 4), (11, 10)],
  .rs 1806113 1 11,
  .force 17707 1 [(3, 4), (11, 10), (1806113, 1)],
  .up 17707 1,
  .rs 17707 1 14,
  .par2 1806113 17707,
  .force 2133031 1 [(3, 4), (11, 10), (17707, 2), (1806113, 1)],
  .up 2133031 1,
  .rs 2133031 1 9,
  .par2 1806113 2133031,
  .force 1516607793331 1 [(3, 4), (11, 10), (17707, 2), (1806113, 1), (2133031, 2)],
  .up 1516607793331 1,
  .rs 1516607793331 1 4,
  .par2 1806113 1516607793331,
  .big [(3, 4), (11, 10), (17707, 2), (1806113, 1), (2133031, 2), (1516607793331, 2)],
  .big [(3, 4), (11, 10), (17707, 2), (1806113, 1), (2133031, 2)],
  .big [(3, 4), (11, 10), (17707, 2), (1806113, 1), (2133031, 4)],
  .big [(3, 4), (11, 10), (17707, 2), (1806113, 1), (2133031, 6)],
  .big [(3, 4), (11, 10), (17707, 2), (1806113, 1)],
  .force 98311534883794601 1 [(3, 4), (11, 10), (17707, 4), (1806113, 1)],
  .up 98311534883794601 1,
  .rs 98311534883794601 1 4,
  .par2 1806113 98311534883794601,
  .big [(3, 4), (11, 10), (17707, 4), (1806113, 1), (98311534883794601, 2)],
  .big [(3, 4), (11, 10), (17707, 4), (1806113, 1)],
  .force 30824387179353424155370957 1 [(3, 4), (11, 10), (17707, 6), (1806113, 1)],
  .up 30824387179353424155370957 1,
  .big [(3, 4), (11, 10), (17707, 6), (1806113, 1)],
  .big [(3, 4), (11, 10), (17707, 10), (1806113, 1)],
  .big [(3, 4), (11, 10), (17707, 12), (1806113, 1)],
  .big [(3, 4), (11, 10), (1806113, 1)],
  .force 171686630257 1 [(3, 4), (11, 10), (1806113, 2)],
  .rs 171686630257 1 6,
  .force 77689 1 [(3, 4), (11, 10), (1806113, 2), (171686630257, 1)],
  .up 77689 1,
  .rs 77689 1 8,
  .par2 171686630257 77689,
  .force 54375301 1 [(3, 4), (11, 10), (77689, 2), (1806113, 2), (171686630257, 1)],
  .up 54375301 1,
  .rs 54375301 1 4,
  .par2 171686630257 54375301,
  .big [(3, 4), (11, 10), (77689, 2), (1806113, 2), (54375301, 2), (171686630257, 1)],
  .big [(3, 4), (11, 10), (77689, 2), (1806113, 2), (171686630257, 1)],
  .big [(3, 4), (11, 10), (77689, 4), (1806113, 2), (171686630257, 1)],
  .big [(3, 4), (11, 10), (77689, 6), (1806113, 2), (171686630257, 1)],
  .big [(3, 4), (11, 10), (1806113, 2), (171686630257, 1)],
  .force 2155876969481479 1 [(3, 4), (11, 10), (1806113, 2), (171686630257, 2)],
  .up 2155876969481479 1,
  .big [(3, 4), (11, 10), (1806113, 2), (171686630257, 2)],
  .big [(3, 4), (11, 10), (1806113, 2), (171686630257, 4)],
  .big [(3, 4), (11, 10), (1806113, 2)],
  .force 69710210289691 1 [(3, 4), (11, 10), (1806113, 4)],
  .up 69710210289691 1,
  .big [(3, 4), (11, 10), (1806113, 4)],
  .big [(3, 4), (11, 10), (1806113, 6)],
  .big [(3, 4), (11, 10)],
  .force 3158528101 1 [(3, 4), (11, 12)],
  .rs 3158528101 1 8,
  .force 1579264051 1 [(3, 4), (11, 12), (3158528101, 1)],
  .up 1579264051 1,
  .rs 1579264051 1 7,
  .par2 3158528101 1579264051,
  .force 43755700778249029 1 [(3, 4), (11, 12), (1579264051, 2), (3158528101, 1)],
  .up 43755700778249029 1,
  .big [(3, 4), (11, 12), (1579264051, 2), (3158528101, 1)],
  .big [(3, 4), (11, 12), (1579264051, 4), (3158528101, 1)],
  .big [(3, 4), (11, 12), (3158528101, 1)],
  .force 3325433255988398101 1 [(3, 4), (11, 12), (3158528101, 2)],
  .rs 3325433255988398101 1 4,
  .force 31012561 1 [(3, 4), (11, 12), (3158528101, 2), (3325433255988398101, 1)],
  .up 31012561 1,
  .big [(3, 4), (11, 12), (3158528101, 2), (3325433255988398101, 1)],
  .big [(3, 4), (11, 12), (3158528101, 2), (3325433255988398101, 2)],
  .big [(3, 4), (11, 12), (3158528101, 2)],
  .big [(3, 4), (11, 12), (3158528101, 4)],
  .big [(3, 4), (11, 12), (3158528101, 6)],
  .big [(3, 4), (11, 12)],
  .force 50544702849929377 1 [(3, 4), (11, 16)],
  .rs 50544702849929377 1 5,
  .force 239337374873 1 [(3, 4), (11, 16), (50544702849929377, 1)],
  .up 239337374873 1,
  .rs 239337374873 1 5,
  .par2 50544702849929377 239337374873,
  .big [(3, 4), (11, 16), (239337374873, 2), (50544702849929377, 1)],
  .big [(3, 4), (11, 16), (50544702849929377, 1)],
  .big [(3, 4), (11, 16), (50544702849929377, 2)],
  .big [(3, 4), (11, 16)],
  .force 6115909044841454629 1 [(3, 4), (11, 18)],
  .rs 6115909044841454629 1 5,
  .force 278218153 1 [(3, 4), (11, 18), (6115909044841454629, 1)],
  .up 278218153 1,
  .rs 278218153 1 5,
  .par2 6115909044841454629 278218153,
  .big [(3, 4), (11, 18), (278218153, 2), (6115909044841454629, 1)],
  .big [(3, 4), (11, 18), (6115909044841454629, 1)],
  .big [(3, 4), (11, 18), (6115909044841454629, 2)],
  .big [(3, 4), (11, 18)],
  .force 3740221981231 1 [(3, 4), (11, 22)],
  .up 3740221981231 1,
  .rs 3740221981231 1 5,
  .parS 3740221981231,
  .big [(3, 4), (11, 22), (3740221981231, 2)],
  .big [(3, 4), (11, 22)],
  .force 303309617049998388989376043 1 [(3, 4), (11, 28)],
  .up 303309617049998388989376043 1,
  .big [(3, 4), (11, 28)],
  .force 157571957584602258799 1 [(3, 4), (11, 30)],
  .up 157571957584602258799 1,
  .big [(3, 4), (11, 30)],
  .force 2615418118891695851 1 [(3, 4), (11, 36)],
  .up 2615418118891695851 1,
  .big [(3, 4), (11, 36)],
  .big [(3, 4), (11, 40)],
  .big [(3, 4), (11, 42)],
  .big [(3, 4), (11, 46)],
  .big [(3, 4), (11, 52)],
  .big [(3, 4), (11, 58)],
  .big [(3, 4), (11, 60)],
  .big [(3, 4), (11, 66)],
  .big [(3, 4), (11, 70)],
  .big [(3, 4), (11, 72)],
  .big [(3, 4)],
  .force 1093 1 [(3, 6)],
  .rs 1093 1 27,
  .force 547 1 [(3, 6), (1093, 1)],
  .up 547 1,
  .rs 547 1 28,
  .par2 1093 547,
  .force 613 1 [(3, 6), (547, 2), (1093, 1)],
  .up 613 1,
  .rs 613 1 25,
  .par2 1093 613,
  .force 17923 1 [(3, 6), (547, 2), (613, 2), (1093, 1)],
  .up 17923 1,
  .rs 17923 1 15,
  .par2 1093 17923,
  .force 265717 1 [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 2)],
  .up 265717 1,
  .rs 265717 1 10,
  .par2 1093 265717,
  .force 3362180467 1 [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 2), (265717, 2)],
  .up 3362180467 1,
  .rs 3362180467 1 5,
  .par2 1093 3362180467,
  .big [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 2), (265717, 2), (3362180467, 2)],
  .big [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 2), (265717, 2)],
  .force 38833995162778271 1 [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 2), (265717, 4)],
  .up 38833995162778271 1,
  .big [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 2), (265717, 4)],
  .big [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 2), (265717, 6)],
  .big [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 2)],
  .force 343540871 1 [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 4)],
  .up 343540871 1,
  .rs 343540871 1 5,
  .par2 1093 343540871,
  .big [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 4), (343540871, 2)],
  .big [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 4)],
  .force 28769600332597803883 1 [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 6)],
  .up 28769600332597803883 1,
  .big [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 6)],
  .big [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 10)],
  .big [(3, 6), (547, 2), (613, 2), (1093, 1), (17923, 12)],
  .big [(3, 6), (547, 2), (613, 2), (1093, 1)],
  .force 53551 1 [(3, 6), (547, 2), (613, 4), (1093, 1)],
  .up 53551 1,
  .rs 53551 1 12,
  .par2 1093 53551,
  .force 955921051 1 [(3, 6), (547, 2), (613, 4), (1093, 1), (53551, 2)],
  .up 955921051 1,
  .rs 955921051 1 6,
  .par2 1093 955921051,
  .force 85584439140289 1 [(3, 6), (547, 2), (613, 4), (1093, 1), (53551, 2), (955921051, 2)],
  .up 85584439140289 1,
  .big [(3, 6), (547, 2), (613, 4), (1093, 1), (53551, 2), (955921051, 2)],
  .big [(3, 6), (547, 2), (613, 4), (1093, 1), (53551, 2), (955921051, 4)],
  .big [(3, 6), (547, 2), (613, 4), (1093, 1), (53551, 2)],
  .force 1235534918771 1 [(3, 6), (547, 2), (613, 4), (1093, 1), (53551, 4)],
  .up 1235534918771 1,
  .big [(3, 6), (547, 2), (613, 4), (1093, 1), (53551, 4)],
  .big [(3, 6), (547, 2), (613, 4), (1093, 1), (53551, 6)],
  .big [(3, 6), (547, 2), (613, 4), (1093, 1), (53551, 10)],
  .big [(3, 6), (547, 2), (613, 4), (1093, 1)],
  .force 312410911 1 [(3, 6), (547, 2), (613, 6), (1093, 1)],
  .up 312410911 1,
  .rs 312410911 1 6,
  .par2 1093 312410911,
  .force 199592183280697 1 [(3, 6), (547, 2), (613, 6), (1093, 1), (312410911, 2)],
  .up 199592183280697 1,
  .big [(3, 6), (547, 2), (613, 6), (1093, 1), (312410911, 2)],
  .big [(3, 6), (547, 2), (613, 6), (1093, 1), (312410911, 4)],
  .big [(3, 6), (547, 2), (613, 6), (1093, 1)],
  .force 445455365264339 1 [(3, 6), (547, 2), (613, 10), (1093, 1)],
  .up 445455365264339 1,
  .big [(3, 6), (547, 2), (613, 10), (1093, 1)],
  .big [(3, 6), (547, 2), (613, 12), (1093, 1)],
  .big [(3, 6), (547, 2), (613, 16), (1093, 1)],
  .big [(3, 6), (547, 2), (613, 18), (1093, 1)],
  .big [(3, 6), (547, 2), (613, 22), (1093, 1)],
  .big [(3, 6), (547, 2), (1093, 1)],
  .force 208097431 1 [(3, 6), (547, 4), (1093, 1)],
  .up 208097431 1,
  .rs 208097431 1 9,
  .par2 1093 208097431,
  .force 26209 1 [(3, 6), (547, 4), (1093, 1), (208097431, 2)],
  .up 26209 1,
  .rs 26209 1 9,
  .par2 1093 26209,
  .force 228979297 1 [(3, 6), (547, 4), (1093, 1), (26209, 2), (208097431, 2)],
  .up 228979297 1,
  .rs 228979297 1 4,
  .par2 1093 228979297,
  .big [(3, 6), (547, 4), (1093, 1), (26209, 2), (208097431, 2), (228979297, 2)],
  .big [(3, 6), (547, 4), (1093, 1), (26209, 2), (208097431, 2)],
  .big [(3, 6), (547, 4), (1093, 1), (26209, 4), (208097431, 2)],
  .big [(3, 6), (547, 4), (1093, 1), (26209, 6), (208097431, 2)],
  .big [(3, 6), (547, 4), (1093, 1), (208097431, 2)],
  .big [(3, 6), (547, 4), (1093, 1), (208097431, 4)],
  .big [(3, 6), (547, 4), (1093, 1), (208097431, 6)],
  .big [(3, 6), (547, 4), (1093, 1)],
  .force 132197305635599 1 [(3, 6), (547, 6), (1093, 1)],
  .up 132197305635599 1,
  .rs 132197305635599 1 5,
  .par2 1093 132197305635599,
  .big [(3, 6), (547, 6), (1093, 1), (132197305635599, 2)],
  .big [(3, 6), (547, 6), (1093, 1)],
  .force 9630092768572369626677 1 [(3, 6), (547, 10), (1093, 1)],
  .up 9630092768572369626677 1,
  .big [(3, 6), (547, 10), (1093, 1)],
  .force 12560063349523 1 [(3, 6), (547, 12), (1093, 1)],
  .up 12560063349523 1,
  .big [(3, 6), (547, 12), (1093, 1)],
  .big [(3, 6), (547, 16), (1093, 1)],
  .big [(3, 6), (547, 18), (1093, 1)],
  .big [(3, 6), (547, 22), (1093, 1)],
  .big [(3, 6), (1093, 1)],
  .force 398581 1 [(3, 6), (1093, 2)],
  .rs 398581 1 14,
  .force 617 1 [(3, 6), (1093, 2), (398581, 1)],
  .up 617 1,
  .rs 617 1 24,
  .par2 398581 617,
  .force 3931 1 [(3, 6), (617, 2), (1093, 2), (398581, 1)],
  .up 3931 1,
  .rs 3931 1 17,
  .par2 398581 3931,
  .force 23743 1 [(3, 6), (617, 2), (1093, 2), (3931, 2), (398581, 1)],
  .up 23743 1,
  .rs 23743 1 12,
  .par2 398581 23743,
  .force 5078863 1 [(3, 6), (617, 2), (1093, 2), (3931, 2), (23743, 2), (398581, 1)],
  .up 5078863 1,
  .rs 5078863 1 7,
  .par2 398581 5078863,
  .force 193311109 1 [(3, 6), (617, 2), (1093, 2), (3931, 2), (23743, 2), (398581, 1), (5078863, 2)],
  .up 193311109 1,
  .big [(3, 6), (617, 2), (1093, 2), (3931, 2), (23743, 2), (398581, 1), (5078863, 2)],
  .big [(3, 6), (617, 2), (1093, 2), (3931, 2), (23743, 2), (398581, 1), (5078863, 4)],
  .big [(3, 6), (617, 2), (1093, 2), (3931, 2), (23743, 2), (398581, 1)],
  .force 10464092501131 1 [(3, 6), (617, 2), (1093, 2), (3931, 2), (23743, 4), (398581, 1)],
  .up 10464092501131 1,
  .big [(3, 6), (617, 2), (1093, 2), (3931, 2), (23743, 4), (398581, 1)],
  .big [(3, 6), (617, 2), (1093, 2), (3931, 2), (23743, 6), (398581, 1)],
  .big [(3, 6), (617, 2), (1093, 2), (3931, 2), (23743, 10), (398581, 1)],
  .big [(3, 6), (617, 2), (1093, 2), (3931, 2), (398581, 1)],
  .force 4342701505151 1 [(3, 6), (617, 2), (1093, 2), (3931, 4), (398581, 1)],
  .up 4342701505151 1,
  .rs 4342701505151 1 5,
  .par2 398581 4342701505151,
  .big [(3, 6), (617, 2), (1093, 2), (3931, 4), (398581, 1), (4342701505151, 2)],
  .big [(3, 6), (617, 2), (1093, 2), (3931, 4), (398581, 1)],
  .force 22351248070103 1 [(3, 6), (617, 2), (1093, 2), (3931, 6), (398581, 1)],
  .up 22351248070103 1,
  .big [(3, 6), (617, 2), (1093, 2), (3931, 6), (398581, 1)],
  .big [(3, 6), (617, 2), (1093, 2), (3931, 10), (398581, 1)],
  .big [(3, 6), (617, 2), (1093, 2), (3931, 12), (398581, 1)],
  .big [(3, 6), (617, 2), (1093, 2), (398581, 1)],
  .force 145159381141 1 [(3, 6), (617, 4), (1093, 2), (398581, 1)],
  .up 145159381141 1,
  .rs 145159381141 1 6,
  .par2 398581 145159381141,
  .force 55439996877924151 1 [(3, 6), (617, 4), (1093, 2), (398581, 1), (145159381141, 2)],
  .up 55439996877924151 1,
  .big [(3, 6), (617, 4), (1093, 2), (398581, 1), (145159381141, 2)],
  .big [(3, 6), (617, 4), (1093, 2), (398581, 1), (145159381141, 4)],
  .big [(3, 6), (617, 4), (1093, 2), (398581, 1)],
  .force 268628879 1 [(3, 6), (617, 6), (1093, 2), (398581, 1)],
  .up 268628879 1,
  .rs 268628879 1 6,
  .par2 398581 268628879,
  .force 5524111988167 1 [(3, 6), (617, 6), (1093, 2), (398581, 1), (268628879, 2)],
  .up 5524111988167 1,
  .big [(3, 6), (617, 6), (1093, 2), (398581, 1), (268628879, 2)],
  .big [(3, 6), (617, 6), (1093, 2), (398581, 1), (268628879, 4)],
  .big [(3, 6), (617, 6), (1093, 2), (398581, 1)],
  .force 10866472977391930428570371 1 [(3, 6), (617, 10), (1093, 2), (398581, 1)],
  .up 10866472977391930428570371 1,
  .big [(3, 6), (617, 10), (1093, 2), (398581, 1)],
  .big [(3, 6), (617, 12), (1093, 2), (398581, 1)],
  .big [(3, 6), (617, 16), (1093, 2), (398581, 1)],
  .big [(3, 6), (617, 18), (1093, 2), (398581, 1)],
  .big [(3, 6), (617, 22), (1093, 2), (398581, 1)],
  .big [(3, 6), (1093, 2), (398581, 1)],
  .force 32668561 1 [(3, 6), (1093, 2), (398581, 2)],
  .rs 32668561 1 9,
  .force 19993 1 [(3, 6), (1093, 2), (398581, 2), (32668561, 1)],
  .up 19993 1,
  .rs 19993 1 12,
  .par2 32668561 19993,
  .force 1825297 1 [(3, 6), (1093, 2), (19993, 2), (398581, 2), (32668561, 1)],
  .up 1825297 1,
  .rs 1825297 1 7,
  .par2 32668561 1825297,
  .force 3397663 1 [(3, 6), (1093, 2), (19993, 2), (398581, 2), (1825297, 2), (32668561, 1)],
  .up 3397663 1,
  .rs 3397663 1 4,
  .par2 32668561 3397663,
  .big [(3, 6), (1093, 2), (19993, 2), (398581, 2), (1825297, 2), (3397663, 2), (32668561, 1)],
  .big [(3, 6), (1093, 2), (19993, 2), (398581, 2), (1825297, 2), (32668561, 1)],
  .big [(3, 6), (1093, 2), (19993, 2), (398581, 2), (1825297, 4), (32668561, 1)],
  .big [(3, 6), (1093, 2), (19993, 2), (398581, 2), (32668561, 1)],
  .force 4330075325201 1 [(3, 6), (1093, 2), (19993, 4), (398581, 2), (32668561, 1)],
  .up 4330075325201 1,
  .big [(3, 6), (1093, 2), (19993, 4), (398581, 2), (32668561, 1)],
  .big [(3, 6), (1093, 2), (19993, 6), (398581, 2), (32668561, 1)],
  .big [(3, 6), (1093, 2), (19993, 10), (398581, 2), (32668561, 1)],
  .big [(3, 6), (1093, 2), (398581, 2), (32668561, 1)],
  .force 2309087647 1 [(3, 6), (1093, 2), (398581, 2), (32668561, 2)],
  .up 2309087647 1,
  .rs 2309087647 1 5,
  .parS 2309087647,
  .big [(3, 6), (1093, 2), (398581, 2), (32668561, 2), (2309087647, 2)],
  .big [(3, 6), (1093, 2), (398581, 2), (32668561, 2)],
  .big [(3, 6), (1093, 2), (398581, 2), (32668561, 4)],
  .big [(3, 6), (1093, 2), (398581, 2), (32668561, 6)],
  .big [(3, 6), (1093, 2), (398581, 2)],
  .force 2703853428809791 1 [(3, 6), (1093, 2), (398581, 4)],
  .up 2703853428809791 1,
  .rs 2703853428809791 1 4,
  .parS 2703853428809791,
  .big [(3, 6), (1093, 2), (398581, 4), (2703853428809791, 2)]]

/-- Instructions, part 9. -/
def tree3_9 : List Ins := [
  .big [(3, 6), (1093, 2), (398581, 4)],
  .force 189361597248713 1 [(3, 6), (1093, 2), (398581, 6)],
  .rs 189361597248713 1 3,
  .big [(3, 6), (1093, 2), (398581, 6), (189361597248713, 1)],
  .big [(3, 6), (1093, 2), (398581, 6)],
  .big [(3, 6), (1093, 2), (398581, 10)],
  .big [(3, 6), (1093, 2), (398581, 12)],
  .big [(3, 6), (1093, 2)],
  .force 4189129561 1 [(3, 6), (1093, 4)],
  .rs 4189129561 1 8,
  .force 7247629 1 [(3, 6), (1093, 4), (4189129561, 1)],
  .up 7247629 1,
  .rs 7247629 1 9,
  .par2 4189129561 7247629,
  .force 2501339684251 1 [(3, 6), (1093, 4), (7247629, 2), (4189129561, 1)],
  .up 2501339684251 1,
  .rs 2501339684251 1 4,
  .par2 4189129561 2501339684251,
  .big [(3, 6), (1093, 4), (7247629, 2), (4189129561, 1), (2501339684251, 2)],
  .big [(3, 6), (1093, 4), (7247629, 2), (4189129561, 1)],
  .big [(3, 6), (1093, 4), (7247629, 4), (4189129561, 1)],
  .big [(3, 6), (1093, 4), (7247629, 6), (4189129561, 1)],
  .big [(3, 6), (1093, 4), (4189129561, 1)],
  .force 902418613 1 [(3, 6), (1093, 4), (4189129561, 2)],
  .rs 902418613 1 5,
  .force 451209307 1 [(3, 6), (1093, 4), (902418613, 1), (4189129561, 2)],
  .up 451209307 1,
  .rs 451209307 1 4,
  .par2 902418613 451209307,
  .big [(3, 6), (1093, 4), (451209307, 2), (902418613, 1), (4189129561, 2)],
  .big [(3, 6), (1093, 4), (902418613, 1), (4189129561, 2)],
  .big [(3, 6), (1093, 4), (902418613, 2), (4189129561, 2)],
  .big [(3, 6), (1093, 4), (4189129561, 2)],
  .big [(3, 6), (1093, 4), (4189129561, 4)],
  .big [(3, 6), (1093, 4), (4189129561, 6)],
  .big [(3, 6), (1093, 4)],
  .force 562731116179 1 [(3, 6), (1093, 6)],
  .up 562731116179 1,
  .rs 562731116179 1 6,
  .parS 562731116179,
  .force 2790506402989 1 [(3, 6), (1093, 6), (562731116179, 2)],
  .rs 2790506402989 1 3,
  .big [(3, 6), (1093, 6), (562731116179, 2), (2790506402989, 1)],
  .big [(3, 6), (1093, 6), (562731116179, 2)],
  .big [(3, 6), (1093, 6), (562731116179, 4)],
  .big [(3, 6), (1093, 6)],
  .force 6254429058851062673 1 [(3, 6), (1093, 10)],
  .rs 6254429058851062673 1 3,
  .big [(3, 6), (1093, 10), (6254429058851062673, 1)],
  .big [(3, 6), (1093, 10)],
  .force 3778501876319 1 [(3, 6), (1093, 12)],
  .up 3778501876319 1,
  .big [(3, 6), (1093, 12)],
  .big [(3, 6), (1093, 16)],
  .big [(3, 6), (1093, 18)],
  .big [(3, 6), (1093, 22)],
  .big [(3, 6)],
  .force 3851 1 [(3, 10)],
  .up 3851 1,
  .rs 3851 1 22,
  .parS 3851,
  .force 1141081 1 [(3, 10), (3851, 2)],
  .rs 1141081 1 12,
  .force 1693 1 [(3, 10), (3851, 2), (1141081, 1)],
  .up 1693 1,
  .rs 1693 1 19,
  .par2 1141081 1693,
  .force 487 1 [(3, 10), (1693, 2), (3851, 2), (1141081, 1)],
  .up 487 1,
  .rs 487 1 19,
  .par2 1141081 487,
  .force 11317 1 [(3, 10), (487, 2), (1693, 2), (3851, 2), (1141081, 1)],
  .up 11317 1,
  .rs 11317 1 11,
  .par2 1141081 11317,
  .force 42695269 1 [(3, 10), (487, 2), (1693, 2), (3851, 2), (11317, 2), (1141081, 1)],
  .up 42695269 1,
  .rs 42695269 1 6,
  .par2 1141081 42695269,
  .force 481021 1 [(3, 10), (487, 2), (1693, 2), (3851, 2), (11317, 2), (1141081, 1), (42695269, 2)],
  .up 481021 1,
  .big [(3, 10), (487, 2), (1693, 2), (3851, 2), (11317, 2), (1141081, 1), (42695269, 2)],
  .big [(3, 10), (487, 2), (1693, 2), (3851, 2), (11317, 2), (1141081, 1), (42695269, 4)],
  .big [(3, 10), (487, 2), (1693, 2), (3851, 2), (11317, 2), (1141081, 1)],
  .force 1121351701 1 [(3, 10), (487, 2), (1693, 2), (3851, 2), (11317, 4), (1141081, 1)],
  .up 1121351701 1,
  .big [(3, 10), (487, 2), (1693, 2), (3851, 2), (11317, 4), (1141081, 1)],
  .big [(3, 10), (487, 2), (1693, 2), (3851, 2), (11317, 6), (1141081, 1)],
  .big [(3, 10), (487, 2), (1693, 2), (3851, 2), (1141081, 1)],
  .force 2573621 1 [(3, 10), (487, 4), (1693, 2), (3851, 2), (1141081, 1)],
  .up 2573621 1,
  .rs 2573621 1 6,
  .par2 1141081 2573621,
  .force 1803301831 1 [(3, 10), (487, 4), (1693, 2), (3851, 2), (1141081, 1), (2573621, 2)],
  .up 1803301831 1,
  .big [(3, 10), (487, 4), (1693, 2), (3851, 2), (1141081, 1), (2573621, 2)],
  .big [(3, 10), (487, 4), (1693, 2), (3851, 2), (1141081, 1), (2573621, 4)],
  .big [(3, 10), (487, 4), (1693, 2), (3851, 2), (1141081, 1)],
  .force 2937190033 1 [(3, 10), (487, 6), (1693, 2), (3851, 2), (1141081, 1)],
  .up 2937190033 1,
  .rs 2937190033 1 4,
  .par2 1141081 2937190033,
  .big [(3, 10), (487, 6), (1693, 2), (3851, 2), (1141081, 1), (2937190033, 2)],
  .big [(3, 10), (487, 6), (1693, 2), (3851, 2), (1141081, 1)],
  .big [(3, 10), (487, 10), (1693, 2), (3851, 2), (1141081, 1)],
  .big [(3, 10), (487, 12), (1693, 2), (3851, 2), (1141081, 1)],
  .big [(3, 10), (487, 16), (1693, 2), (3851, 2), (1141081, 1)],
  .big [(3, 10), (1693, 2), (3851, 2), (1141081, 1)],
  .force 10012471081 1 [(3, 10), (1693, 4), (3851, 2), (1141081, 1)],
  .up 10012471081 1,
  .rs 10012471081 1 6,
  .par2 1141081 10012471081,
  .force 4773789388470179983 1 [(3, 10), (1693, 4), (3851, 2), (1141081, 1), (10012471081, 2)],
  .up 4773789388470179983 1,
  .big [(3, 10), (1693, 4), (3851, 2), (1141081, 1), (10012471081, 2)],
  .big [(3, 10), (1693, 4), (3851, 2), (1141081, 1), (10012471081, 4)],
  .big [(3, 10), (1693, 4), (3851, 2), (1141081, 1)],
  .force 5700731 1 [(3, 10), (1693, 6), (3851, 2), (1141081, 1)],
  .up 5700731 1,
  .rs 5700731 1 5,
  .par2 1141081 5700731,
  .big [(3, 10), (1693, 6), (3851, 2), (1141081, 1), (5700731, 2)],
  .big [(3, 10), (1693, 6), (3851, 2), (1141081, 1)],
  .big [(3, 10), (1693, 10), (3851, 2), (1141081, 1)],
  .big [(3, 10), (1693, 12), (3851, 2), (1141081, 1)],
  .big [(3, 10), (1693, 16), (3851, 2), (1141081, 1)],
  .big [(3, 10), (3851, 2), (1141081, 1)],
  .force 166393 1 [(3, 10), (3851, 2), (1141081, 2)],
  .rs 166393 1 10,
  .force 53233 1 [(3, 10), (3851, 2), (166393, 1), (1141081, 2)],
  .up 53233 1,
  .rs 53233 1 10,
  .par2 166393 53233,
  .force 944601841 1 [(3, 10), (3851, 2), (53233, 2), (166393, 1), (1141081, 2)],
  .up 944601841 1,
  .rs 944601841 1 5,
  .par2 166393 944601841,
  .big [(3, 10), (3851, 2), (53233, 2), (166393, 1), (1141081, 2), (944601841, 2)],
  .big [(3, 10), (3851, 2), (53233, 2), (166393, 1), (1141081, 2)],
  .force 33061343925391 1 [(3, 10), (3851, 2), (53233, 4), (166393, 1), (1141081, 2)],
  .up 33061343925391 1,
  .big [(3, 10), (3851, 2), (53233, 4), (166393, 1), (1141081, 2)],
  .big [(3, 10), (3851, 2), (53233, 6), (166393, 1), (1141081, 2)],
  .big [(3, 10), (3851, 2), (166393, 1), (1141081, 2)],
  .force 9228932281 1 [(3, 10), (3851, 2), (166393, 2), (1141081, 2)],
  .rs 9228932281 1 5,
  .force 326873 1 [(3, 10), (3851, 2), (166393, 2), (1141081, 2), (9228932281, 1)],
  .up 326873 1,
  .rs 326873 1 5,
  .par2 9228932281 326873,
  .big [(3, 10), (3851, 2), (166393, 2), (326873, 2), (1141081, 2), (9228932281, 1)],
  .big [(3, 10), (3851, 2), (166393, 2), (1141081, 2), (9228932281, 1)],
  .big [(3, 10), (3851, 2), (166393, 2), (1141081, 2), (9228932281, 2)],
  .big [(3, 10), (3851, 2), (166393, 2), (1141081, 2)],
  .force 24727552016409065771 1 [(3, 10), (3851, 2), (166393, 4), (1141081, 2)],
  .up 24727552016409065771 1,
  .big [(3, 10), (3851, 2), (166393, 4), (1141081, 2)],
  .big [(3, 10), (3851, 2), (166393, 6), (1141081, 2)],
  .big [(3, 10), (3851, 2), (1141081, 2)],
  .force 257418443803231 1 [(3, 10), (3851, 2), (1141081, 4)],
  .up 257418443803231 1,
  .rs 257418443803231 1 4,
  .parS 257418443803231,
  .big [(3, 10), (3851, 2), (1141081, 4), (257418443803231, 2)],
  .big [(3, 10), (3851, 2), (1141081, 4)],
  .big [(3, 10), (3851, 2), (1141081, 6)],
  .big [(3, 10), (3851, 2), (1141081, 10)],
  .big [(3, 10), (3851, 2)],
  .force 19218301 1 [(3, 10), (3851, 4)],
  .rs 19218301 1 9,
  .force 2289401 1 [(3, 10), (3851, 4), (19218301, 1)],
  .up 2289401 1,
  .rs 2289401 1 8,
  .par2 19218301 2289401,
  .force 20236908217 1 [(3, 10), (3851, 4), (2289401, 2), (19218301, 1)],
  .up 20236908217 1,
  .rs 20236908217 1 4,
  .par2 19218301 20236908217,
  .big [(3, 10), (3851, 4), (2289401, 2), (19218301, 1), (20236908217, 2)],
  .big [(3, 10), (3851, 4), (2289401, 2), (19218301, 1)],
  .big [(3, 10), (3851, 4), (2289401, 4), (19218301, 1)],
  .big [(3, 10), (3851, 4), (2289401, 6), (19218301, 1)],
  .big [(3, 10), (3851, 4), (19218301, 1)],
  .force 2289401 1 [(3, 10), (3851, 4), (19218301, 2)],
  .rs 2289401 1 6,
  .force 562399 1 [(3, 10), (3851, 4), (2289401, 1), (19218301, 2)],
  .up 562399 1,
  .rs 562399 1 6,
  .par2 2289401 562399,
  .force 5308447 1 [(3, 10), (3851, 4), (562399, 2), (2289401, 1), (19218301, 2)],
  .up 5308447 1,
  .big [(3, 10), (3851, 4), (562399, 2), (2289401, 1), (19218301, 2)],
  .big [(3, 10), (3851, 4), (562399, 4), (2289401, 1), (19218301, 2)],
  .big [(3, 10), (3851, 4), (2289401, 1), (19218301, 2)],
  .force 20236908217 1 [(3, 10), (3851, 4), (2289401, 2), (19218301, 2)],
  .rs 20236908217 1 3,
  .big [(3, 10), (3851, 4), (2289401, 2), (19218301, 2), (20236908217, 1)],
  .big [(3, 10), (3851, 4), (2289401, 2), (19218301, 2)],
  .big [(3, 10), (3851, 4), (2289401, 4), (19218301, 2)],
  .big [(3, 10), (3851, 4), (19218301, 2)],
  .big [(3, 10), (3851, 4), (19218301, 4)],
  .big [(3, 10), (3851, 4), (19218301, 6)],
  .big [(3, 10), (3851, 4)],
  .force 6583580711 1 [(3, 10), (3851, 6)],
  .up 6583580711 1,
  .rs 6583580711 1 6,
  .parS 6583580711,
  .force 1200552169759711 1 [(3, 10), (3851, 6), (6583580711, 2)],
  .up 1200552169759711 1,
  .big [(3, 10), (3851, 6), (6583580711, 2)],
  .big [(3, 10), (3851, 6), (6583580711, 4)],
  .big [(3, 10), (3851, 6)],
  .force 10731999191101 1 [(3, 10), (3851, 10)],
  .rs 10731999191101 1 3,
  .big [(3, 10), (3851, 10), (10731999191101, 1)],
  .big [(3, 10), (3851, 10)],
  .big [(3, 10), (3851, 12)],
  .big [(3, 10), (3851, 16)],
  .big [(3, 10), (3851, 18)],
  .big [(3, 10)],
  .force 797161 1 [(3, 12)],
  .rs 797161 1 14,
  .force 398581 1 [(3, 12), (797161, 1)],
  .up 398581 1,
  .rs 398581 1 14,
  .par2 797161 398581,
  .force 32668561 1 [(3, 12), (398581, 2), (797161, 1)],
  .up 32668561 1,
  .rs 32668561 1 9,
  .par2 797161 32668561,
  .force 2309087647 1 [(3, 12), (398581, 2), (797161, 1), (32668561, 2)],
  .up 2309087647 1,
  .rs 2309087647 1 5,
  .par2 797161 2309087647,
  .big [(3, 12), (398581, 2), (797161, 1), (32668561, 2), (2309087647, 2)],
  .big [(3, 12), (398581, 2), (797161, 1), (32668561, 2)],
  .big [(3, 12), (398581, 2), (797161, 1), (32668561, 4)],
  .big [(3, 12), (398581, 2), (797161, 1), (32668561, 6)],
  .big [(3, 12), (398581, 2), (797161, 1)],
  .force 2703853428809791 1 [(3, 12), (398581, 4), (797161, 1)],
  .up 2703853428809791 1,
  .rs 2703853428809791 1 4,
  .par2 797161 2703853428809791,
  .big [(3, 12), (398581, 4), (797161, 1), (2703853428809791, 2)],
  .big [(3, 12), (398581, 4), (797161, 1)],
  .force 189361597248713 1 [(3, 12), (398581, 6), (797161, 1)],
  .up 189361597248713 1,
  .big [(3, 12), (398581, 6), (797161, 1)],
  .big [(3, 12), (398581, 10), (797161, 1)],
  .big [(3, 12), (398581, 12), (797161, 1)],
  .big [(3, 12), (797161, 1)],
  .force 22996651 1 [(3, 12), (797161, 2)],
  .up 22996651 1,
  .rs 22996651 1 9,
  .parS 22996651,
  .force 4099581241957 1 [(3, 12), (797161, 2), (22996651, 2)],
  .rs 4099581241957 1 5,
  .force 2049790620979 1 [(3, 12), (797161, 2), (22996651, 2), (4099581241957, 1)],
  .up 2049790620979 1,
  .rs 2049790620979 1 4,
  .par2 4099581241957 2049790620979,
  .big [(3, 12), (797161, 2), (22996651, 2), (2049790620979, 2), (4099581241957, 1)],
  .big [(3, 12), (797161, 2), (22996651, 2), (4099581241957, 1)],
  .big [(3, 12), (797161, 2), (22996651, 2), (4099581241957, 2)],
  .big [(3, 12), (797161, 2), (22996651, 2)],
  .big [(3, 12), (797161, 2), (22996651, 4)],
  .big [(3, 12), (797161, 2), (22996651, 6)],
  .big [(3, 12), (797161, 2)],
  .force 169299992707751 1 [(3, 12), (797161, 4)],
  .up 169299992707751 1,
  .rs 169299992707751 1 4,
  .parS 169299992707751,
  .big [(3, 12), (797161, 4), (169299992707751, 2)],
  .big [(3, 12), (797161, 4)],
  .force 116720967413 1 [(3, 12), (797161, 6)],
  .rs 116720967413 1 3,
  .big [(3, 12), (797161, 6), (116720967413, 1)],
  .big [(3, 12), (797161, 6)],
  .big [(3, 12), (797161, 10)],
  .big [(3, 12), (797161, 12)],
  .big [(3, 12)],
  .force 34511 1 [(3, 16)],
  .up 34511 1,
  .rs 34511 1 17,
  .parS 34511,
  .force 4822039 1 [(3, 16), (34511, 2)],
  .up 4822039 1,
  .rs 4822039 1 10,
  .parS 4822039,
  .force 23415976777 1 [(3, 16), (34511, 2), (4822039, 2)],
  .rs 23415976777 1 5,
  .force 10952281 1 [(3, 16), (34511, 2), (4822039, 2), (23415976777, 1)],
  .up 10952281 1,
  .rs 10952281 1 5,
  .par2 23415976777 10952281,
  .big [(3, 16), (34511, 2), (4822039, 2), (10952281, 2), (23415976777, 1)],
  .big [(3, 16), (34511, 2), (4822039, 2), (23415976777, 1)],
  .big [(3, 16), (34511, 2), (4822039, 2), (23415976777, 2)],
  .big [(3, 16), (34511, 2), (4822039, 2)],
  .force 27511055689331 1 [(3, 16), (34511, 2), (4822039, 4)],
  .up 27511055689331 1,
  .big [(3, 16), (34511, 2), (4822039, 4)],
  .big [(3, 16), (34511, 2), (4822039, 6)],
  .big [(3, 16), (34511, 2)],
  .force 89451727381 1 [(3, 16), (34511, 4)],
  .rs 89451727381 1 5,
  .force 47951 1 [(3, 16), (34511, 4), (89451727381, 1)],
  .up 47951 1,
  .rs 47951 1 7,
  .par2 89451727381 47951,
  .force 16747 1 [(3, 16), (34511, 4), (47951, 2), (89451727381, 1)],
  .up 16747 1,
  .rs 16747 1 4,
  .par2 89451727381 16747,
  .big [(3, 16), (16747, 2), (34511, 4), (47951, 2), (89451727381, 1)],
  .big [(3, 16), (34511, 4), (47951, 2), (89451727381, 1)],
  .big [(3, 16), (34511, 4), (47951, 4), (89451727381, 1)],
  .big [(3, 16), (34511, 4), (89451727381, 1)],
  .big [(3, 16), (34511, 4), (89451727381, 2)],
  .big [(3, 16), (34511, 4)],
  .force 28641763802723 1 [(3, 16), (34511, 6)],
  .up 28641763802723 1,
  .rs 28641763802723 1 4,
  .parS 28641763802723,
  .big [(3, 16), (34511, 6), (28641763802723, 2)],
  .big [(3, 16), (34511, 6)],
  .big [(3, 16), (34511, 10)],
  .big [(3, 16), (34511, 12)],
  .big [(3, 16)],
  .force 363889 1 [(3, 18)],
  .rs 363889 1 14,
  .force 36389 1 [(3, 18), (363889, 1)],
  .up 36389 1,
  .rs 36389 1 15,
  .par2 363889 36389,
  .force 926659 1 [(3, 18), (36389, 2), (363889, 1)],
  .up 926659 1,
  .rs 926659 1 10,
  .par2 363889 926659,
  .force 1599181 1 [(3, 18), (36389, 2), (363889, 1), (926659, 2)],
  .up 1599181 1,
  .rs 1599181 1 7,
  .par2 363889 1599181,
  .force 852460489981 1 [(3, 18), (36389, 2), (363889, 1), (926659, 2), (1599181, 2)],
  .up 852460489981 1,
  .big [(3, 18), (36389, 2), (363889, 1), (926659, 2), (1599181, 2)],
  .big [(3, 18), (36389, 2), (363889, 1), (926659, 2), (1599181, 4)],
  .big [(3, 18), (36389, 2), (363889, 1), (926659, 2)],
  .force 77230798373051 1 [(3, 18), (36389, 2), (363889, 1), (926659, 4)],
  .up 77230798373051 1,
  .big [(3, 18), (36389, 2), (363889, 1), (926659, 4)],
  .big [(3, 18), (36389, 2), (363889, 1), (926659, 6)],
  .big [(3, 18), (36389, 2), (363889, 1)],
  .force 71941 1 [(3, 18), (36389, 4), (363889, 1)],
  .up 71941 1,
  .rs 71941 1 8,
  .par2 363889 71941,
  .force 79579 1 [(3, 18), (36389, 4), (71941, 2), (363889, 1)],
  .up 79579 1,
  .rs 79579 1 5,
  .par2 363889 79579,
  .big [(3, 18), (36389, 4), (71941, 2), (79579, 2), (363889, 1)],
  .big [(3, 18), (36389, 4), (71941, 2), (363889, 1)],
  .big [(3, 18), (36389, 4), (71941, 4), (363889, 1)],
  .big [(3, 18), (36389, 4), (71941, 6), (363889, 1)],
  .big [(3, 18), (36389, 4), (363889, 1)],
  .force 2223673948273 1 [(3, 18), (36389, 6), (363889, 1)],
  .up 2223673948273 1,
  .big [(3, 18), (36389, 6), (363889, 1)],
  .big [(3, 18), (36389, 10), (363889, 1)],
  .big [(3, 18), (36389, 12), (363889, 1)],
  .big [(3, 18), (363889, 1)],
  .force 215143 1 [(3, 18), (363889, 2)],
  .up 215143 1,
  .rs 215143 1 11,
  .parS 215143,
  .force 15428908531 1 [(3, 18), (215143, 2), (363889, 2)],
  .up 15428908531 1,
  .rs 15428908531 1 5,
  .parS 15428908531,
  .big [(3, 18), (215143, 2), (363889, 2), (15428908531, 2)],
  .big [(3, 18), (215143, 2), (363889, 2)],
  .force 4750445693592883451 1 [(3, 18), (215143, 4), (363889, 2)],
  .up 4750445693592883451 1,
  .big [(3, 18), (215143, 4), (363889, 2)],
  .big [(3, 18), (215143, 6), (363889, 2)],
  .big [(3, 18), (363889, 2)],
  .force 15782029270873877411 1 [(3, 18), (363889, 4)],
  .up 15782029270873877411 1,
  .rs 15782029270873877411 1 4,
  .parS 15782029270873877411,
  .big [(3, 18), (363889, 4), (15782029270873877411, 2)],
  .big [(3, 18), (363889, 4)],
  .force 14724111939861108567410951 1 [(3, 18), (363889, 6)],
  .up 14724111939861108567410951 1,
  .big [(3, 18), (363889, 6)],
  .big [(3, 18), (363889, 10)],
  .big [(3, 18), (363889, 12)],
  .big [(3, 18)],
  .force 1001523179 1 [(3, 22)]]

/-- Instructions, part 10. -/
def tree3_10 : List Ins := [
  .up 1001523179 1,
  .rs 1001523179 1 9,
  .parS 1001523179,
  .force 16443420968455561 1 [(3, 22), (1001523179, 2)],
  .rs 16443420968455561 1 4,
  .force 6578839 1 [(3, 22), (1001523179, 2), (16443420968455561, 1)],
  .up 6578839 1,
  .rs 6578839 1 5,
  .par2 16443420968455561 6578839,
  .big [(3, 22), (6578839, 2), (1001523179, 2), (16443420968455561, 1)],
  .big [(3, 22), (1001523179, 2), (16443420968455561, 1)],
  .big [(3, 22), (1001523179, 2), (16443420968455561, 2)],
  .big [(3, 22), (1001523179, 2)],
  .big [(3, 22), (1001523179, 4)],
  .big [(3, 22), (1001523179, 6)],
  .big [(3, 22)],
  .force 20381027 1 [(3, 28)],
  .up 20381027 1,
  .rs 20381027 1 10,
  .parS 20381027,
  .force 44988319 1 [(3, 28), (20381027, 2)],
  .up 44988319 1,
  .rs 44988319 1 6,
  .parS 44988319,
  .force 306012541 1 [(3, 28), (20381027, 2), (44988319, 2)],
  .rs 306012541 1 3,
  .big [(3, 28), (20381027, 2), (44988319, 2), (306012541, 1)],
  .big [(3, 28), (20381027, 2), (44988319, 2)],
  .big [(3, 28), (20381027, 2), (44988319, 4)],
  .big [(3, 28), (20381027, 2)],
  .force 172545754771028210096747645881 1 [(3, 28), (20381027, 4)],
  .rs 172545754771028210096747645881 1 3,
  .big [(3, 28), (20381027, 4), (172545754771028210096747645881, 1)],
  .big [(3, 28), (20381027, 4)],
  .big [(3, 28), (20381027, 6)],
  .big [(3, 28)],
  .force 4404047 1 [(3, 30)],
  .up 4404047 1,
  .rs 4404047 1 10,
  .parS 4404047,
  .force 868381 1 [(3, 30), (4404047, 2)],
  .rs 868381 1 8,
  .force 434191 1 [(3, 30), (868381, 1), (4404047, 2)],
  .up 434191 1,
  .rs 434191 1 7,
  .par2 868381 434191,
  .force 102673 1 [(3, 30), (434191, 2), (868381, 1), (4404047, 2)],
  .up 102673 1,
  .rs 102673 1 4,
  .par2 868381 102673,
  .big [(3, 30), (102673, 2), (434191, 2), (868381, 1), (4404047, 2)],
  .big [(3, 30), (434191, 2), (868381, 1), (4404047, 2)],
  .big [(3, 30), (434191, 4), (868381, 1), (4404047, 2)],
  .big [(3, 30), (868381, 1), (4404047, 2)],
  .force 164443 1 [(3, 30), (868381, 2), (4404047, 2)],
  .up 164443 1,
  .rs 164443 1 5,
  .parS 164443,
  .big [(3, 30), (164443, 2), (868381, 2), (4404047, 2)],
  .big [(3, 30), (868381, 2), (4404047, 2)],
  .big [(3, 30), (868381, 4), (4404047, 2)],
  .big [(3, 30), (868381, 6), (4404047, 2)],
  .big [(3, 30), (4404047, 2)],
  .force 10654978292191 1 [(3, 30), (4404047, 4)],
  .up 10654978292191 1,
  .big [(3, 30), (4404047, 4)],
  .big [(3, 30), (4404047, 6)],
  .big [(3, 30)],
  .force 17189128703 1 [(3, 36)],
  .up 17189128703 1,
  .rs 17189128703 1 7,
  .parS 17189128703,
  .force 33608357287 1 [(3, 36), (17189128703, 2)],
  .up 33608357287 1,
  .rs 33608357287 1 4,
  .parS 33608357287,
  .big [(3, 36), (17189128703, 2), (33608357287, 2)],
  .big [(3, 36), (17189128703, 2)],
  .big [(3, 36), (17189128703, 4)],
  .big [(3, 36)],
  .force 86950696619 1 [(3, 40)],
  .up 86950696619 1,
  .rs 86950696619 1 6,
  .parS 86950696619,
  .force 7560423642616328727781 1 [(3, 40), (86950696619, 2)],
  .rs 7560423642616328727781 1 3,
  .big [(3, 40), (86950696619, 2), (7560423642616328727781, 1)],
  .big [(3, 40), (86950696619, 2)],
  .big [(3, 40), (86950696619, 4)],
  .big [(3, 40)],
  .force 380808546861411923 1 [(3, 42)],
  .up 380808546861411923 1,
  .rs 380808546861411923 1 5,
  .parS 380808546861411923,
  .big [(3, 42), (380808546861411923, 2)],
  .big [(3, 42)],
  .force 96656723 1 [(3, 46)],
  .up 96656723 1,
  .rs 96656723 1 7,
  .parS 96656723,
  .force 274223552137 1 [(3, 46), (96656723, 2)],
  .rs 274223552137 1 3,
  .big [(3, 46), (96656723, 2), (274223552137, 1)],
  .big [(3, 46), (96656723, 2)],
  .big [(3, 46), (96656723, 4)],
  .big [(3, 46)],
  .force 3747607031112307667 1 [(3, 52)],
  .up 3747607031112307667 1,
  .rs 3747607031112307667 1 4,
  .parS 3747607031112307667,
  .big [(3, 52), (3747607031112307667, 2)],
  .big [(3, 52)],
  .force 489769993189671059 1 [(3, 58)],
  .up 489769993189671059 1,
  .rs 489769993189671059 1 4,
  .parS 489769993189671059,
  .big [(3, 58), (489769993189671059, 2)],
  .big [(3, 58)],
  .force 105293313660391861035901 1 [(3, 60)],
  .rs 105293313660391861035901 1 3,
  .big [(3, 60), (105293313660391861035901, 1)],
  .big [(3, 60)],
  .force 475384700124973 1 [(3, 66)],
  .rs 475384700124973 1 4,
  .force 441019876741 1 [(3, 66), (475384700124973, 1)],
  .up 441019876741 1,
  .big [(3, 66), (475384700124973, 1)],
  .big [(3, 66), (475384700124973, 2)],
  .big [(3, 66)],
  .force 3754733257489862401973357979128773 1 [(3, 70)],
  .rs 3754733257489862401973357979128773 1 3,
  .big [(3, 70), (3754733257489862401973357979128773, 1)],
  .big [(3, 70)],
  .force 9460375336977361 1 [(3, 72)],
  .rs 9460375336977361 1 3,
  .big [(3, 72), (9460375336977361, 1)],
  .big [(3, 72)],
  .force 145171177264407947 1 [(3, 78)],
  .up 145171177264407947 1,
  .big [(3, 78)],
  .force 950996059627210897943351 1 [(3, 82)],
  .up 950996059627210897943351 1,
  .big [(3, 82)],
  .big [(3, 88)],
  .big [(3, 96)],
  .big [(3, 100)],
  .big [(3, 102)],
  .big [(3, 106)],
  .big [(3, 108)],
  .big [(3, 112)],
  .big [(3, 126)],
  .big [(3, 130)],
  .big [(3, 136)],
  .big [(3, 138)],
  .big [(3, 148)],
  .big [(3, 150)],
  .big [(3, 156)],
  .big [(3, 162)],
  .big []]

/-- The tree for `3`. -/
def tree3 : List Ins := tree3_0 ++ tree3_1 ++ tree3_2 ++ tree3_3 ++ tree3_4 ++ tree3_5 ++ tree3_6 ++ tree3_7 ++ tree3_8 ++ tree3_9 ++ tree3_10

/-- Instructions, part 0. -/
def tree5_0 : List Ins := [
  .rs 5 1 115,
  .force 3 1 [(5, 1)],
  .ndc 3,
  .force 31 1 [(5, 2)],
  .up 31 1,
  .rs 31 1 54,
  .parS 31,
  .force 331 1 [(5, 2), (31, 2)],
  .up 331 1,
  .rs 331 1 31,
  .parS 331,
  .force 5233 1 [(5, 2), (31, 2), (331, 2)],
  .rs 5233 1 20,
  .force 2617 1 [(5, 2), (31, 2), (331, 2), (5233, 1)],
  .up 2617 1,
  .rs 2617 1 20,
  .par2 5233 2617,
  .force 11833 1 [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1)],
  .up 11833 1,
  .rs 11833 1 15,
  .par2 5233 11833,
  .force 18043 1 [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 2)],
  .up 18043 1,
  .rs 18043 1 11,
  .par2 5233 18043,
  .force 15503233 1 [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 2), (18043, 2)],
  .up 15503233 1,
  .rs 15503233 1 6,
  .par2 5233 15503233,
  .force 11445249950263 1 [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 2), (18043, 2), (15503233, 2)],
  .up 11445249950263 1,
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 2), (18043, 2), (15503233, 2)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 2), (18043, 2), (15503233, 4)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 2), (18043, 2)],
  .force 8341832431 1 [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 2), (18043, 4)],
  .up 8341832431 1,
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 2), (18043, 4)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 2), (18043, 6)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 2)],
  .force 865622988431 1 [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 4)],
  .up 865622988431 1,
  .rs 865622988431 1 4,
  .par2 5233 865622988431,
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 4), (865622988431, 2)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 4)],
  .force 3734409164527273 1 [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 6)],
  .up 3734409164527273 1,
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 6)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 10)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1), (11833, 12)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 2), (5233, 1)],
  .force 46922470889141 1 [(5, 2), (31, 2), (331, 2), (2617, 4), (5233, 1)],
  .up 46922470889141 1,
  .rs 46922470889141 1 5,
  .par2 5233 46922470889141,
  .big [(5, 2), (31, 2), (331, 2), (2617, 4), (5233, 1), (46922470889141, 2)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 4), (5233, 1)],
  .force 11627796440687491 1 [(5, 2), (31, 2), (331, 2), (2617, 6), (5233, 1)],
  .up 11627796440687491 1,
  .rs 11627796440687491 1 4,
  .par2 5233 11627796440687491,
  .big [(5, 2), (31, 2), (331, 2), (2617, 6), (5233, 1), (11627796440687491, 2)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 6), (5233, 1)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 10), (5233, 1)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 12), (5233, 1)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 16), (5233, 1)],
  .big [(5, 2), (31, 2), (331, 2), (2617, 18), (5233, 1)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 1)],
  .force 42073 1 [(5, 2), (31, 2), (331, 2), (5233, 2)],
  .rs 42073 1 14,
  .force 193 1 [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 1)],
  .up 193 1,
  .rs 193 1 24,
  .par2 42073 193,
  .force 1783 1 [(5, 2), (31, 2), (193, 2), (331, 2), (5233, 2), (42073, 1)],
  .up 1783 1,
  .rs 1783 1 16,
  .par2 42073 1783,
  .force 1279 1 [(5, 2), (31, 2), (193, 2), (331, 2), (1783, 2), (5233, 2), (42073, 1)],
  .up 1279 1,
  .rs 1279 1 13,
  .par2 42073 1279,
  .force 2383 1 [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 2), (1783, 2), (5233, 2), (42073, 1)],
  .up 2383 1,
  .rs 2383 1 10,
  .par2 42073 2383,
  .force 12541 1 [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 2), (1783, 2), (2383, 2), (5233, 2), (42073, 1)],
  .up 12541 1,
  .rs 12541 1 6,
  .par2 42073 12541,
  .force 576151 1 [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 2), (1783, 2), (2383, 2), (5233, 2), (12541, 2), (42073, 1)],
  .up 576151 1,
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 2), (1783, 2), (2383, 2), (5233, 2), (12541, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 2), (1783, 2), (2383, 2), (5233, 2), (12541, 4), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 2), (1783, 2), (2383, 2), (5233, 2), (42073, 1)],
  .force 32261046755681 1 [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 2), (1783, 2), (2383, 4), (5233, 2), (42073, 1)],
  .up 32261046755681 1,
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 2), (1783, 2), (2383, 4), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 2), (1783, 2), (2383, 6), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 2), (1783, 2), (5233, 2), (42073, 1)],
  .force 7853576701 1 [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 4), (1783, 2), (5233, 2), (42073, 1)],
  .up 7853576701 1,
  .rs 7853576701 1 4,
  .par2 42073 7853576701,
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 4), (1783, 2), (5233, 2), (42073, 1), (7853576701, 2)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 4), (1783, 2), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 6), (1783, 2), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1279, 10), (1783, 2), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1783, 2), (5233, 2), (42073, 1)],
  .force 4849081 1 [(5, 2), (31, 2), (193, 2), (331, 2), (1783, 4), (5233, 2), (42073, 1)],
  .up 4849081 1,
  .rs 4849081 1 6,
  .par2 42073 4849081,
  .force 602912599837 1 [(5, 2), (31, 2), (193, 2), (331, 2), (1783, 4), (5233, 2), (42073, 1), (4849081, 2)],
  .up 602912599837 1,
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1783, 4), (5233, 2), (42073, 1), (4849081, 2)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1783, 4), (5233, 2), (42073, 1), (4849081, 4)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1783, 4), (5233, 2), (42073, 1)],
  .force 32147832919817717593 1 [(5, 2), (31, 2), (193, 2), (331, 2), (1783, 6), (5233, 2), (42073, 1)],
  .up 32147832919817717593 1,
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1783, 6), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1783, 10), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (1783, 12), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 2), (331, 2), (5233, 2), (42073, 1)],
  .force 1394714501 1 [(5, 2), (31, 2), (193, 4), (331, 2), (5233, 2), (42073, 1)],
  .up 1394714501 1,
  .rs 1394714501 1 6,
  .par2 42073 1394714501,
  .force 6562429921 1 [(5, 2), (31, 2), (193, 4), (331, 2), (5233, 2), (42073, 1), (1394714501, 2)],
  .up 6562429921 1,
  .big [(5, 2), (31, 2), (193, 4), (331, 2), (5233, 2), (42073, 1), (1394714501, 2)],
  .big [(5, 2), (31, 2), (193, 4), (331, 2), (5233, 2), (42073, 1), (1394714501, 4)],
  .big [(5, 2), (31, 2), (193, 4), (331, 2), (5233, 2), (42073, 1)],
  .force 1208179545301 1 [(5, 2), (31, 2), (193, 6), (331, 2), (5233, 2), (42073, 1)],
  .up 1208179545301 1,
  .rs 1208179545301 1 5,
  .par2 42073 1208179545301,
  .big [(5, 2), (31, 2), (193, 6), (331, 2), (5233, 2), (42073, 1), (1208179545301, 2)],
  .big [(5, 2), (31, 2), (193, 6), (331, 2), (5233, 2), (42073, 1)],
  .force 2662289521 1 [(5, 2), (31, 2), (193, 10), (331, 2), (5233, 2), (42073, 1)],
  .up 2662289521 1,
  .big [(5, 2), (31, 2), (193, 10), (331, 2), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 12), (331, 2), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 16), (331, 2), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 18), (331, 2), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (193, 22), (331, 2), (5233, 2), (42073, 1)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 1)],
  .force 75931 1 [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 2)],
  .up 75931 1,
  .rs 75931 1 11,
  .parS 75931,
  .force 787 1 [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 2), (75931, 2)],
  .up 787 1,
  .rs 787 1 11,
  .parS 787,
  .force 409 1 [(5, 2), (31, 2), (331, 2), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .rs 409 1 9,
  .force 151 1 [(5, 2), (31, 2), (331, 2), (409, 1), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .up 151 1,
  .rs 151 1 10,
  .par2 409 151,
  .force 1093 1 [(5, 2), (31, 2), (151, 2), (331, 2), (409, 1), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .up 1093 1,
  .rs 1093 1 5,
  .par2 409 1093,
  .big [(5, 2), (31, 2), (151, 2), (331, 2), (409, 1), (787, 2), (1093, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(5, 2), (31, 2), (151, 2), (331, 2), (409, 1), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .force 104670301 1 [(5, 2), (31, 2), (151, 4), (331, 2), (409, 1), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .up 104670301 1,
  .big [(5, 2), (31, 2), (151, 4), (331, 2), (409, 1), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(5, 2), (31, 2), (151, 6), (331, 2), (409, 1), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(5, 2), (31, 2), (331, 2), (409, 1), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .force 55897 1 [(5, 2), (31, 2), (331, 2), (409, 2), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .rs 55897 1 4,
  .force 1471 1 [(5, 2), (31, 2), (331, 2), (409, 2), (787, 2), (5233, 2), (42073, 2), (55897, 1), (75931, 2)],
  .up 1471 1,
  .rs 1471 1 4,
  .par2 55897 1471,
  .big [(5, 2), (31, 2), (331, 2), (409, 2), (787, 2), (1471, 2), (5233, 2), (42073, 2), (55897, 1), (75931, 2)],
  .big [(5, 2), (31, 2), (331, 2), (409, 2), (787, 2), (5233, 2), (42073, 2), (55897, 1), (75931, 2)],
  .big [(5, 2), (31, 2), (331, 2), (409, 2), (787, 2), (5233, 2), (42073, 2), (55897, 2), (75931, 2)],
  .big [(5, 2), (31, 2), (331, 2), (409, 2), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(5, 2), (31, 2), (331, 2), (409, 4), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(5, 2), (31, 2), (331, 2), (409, 6), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(5, 2), (31, 2), (331, 2), (787, 2), (5233, 2), (42073, 2), (75931, 2)],
  .force 672901 1 [(5, 2), (31, 2), (331, 2), (787, 4), (5233, 2), (42073, 2), (75931, 2)],
  .rs 672901 1 3,
  .force 570821 1 [(5, 2), (31, 2), (331, 2), (787, 4), (5233, 2), (42073, 2), (75931, 2), (672901, 1)],
  .up 570821 1,
  .big [(5, 2), (31, 2), (331, 2), (787, 4), (5233, 2), (42073, 2), (75931, 2), (672901, 1)],
  .big [(5, 2), (31, 2), (331, 2), (787, 4), (5233, 2), (42073, 2), (75931, 2)],
  .big [(5, 2), (31, 2), (331, 2), (787, 6), (5233, 2), (42073, 2), (75931, 2)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 2), (75931, 2)],
  .force 687262545131 1 [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 2), (75931, 4)],
  .up 687262545131 1,
  .big [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 2), (75931, 4)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 2), (75931, 6)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 2)],
  .force 284860058207025151 1 [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 4)],
  .up 284860058207025151 1,
  .rs 284860058207025151 1 4,
  .parS 284860058207025151,
  .big [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 4), (284860058207025151, 2)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 4)],
  .force 248366755289421259 1 [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 6)],
  .up 248366755289421259 1,
  .big [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 6)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 10)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 2), (42073, 12)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 2)],
  .force 41213191 1 [(5, 2), (31, 2), (331, 2), (5233, 4)],
  .up 41213191 1,
  .rs 41213191 1 7,
  .parS 41213191,
  .force 183067 1 [(5, 2), (31, 2), (331, 2), (5233, 4), (41213191, 2)],
  .up 183067 1,
  .rs 183067 1 5,
  .parS 183067,
  .big [(5, 2), (31, 2), (331, 2), (5233, 4), (183067, 2), (41213191, 2)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 4), (41213191, 2)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 4), (41213191, 4)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 4)],
  .force 5522944621250897 1 [(5, 2), (31, 2), (331, 2), (5233, 6)],
  .rs 5522944621250897 1 4,
  .force 148012666057 1 [(5, 2), (31, 2), (331, 2), (5233, 6), (5522944621250897, 1)],
  .up 148012666057 1,
  .big [(5, 2), (31, 2), (331, 2), (5233, 6), (5522944621250897, 1)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 6), (5522944621250897, 2)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 6)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 10)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 12)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 16)],
  .big [(5, 2), (31, 2), (331, 2), (5233, 18)],
  .big [(5, 2), (31, 2), (331, 2)],
  .force 63601 1 [(5, 2), (31, 2), (331, 4)],
  .rs 63601 1 14,
  .force 37861 1 [(5, 2), (31, 2), (331, 4), (63601, 1)],
  .up 37861 1,
  .rs 37861 1 13,
  .par2 63601 37861,
  .force 10753 1 [(5, 2), (31, 2), (331, 4), (37861, 2), (63601, 1)],
  .up 10753 1,
  .rs 10753 1 12,
  .par2 63601 10753,
  .force 1201 1 [(5, 2), (31, 2), (331, 4), (10753, 2), (37861, 2), (63601, 1)],
  .up 1201 1,
  .rs 1201 1 10,
  .par2 63601 1201,
  .force 68743 1 [(5, 2), (31, 2), (331, 4), (1201, 2), (10753, 2), (37861, 2), (63601, 1)],
  .up 68743 1,
  .rs 68743 1 6,
  .par2 63601 68743,
  .force 1575222931 1 [(5, 2), (31, 2), (331, 4), (1201, 2), (10753, 2), (37861, 2), (63601, 1), (68743, 2)],
  .up 1575222931 1,
  .big [(5, 2), (31, 2), (331, 4), (1201, 2), (10753, 2), (37861, 2), (63601, 1), (68743, 2)],
  .big [(5, 2), (31, 2), (331, 4), (1201, 2), (10753, 2), (37861, 2), (63601, 1), (68743, 4)],
  .big [(5, 2), (31, 2), (331, 4), (1201, 2), (10753, 2), (37861, 2), (63601, 1)],
  .force 416450882401 1 [(5, 2), (31, 2), (331, 4), (1201, 4), (10753, 2), (37861, 2), (63601, 1)],
  .up 416450882401 1,
  .big [(5, 2), (31, 2), (331, 4), (1201, 4), (10753, 2), (37861, 2), (63601, 1)],
  .big [(5, 2), (31, 2), (331, 4), (1201, 6), (10753, 2), (37861, 2), (63601, 1)],
  .big [(5, 2), (31, 2), (331, 4), (10753, 2), (37861, 2), (63601, 1)],
  .force 13370848663151621 1 [(5, 2), (31, 2), (331, 4), (10753, 4), (37861, 2), (63601, 1)],
  .up 13370848663151621 1,
  .big [(5, 2), (31, 2), (331, 4), (10753, 4), (37861, 2), (63601, 1)],
  .big [(5, 2), (31, 2), (331, 4), (10753, 6), (37861, 2), (63601, 1)],
  .big [(5, 2), (31, 2), (331, 4), (10753, 10), (37861, 2), (63601, 1)],
  .big [(5, 2), (31, 2), (331, 4), (37861, 2), (63601, 1)],
  .force 99244068137581 1 [(5, 2), (31, 2), (331, 4), (37861, 4), (63601, 1)],
  .up 99244068137581 1,
  .rs 99244068137581 1 4,
  .par2 63601 99244068137581,
  .big [(5, 2), (31, 2), (331, 4), (37861, 4), (63601, 1), (99244068137581, 2)],
  .big [(5, 2), (31, 2), (331, 4), (37861, 4), (63601, 1)],
  .big [(5, 2), (31, 2), (331, 4), (37861, 6), (63601, 1)],
  .big [(5, 2), (31, 2), (331, 4), (37861, 10), (63601, 1)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 1)],
  .force 612067 1 [(5, 2), (31, 2), (331, 4), (63601, 2)],
  .up 612067 1,
  .rs 612067 1 9,
  .parS 612067,
  .force 26010319 1 [(5, 2), (31, 2), (331, 4), (63601, 2), (612067, 2)],
  .up 26010319 1,
  .rs 26010319 1 6,
  .parS 26010319,
  .force 527135461 1 [(5, 2), (31, 2), (331, 4), (63601, 2), (612067, 2), (26010319, 2)],
  .rs 527135461 1 3,
  .big [(5, 2), (31, 2), (331, 4), (63601, 2), (612067, 2), (26010319, 2), (527135461, 1)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 2), (612067, 2), (26010319, 2)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 2), (612067, 2), (26010319, 4)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 2), (612067, 2)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 2), (612067, 4)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 2), (612067, 6)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 2)],
  .force 50408381 1 [(5, 2), (31, 2), (331, 4), (63601, 4)],
  .rs 50408381 1 5,
  .force 8401397 1 [(5, 2), (31, 2), (331, 4), (63601, 4), (50408381, 1)],
  .up 8401397 1,
  .rs 8401397 1 5,
  .par2 50408381 8401397,
  .big [(5, 2), (31, 2), (331, 4), (63601, 4), (8401397, 2), (50408381, 1)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 4), (50408381, 1)],
  .force 11709700117279 1 [(5, 2), (31, 2), (331, 4), (63601, 4), (50408381, 2)],
  .up 11709700117279 1,
  .big [(5, 2), (31, 2), (331, 4), (63601, 4), (50408381, 2)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 4)],
  .force 1539295634290340976189184549 1 [(5, 2), (31, 2), (331, 4), (63601, 6)],
  .rs 1539295634290340976189184549 1 3,
  .big [(5, 2), (31, 2), (331, 4), (63601, 6), (1539295634290340976189184549, 1)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 6)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 10)],
  .big [(5, 2), (31, 2), (331, 4), (63601, 12)],
  .big [(5, 2), (31, 2), (331, 4)],
  .force 604842197 1 [(5, 2), (31, 2), (331, 6)],
  .rs 604842197 1 7,
  .force 2180921 1 [(5, 2), (31, 2), (331, 6), (604842197, 1)],
  .up 2180921 1,
  .rs 2180921 1 8,
  .par2 604842197 2180921,
  .force 1478526139 1 [(5, 2), (31, 2), (331, 6), (2180921, 2), (604842197, 1)],
  .up 1478526139 1,
  .rs 1478526139 1 4,
  .par2 604842197 1478526139,
  .big [(5, 2), (31, 2), (331, 6), (2180921, 2), (604842197, 1), (1478526139, 2)],
  .big [(5, 2), (31, 2), (331, 6), (2180921, 2), (604842197, 1)],
  .big [(5, 2), (31, 2), (331, 6), (2180921, 4), (604842197, 1)],
  .big [(5, 2), (31, 2), (331, 6), (2180921, 6), (604842197, 1)],
  .big [(5, 2), (31, 2), (331, 6), (604842197, 1)],
  .force 365834083876629007 1 [(5, 2), (31, 2), (331, 6), (604842197, 2)],
  .up 365834083876629007 1,
  .big [(5, 2), (31, 2), (331, 6), (604842197, 2)],
  .big [(5, 2), (31, 2), (331, 6), (604842197, 4)],
  .big [(5, 2), (31, 2), (331, 6)],
  .force 703207451121161180833 1 [(5, 2), (31, 2), (331, 10)],
  .rs 703207451121161180833 1 4,
  .force 5959385178992891363 1 [(5, 2), (31, 2), (331, 10), (703207451121161180833, 1)],
  .up 5959385178992891363 1,
  .big [(5, 2), (31, 2), (331, 10), (703207451121161180833, 1)],
  .big [(5, 2), (31, 2), (331, 10), (703207451121161180833, 2)],
  .big [(5, 2), (31, 2), (331, 10)],
  .force 80037421623539251 1 [(5, 2), (31, 2), (331, 12)],
  .up 80037421623539251 1,
  .big [(5, 2), (31, 2), (331, 12)],
  .big [(5, 2), (31, 2), (331, 16)],
  .big [(5, 2), (31, 2), (331, 18)],
  .big [(5, 2), (31, 2), (331, 22)],
  .big [(5, 2), (31, 2), (331, 28)],
  .big [(5, 2), (31, 2)],
  .force 17351 1 [(5, 2), (31, 4)],
  .up 17351 1,
  .rs 17351 1 18,
  .parS 17351,
  .force 21787 1 [(5, 2), (31, 4), (17351, 2)],
  .up 21787 1,
  .rs 21787 1 15,
  .parS 21787,
  .force 5104249 1 [(5, 2), (31, 4), (17351, 2), (21787, 2)],
  .rs 5104249 1 9,
  .force 1201 1 [(5, 2), (31, 4), (17351, 2), (21787, 2), (5104249, 1)],
  .up 1201 1,
  .rs 1201 1 14,
  .par2 5104249 1201,
  .force 68743 1 [(5, 2), (31, 4), (1201, 2), (17351, 2), (21787, 2), (5104249, 1)],
  .up 68743 1,
  .rs 68743 1 8,
  .par2 5104249 68743,
  .force 1575222931 1 [(5, 2), (31, 4), (1201, 2), (17351, 2), (21787, 2), (68743, 2), (5104249, 1)],
  .up 1575222931 1,
  .rs 1575222931 1 4,
  .par2 5104249 1575222931,
  .big [(5, 2), (31, 4), (1201, 2), (17351, 2), (21787, 2), (68743, 2), (5104249, 1), (1575222931, 2)],
  .big [(5, 2), (31, 4), (1201, 2), (17351, 2), (21787, 2), (68743, 2), (5104249, 1)],
  .big [(5, 2), (31, 4), (1201, 2), (17351, 2), (21787, 2), (68743, 4), (5104249, 1)],
  .big [(5, 2), (31, 4), (1201, 2), (17351, 2), (21787, 2), (68743, 6), (5104249, 1)],
  .big [(5, 2), (31, 4), (1201, 2), (17351, 2), (21787, 2), (5104249, 1)],
  .force 416450882401 1 [(5, 2), (31, 4), (1201, 4), (17351, 2), (21787, 2), (5104249, 1)],
  .up 416450882401 1,
  .rs 416450882401 1 4,
  .par2 5104249 416450882401,
  .big [(5, 2), (31, 4), (1201, 4), (17351, 2), (21787, 2), (5104249, 1), (416450882401, 2)],
  .big [(5, 2), (31, 4), (1201, 4), (17351, 2), (21787, 2), (5104249, 1)],
  .force 102057353159483 1 [(5, 2), (31, 4), (1201, 6), (17351, 2), (21787, 2), (5104249, 1)],
  .up 102057353159483 1,
  .big [(5, 2), (31, 4), (1201, 6), (17351, 2), (21787, 2), (5104249, 1)],
  .big [(5, 2), (31, 4), (1201, 10), (17351, 2), (21787, 2), (5104249, 1)],
  .big [(5, 2), (31, 4), (1201, 12), (17351, 2), (21787, 2), (5104249, 1)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 2), (5104249, 1)],
  .force 656737 1 [(5, 2), (31, 4), (17351, 2), (21787, 2), (5104249, 2)],
  .rs 656737 1 6,
  .force 216781 1 [(5, 2), (31, 4), (17351, 2), (21787, 2), (656737, 1), (5104249, 2)],
  .up 216781 1,
  .rs 216781 1 6,
  .par2 656737 216781,
  .force 8009 1 [(5, 2), (31, 4), (17351, 2), (21787, 2), (216781, 2), (656737, 1), (5104249, 2)],
  .up 8009 1,
  .big [(5, 2), (31, 4), (17351, 2), (21787, 2), (216781, 2), (656737, 1), (5104249, 2)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 2), (216781, 4), (656737, 1), (5104249, 2)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 2), (656737, 1), (5104249, 2)],
  .force 216781 1 [(5, 2), (31, 4), (17351, 2), (21787, 2), (656737, 2), (5104249, 2)],
  .rs 216781 1 3]

/-- Instructions, part 1. -/
def tree5_1 : List Ins := [
  .big [(5, 2), (31, 4), (17351, 2), (21787, 2), (216781, 1), (656737, 2), (5104249, 2)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 2), (656737, 2), (5104249, 2)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 2), (656737, 4), (5104249, 2)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 2), (5104249, 2)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 2), (5104249, 4)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 2), (5104249, 6)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 2)],
  .force 166484861 1 [(5, 2), (31, 4), (17351, 2), (21787, 4)],
  .rs 166484861 1 5,
  .force 67231 1 [(5, 2), (31, 4), (17351, 2), (21787, 4), (166484861, 1)],
  .up 67231 1,
  .rs 67231 1 6,
  .par2 166484861 67231,
  .force 6579439 1 [(5, 2), (31, 4), (17351, 2), (21787, 4), (67231, 2), (166484861, 1)],
  .up 6579439 1,
  .big [(5, 2), (31, 4), (17351, 2), (21787, 4), (67231, 2), (166484861, 1)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 4), (67231, 4), (166484861, 1)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 4), (166484861, 1)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 4), (166484861, 2)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 4)],
  .force 1622337552083173402331 1 [(5, 2), (31, 4), (17351, 2), (21787, 6)],
  .up 1622337552083173402331 1,
  .big [(5, 2), (31, 4), (17351, 2), (21787, 6)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 10)],
  .big [(5, 2), (31, 4), (17351, 2), (21787, 12)],
  .big [(5, 2), (31, 4), (17351, 2)],
  .force 1648012040336791 1 [(5, 2), (31, 4), (17351, 4)],
  .up 1648012040336791 1,
  .rs 1648012040336791 1 5,
  .parS 1648012040336791,
  .big [(5, 2), (31, 4), (17351, 4), (1648012040336791, 2)],
  .big [(5, 2), (31, 4), (17351, 4)],
  .force 68917740951781 1 [(5, 2), (31, 4), (17351, 6)],
  .rs 68917740951781 1 4,
  .force 395950646197 1 [(5, 2), (31, 4), (17351, 6), (68917740951781, 1)],
  .up 395950646197 1,
  .big [(5, 2), (31, 4), (17351, 6), (68917740951781, 1)],
  .big [(5, 2), (31, 4), (17351, 6), (68917740951781, 2)],
  .big [(5, 2), (31, 4), (17351, 6)],
  .big [(5, 2), (31, 4), (17351, 10)],
  .big [(5, 2), (31, 4), (17351, 12)],
  .big [(5, 2), (31, 4), (17351, 16)],
  .big [(5, 2), (31, 4)],
  .force 917087137 1 [(5, 2), (31, 6)],
  .rs 917087137 1 9,
  .force 28729 1 [(5, 2), (31, 6), (917087137, 1)],
  .up 28729 1,
  .rs 28729 1 14,
  .par2 917087137 28729,
  .force 93169 1 [(5, 2), (31, 6), (28729, 2), (917087137, 1)],
  .up 93169 1,
  .rs 93169 1 10,
  .par2 917087137 93169,
  .force 163411 1 [(5, 2), (31, 6), (28729, 2), (93169, 2), (917087137, 1)],
  .up 163411 1,
  .rs 163411 1 7,
  .par2 917087137 163411,
  .force 2045761 1 [(5, 2), (31, 6), (28729, 2), (93169, 2), (163411, 2), (917087137, 1)],
  .up 2045761 1,
  .rs 2045761 1 4,
  .par2 917087137 2045761,
  .big [(5, 2), (31, 6), (28729, 2), (93169, 2), (163411, 2), (2045761, 2), (917087137, 1)],
  .big [(5, 2), (31, 6), (28729, 2), (93169, 2), (163411, 2), (917087137, 1)],
  .big [(5, 2), (31, 6), (28729, 2), (93169, 2), (163411, 4), (917087137, 1)],
  .big [(5, 2), (31, 6), (28729, 2), (93169, 2), (917087137, 1)],
  .force 89295617581 1 [(5, 2), (31, 6), (28729, 2), (93169, 4), (917087137, 1)],
  .up 89295617581 1,
  .big [(5, 2), (31, 6), (28729, 2), (93169, 4), (917087137, 1)],
  .big [(5, 2), (31, 6), (28729, 2), (93169, 6), (917087137, 1)],
  .big [(5, 2), (31, 6), (28729, 2), (917087137, 1)],
  .force 7670501 1 [(5, 2), (31, 6), (28729, 4), (917087137, 1)],
  .up 7670501 1,
  .rs 7670501 1 5,
  .par2 917087137 7670501,
  .big [(5, 2), (31, 6), (28729, 4), (7670501, 2), (917087137, 1)],
  .big [(5, 2), (31, 6), (28729, 4), (917087137, 1)],
  .force 5742692449452968574979 1 [(5, 2), (31, 6), (28729, 6), (917087137, 1)],
  .up 5742692449452968574979 1,
  .big [(5, 2), (31, 6), (28729, 6), (917087137, 1)],
  .big [(5, 2), (31, 6), (28729, 10), (917087137, 1)],
  .big [(5, 2), (31, 6), (28729, 12), (917087137, 1)],
  .big [(5, 2), (31, 6), (917087137, 1)],
  .force 38533987 1 [(5, 2), (31, 6), (917087137, 2)],
  .up 38533987 1,
  .rs 38533987 1 7,
  .parS 38533987,
  .force 15441801523 1 [(5, 2), (31, 6), (38533987, 2), (917087137, 2)],
  .up 15441801523 1,
  .big [(5, 2), (31, 6), (38533987, 2), (917087137, 2)],
  .big [(5, 2), (31, 6), (38533987, 4), (917087137, 2)],
  .big [(5, 2), (31, 6), (917087137, 2)],
  .big [(5, 2), (31, 6), (917087137, 4)],
  .big [(5, 2), (31, 6), (917087137, 6)],
  .big [(5, 2), (31, 6)],
  .force 150332843 1 [(5, 2), (31, 10)],
  .up 150332843 1,
  .rs 150332843 1 8,
  .parS 150332843,
  .force 127473943 1 [(5, 2), (31, 10), (150332843, 2)],
  .up 127473943 1,
  .rs 127473943 1 5,
  .parS 127473943,
  .big [(5, 2), (31, 10), (127473943, 2), (150332843, 2)],
  .big [(5, 2), (31, 10), (150332843, 2)],
  .big [(5, 2), (31, 10), (150332843, 4)],
  .big [(5, 2), (31, 10), (150332843, 6)],
  .big [(5, 2), (31, 10)],
  .force 7908811 1 [(5, 2), (31, 12)],
  .up 7908811 1,
  .rs 7908811 1 9,
  .parS 7908811,
  .force 2426789 1 [(5, 2), (31, 12), (7908811, 2)],
  .rs 2426789 1 6,
  .force 42407 1 [(5, 2), (31, 12), (2426789, 1), (7908811, 2)],
  .up 42407 1,
  .rs 42407 1 6,
  .par2 2426789 42407,
  .force 1222567 1 [(5, 2), (31, 12), (42407, 2), (2426789, 1), (7908811, 2)],
  .up 1222567 1,
  .big [(5, 2), (31, 12), (42407, 2), (2426789, 1), (7908811, 2)],
  .big [(5, 2), (31, 12), (42407, 4), (2426789, 1), (7908811, 2)],
  .big [(5, 2), (31, 12), (2426789, 1), (7908811, 2)],
  .force 5889307277311 1 [(5, 2), (31, 12), (2426789, 2), (7908811, 2)],
  .up 5889307277311 1,
  .big [(5, 2), (31, 12), (2426789, 2), (7908811, 2)],
  .big [(5, 2), (31, 12), (2426789, 4), (7908811, 2)],
  .big [(5, 2), (31, 12), (7908811, 2)],
  .big [(5, 2), (31, 12), (7908811, 4)],
  .big [(5, 2), (31, 12), (7908811, 6)],
  .big [(5, 2), (31, 12)],
  .force 751670559138758105956097 1 [(5, 2), (31, 16)],
  .rs 751670559138758105956097 1 4,
  .force 11388947865738759181153 1 [(5, 2), (31, 16), (751670559138758105956097, 1)],
  .up 11388947865738759181153 1,
  .big [(5, 2), (31, 16), (751670559138758105956097, 1)],
  .big [(5, 2), (31, 16), (751670559138758105956097, 2)],
  .big [(5, 2), (31, 16)],
  .force 88770666332610762169 1 [(5, 2), (31, 18)],
  .rs 88770666332610762169 1 4,
  .force 807006057569188747 1 [(5, 2), (31, 18), (88770666332610762169, 1)],
  .up 807006057569188747 1,
  .big [(5, 2), (31, 18), (88770666332610762169, 1)],
  .big [(5, 2), (31, 18), (88770666332610762169, 2)],
  .big [(5, 2), (31, 18)],
  .force 7176374761323733117 1 [(5, 2), (31, 22)],
  .rs 7176374761323733117 1 3,
  .big [(5, 2), (31, 22), (7176374761323733117, 1)],
  .big [(5, 2), (31, 22)],
  .big [(5, 2), (31, 28)],
  .big [(5, 2), (31, 30)],
  .big [(5, 2), (31, 36)],
  .big [(5, 2), (31, 40)],
  .big [(5, 2), (31, 42)],
  .big [(5, 2), (31, 46)],
  .big [(5, 2), (31, 52)],
  .big [(5, 2)],
  .force 71 1 [(5, 4)],
  .up 71 1,
  .rs 71 1 42,
  .parS 71,
  .force 5113 1 [(5, 4), (71, 2)],
  .rs 5113 1 21,
  .force 2557 1 [(5, 4), (71, 2), (5113, 1)],
  .up 2557 1,
  .rs 2557 1 21,
  .par2 5113 2557,
  .force 97 1 [(5, 4), (71, 2), (2557, 2), (5113, 1)],
  .up 97 1,
  .rs 97 1 30,
  .par2 5113 97,
  .force 3169 1 [(5, 4), (71, 2), (97, 2), (2557, 2), (5113, 1)],
  .up 3169 1,
  .rs 3169 1 16,
  .par2 5113 3169,
  .force 3348577 1 [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 2), (5113, 1)],
  .up 3348577 1,
  .rs 3348577 1 8,
  .par2 5113 3348577,
  .force 3737657091169 1 [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 2), (5113, 1), (3348577, 2)],
  .up 3737657091169 1,
  .rs 3737657091169 1 4,
  .par2 5113 3737657091169,
  .big [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 2), (5113, 1), (3348577, 2), (3737657091169, 2)],
  .big [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 2), (5113, 1), (3348577, 2)],
  .big [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 2), (5113, 1), (3348577, 4)],
  .big [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 2), (5113, 1), (3348577, 6)],
  .big [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 2), (5113, 1)],
  .force 1653850268201 1 [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 4), (5113, 1)],
  .up 1653850268201 1,
  .rs 1653850268201 1 4,
  .par2 5113 1653850268201,
  .big [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 4), (5113, 1), (1653850268201, 2)],
  .big [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 4), (5113, 1)],
  .force 3447899565839 1 [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 6), (5113, 1)],
  .up 3447899565839 1,
  .big [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 6), (5113, 1)],
  .big [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 10), (5113, 1)],
  .big [(5, 4), (71, 2), (97, 2), (2557, 2), (3169, 12), (5113, 1)],
  .big [(5, 4), (71, 2), (97, 2), (2557, 2), (5113, 1)],
  .force 262321 1 [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1)],
  .up 262321 1,
  .rs 262321 1 10,
  .par2 5113 262321,
  .force 5701 1 [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1), (262321, 2)],
  .up 5701 1,
  .rs 5701 1 9,
  .par2 5113 5701,
  .force 10835701 1 [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1), (5701, 2), (262321, 2)],
  .up 10835701 1,
  .rs 10835701 1 4,
  .par2 5113 10835701,
  .big [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1), (5701, 2), (262321, 2), (10835701, 2)],
  .big [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1), (5701, 2), (262321, 2)],
  .big [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1), (5701, 4), (262321, 2)],
  .big [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1), (5701, 6), (262321, 2)],
  .big [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1), (262321, 2)],
  .force 1856918071 1 [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1), (262321, 4)],
  .up 1856918071 1,
  .big [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1), (262321, 4)],
  .big [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1), (262321, 6)],
  .big [(5, 4), (71, 2), (97, 4), (2557, 2), (5113, 1)],
  .force 20241187 1 [(5, 4), (71, 2), (97, 6), (2557, 2), (5113, 1)],
  .up 20241187 1,
  .rs 20241187 1 7,
  .par2 5113 20241187,
  .force 1890771811 1 [(5, 4), (71, 2), (97, 6), (2557, 2), (5113, 1), (20241187, 2)],
  .up 1890771811 1,
  .rs 1890771811 1 4,
  .par2 5113 1890771811,
  .big [(5, 4), (71, 2), (97, 6), (2557, 2), (5113, 1), (20241187, 2), (1890771811, 2)],
  .big [(5, 4), (71, 2), (97, 6), (2557, 2), (5113, 1), (20241187, 2)],
  .big [(5, 4), (71, 2), (97, 6), (2557, 2), (5113, 1), (20241187, 4)],
  .big [(5, 4), (71, 2), (97, 6), (2557, 2), (5113, 1)],
  .force 837197335075000483 1 [(5, 4), (71, 2), (97, 10), (2557, 2), (5113, 1)],
  .up 837197335075000483 1,
  .big [(5, 4), (71, 2), (97, 10), (2557, 2), (5113, 1)],
  .force 8224356155341457 1 [(5, 4), (71, 2), (97, 12), (2557, 2), (5113, 1)],
  .up 8224356155341457 1,
  .big [(5, 4), (71, 2), (97, 12), (2557, 2), (5113, 1)],
  .big [(5, 4), (71, 2), (97, 16), (2557, 2), (5113, 1)],
  .big [(5, 4), (71, 2), (97, 18), (2557, 2), (5113, 1)],
  .big [(5, 4), (71, 2), (97, 22), (2557, 2), (5113, 1)],
  .big [(5, 4), (71, 2), (97, 28), (2557, 2), (5113, 1)],
  .big [(5, 4), (71, 2), (2557, 2), (5113, 1)],
  .force 323683781 1 [(5, 4), (71, 2), (2557, 4), (5113, 1)],
  .up 323683781 1,
  .rs 323683781 1 7,
  .par2 5113 323683781,
  .force 104771190406139743 1 [(5, 4), (71, 2), (2557, 4), (5113, 1), (323683781, 2)],
  .up 104771190406139743 1,
  .big [(5, 4), (71, 2), (2557, 4), (5113, 1), (323683781, 2)],
  .big [(5, 4), (71, 2), (2557, 4), (5113, 1), (323683781, 4)],
  .big [(5, 4), (71, 2), (2557, 4), (5113, 1)],
  .force 3353767033 1 [(5, 4), (71, 2), (2557, 6), (5113, 1)],
  .up 3353767033 1,
  .rs 3353767033 1 5,
  .par2 5113 3353767033,
  .big [(5, 4), (71, 2), (2557, 6), (5113, 1), (3353767033, 2)],
  .big [(5, 4), (71, 2), (2557, 6), (5113, 1)],
  .big [(5, 4), (71, 2), (2557, 10), (5113, 1)],
  .big [(5, 4), (71, 2), (2557, 12), (5113, 1)],
  .big [(5, 4), (71, 2), (2557, 16), (5113, 1)],
  .big [(5, 4), (71, 2), (2557, 18), (5113, 1)],
  .big [(5, 4), (71, 2), (5113, 1)],
  .force 8715961 1 [(5, 4), (71, 2), (5113, 2)],
  .rs 8715961 1 11,
  .force 92723 1 [(5, 4), (71, 2), (5113, 2), (8715961, 1)],
  .up 92723 1,
  .rs 92723 1 13,
  .par2 8715961 92723,
  .force 8597647453 1 [(5, 4), (71, 2), (5113, 2), (92723, 2), (8715961, 1)],
  .up 8597647453 1,
  .rs 8597647453 1 6,
  .par2 8715961 8597647453,
  .force 1049590933663 1 [(5, 4), (71, 2), (5113, 2), (92723, 2), (8715961, 1), (8597647453, 2)],
  .up 1049590933663 1,
  .big [(5, 4), (71, 2), (5113, 2), (92723, 2), (8715961, 1), (8597647453, 2)],
  .big [(5, 4), (71, 2), (5113, 2), (92723, 2), (8715961, 1), (8597647453, 4)],
  .big [(5, 4), (71, 2), (5113, 2), (92723, 2), (8715961, 1)],
  .force 216770511782448821 1 [(5, 4), (71, 2), (5113, 2), (92723, 4), (8715961, 1)],
  .up 216770511782448821 1,
  .big [(5, 4), (71, 2), (5113, 2), (92723, 4), (8715961, 1)],
  .big [(5, 4), (71, 2), (5113, 2), (92723, 6), (8715961, 1)],
  .big [(5, 4), (71, 2), (5113, 2), (92723, 10), (8715961, 1)],
  .big [(5, 4), (71, 2), (5113, 2), (8715961, 1)],
  .force 3617523089023 1 [(5, 4), (71, 2), (5113, 2), (8715961, 2)],
  .up 3617523089023 1,
  .rs 3617523089023 1 5,
  .parS 3617523089023,
  .big [(5, 4), (71, 2), (5113, 2), (8715961, 2), (3617523089023, 2)],
  .big [(5, 4), (71, 2), (5113, 2), (8715961, 2)],
  .force 7105848287681981 1 [(5, 4), (71, 2), (5113, 2), (8715961, 4)],
  .rs 7105848287681981 1 3,
  .big [(5, 4), (71, 2), (5113, 2), (8715961, 4), (7105848287681981, 1)],
  .big [(5, 4), (71, 2), (5113, 2), (8715961, 4)],
  .big [(5, 4), (71, 2), (5113, 2), (8715961, 6)],
  .big [(5, 4), (71, 2), (5113, 2)],
  .force 13080080081 1 [(5, 4), (71, 2), (5113, 4)],
  .rs 13080080081 1 7,
  .force 94783189 1 [(5, 4), (71, 2), (5113, 4), (13080080081, 1)],
  .up 94783189 1,
  .rs 94783189 1 7,
  .par2 13080080081 94783189,
  .force 34540591 1 [(5, 4), (71, 2), (5113, 4), (94783189, 2), (13080080081, 1)],
  .up 34540591 1,
  .rs 34540591 1 4,
  .par2 13080080081 34540591,
  .big [(5, 4), (71, 2), (5113, 4), (34540591, 2), (94783189, 2), (13080080081, 1)],
  .big [(5, 4), (71, 2), (5113, 4), (94783189, 2), (13080080081, 1)],
  .big [(5, 4), (71, 2), (5113, 4), (94783189, 4), (13080080081, 1)],
  .big [(5, 4), (71, 2), (5113, 4), (13080080081, 1)],
  .force 21261152595806269 1 [(5, 4), (71, 2), (5113, 4), (13080080081, 2)],
  .rs 21261152595806269 1 3,
  .big [(5, 4), (71, 2), (5113, 4), (13080080081, 2), (21261152595806269, 1)],
  .big [(5, 4), (71, 2), (5113, 4), (13080080081, 2)],
  .big [(5, 4), (71, 2), (5113, 4), (13080080081, 4)],
  .big [(5, 4), (71, 2), (5113, 4)],
  .force 10768274427527 1 [(5, 4), (71, 2), (5113, 6)],
  .up 10768274427527 1,
  .rs 10768274427527 1 5,
  .parS 10768274427527,
  .big [(5, 4), (71, 2), (5113, 6), (10768274427527, 2)],
  .big [(5, 4), (71, 2), (5113, 6)],
  .big [(5, 4), (71, 2), (5113, 10)],
  .big [(5, 4), (71, 2), (5113, 12)],
  .big [(5, 4), (71, 2), (5113, 16)],
  .big [(5, 4), (71, 2), (5113, 18)],
  .big [(5, 4), (71, 2)],
  .force 2221 1 [(5, 4), (71, 4)],
  .rs 2221 1 21,
  .force 211 1 [(5, 4), (71, 4), (2221, 1)],
  .up 211 1,
  .rs 211 1 27,
  .par2 2221 211,
  .force 101 1 [(5, 4), (71, 4), (211, 2), (2221, 1)],
  .up 101 1,
  .rs 101 1 28,
  .par2 2221 101,
  .force 10303 1 [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1)],
  .up 10303 1,
  .rs 10303 1 14,
  .par2 2221 10303,
  .force 6073 1 [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (10303, 2)],
  .up 6073 1,
  .rs 6073 1 11,
  .par2 2221 6073,
  .force 12637 1 [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (6073, 2), (10303, 2)],
  .up 12637 1,
  .rs 12637 1 8,
  .par2 2221 12637,
  .force 104179 1 [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (6073, 2), (10303, 2), (12637, 2)],
  .up 104179 1,
  .rs 104179 1 4,
  .par2 2221 104179,
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (6073, 2), (10303, 2), (12637, 2), (104179, 2)],
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (6073, 2), (10303, 2), (12637, 2)],
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (6073, 2), (10303, 2), (12637, 4)],
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (6073, 2), (10303, 2), (12637, 6)],
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (6073, 2), (10303, 2)],
  .force 11677891 1 [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (6073, 4), (10303, 2)],
  .up 11677891 1,
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (6073, 4), (10303, 2)],
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (6073, 6), (10303, 2)],
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (10303, 2)],
  .force 372649725281 1 [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (10303, 4)],
  .up 372649725281 1,
  .rs 372649725281 1 4,
  .par2 2221 372649725281,
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (10303, 4), (372649725281, 2)],
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (10303, 4)],
  .force 4513076485163 1 [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (10303, 6)],
  .up 4513076485163 1,
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (10303, 6)],
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (10303, 10)],
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1), (10303, 12)],
  .big [(5, 4), (71, 4), (101, 2), (211, 2), (2221, 1)],
  .force 1381 1 [(5, 4), (71, 4), (101, 4), (211, 2), (2221, 1)],
  .up 1381 1,
  .rs 1381 1 15,
  .par2 2221 1381,
  .force 6991 1 [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 2), (2221, 1)],
  .up 6991 1,
  .rs 6991 1 10,
  .par2 2221 6991,
  .force 16293691 1 [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 2), (2221, 1), (6991, 2)],
  .up 16293691 1,
  .rs 16293691 1 5,
  .par2 2221 16293691,
  .big [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 2), (2221, 1), (6991, 2), (16293691, 2)],
  .big [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 2), (2221, 1), (6991, 2)],
  .force 35761058621 1 [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 2), (2221, 1), (6991, 4)],
  .up 35761058621 1,
  .big [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 2), (2221, 1), (6991, 4)],
  .big [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 2), (2221, 1), (6991, 6)],
  .big [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 2), (2221, 1)],
  .force 822761 1 [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 4), (2221, 1)],
  .up 822761 1,
  .rs 822761 1 5,
  .par2 2221 822761,
  .big [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 4), (2221, 1), (822761, 2)]]

/-- Instructions, part 2. -/
def tree5_2 : List Ins := [
  .big [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 4), (2221, 1)],
  .force 46848518953531 1 [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 6), (2221, 1)],
  .up 46848518953531 1,
  .big [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 6), (2221, 1)],
  .big [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 10), (2221, 1)],
  .big [(5, 4), (71, 4), (101, 4), (211, 2), (1381, 12), (2221, 1)],
  .big [(5, 4), (71, 4), (101, 4), (211, 2), (2221, 1)],
  .force 15100497917 1 [(5, 4), (71, 4), (101, 6), (211, 2), (2221, 1)],
  .up 15100497917 1,
  .rs 15100497917 1 6,
  .par2 2221 15100497917,
  .force 228025037356421836807 1 [(5, 4), (71, 4), (101, 6), (211, 2), (2221, 1), (15100497917, 2)],
  .up 228025037356421836807 1,
  .big [(5, 4), (71, 4), (101, 6), (211, 2), (2221, 1), (15100497917, 2)],
  .big [(5, 4), (71, 4), (101, 6), (211, 2), (2221, 1), (15100497917, 4)],
  .big [(5, 4), (71, 4), (101, 6), (211, 2), (2221, 1)],
  .force 2585122674619 1 [(5, 4), (71, 4), (101, 10), (211, 2), (2221, 1)],
  .up 2585122674619 1,
  .rs 2585122674619 1 4,
  .par2 2221 2585122674619,
  .big [(5, 4), (71, 4), (101, 10), (211, 2), (2221, 1), (2585122674619, 2)],
  .big [(5, 4), (71, 4), (101, 10), (211, 2), (2221, 1)],
  .force 2891083442729 1 [(5, 4), (71, 4), (101, 12), (211, 2), (2221, 1)],
  .up 2891083442729 1,
  .big [(5, 4), (71, 4), (101, 12), (211, 2), (2221, 1)],
  .big [(5, 4), (71, 4), (101, 16), (211, 2), (2221, 1)],
  .big [(5, 4), (71, 4), (101, 18), (211, 2), (2221, 1)],
  .big [(5, 4), (71, 4), (101, 22), (211, 2), (2221, 1)],
  .big [(5, 4), (71, 4), (211, 2), (2221, 1)],
  .force 292661 1 [(5, 4), (71, 4), (211, 4), (2221, 1)],
  .up 292661 1,
  .rs 292661 1 10,
  .par2 2221 292661,
  .force 85650753583 1 [(5, 4), (71, 4), (211, 4), (2221, 1), (292661, 2)],
  .up 85650753583 1,
  .rs 85650753583 1 5,
  .par2 2221 85650753583,
  .big [(5, 4), (71, 4), (211, 4), (2221, 1), (292661, 2), (85650753583, 2)],
  .big [(5, 4), (71, 4), (211, 4), (2221, 1), (292661, 2)],
  .force 3646526369051 1 [(5, 4), (71, 4), (211, 4), (2221, 1), (292661, 4)],
  .up 3646526369051 1,
  .big [(5, 4), (71, 4), (211, 4), (2221, 1), (292661, 4)],
  .big [(5, 4), (71, 4), (211, 4), (2221, 1), (292661, 6)],
  .big [(5, 4), (71, 4), (211, 4), (2221, 1)],
  .force 41233879 1 [(5, 4), (71, 4), (211, 6), (2221, 1)],
  .up 41233879 1,
  .rs 41233879 1 7,
  .par2 2221 41233879,
  .force 2351635987027 1 [(5, 4), (71, 4), (211, 6), (2221, 1), (41233879, 2)],
  .up 2351635987027 1,
  .big [(5, 4), (71, 4), (211, 6), (2221, 1), (41233879, 2)],
  .big [(5, 4), (71, 4), (211, 6), (2221, 1), (41233879, 4)],
  .big [(5, 4), (71, 4), (211, 6), (2221, 1)],
  .force 3693170746409441903 1 [(5, 4), (71, 4), (211, 10), (2221, 1)],
  .up 3693170746409441903 1,
  .big [(5, 4), (71, 4), (211, 10), (2221, 1)],
  .force 1606424290213518947263 1 [(5, 4), (71, 4), (211, 12), (2221, 1)],
  .up 1606424290213518947263 1,
  .big [(5, 4), (71, 4), (211, 12), (2221, 1)],
  .big [(5, 4), (71, 4), (211, 16), (2221, 1)],
  .big [(5, 4), (71, 4), (211, 18), (2221, 1)],
  .big [(5, 4), (71, 4), (211, 22), (2221, 1)],
  .big [(5, 4), (71, 4), (2221, 1)],
  .force 235003 1 [(5, 4), (71, 4), (2221, 2)],
  .up 235003 1,
  .rs 235003 1 12,
  .parS 235003,
  .force 122971 1 [(5, 4), (71, 4), (2221, 2), (235003, 2)],
  .up 122971 1,
  .rs 122971 1 9,
  .parS 122971,
  .force 3318409 1 [(5, 4), (71, 4), (2221, 2), (122971, 2), (235003, 2)],
  .rs 3318409 1 6,
  .force 331841 1 [(5, 4), (71, 4), (2221, 2), (122971, 2), (235003, 2), (3318409, 1)],
  .up 331841 1,
  .rs 331841 1 5,
  .par2 3318409 331841,
  .big [(5, 4), (71, 4), (2221, 2), (122971, 2), (235003, 2), (331841, 2), (3318409, 1)],
  .big [(5, 4), (71, 4), (2221, 2), (122971, 2), (235003, 2), (3318409, 1)],
  .force 78149713 1 [(5, 4), (71, 4), (2221, 2), (122971, 2), (235003, 2), (3318409, 2)],
  .rs 78149713 1 3,
  .big [(5, 4), (71, 4), (2221, 2), (122971, 2), (235003, 2), (3318409, 2), (78149713, 1)],
  .big [(5, 4), (71, 4), (2221, 2), (122971, 2), (235003, 2), (3318409, 2)],
  .big [(5, 4), (71, 4), (2221, 2), (122971, 2), (235003, 2), (3318409, 4)],
  .big [(5, 4), (71, 4), (2221, 2), (122971, 2), (235003, 2)],
  .big [(5, 4), (71, 4), (2221, 2), (122971, 4), (235003, 2)],
  .big [(5, 4), (71, 4), (2221, 2), (122971, 6), (235003, 2)],
  .big [(5, 4), (71, 4), (2221, 2), (235003, 2)],
  .force 32488790012831 1 [(5, 4), (71, 4), (2221, 2), (235003, 4)],
  .up 32488790012831 1,
  .big [(5, 4), (71, 4), (2221, 2), (235003, 4)],
  .big [(5, 4), (71, 4), (2221, 2), (235003, 6)],
  .big [(5, 4), (71, 4), (2221, 2), (235003, 10)],
  .big [(5, 4), (71, 4), (2221, 2)],
  .force 17950001 1 [(5, 4), (71, 4), (2221, 4)],
  .rs 17950001 1 8,
  .force 427381 1 [(5, 4), (71, 4), (2221, 4), (17950001, 1)],
  .up 427381 1,
  .rs 427381 1 8,
  .par2 17950001 427381,
  .force 69424153 1 [(5, 4), (71, 4), (2221, 4), (427381, 2), (17950001, 1)],
  .up 69424153 1,
  .rs 69424153 1 4,
  .par2 17950001 69424153,
  .big [(5, 4), (71, 4), (2221, 4), (427381, 2), (17950001, 1), (69424153, 2)],
  .big [(5, 4), (71, 4), (2221, 4), (427381, 2), (17950001, 1)],
  .big [(5, 4), (71, 4), (2221, 4), (427381, 4), (17950001, 1)],
  .big [(5, 4), (71, 4), (2221, 4), (427381, 6), (17950001, 1)],
  .big [(5, 4), (71, 4), (2221, 4), (17950001, 1)],
  .force 19350342553 1 [(5, 4), (71, 4), (2221, 4), (17950001, 2)],
  .rs 19350342553 1 4,
  .force 271241 1 [(5, 4), (71, 4), (2221, 4), (17950001, 2), (19350342553, 1)],
  .up 271241 1,
  .rs 271241 1 4,
  .par2 19350342553 271241,
  .big [(5, 4), (71, 4), (2221, 4), (271241, 2), (17950001, 2), (19350342553, 1)],
  .big [(5, 4), (71, 4), (2221, 4), (17950001, 2), (19350342553, 1)],
  .big [(5, 4), (71, 4), (2221, 4), (17950001, 2), (19350342553, 2)],
  .big [(5, 4), (71, 4), (2221, 4), (17950001, 2)],
  .big [(5, 4), (71, 4), (2221, 4), (17950001, 4)],
  .big [(5, 4), (71, 4), (2221, 4), (17950001, 6)],
  .big [(5, 4), (71, 4), (2221, 4)],
  .force 1183576566098753 1 [(5, 4), (71, 4), (2221, 6)],
  .rs 1183576566098753 1 4,
  .force 12809 1 [(5, 4), (71, 4), (2221, 6), (1183576566098753, 1)],
  .up 12809 1,
  .rs 12809 1 5,
  .par2 1183576566098753 12809,
  .big [(5, 4), (71, 4), (2221, 6), (12809, 2), (1183576566098753, 1)],
  .big [(5, 4), (71, 4), (2221, 6), (1183576566098753, 1)],
  .big [(5, 4), (71, 4), (2221, 6), (1183576566098753, 2)],
  .big [(5, 4), (71, 4), (2221, 6)],
  .big [(5, 4), (71, 4), (2221, 10)],
  .big [(5, 4), (71, 4), (2221, 12)],
  .big [(5, 4), (71, 4), (2221, 16)],
  .big [(5, 4), (71, 4), (2221, 18)],
  .big [(5, 4), (71, 4)],
  .force 21020917 1 [(5, 4), (71, 6)],
  .rs 21020917 1 10,
  .force 10510459 1 [(5, 4), (71, 6), (21020917, 1)],
  .up 10510459 1,
  .rs 10510459 1 9,
  .par2 21020917 10510459,
  .force 85375177 1 [(5, 4), (71, 6), (10510459, 2), (21020917, 1)],
  .up 85375177 1,
  .rs 85375177 1 6,
  .par2 21020917 85375177,
  .force 127875805844851 1 [(5, 4), (71, 6), (10510459, 2), (21020917, 1), (85375177, 2)],
  .up 127875805844851 1,
  .big [(5, 4), (71, 6), (10510459, 2), (21020917, 1), (85375177, 2)],
  .big [(5, 4), (71, 6), (10510459, 2), (21020917, 1), (85375177, 4)],
  .big [(5, 4), (71, 6), (10510459, 2), (21020917, 1)],
  .big [(5, 4), (71, 6), (10510459, 4), (21020917, 1)],
  .big [(5, 4), (71, 6), (10510459, 6), (21020917, 1)],
  .big [(5, 4), (71, 6), (21020917, 1)],
  .force 97292389 1 [(5, 4), (71, 6), (21020917, 2)],
  .rs 97292389 1 6,
  .force 1513921 1 [(5, 4), (71, 6), (21020917, 2), (97292389, 1)],
  .up 1513921 1,
  .rs 1513921 1 6,
  .par2 97292389 1513921,
  .force 11131 1 [(5, 4), (71, 6), (1513921, 2), (21020917, 2), (97292389, 1)],
  .up 11131 1,
  .rs 11131 1 4,
  .par2 97292389 11131,
  .big [(5, 4), (71, 6), (11131, 2), (1513921, 2), (21020917, 2), (97292389, 1)],
  .big [(5, 4), (71, 6), (1513921, 2), (21020917, 2), (97292389, 1)],
  .big [(5, 4), (71, 6), (1513921, 4), (21020917, 2), (97292389, 1)],
  .big [(5, 4), (71, 6), (21020917, 2), (97292389, 1)],
  .force 25813566589 1 [(5, 4), (71, 6), (21020917, 2), (97292389, 2)],
  .rs 25813566589 1 3,
  .big [(5, 4), (71, 6), (21020917, 2), (97292389, 2), (25813566589, 1)],
  .big [(5, 4), (71, 6), (21020917, 2), (97292389, 2)],
  .big [(5, 4), (71, 6), (21020917, 2), (97292389, 4)],
  .big [(5, 4), (71, 6), (21020917, 2)],
  .force 19566123517737808021 1 [(5, 4), (71, 6), (21020917, 4)],
  .rs 19566123517737808021 1 3,
  .big [(5, 4), (71, 6), (21020917, 4), (19566123517737808021, 1)],
  .big [(5, 4), (71, 6), (21020917, 4)],
  .big [(5, 4), (71, 6), (21020917, 6)],
  .big [(5, 4), (71, 6)],
  .force 143554218709131407 1 [(5, 4), (71, 10)],
  .up 143554218709131407 1,
  .rs 143554218709131407 1 5,
  .parS 143554218709131407,
  .big [(5, 4), (71, 10), (143554218709131407, 2)],
  .big [(5, 4), (71, 10)],
  .force 5196608121641 1 [(5, 4), (71, 12)],
  .rs 5196608121641 1 5,
  .force 3202878953 1 [(5, 4), (71, 12), (5196608121641, 1)],
  .up 3202878953 1,
  .rs 3202878953 1 4,
  .par2 5196608121641 3202878953,
  .big [(5, 4), (71, 12), (3202878953, 2), (5196608121641, 1)],
  .big [(5, 4), (71, 12), (5196608121641, 1)],
  .big [(5, 4), (71, 12), (5196608121641, 2)],
  .big [(5, 4), (71, 12)],
  .force 484563667343825089 1 [(5, 4), (71, 16)],
  .rs 484563667343825089 1 3,
  .big [(5, 4), (71, 16), (484563667343825089, 1)],
  .big [(5, 4), (71, 16)],
  .force 1121659287043817009 1 [(5, 4), (71, 18)],
  .rs 1121659287043817009 1 3,
  .big [(5, 4), (71, 18), (1121659287043817009, 1)],
  .big [(5, 4), (71, 18)],
  .big [(5, 4), (71, 22)],
  .big [(5, 4), (71, 28)],
  .big [(5, 4), (71, 30)],
  .big [(5, 4), (71, 36)],
  .big [(5, 4), (71, 40)],
  .big [(5, 4)],
  .force 19531 1 [(5, 6)],
  .up 19531 1,
  .rs 19531 1 19,
  .parS 19531,
  .force 127159831 1 [(5, 6), (19531, 2)],
  .up 127159831 1,
  .rs 127159831 1 10,
  .parS 127159831,
  .force 763058587 1 [(5, 6), (19531, 2), (127159831, 2)],
  .up 763058587 1,
  .rs 763058587 1 6,
  .parS 763058587,
  .force 30652009 1 [(5, 6), (19531, 2), (127159831, 2), (763058587, 2)],
  .rs 30652009 1 3,
  .force 7063513 1 [(5, 6), (19531, 2), (30652009, 1), (127159831, 2), (763058587, 2)],
  .up 7063513 1,
  .big [(5, 6), (19531, 2), (30652009, 1), (127159831, 2), (763058587, 2)],
  .big [(5, 6), (19531, 2), (127159831, 2), (763058587, 2)],
  .big [(5, 6), (19531, 2), (127159831, 2), (763058587, 4)],
  .big [(5, 6), (19531, 2), (127159831, 2)],
  .force 5580127603378541 1 [(5, 6), (19531, 2), (127159831, 4)],
  .rs 5580127603378541 1 3,
  .big [(5, 6), (19531, 2), (127159831, 4), (5580127603378541, 1)],
  .big [(5, 6), (19531, 2), (127159831, 4)],
  .big [(5, 6), (19531, 2), (127159831, 6)],
  .big [(5, 6), (19531, 2)],
  .force 32009891 1 [(5, 6), (19531, 4)],
  .up 32009891 1,
  .rs 32009891 1 8,
  .parS 32009891,
  .force 4760281 1 [(5, 6), (19531, 4), (32009891, 2)],
  .rs 4760281 1 5,
  .force 2380141 1 [(5, 6), (19531, 4), (4760281, 1), (32009891, 2)],
  .up 2380141 1,
  .rs 2380141 1 4,
  .par2 4760281 2380141,
  .big [(5, 6), (19531, 4), (2380141, 2), (4760281, 1), (32009891, 2)],
  .big [(5, 6), (19531, 4), (4760281, 1), (32009891, 2)],
  .big [(5, 6), (19531, 4), (4760281, 2), (32009891, 2)],
  .big [(5, 6), (19531, 4), (32009891, 2)],
  .big [(5, 6), (19531, 4), (32009891, 4)],
  .big [(5, 6), (19531, 4), (32009891, 6)],
  .big [(5, 6), (19531, 4)],
  .force 12567292335484050831661 1 [(5, 6), (19531, 6)],
  .rs 12567292335484050831661 1 4,
  .force 10926617075177803 1 [(5, 6), (19531, 6), (12567292335484050831661, 1)],
  .up 10926617075177803 1,
  .big [(5, 6), (19531, 6), (12567292335484050831661, 1)],
  .big [(5, 6), (19531, 6), (12567292335484050831661, 2)],
  .big [(5, 6), (19531, 6)],
  .big [(5, 6), (19531, 10)],
  .big [(5, 6), (19531, 12)],
  .big [(5, 6), (19531, 16)],
  .big [(5, 6)],
  .force 12207031 1 [(5, 10)],
  .up 12207031 1,
  .rs 12207031 1 12,
  .parS 12207031,
  .force 6811369 1 [(5, 10), (12207031, 2)],
  .rs 6811369 1 9,
  .force 1041757 1 [(5, 10), (6811369, 1), (12207031, 2)],
  .up 1041757 1,
  .rs 1041757 1 9,
  .par2 6811369 1041757,
  .force 185419219 1 [(5, 10), (1041757, 2), (6811369, 1), (12207031, 2)],
  .up 185419219 1,
  .rs 185419219 1 5,
  .par2 6811369 185419219,
  .big [(5, 10), (1041757, 2), (6811369, 1), (12207031, 2), (185419219, 2)],
  .big [(5, 10), (1041757, 2), (6811369, 1), (12207031, 2)],
  .big [(5, 10), (1041757, 4), (6811369, 1), (12207031, 2)],
  .big [(5, 10), (1041757, 6), (6811369, 1), (12207031, 2)],
  .big [(5, 10), (6811369, 1), (12207031, 2)],
  .force 15464918155177 1 [(5, 10), (6811369, 2), (12207031, 2)],
  .rs 15464918155177 1 4,
  .force 1600591819 1 [(5, 10), (6811369, 2), (12207031, 2), (15464918155177, 1)],
  .up 1600591819 1,
  .rs 1600591819 1 4,
  .par2 15464918155177 1600591819,
  .big [(5, 10), (6811369, 2), (12207031, 2), (1600591819, 2), (15464918155177, 1)],
  .big [(5, 10), (6811369, 2), (12207031, 2), (15464918155177, 1)],
  .big [(5, 10), (6811369, 2), (12207031, 2), (15464918155177, 2)],
  .big [(5, 10), (6811369, 2), (12207031, 2)],
  .big [(5, 10), (6811369, 4), (12207031, 2)],
  .big [(5, 10), (6811369, 6), (12207031, 2)],
  .big [(5, 10), (12207031, 2)],
  .force 33899939683211028917156831 1 [(5, 10), (12207031, 4)],
  .up 33899939683211028917156831 1,
  .big [(5, 10), (12207031, 4)],
  .big [(5, 10), (12207031, 6)],
  .big [(5, 10), (12207031, 10)],
  .big [(5, 10)],
  .force 305175781 1 [(5, 12)],
  .rs 305175781 1 10,
  .force 43609 1 [(5, 12), (305175781, 1)],
  .up 43609 1,
  .rs 43609 1 14,
  .par2 305175781 43609,
  .force 633929497 1 [(5, 12), (43609, 2), (305175781, 1)],
  .up 633929497 1,
  .rs 633929497 1 7,
  .par2 305175781 633929497,
  .force 1433991301 1 [(5, 12), (43609, 2), (305175781, 1), (633929497, 2)],
  .up 1433991301 1,
  .rs 1433991301 1 4,
  .par2 305175781 1433991301,
  .big [(5, 12), (43609, 2), (305175781, 1), (633929497, 2), (1433991301, 2)],
  .big [(5, 12), (43609, 2), (305175781, 1), (633929497, 2)],
  .big [(5, 12), (43609, 2), (305175781, 1), (633929497, 4)],
  .big [(5, 12), (43609, 2), (305175781, 1)],
  .force 9967721 1 [(5, 12), (43609, 4), (305175781, 1)],
  .up 9967721 1,
  .rs 9967721 1 6,
  .par2 305175781 9967721,
  .force 552284737 1 [(5, 12), (43609, 4), (9967721, 2), (305175781, 1)],
  .up 552284737 1,
  .big [(5, 12), (43609, 4), (9967721, 2), (305175781, 1)],
  .big [(5, 12), (43609, 4), (9967721, 4), (305175781, 1)],
  .big [(5, 12), (43609, 4), (305175781, 1)],
  .force 5968930061879 1 [(5, 12), (43609, 6), (305175781, 1)],
  .up 5968930061879 1,
  .big [(5, 12), (43609, 6), (305175781, 1)],
  .big [(5, 12), (43609, 10), (305175781, 1)],
  .big [(5, 12), (43609, 12), (305175781, 1)],
  .big [(5, 12), (305175781, 1)],
  .force 12340172617 1 [(5, 12), (305175781, 2)],
  .rs 12340172617 1 6,
  .force 6170086309 1 [(5, 12), (305175781, 2), (12340172617, 1)],
  .up 6170086309 1,
  .rs 6170086309 1 5,
  .par2 12340172617 6170086309,
  .big [(5, 12), (305175781, 2), (6170086309, 2), (12340172617, 1)],
  .big [(5, 12), (305175781, 2), (12340172617, 1)],
  .force 280441731546402949 1 [(5, 12), (305175781, 2), (12340172617, 2)],
  .rs 280441731546402949 1 3,
  .big [(5, 12), (305175781, 2), (12340172617, 2), (280441731546402949, 1)],
  .big [(5, 12), (305175781, 2), (12340172617, 2)],
  .big [(5, 12), (305175781, 2), (12340172617, 4)],
  .big [(5, 12), (305175781, 2)],
  .force 29320017968958271 1 [(5, 12), (305175781, 4)],
  .up 29320017968958271 1,
  .big [(5, 12), (305175781, 4)],
  .big [(5, 12), (305175781, 6)],
  .big [(5, 12)],
  .force 466344409 1 [(5, 16)],
  .rs 466344409 1 9,
  .force 6662063 1 [(5, 16), (466344409, 1)],
  .up 6662063 1,
  .rs 6662063 1 10,
  .par2 466344409 6662063,
  .force 6340441439719 1 [(5, 16), (6662063, 2), (466344409, 1)],
  .up 6340441439719 1,
  .rs 6340441439719 1 5,
  .par2 466344409 6340441439719,
  .big [(5, 16), (6662063, 2), (466344409, 1), (6340441439719, 2)],
  .big [(5, 16), (6662063, 2), (466344409, 1)],
  .force 646835392346141 1 [(5, 16), (6662063, 4), (466344409, 1)],
  .up 646835392346141 1,
  .big [(5, 16), (6662063, 4), (466344409, 1)],
  .big [(5, 16), (6662063, 6), (466344409, 1)],
  .big [(5, 16), (466344409, 1)],
  .force 3815387864419363 1 [(5, 16), (466344409, 2)],
  .up 3815387864419363 1,
  .rs 3815387864419363 1 4,
  .parS 3815387864419363,
  .big [(5, 16), (466344409, 2), (3815387864419363, 2)],
  .big [(5, 16), (466344409, 2)],
  .big [(5, 16), (466344409, 4)],
  .big [(5, 16), (466344409, 6)],
  .big [(5, 16)],
  .force 3981071 1 [(5, 18)],
  .up 3981071 1,
  .rs 3981071 1 11,
  .parS 3981071,
  .force 1219148483701 1 [(5, 18), (3981071, 2)],
  .rs 1219148483701 1 5,
  .force 19663685221 1 [(5, 18), (3981071, 2), (1219148483701, 1)],
  .up 19663685221 1,
  .rs 19663685221 1 5,
  .par2 1219148483701 19663685221,
  .big [(5, 18), (3981071, 2), (19663685221, 2), (1219148483701, 1)],
  .big [(5, 18), (3981071, 2), (1219148483701, 1)],
  .big [(5, 18), (3981071, 2), (1219148483701, 2)],
  .big [(5, 18), (3981071, 2)],
  .force 5378193516362980863601 1 [(5, 18), (3981071, 4)],
  .rs 5378193516362980863601 1 3,
  .big [(5, 18), (3981071, 4), (5378193516362980863601, 1)],
  .big [(5, 18), (3981071, 4)],
  .big [(5, 18), (3981071, 6)]]

/-- Instructions, part 3. -/
def tree5_3 : List Ins := [
  .big [(5, 18)],
  .force 332207361361 1 [(5, 22)],
  .rs 332207361361 1 7,
  .force 612928711 1 [(5, 22), (332207361361, 1)],
  .up 612928711 1,
  .rs 612928711 1 7,
  .par2 332207361361 612928711,
  .force 2663944399 1 [(5, 22), (612928711, 2), (332207361361, 1)],
  .up 2663944399 1,
  .rs 2663944399 1 4,
  .par2 332207361361 2663944399,
  .big [(5, 22), (612928711, 2), (2663944399, 2), (332207361361, 1)],
  .big [(5, 22), (612928711, 2), (332207361361, 1)],
  .big [(5, 22), (612928711, 4), (332207361361, 1)],
  .big [(5, 22), (332207361361, 1)],
  .force 719272201686877 1 [(5, 22), (332207361361, 2)],
  .rs 719272201686877 1 3,
  .big [(5, 22), (332207361361, 2), (719272201686877, 1)],
  .big [(5, 22), (332207361361, 2)],
  .big [(5, 22), (332207361361, 4)],
  .big [(5, 22)],
  .force 22125996444329 1 [(5, 28)],
  .rs 22125996444329 1 5,
  .force 822599 1 [(5, 28), (22125996444329, 1)],
  .up 822599 1,
  .rs 822599 1 7,
  .par2 22125996444329 822599,
  .force 17634931 1 [(5, 28), (822599, 2), (22125996444329, 1)],
  .up 17634931 1,
  .rs 17634931 1 4,
  .par2 22125996444329 17634931,
  .big [(5, 28), (822599, 2), (17634931, 2), (22125996444329, 1)],
  .big [(5, 28), (822599, 2), (22125996444329, 1)],
  .big [(5, 28), (822599, 4), (22125996444329, 1)],
  .big [(5, 28), (22125996444329, 1)],
  .big [(5, 28), (22125996444329, 2)],
  .big [(5, 28)],
  .force 625552508473588471 1 [(5, 30)],
  .up 625552508473588471 1,
  .rs 625552508473588471 1 5,
  .parS 625552508473588471,
  .big [(5, 30), (625552508473588471, 2)],
  .big [(5, 30)],
  .force 8737481256739 1 [(5, 36)],
  .up 8737481256739 1,
  .rs 8737481256739 1 5,
  .parS 8737481256739,
  .big [(5, 36), (8737481256739, 2)],
  .big [(5, 36)],
  .force 5079304643216687969 1 [(5, 40)],
  .rs 5079304643216687969 1 4,
  .force 169310154773889599 1 [(5, 40), (5079304643216687969, 1)],
  .up 169310154773889599 1,
  .big [(5, 40), (5079304643216687969, 1)],
  .big [(5, 40), (5079304643216687969, 2)],
  .big [(5, 40)],
  .force 172827552198815888791 1 [(5, 42)],
  .up 172827552198815888791 1,
  .big [(5, 42)],
  .force 177635683940025046467781066894531 1 [(5, 46)],
  .up 177635683940025046467781066894531 1,
  .big [(5, 46)],
  .force 27145365052629449 1 [(5, 52)],
  .rs 27145365052629449 1 3,
  .big [(5, 52), (27145365052629449, 1)],
  .big [(5, 52)],
  .big [(5, 58)],
  .big [(5, 60)],
  .big [(5, 66)],
  .big [(5, 70)],
  .big [(5, 72)],
  .big [(5, 78)],
  .big [(5, 82)],
  .big [(5, 88)],
  .big [(5, 96)],
  .big [(5, 100)],
  .big [(5, 102)],
  .big [(5, 106)],
  .big [(5, 108)],
  .big [(5, 112)],
  .big []]

/-- The tree for `5`. -/
def tree5 : List Ins := tree5_0 ++ tree5_1 ++ tree5_2 ++ tree5_3

/-- Instructions, part 0. -/
def tree7_0 : List Ins := [
  .up 7 1,
  .rs 7 1 95,
  .parS 7,
  .force 19 1 [(7, 2)],
  .up 19 1,
  .rs 19 1 62,
  .parS 19,
  .force 127 1 [(7, 2), (19, 2)],
  .up 127 1,
  .rs 127 1 37,
  .parS 127,
  .force 5419 1 [(7, 2), (19, 2), (127, 2)],
  .up 5419 1,
  .rs 5419 1 20,
  .parS 5419,
  .force 1009 1 [(7, 2), (19, 2), (127, 2), (5419, 2)],
  .rs 1009 1 21,
  .force 313 1 [(7, 2), (19, 2), (127, 2), (1009, 1), (5419, 2)],
  .up 313 1,
  .rs 313 1 23,
  .par2 1009 313,
  .force 181 2 [(7, 2), (19, 2), (127, 2), (313, 2), (1009, 1), (5419, 2)],
  .rs 181 1 23,
  .par2 1009 181,
  .force 139 1 [(7, 2), (19, 2), (127, 2), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .up 139 1,
  .rs 139 1 21,
  .par2 1009 139,
  .force 499 1 [(7, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .up 499 1,
  .rs 499 1 15,
  .par2 1009 499,
  .force 109 2 [(7, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .rs 109 1 16,
  .par2 1009 109,
  .force 571 1 [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .up 571 1,
  .rs 571 1 11,
  .par2 1009 571,
  .force 151 1 [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .up 151 1,
  .rs 151 1 9,
  .par2 1009 151,
  .force 1093 1 [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (151, 2), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .up 1093 1,
  .rs 1093 1 5,
  .par2 1009 1093,
  .big [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (151, 2), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (1093, 2), (5419, 2)],
  .big [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (151, 2), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (151, 4), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (151, 6), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (571, 2), (1009, 1), (5419, 2)],
  .force 11631811 1 [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (571, 4), (1009, 1), (5419, 2)],
  .up 11631811 1,
  .big [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (571, 4), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (571, 6), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (109, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .force 24061 1 [(7, 2), (19, 2), (109, 4), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .up 24061 1,
  .rs 24061 1 6,
  .par2 1009 24061,
  .force 46807 1 [(7, 2), (19, 2), (109, 4), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2), (24061, 2)],
  .up 46807 1,
  .big [(7, 2), (19, 2), (109, 4), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2), (24061, 2)],
  .big [(7, 2), (19, 2), (109, 4), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2), (24061, 4)],
  .big [(7, 2), (19, 2), (109, 4), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .force 53306107 1 [(7, 2), (19, 2), (109, 6), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .up 53306107 1,
  .big [(7, 2), (19, 2), (109, 6), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (109, 10), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (109, 12), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 2), (1009, 1), (5419, 2)],
  .force 55918991 1 [(7, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 4), (1009, 1), (5419, 2)],
  .up 55918991 1,
  .rs 55918991 1 4,
  .par2 1009 55918991,
  .big [(7, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 4), (1009, 1), (5419, 2), (55918991, 2)],
  .big [(7, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 4), (1009, 1), (5419, 2)],
  .force 236022613 1 [(7, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 6), (1009, 1), (5419, 2)],
  .up 236022613 1,
  .big [(7, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 6), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 10), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (499, 12), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (139, 2), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .force 9170881 1 [(7, 2), (19, 2), (127, 2), (139, 4), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .up 9170881 1,
  .rs 9170881 1 6,
  .par2 1009 9170881,
  .force 752449 1 [(7, 2), (19, 2), (127, 2), (139, 4), (181, 2), (313, 2), (1009, 1), (5419, 2), (9170881, 2)],
  .up 752449 1,
  .big [(7, 2), (19, 2), (127, 2), (139, 4), (181, 2), (313, 2), (1009, 1), (5419, 2), (9170881, 2)],
  .big [(7, 2), (19, 2), (127, 2), (139, 4), (181, 2), (313, 2), (1009, 1), (5419, 2), (9170881, 4)],
  .big [(7, 2), (19, 2), (127, 2), (139, 4), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .force 87683177 1 [(7, 2), (19, 2), (127, 2), (139, 6), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .up 87683177 1,
  .rs 87683177 1 5,
  .par2 1009 87683177,
  .big [(7, 2), (19, 2), (127, 2), (139, 6), (181, 2), (313, 2), (1009, 1), (5419, 2), (87683177, 2)],
  .big [(7, 2), (19, 2), (127, 2), (139, 6), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (139, 10), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (139, 12), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (139, 16), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (139, 18), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (181, 2), (313, 2), (1009, 1), (5419, 2)],
  .force 19622651 1 [(7, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2)],
  .up 19622651 1,
  .rs 19622651 1 7,
  .par2 1009 19622651,
  .force 479971 1 [(7, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2), (19622651, 2)],
  .up 479971 1,
  .rs 479971 1 4,
  .par2 1009 479971,
  .big [(7, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2), (479971, 2), (19622651, 2)],
  .big [(7, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2), (19622651, 2)],
  .big [(7, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2), (19622651, 4)],
  .big [(7, 2), (19, 2), (127, 2), (181, 4), (313, 2), (1009, 1), (5419, 2)],
  .force 4338835663 1 [(7, 2), (19, 2), (127, 2), (181, 6), (313, 2), (1009, 1), (5419, 2)],
  .up 4338835663 1,
  .rs 4338835663 1 5,
  .par2 1009 4338835663,
  .big [(7, 2), (19, 2), (127, 2), (181, 6), (313, 2), (1009, 1), (5419, 2), (4338835663, 2)],
  .big [(7, 2), (19, 2), (127, 2), (181, 6), (313, 2), (1009, 1), (5419, 2)],
  .force 52198426022458982993 1 [(7, 2), (19, 2), (127, 2), (181, 10), (313, 2), (1009, 1), (5419, 2)],
  .up 52198426022458982993 1,
  .big [(7, 2), (19, 2), (127, 2), (181, 10), (313, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (181, 12), (313, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (181, 16), (313, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (181, 18), (313, 2), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (313, 2), (1009, 1), (5419, 2)],
  .force 875335231 1 [(7, 2), (19, 2), (127, 2), (313, 4), (1009, 1), (5419, 2)],
  .up 875335231 1,
  .rs 875335231 1 6,
  .par2 1009 875335231,
  .force 405784411 1 [(7, 2), (19, 2), (127, 2), (313, 4), (1009, 1), (5419, 2), (875335231, 2)],
  .up 405784411 1,
  .big [(7, 2), (19, 2), (127, 2), (313, 4), (1009, 1), (5419, 2), (875335231, 2)],
  .big [(7, 2), (19, 2), (127, 2), (313, 4), (1009, 1), (5419, 2), (875335231, 4)],
  .big [(7, 2), (19, 2), (127, 2), (313, 4), (1009, 1), (5419, 2)],
  .force 32528030679467 1 [(7, 2), (19, 2), (127, 2), (313, 6), (1009, 1), (5419, 2)],
  .up 32528030679467 1,
  .rs 32528030679467 1 4,
  .par2 1009 32528030679467,
  .big [(7, 2), (19, 2), (127, 2), (313, 6), (1009, 1), (5419, 2), (32528030679467, 2)],
  .big [(7, 2), (19, 2), (127, 2), (313, 6), (1009, 1), (5419, 2)],
  .force 4805923863681403 1 [(7, 2), (19, 2), (127, 2), (313, 10), (1009, 1), (5419, 2)],
  .up 4805923863681403 1,
  .big [(7, 2), (19, 2), (127, 2), (313, 10), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (313, 12), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (313, 16), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (313, 18), (1009, 1), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 1), (5419, 2)],
  .force 9181 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2)],
  .rs 9181 1 14,
  .force 4591 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 1)],
  .up 4591 1,
  .rs 4591 1 14,
  .par2 9181 4591,
  .force 55333 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1)],
  .up 55333 1,
  .rs 55333 1 9,
  .par2 9181 55333,
  .force 2780923 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1), (55333, 2)],
  .up 2780923 1,
  .rs 2780923 1 5,
  .par2 9181 2780923,
  .force 135676061629 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1), (55333, 2), (2780923, 2)],
  .up 135676061629 1,
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1), (55333, 2), (2780923, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1), (55333, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1), (55333, 4)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1), (55333, 6)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 2), (5419, 2), (9181, 1)],
  .force 8079064749671 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 4), (5419, 2), (9181, 1)],
  .up 8079064749671 1,
  .rs 8079064749671 1 4,
  .par2 9181 8079064749671,
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 4), (5419, 2), (9181, 1), (8079064749671, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 4), (5419, 2), (9181, 1)],
  .force 36825984292217 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 6), (5419, 2), (9181, 1)],
  .up 36825984292217 1,
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 6), (5419, 2), (9181, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 10), (5419, 2), (9181, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (4591, 12), (5419, 2), (9181, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 1)],
  .force 1423 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 2)],
  .up 1423 1,
  .rs 1423 1 14,
  .parS 1423,
  .force 96493 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2)],
  .rs 96493 1 8,
  .force 48247 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 1)],
  .up 48247 1,
  .rs 48247 1 7,
  .par2 96493 48247,
  .force 775940419 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (48247, 2), (96493, 1)],
  .up 775940419 1,
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (48247, 2), (96493, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (48247, 4), (96493, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 1)],
  .force 163350799 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 2)],
  .up 163350799 1,
  .rs 163350799 1 4,
  .parS 163350799,
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 2), (163350799, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 4)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2), (96493, 6)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 2), (5419, 2), (9181, 2)],
  .force 40497241 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2)],
  .rs 40497241 1 4,
  .force 36353 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2), (40497241, 1)],
  .up 36353 1,
  .rs 36353 1 4,
  .par2 40497241 36353,
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2), (36353, 2), (40497241, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2), (40497241, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2), (40497241, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 4), (5419, 2), (9181, 2)],
  .force 417335431509277 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 6), (5419, 2), (9181, 2)],
  .rs 417335431509277 1 3,
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 6), (5419, 2), (9181, 2), (417335431509277, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 6), (5419, 2), (9181, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 10), (5419, 2), (9181, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (1423, 12), (5419, 2), (9181, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 2)],
  .force 125642407351 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 4)],
  .up 125642407351 1,
  .rs 125642407351 1 4,
  .parS 125642407351,
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 4), (125642407351, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 4)],
  .force 19937168287 1 [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 6)],
  .up 19937168287 1,
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 6)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 10)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2), (9181, 12)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 2), (5419, 2)],
  .force 1037517185381 1 [(7, 2), (19, 2), (127, 2), (1009, 4), (5419, 2)],
  .rs 1037517185381 1 5,
  .force 172919530897 1 [(7, 2), (19, 2), (127, 2), (1009, 4), (5419, 2), (1037517185381, 1)],
  .up 172919530897 1,
  .rs 172919530897 1 4,
  .par2 1037517185381 172919530897,
  .big [(7, 2), (19, 2), (127, 2), (1009, 4), (5419, 2), (172919530897, 2), (1037517185381, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 4), (5419, 2), (1037517185381, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 4), (5419, 2), (1037517185381, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 4), (5419, 2)],
  .force 1024823381 1 [(7, 2), (19, 2), (127, 2), (1009, 6), (5419, 2)],
  .rs 1024823381 1 5,
  .force 15527627 1 [(7, 2), (19, 2), (127, 2), (1009, 6), (5419, 2), (1024823381, 1)],
  .up 15527627 1,
  .rs 15527627 1 4,
  .par2 1024823381 15527627,
  .big [(7, 2), (19, 2), (127, 2), (1009, 6), (5419, 2), (15527627, 2), (1024823381, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 6), (5419, 2), (1024823381, 1)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 6), (5419, 2), (1024823381, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 6), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 10), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 12), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 16), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (1009, 18), (5419, 2)],
  .big [(7, 2), (19, 2), (127, 2), (5419, 2)],
  .force 836561914831 1 [(7, 2), (19, 2), (127, 2), (5419, 4)],
  .up 836561914831 1,
  .rs 836561914831 1 6,
  .parS 836561914831,
  .force 347568611538691 1 [(7, 2), (19, 2), (127, 2), (5419, 4), (836561914831, 2)],
  .up 347568611538691 1,
  .big [(7, 2), (19, 2), (127, 2), (5419, 4), (836561914831, 2)],
  .big [(7, 2), (19, 2), (127, 2), (5419, 4), (836561914831, 4)],
  .big [(7, 2), (19, 2), (127, 2), (5419, 4)],
  .force 829621381 1 [(7, 2), (19, 2), (127, 2), (5419, 6)],
  .rs 829621381 1 5,
  .force 414810691 1 [(7, 2), (19, 2), (127, 2), (5419, 6), (829621381, 1)],
  .up 414810691 1,
  .rs 414810691 1 4,
  .par2 829621381 414810691,
  .big [(7, 2), (19, 2), (127, 2), (5419, 6), (414810691, 2), (829621381, 1)],
  .big [(7, 2), (19, 2), (127, 2), (5419, 6), (829621381, 1)],
  .big [(7, 2), (19, 2), (127, 2), (5419, 6), (829621381, 2)],
  .big [(7, 2), (19, 2), (127, 2), (5419, 6)],
  .big [(7, 2), (19, 2), (127, 2), (5419, 10)],
  .big [(7, 2), (19, 2), (127, 2), (5419, 12)],
  .big [(7, 2), (19, 2), (127, 2), (5419, 16)],
  .big [(7, 2), (19, 2), (127, 2), (5419, 18)],
  .big [(7, 2), (19, 2), (127, 2)],
  .force 262209281 1 [(7, 2), (19, 2), (127, 4)],
  .rs 262209281 1 9,
  .force 13931 1 [(7, 2), (19, 2), (127, 4), (262209281, 1)],
  .up 13931 1,
  .rs 13931 1 14,
  .par2 262209281 13931,
  .force 194086693 1 [(7, 2), (19, 2), (127, 4), (13931, 2), (262209281, 1)],
  .up 194086693 1,
  .rs 194086693 1 7,
  .par2 262209281 194086693,
  .force 1380277 1 [(7, 2), (19, 2), (127, 4), (13931, 2), (194086693, 2), (262209281, 1)],
  .up 1380277 1,
  .rs 1380277 1 4,
  .par2 262209281 1380277,
  .big [(7, 2), (19, 2), (127, 4), (13931, 2), (1380277, 2), (194086693, 2), (262209281, 1)],
  .big [(7, 2), (19, 2), (127, 4), (13931, 2), (194086693, 2), (262209281, 1)],
  .big [(7, 2), (19, 2), (127, 4), (13931, 2), (194086693, 4), (262209281, 1)],
  .big [(7, 2), (19, 2), (127, 4), (13931, 2), (262209281, 1)],
  .force 1394813567261 1 [(7, 2), (19, 2), (127, 4), (13931, 4), (262209281, 1)],
  .up 1394813567261 1,
  .rs 1394813567261 1 4,
  .par2 262209281 1394813567261,
  .big [(7, 2), (19, 2), (127, 4), (13931, 4), (262209281, 1), (1394813567261, 2)],
  .big [(7, 2), (19, 2), (127, 4), (13931, 4), (262209281, 1)],
  .force 285472521588928549 1 [(7, 2), (19, 2), (127, 4), (13931, 6), (262209281, 1)],
  .up 285472521588928549 1,
  .big [(7, 2), (19, 2), (127, 4), (13931, 6), (262209281, 1)],
  .big [(7, 2), (19, 2), (127, 4), (13931, 10), (262209281, 1)],
  .big [(7, 2), (19, 2), (127, 4), (13931, 12), (262209281, 1)],
  .big [(7, 2), (19, 2), (127, 4), (262209281, 1)],
  .force 4296301150081 1 [(7, 2), (19, 2), (127, 4), (262209281, 2)],
  .rs 4296301150081 1 5,
  .force 123152587 1 [(7, 2), (19, 2), (127, 4), (262209281, 2), (4296301150081, 1)],
  .up 123152587 1,
  .rs 123152587 1 5,
  .par2 4296301150081 123152587,
  .big [(7, 2), (19, 2), (127, 4), (123152587, 2), (262209281, 2), (4296301150081, 1)],
  .big [(7, 2), (19, 2), (127, 4), (262209281, 2), (4296301150081, 1)],
  .big [(7, 2), (19, 2), (127, 4), (262209281, 2), (4296301150081, 2)],
  .big [(7, 2), (19, 2), (127, 4), (262209281, 2)],
  .big [(7, 2), (19, 2), (127, 4), (262209281, 4)],
  .big [(7, 2), (19, 2), (127, 4), (262209281, 6)],
  .big [(7, 2), (19, 2), (127, 4)],
  .force 162709 1 [(7, 2), (19, 2), (127, 6)],
  .rs 162709 1 12,
  .force 86353 1 [(7, 2), (19, 2), (127, 6), (162709, 1)],
  .up 86353 1,
  .rs 86353 1 12,
  .par2 162709 86353,
  .force 2485642321 1 [(7, 2), (19, 2), (127, 6), (86353, 2), (162709, 1)],
  .up 2485642321 1,
  .rs 2485642321 1 6,
  .par2 162709 2485642321,
  .force 2202194614231 1 [(7, 2), (19, 2), (127, 6), (86353, 2), (162709, 1), (2485642321, 2)],
  .up 2202194614231 1,
  .big [(7, 2), (19, 2), (127, 6), (86353, 2), (162709, 1), (2485642321, 2)],
  .big [(7, 2), (19, 2), (127, 6), (86353, 2), (162709, 1), (2485642321, 4)],
  .big [(7, 2), (19, 2), (127, 6), (86353, 2), (162709, 1)],
  .force 8970971 1 [(7, 2), (19, 2), (127, 6), (86353, 4), (162709, 1)],
  .up 8970971 1,
  .rs 8970971 1 4,
  .par2 162709 8970971,
  .big [(7, 2), (19, 2), (127, 6), (86353, 4), (162709, 1), (8970971, 2)],
  .big [(7, 2), (19, 2), (127, 6), (86353, 4), (162709, 1)],
  .big [(7, 2), (19, 2), (127, 6), (86353, 6), (162709, 1)],
  .big [(7, 2), (19, 2), (127, 6), (86353, 10), (162709, 1)],
  .big [(7, 2), (19, 2), (127, 6), (162709, 1)],
  .force 8824793797 1 [(7, 2), (19, 2), (127, 6), (162709, 2)],
  .rs 8824793797 1 6,
  .force 2409829 1 [(7, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 1)],
  .up 2409829 1,
  .rs 2409829 1 6,
  .par2 8824793797 2409829,
  .force 4252519 1 [(7, 2), (19, 2), (127, 6), (162709, 2), (2409829, 2), (8824793797, 1)],
  .up 4252519 1,
  .big [(7, 2), (19, 2), (127, 6), (162709, 2), (2409829, 2), (8824793797, 1)],
  .big [(7, 2), (19, 2), (127, 6), (162709, 2), (2409829, 4), (8824793797, 1)],
  .big [(7, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 1)],
  .force 425557298187947929 1 [(7, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 2)],
  .rs 425557298187947929 1 3,
  .big [(7, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 2), (425557298187947929, 1)],
  .big [(7, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 2)],
  .big [(7, 2), (19, 2), (127, 6), (162709, 2), (8824793797, 4)],
  .big [(7, 2), (19, 2), (127, 6), (162709, 2)],
  .force 700888562389531127981 1 [(7, 2), (19, 2), (127, 6), (162709, 4)],
  .rs 700888562389531127981 1 3,
  .big [(7, 2), (19, 2), (127, 6), (162709, 4), (700888562389531127981, 1)],
  .big [(7, 2), (19, 2), (127, 6), (162709, 4)],
  .big [(7, 2), (19, 2), (127, 6), (162709, 6)],
  .big [(7, 2), (19, 2), (127, 6), (162709, 10)],
  .big [(7, 2), (19, 2), (127, 6)],
  .force 47834644354838156839 1 [(7, 2), (19, 2), (127, 10)],
  .up 47834644354838156839 1,
  .rs 47834644354838156839 1 4,
  .parS 47834644354838156839,
  .big [(7, 2), (19, 2), (127, 10), (47834644354838156839, 2)],
  .big [(7, 2), (19, 2), (127, 10)],
  .force 1437263292796553 1 [(7, 2), (19, 2), (127, 12)],
  .rs 1437263292796553 1 4,
  .force 12346432697 1 [(7, 2), (19, 2), (127, 12), (1437263292796553, 1)],
  .up 12346432697 1,
  .big [(7, 2), (19, 2), (127, 12), (1437263292796553, 1)],
  .big [(7, 2), (19, 2), (127, 12), (1437263292796553, 2)],
  .big [(7, 2), (19, 2), (127, 12)],
  .force 115512048133057 1 [(7, 2), (19, 2), (127, 16)],
  .rs 115512048133057 1 3,
  .big [(7, 2), (19, 2), (127, 16), (115512048133057, 1)],
  .big [(7, 2), (19, 2), (127, 16)],
  .big [(7, 2), (19, 2), (127, 18)],
  .big [(7, 2), (19, 2), (127, 22)],
  .big [(7, 2), (19, 2), (127, 28)],
  .big [(7, 2), (19, 2), (127, 30)],
  .big [(7, 2), (19, 2)],
  .force 911 1 [(7, 2), (19, 4)]]

/-- Instructions, part 1. -/
def tree7_1 : List Ins := [
  .up 911 1,
  .rs 911 1 25,
  .parS 911,
  .force 830833 1 [(7, 2), (19, 4), (911, 2)],
  .rs 830833 1 12,
  .force 3271 1 [(7, 2), (19, 4), (911, 2), (830833, 1)],
  .up 3271 1,
  .rs 3271 1 17,
  .par2 830833 3271,
  .force 509653 1 [(7, 2), (19, 4), (911, 2), (3271, 2), (830833, 1)],
  .up 509653 1,
  .rs 509653 1 10,
  .par2 830833 509653,
  .force 12368890003 1 [(7, 2), (19, 4), (911, 2), (3271, 2), (509653, 2), (830833, 1)],
  .up 12368890003 1,
  .rs 12368890003 1 5,
  .par2 830833 12368890003,
  .big [(7, 2), (19, 4), (911, 2), (3271, 2), (509653, 2), (830833, 1), (12368890003, 2)],
  .big [(7, 2), (19, 4), (911, 2), (3271, 2), (509653, 2), (830833, 1)],
  .force 83988573481 1 [(7, 2), (19, 4), (911, 2), (3271, 2), (509653, 4), (830833, 1)],
  .up 83988573481 1,
  .big [(7, 2), (19, 4), (911, 2), (3271, 2), (509653, 4), (830833, 1)],
  .big [(7, 2), (19, 4), (911, 2), (3271, 2), (509653, 6), (830833, 1)],
  .big [(7, 2), (19, 4), (911, 2), (3271, 2), (830833, 1)],
  .force 30514801 1 [(7, 2), (19, 4), (911, 2), (3271, 4), (830833, 1)],
  .up 30514801 1,
  .rs 30514801 1 6,
  .par2 830833 30514801,
  .force 8943553 1 [(7, 2), (19, 4), (911, 2), (3271, 4), (830833, 1), (30514801, 2)],
  .up 8943553 1,
  .big [(7, 2), (19, 4), (911, 2), (3271, 4), (830833, 1), (30514801, 2)],
  .big [(7, 2), (19, 4), (911, 2), (3271, 4), (830833, 1), (30514801, 4)],
  .big [(7, 2), (19, 4), (911, 2), (3271, 4), (830833, 1)],
  .force 2002734973 1 [(7, 2), (19, 4), (911, 2), (3271, 6), (830833, 1)],
  .up 2002734973 1,
  .rs 2002734973 1 4,
  .par2 830833 2002734973,
  .big [(7, 2), (19, 4), (911, 2), (3271, 6), (830833, 1), (2002734973, 2)],
  .big [(7, 2), (19, 4), (911, 2), (3271, 6), (830833, 1)],
  .big [(7, 2), (19, 4), (911, 2), (3271, 10), (830833, 1)],
  .big [(7, 2), (19, 4), (911, 2), (3271, 12), (830833, 1)],
  .big [(7, 2), (19, 4), (911, 2), (830833, 1)],
  .force 861001 1 [(7, 2), (19, 4), (911, 2), (830833, 2)],
  .rs 861001 1 9,
  .force 2851 1 [(7, 2), (19, 4), (911, 2), (830833, 2), (861001, 1)],
  .up 2851 1,
  .rs 2851 1 12,
  .par2 861001 2851,
  .force 5779 1 [(7, 2), (19, 4), (911, 2), (2851, 2), (830833, 2), (861001, 1)],
  .up 5779 1,
  .rs 5779 1 9,
  .par2 861001 5779,
  .force 3889 1 [(7, 2), (19, 4), (911, 2), (2851, 2), (5779, 2), (830833, 2), (861001, 1)],
  .up 3889 1,
  .rs 3889 1 6,
  .par2 861001 3889,
  .force 102913 1 [(7, 2), (19, 4), (911, 2), (2851, 2), (3889, 2), (5779, 2), (830833, 2), (861001, 1)],
  .up 102913 1,
  .big [(7, 2), (19, 4), (911, 2), (2851, 2), (3889, 2), (5779, 2), (830833, 2), (861001, 1)],
  .big [(7, 2), (19, 4), (911, 2), (2851, 2), (3889, 4), (5779, 2), (830833, 2), (861001, 1)],
  .big [(7, 2), (19, 4), (911, 2), (2851, 2), (5779, 2), (830833, 2), (861001, 1)],
  .big [(7, 2), (19, 4), (911, 2), (2851, 2), (5779, 4), (830833, 2), (861001, 1)],
  .big [(7, 2), (19, 4), (911, 2), (2851, 2), (5779, 6), (830833, 2), (861001, 1)],
  .big [(7, 2), (19, 4), (911, 2), (2851, 2), (830833, 2), (861001, 1)],
  .force 23468881 1 [(7, 2), (19, 4), (911, 2), (2851, 4), (830833, 2), (861001, 1)],
  .up 23468881 1,
  .rs 23468881 1 4,
  .par2 861001 23468881,
  .big [(7, 2), (19, 4), (911, 2), (2851, 4), (830833, 2), (861001, 1), (23468881, 2)],
  .big [(7, 2), (19, 4), (911, 2), (2851, 4), (830833, 2), (861001, 1)],
  .big [(7, 2), (19, 4), (911, 2), (2851, 6), (830833, 2), (861001, 1)],
  .big [(7, 2), (19, 4), (911, 2), (2851, 10), (830833, 2), (861001, 1)],
  .big [(7, 2), (19, 4), (911, 2), (830833, 2), (861001, 1)],
  .force 217081 1 [(7, 2), (19, 4), (911, 2), (830833, 2), (861001, 2)],
  .rs 217081 1 7,
  .force 108541 1 [(7, 2), (19, 4), (911, 2), (217081, 1), (830833, 2), (861001, 2)],
  .up 108541 1,
  .rs 108541 1 6,
  .par2 217081 108541,
  .force 3927085741 1 [(7, 2), (19, 4), (911, 2), (108541, 2), (217081, 1), (830833, 2), (861001, 2)],
  .up 3927085741 1,
  .big [(7, 2), (19, 4), (911, 2), (108541, 2), (217081, 1), (830833, 2), (861001, 2)],
  .big [(7, 2), (19, 4), (911, 2), (108541, 4), (217081, 1), (830833, 2), (861001, 2)],
  .big [(7, 2), (19, 4), (911, 2), (217081, 1), (830833, 2), (861001, 2)],
  .force 1077301 1 [(7, 2), (19, 4), (911, 2), (217081, 2), (830833, 2), (861001, 2)],
  .rs 1077301 1 4,
  .force 538651 1 [(7, 2), (19, 4), (911, 2), (217081, 2), (830833, 2), (861001, 2), (1077301, 1)],
  .up 538651 1,
  .big [(7, 2), (19, 4), (911, 2), (217081, 2), (830833, 2), (861001, 2), (1077301, 1)],
  .big [(7, 2), (19, 4), (911, 2), (217081, 2), (830833, 2), (861001, 2), (1077301, 2)],
  .big [(7, 2), (19, 4), (911, 2), (217081, 2), (830833, 2), (861001, 2)],
  .big [(7, 2), (19, 4), (911, 2), (217081, 4), (830833, 2), (861001, 2)],
  .big [(7, 2), (19, 4), (911, 2), (830833, 2), (861001, 2)],
  .big [(7, 2), (19, 4), (911, 2), (830833, 2), (861001, 4)],
  .big [(7, 2), (19, 4), (911, 2), (830833, 2), (861001, 6)],
  .big [(7, 2), (19, 4), (911, 2), (830833, 2)],
  .force 2249049650927341 1 [(7, 2), (19, 4), (911, 2), (830833, 4)],
  .rs 2249049650927341 1 4,
  .force 131500009 1 [(7, 2), (19, 4), (911, 2), (830833, 4), (2249049650927341, 1)],
  .up 131500009 1,
  .big [(7, 2), (19, 4), (911, 2), (830833, 4), (2249049650927341, 1)],
  .big [(7, 2), (19, 4), (911, 2), (830833, 4), (2249049650927341, 2)],
  .big [(7, 2), (19, 4), (911, 2), (830833, 4)],
  .big [(7, 2), (19, 4), (911, 2), (830833, 6)],
  .big [(7, 2), (19, 4), (911, 2), (830833, 10)],
  .big [(7, 2), (19, 4), (911, 2)],
  .force 17884211 1 [(7, 2), (19, 4), (911, 4)],
  .up 17884211 1,
  .rs 17884211 1 9,
  .parS 17884211,
  .force 45692145853819 1 [(7, 2), (19, 4), (911, 4), (17884211, 2)],
  .up 45692145853819 1,
  .rs 45692145853819 1 4,
  .parS 45692145853819,
  .big [(7, 2), (19, 4), (911, 4), (17884211, 2), (45692145853819, 2)],
  .big [(7, 2), (19, 4), (911, 4), (17884211, 2)],
  .big [(7, 2), (19, 4), (911, 4), (17884211, 4)],
  .big [(7, 2), (19, 4), (911, 4), (17884211, 6)],
  .big [(7, 2), (19, 4), (911, 4)],
  .force 81750272028928231 1 [(7, 2), (19, 4), (911, 6)],
  .up 81750272028928231 1,
  .rs 81750272028928231 1 5,
  .parS 81750272028928231,
  .big [(7, 2), (19, 4), (911, 6), (81750272028928231, 2)],
  .big [(7, 2), (19, 4), (911, 6)],
  .force 247174661801 1 [(7, 2), (19, 4), (911, 10)],
  .rs 247174661801 1 3,
  .big [(7, 2), (19, 4), (911, 10), (247174661801, 1)],
  .big [(7, 2), (19, 4), (911, 10)],
  .big [(7, 2), (19, 4), (911, 12)],
  .big [(7, 2), (19, 4), (911, 16)],
  .big [(7, 2), (19, 4), (911, 18)],
  .big [(7, 2), (19, 4), (911, 22)],
  .big [(7, 2), (19, 4)],
  .force 70841 1 [(7, 2), (19, 6)],
  .rs 70841 1 15,
  .force 11807 1 [(7, 2), (19, 6), (70841, 1)],
  .up 11807 1,
  .rs 11807 1 16,
  .par2 70841 11807,
  .force 2017 1 [(7, 2), (19, 6), (11807, 2), (70841, 1)],
  .up 2017 1,
  .rs 2017 1 16,
  .par2 70841 2017,
  .force 4099 1 [(7, 2), (19, 6), (2017, 2), (11807, 2), (70841, 1)],
  .up 4099 1,
  .rs 4099 1 12,
  .par2 70841 4099,
  .force 800281 1 [(7, 2), (19, 6), (2017, 2), (4099, 2), (11807, 2), (70841, 1)],
  .up 800281 1,
  .rs 800281 1 7,
  .par2 70841 800281,
  .force 48071041 1 [(7, 2), (19, 6), (2017, 2), (4099, 2), (11807, 2), (70841, 1), (800281, 2)],
  .up 48071041 1,
  .big [(7, 2), (19, 6), (2017, 2), (4099, 2), (11807, 2), (70841, 1), (800281, 2)],
  .big [(7, 2), (19, 6), (2017, 2), (4099, 2), (11807, 2), (70841, 1), (800281, 4)],
  .big [(7, 2), (19, 6), (2017, 2), (4099, 2), (11807, 2), (70841, 1)],
  .force 369023021 1 [(7, 2), (19, 6), (2017, 2), (4099, 4), (11807, 2), (70841, 1)],
  .up 369023021 1,
  .rs 369023021 1 4,
  .par2 70841 369023021,
  .big [(7, 2), (19, 6), (2017, 2), (4099, 4), (11807, 2), (70841, 1), (369023021, 2)],
  .big [(7, 2), (19, 6), (2017, 2), (4099, 4), (11807, 2), (70841, 1)],
  .big [(7, 2), (19, 6), (2017, 2), (4099, 6), (11807, 2), (70841, 1)],
  .big [(7, 2), (19, 6), (2017, 2), (4099, 10), (11807, 2), (70841, 1)],
  .big [(7, 2), (19, 6), (2017, 2), (11807, 2), (70841, 1)],
  .force 617341 1 [(7, 2), (19, 6), (2017, 4), (11807, 2), (70841, 1)],
  .up 617341 1,
  .rs 617341 1 6,
  .par2 70841 617341,
  .force 39409 1 [(7, 2), (19, 6), (2017, 4), (11807, 2), (70841, 1), (617341, 2)],
  .up 39409 1,
  .rs 39409 1 4,
  .par2 70841 39409,
  .big [(7, 2), (19, 6), (2017, 4), (11807, 2), (39409, 2), (70841, 1), (617341, 2)],
  .big [(7, 2), (19, 6), (2017, 4), (11807, 2), (70841, 1), (617341, 2)],
  .big [(7, 2), (19, 6), (2017, 4), (11807, 2), (70841, 1), (617341, 4)],
  .big [(7, 2), (19, 6), (2017, 4), (11807, 2), (70841, 1)],
  .force 1727870509 1 [(7, 2), (19, 6), (2017, 6), (11807, 2), (70841, 1)],
  .up 1727870509 1,
  .big [(7, 2), (19, 6), (2017, 6), (11807, 2), (70841, 1)],
  .big [(7, 2), (19, 6), (2017, 10), (11807, 2), (70841, 1)],
  .big [(7, 2), (19, 6), (2017, 12), (11807, 2), (70841, 1)],
  .big [(7, 2), (19, 6), (11807, 2), (70841, 1)],
  .force 280257881 1 [(7, 2), (19, 6), (11807, 4), (70841, 1)],
  .up 280257881 1,
  .rs 280257881 1 6,
  .par2 70841 280257881,
  .force 596514349 1 [(7, 2), (19, 6), (11807, 4), (70841, 1), (280257881, 2)],
  .up 596514349 1,
  .big [(7, 2), (19, 6), (11807, 4), (70841, 1), (280257881, 2)],
  .big [(7, 2), (19, 6), (11807, 4), (70841, 1), (280257881, 4)],
  .big [(7, 2), (19, 6), (11807, 4), (70841, 1)],
  .force 1807475964966137691443 1 [(7, 2), (19, 6), (11807, 6), (70841, 1)],
  .up 1807475964966137691443 1,
  .big [(7, 2), (19, 6), (11807, 6), (70841, 1)],
  .big [(7, 2), (19, 6), (11807, 10), (70841, 1)],
  .big [(7, 2), (19, 6), (11807, 12), (70841, 1)],
  .big [(7, 2), (19, 6), (70841, 1)],
  .force 128341 1 [(7, 2), (19, 6), (70841, 2)],
  .rs 128341 1 12,
  .force 64171 1 [(7, 2), (19, 6), (70841, 2), (128341, 1)],
  .up 64171 1,
  .rs 64171 1 11,
  .par2 128341 64171,
  .force 39103 1 [(7, 2), (19, 6), (64171, 2), (70841, 2), (128341, 1)],
  .up 39103 1,
  .rs 39103 1 9,
  .par2 128341 39103,
  .force 67411 1 [(7, 2), (19, 6), (39103, 2), (64171, 2), (70841, 2), (128341, 1)],
  .up 67411 1,
  .rs 67411 1 6,
  .par2 128341 67411,
  .force 1514770111 1 [(7, 2), (19, 6), (39103, 2), (64171, 2), (67411, 2), (70841, 2), (128341, 1)],
  .up 1514770111 1,
  .big [(7, 2), (19, 6), (39103, 2), (64171, 2), (67411, 2), (70841, 2), (128341, 1)],
  .big [(7, 2), (19, 6), (39103, 2), (64171, 2), (67411, 4), (70841, 2), (128341, 1)],
  .big [(7, 2), (19, 6), (39103, 2), (64171, 2), (70841, 2), (128341, 1)],
  .big [(7, 2), (19, 6), (39103, 4), (64171, 2), (70841, 2), (128341, 1)],
  .big [(7, 2), (19, 6), (39103, 6), (64171, 2), (70841, 2), (128341, 1)],
  .big [(7, 2), (19, 6), (64171, 2), (70841, 2), (128341, 1)],
  .force 33579221106357041 1 [(7, 2), (19, 6), (64171, 4), (70841, 2), (128341, 1)],
  .up 33579221106357041 1,
  .big [(7, 2), (19, 6), (64171, 4), (70841, 2), (128341, 1)],
  .big [(7, 2), (19, 6), (64171, 6), (70841, 2), (128341, 1)],
  .big [(7, 2), (19, 6), (70841, 2), (128341, 1)],
  .force 5490513541 1 [(7, 2), (19, 6), (70841, 2), (128341, 2)],
  .rs 5490513541 1 6,
  .force 2745256771 1 [(7, 2), (19, 6), (70841, 2), (128341, 2), (5490513541, 1)],
  .up 2745256771 1,
  .rs 2745256771 1 5,
  .par2 5490513541 2745256771,
  .big [(7, 2), (19, 6), (70841, 2), (128341, 2), (2745256771, 2), (5490513541, 1)],
  .big [(7, 2), (19, 6), (70841, 2), (128341, 2), (5490513541, 1)],
  .force 1435511378542612963 1 [(7, 2), (19, 6), (70841, 2), (128341, 2), (5490513541, 2)],
  .up 1435511378542612963 1,
  .big [(7, 2), (19, 6), (70841, 2), (128341, 2), (5490513541, 2)],
  .big [(7, 2), (19, 6), (70841, 2), (128341, 2), (5490513541, 4)],
  .big [(7, 2), (19, 6), (70841, 2), (128341, 2)],
  .force 12833941 1 [(7, 2), (19, 6), (70841, 2), (128341, 4)],
  .rs 12833941 1 4,
  .force 1058821 1 [(7, 2), (19, 6), (70841, 2), (128341, 4), (12833941, 1)],
  .up 1058821 1,
  .big [(7, 2), (19, 6), (70841, 2), (128341, 4), (12833941, 1)],
  .big [(7, 2), (19, 6), (70841, 2), (128341, 4), (12833941, 2)],
  .big [(7, 2), (19, 6), (70841, 2), (128341, 4)],
  .big [(7, 2), (19, 6), (70841, 2), (128341, 6)],
  .big [(7, 2), (19, 6), (70841, 2), (128341, 10)],
  .big [(7, 2), (19, 6), (70841, 2)],
  .force 1163018639068051 1 [(7, 2), (19, 6), (70841, 4)],
  .up 1163018639068051 1,
  .rs 1163018639068051 1 4,
  .parS 1163018639068051,
  .big [(7, 2), (19, 6), (70841, 4), (1163018639068051, 2)],
  .big [(7, 2), (19, 6), (70841, 4)],
  .force 98811777493935291929249 1 [(7, 2), (19, 6), (70841, 6)],
  .rs 98811777493935291929249 1 3,
  .big [(7, 2), (19, 6), (70841, 6), (98811777493935291929249, 1)],
  .big [(7, 2), (19, 6), (70841, 6)],
  .big [(7, 2), (19, 6), (70841, 10)],
  .big [(7, 2), (19, 6), (70841, 12)],
  .big [(7, 2), (19, 6)],
  .force 62060021 1 [(7, 2), (19, 10)],
  .rs 62060021 1 9,
  .force 104281 1 [(7, 2), (19, 10), (62060021, 1)],
  .up 104281 1,
  .rs 104281 1 11,
  .par2 62060021 104281,
  .force 179743 1 [(7, 2), (19, 10), (104281, 2), (62060021, 1)],
  .up 179743 1,
  .rs 179743 1 8,
  .par2 62060021 179743,
  .force 49627843 1 [(7, 2), (19, 10), (104281, 2), (179743, 2), (62060021, 1)],
  .up 49627843 1,
  .rs 49627843 1 4,
  .par2 62060021 49627843,
  .big [(7, 2), (19, 10), (104281, 2), (179743, 2), (49627843, 2), (62060021, 1)],
  .big [(7, 2), (19, 10), (104281, 2), (179743, 2), (62060021, 1)],
  .big [(7, 2), (19, 10), (104281, 2), (179743, 4), (62060021, 1)],
  .big [(7, 2), (19, 10), (104281, 2), (179743, 6), (62060021, 1)],
  .big [(7, 2), (19, 10), (104281, 2), (62060021, 1)],
  .force 181345750520141 1 [(7, 2), (19, 10), (104281, 4), (62060021, 1)],
  .up 181345750520141 1,
  .big [(7, 2), (19, 10), (104281, 4), (62060021, 1)],
  .big [(7, 2), (19, 10), (104281, 6), (62060021, 1)],
  .big [(7, 2), (19, 10), (62060021, 1)],
  .force 17748600316039 1 [(7, 2), (19, 10), (62060021, 2)],
  .up 17748600316039 1,
  .rs 17748600316039 1 5,
  .parS 17748600316039,
  .big [(7, 2), (19, 10), (62060021, 2), (17748600316039, 2)],
  .big [(7, 2), (19, 10), (62060021, 2)],
  .big [(7, 2), (19, 10), (62060021, 4)],
  .big [(7, 2), (19, 10), (62060021, 6)],
  .big [(7, 2), (19, 10)],
  .force 133338869 1 [(7, 2), (19, 12)],
  .rs 133338869 1 8,
  .force 29251 1 [(7, 2), (19, 12), (133338869, 1)],
  .up 29251 1,
  .rs 29251 1 11,
  .par2 133338869 29251,
  .force 1477807 1 [(7, 2), (19, 12), (29251, 2), (133338869, 1)],
  .up 1477807 1,
  .rs 1477807 1 7,
  .par2 133338869 1477807,
  .force 2167621 1 [(7, 2), (19, 12), (29251, 2), (1477807, 2), (133338869, 1)],
  .up 2167621 1,
  .rs 2167621 1 4,
  .par2 133338869 2167621,
  .big [(7, 2), (19, 12), (29251, 2), (1477807, 2), (2167621, 2), (133338869, 1)],
  .big [(7, 2), (19, 12), (29251, 2), (1477807, 2), (133338869, 1)],
  .big [(7, 2), (19, 12), (29251, 2), (1477807, 4), (133338869, 1)],
  .big [(7, 2), (19, 12), (29251, 2), (133338869, 1)],
  .force 3571279638916061 1 [(7, 2), (19, 12), (29251, 4), (133338869, 1)],
  .up 3571279638916061 1,
  .big [(7, 2), (19, 12), (29251, 4), (133338869, 1)],
  .big [(7, 2), (19, 12), (29251, 6), (133338869, 1)],
  .big [(7, 2), (19, 12), (133338869, 1)],
  .force 316950847 1 [(7, 2), (19, 12), (133338869, 2)],
  .up 316950847 1,
  .rs 316950847 1 5,
  .parS 316950847,
  .big [(7, 2), (19, 12), (133338869, 2), (316950847, 2)],
  .big [(7, 2), (19, 12), (133338869, 2)],
  .big [(7, 2), (19, 12), (133338869, 4)],
  .big [(7, 2), (19, 12), (133338869, 6)],
  .big [(7, 2), (19, 12)],
  .force 99995282631947 1 [(7, 2), (19, 16)],
  .up 99995282631947 1,
  .rs 99995282631947 1 5,
  .parS 99995282631947,
  .big [(7, 2), (19, 16), (99995282631947, 2)],
  .big [(7, 2), (19, 16)],
  .force 109912203092239643840221 1 [(7, 2), (19, 18)],
  .rs 109912203092239643840221 1 4,
  .force 16842464147039939 1 [(7, 2), (19, 18), (109912203092239643840221, 1)],
  .up 16842464147039939 1,
  .big [(7, 2), (19, 18), (109912203092239643840221, 1)],
  .big [(7, 2), (19, 18), (109912203092239643840221, 2)],
  .big [(7, 2), (19, 18)],
  .force 1335495402823 1 [(7, 2), (19, 22)],
  .up 1335495402823 1,
  .rs 1335495402823 1 4,
  .parS 1335495402823,
  .big [(7, 2), (19, 22), (1335495402823, 2)],
  .big [(7, 2), (19, 22)],
  .force 165049085515149863 1 [(7, 2), (19, 28)],
  .up 165049085515149863 1,
  .big [(7, 2), (19, 28)],
  .force 243270318891483838103593381595151809701 1 [(7, 2), (19, 30)],
  .rs 243270318891483838103593381595151809701 1 3,
  .big [(7, 2), (19, 30), (243270318891483838103593381595151809701, 1)],
  .big [(7, 2), (19, 30)],
  .big [(7, 2), (19, 36)],
  .big [(7, 2), (19, 40)],
  .big [(7, 2), (19, 42)],
  .big [(7, 2), (19, 46)],
  .big [(7, 2), (19, 52)],
  .big [(7, 2), (19, 58)],
  .big [(7, 2), (19, 60)],
  .big [(7, 2)],
  .force 2801 1 [(7, 4)],
  .rs 2801 1 23,
  .force 467 1 [(7, 4), (2801, 1)],
  .up 467 1,
  .rs 467 1 28,
  .par2 2801 467,
  .force 11503 1 [(7, 4), (467, 2), (2801, 1)],
  .up 11503 1,
  .rs 11503 1 18,
  .par2 2801 11503,
  .force 8527 1 [(7, 4), (467, 2), (2801, 1), (11503, 2)],
  .up 8527 1,
  .rs 8527 1 15,
  .par2 2801 8527,
  .force 24239419 1 [(7, 4), (467, 2), (2801, 1), (8527, 2), (11503, 2)],
  .up 24239419 1,
  .rs 24239419 1 8,
  .par2 2801 24239419,
  .force 58579 1 [(7, 4), (467, 2), (2801, 1), (8527, 2), (11503, 2), (24239419, 2)],
  .up 58579 1,
  .rs 58579 1 6,
  .par2 2801 58579,
  .force 1143852607 1 [(7, 4), (467, 2), (2801, 1), (8527, 2), (11503, 2), (58579, 2), (24239419, 2)],
  .up 1143852607 1,
  .big [(7, 4), (467, 2), (2801, 1), (8527, 2), (11503, 2), (58579, 2), (24239419, 2)],
  .big [(7, 4), (467, 2), (2801, 1), (8527, 2), (11503, 2), (58579, 4), (24239419, 2)],
  .big [(7, 4), (467, 2), (2801, 1), (8527, 2), (11503, 2), (24239419, 2)],
  .big [(7, 4), (467, 2), (2801, 1), (8527, 2), (11503, 2), (24239419, 4)],
  .big [(7, 4), (467, 2), (2801, 1), (8527, 2), (11503, 2), (24239419, 6)],
  .big [(7, 4), (467, 2), (2801, 1), (8527, 2), (11503, 2)],
  .force 170558863220351 1 [(7, 4), (467, 2), (2801, 1), (8527, 4), (11503, 2)],
  .up 170558863220351 1,
  .rs 170558863220351 1 4,
  .par2 2801 170558863220351,
  .big [(7, 4), (467, 2), (2801, 1), (8527, 4), (11503, 2), (170558863220351, 2)],
  .big [(7, 4), (467, 2), (2801, 1), (8527, 4), (11503, 2)],
  .force 138333204689 1 [(7, 4), (467, 2), (2801, 1), (8527, 6), (11503, 2)],
  .up 138333204689 1,
  .big [(7, 4), (467, 2), (2801, 1), (8527, 6), (11503, 2)]]

/-- Instructions, part 2. -/
def tree7_2 : List Ins := [
  .big [(7, 4), (467, 2), (2801, 1), (8527, 10), (11503, 2)],
  .big [(7, 4), (467, 2), (2801, 1), (8527, 12), (11503, 2)],
  .big [(7, 4), (467, 2), (2801, 1), (11503, 2)],
  .force 564833623891391 1 [(7, 4), (467, 2), (2801, 1), (11503, 4)],
  .up 564833623891391 1,
  .rs 564833623891391 1 5,
  .par2 2801 564833623891391,
  .big [(7, 4), (467, 2), (2801, 1), (11503, 4), (564833623891391, 2)],
  .big [(7, 4), (467, 2), (2801, 1), (11503, 4)],
  .force 4811739025283 1 [(7, 4), (467, 2), (2801, 1), (11503, 6)],
  .up 4811739025283 1,
  .rs 4811739025283 1 4,
  .par2 2801 4811739025283,
  .big [(7, 4), (467, 2), (2801, 1), (11503, 6), (4811739025283, 2)],
  .big [(7, 4), (467, 2), (2801, 1), (11503, 6)],
  .big [(7, 4), (467, 2), (2801, 1), (11503, 10)],
  .big [(7, 4), (467, 2), (2801, 1), (11503, 12)],
  .big [(7, 4), (467, 2), (2801, 1), (11503, 16)],
  .big [(7, 4), (467, 2), (2801, 1)],
  .force 3409261 1 [(7, 4), (467, 4), (2801, 1)],
  .up 3409261 1,
  .rs 3409261 1 10,
  .par2 2801 3409261,
  .force 42451 1 [(7, 4), (467, 4), (2801, 1), (3409261, 2)],
  .up 42451 1,
  .rs 42451 1 9,
  .par2 2801 42451,
  .force 40531 1 [(7, 4), (467, 4), (2801, 1), (42451, 2), (3409261, 2)],
  .up 40531 1,
  .rs 40531 1 6,
  .par2 2801 40531,
  .force 125683 1 [(7, 4), (467, 4), (2801, 1), (40531, 2), (42451, 2), (3409261, 2)],
  .up 125683 1,
  .big [(7, 4), (467, 4), (2801, 1), (40531, 2), (42451, 2), (3409261, 2)],
  .big [(7, 4), (467, 4), (2801, 1), (40531, 4), (42451, 2), (3409261, 2)],
  .big [(7, 4), (467, 4), (2801, 1), (42451, 2), (3409261, 2)],
  .big [(7, 4), (467, 4), (2801, 1), (42451, 4), (3409261, 2)],
  .big [(7, 4), (467, 4), (2801, 1), (42451, 6), (3409261, 2)],
  .big [(7, 4), (467, 4), (2801, 1), (3409261, 2)],
  .force 2226081858886600201 1 [(7, 4), (467, 4), (2801, 1), (3409261, 4)],
  .up 2226081858886600201 1,
  .big [(7, 4), (467, 4), (2801, 1), (3409261, 4)],
  .big [(7, 4), (467, 4), (2801, 1), (3409261, 6)],
  .big [(7, 4), (467, 4), (2801, 1)],
  .force 221110919 1 [(7, 4), (467, 6), (2801, 1)],
  .up 221110919 1,
  .rs 221110919 1 7,
  .par2 2801 221110919,
  .force 3760772209395037 1 [(7, 4), (467, 6), (2801, 1), (221110919, 2)],
  .up 3760772209395037 1,
  .big [(7, 4), (467, 6), (2801, 1), (221110919, 2)],
  .big [(7, 4), (467, 6), (2801, 1), (221110919, 4)],
  .big [(7, 4), (467, 6), (2801, 1)],
  .force 494424256962371823779424877 1 [(7, 4), (467, 10), (2801, 1)],
  .up 494424256962371823779424877 1,
  .big [(7, 4), (467, 10), (2801, 1)],
  .force 47009039042447030231489 1 [(7, 4), (467, 12), (2801, 1)],
  .up 47009039042447030231489 1,
  .big [(7, 4), (467, 12), (2801, 1)],
  .big [(7, 4), (467, 16), (2801, 1)],
  .big [(7, 4), (467, 18), (2801, 1)],
  .big [(7, 4), (467, 22), (2801, 1)],
  .big [(7, 4), (2801, 1)],
  .force 4933 1 [(7, 4), (2801, 2)],
  .rs 4933 1 19,
  .force 2467 1 [(7, 4), (2801, 2), (4933, 1)],
  .up 2467 1,
  .rs 2467 1 20,
  .par2 4933 2467,
  .force 7489 1 [(7, 4), (2467, 2), (2801, 2), (4933, 1)],
  .up 7489 1,
  .rs 7489 1 15,
  .par2 4933 7489,
  .force 306517 1 [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 2)],
  .up 306517 1,
  .rs 306517 1 9,
  .par2 4933 306517,
  .force 11311 1 [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 2), (306517, 2)],
  .up 11311 1,
  .rs 11311 1 7,
  .par2 4933 11311,
  .force 4783 1 [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 2), (11311, 2), (306517, 2)],
  .up 4783 1,
  .rs 4783 1 5,
  .par2 4933 4783,
  .big [(7, 4), (2467, 2), (2801, 2), (4783, 2), (4933, 1), (7489, 2), (11311, 2), (306517, 2)],
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 2), (11311, 2), (306517, 2)],
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 2), (11311, 4), (306517, 2)],
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 2), (306517, 2)],
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 2), (306517, 4)],
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 2), (306517, 6)],
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 2)],
  .force 285996443195311 1 [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 4)],
  .up 285996443195311 1,
  .rs 285996443195311 1 4,
  .par2 4933 285996443195311,
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 4), (285996443195311, 2)],
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 4)],
  .force 282097794109643 1 [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 6)],
  .up 282097794109643 1,
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 6)],
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 10)],
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1), (7489, 12)],
  .big [(7, 4), (2467, 2), (2801, 2), (4933, 1)],
  .force 10177286401 1 [(7, 4), (2467, 4), (2801, 2), (4933, 1)],
  .up 10177286401 1,
  .rs 10177286401 1 6,
  .par2 4933 10177286401,
  .force 2164387 1 [(7, 4), (2467, 4), (2801, 2), (4933, 1), (10177286401, 2)],
  .up 2164387 1,
  .big [(7, 4), (2467, 4), (2801, 2), (4933, 1), (10177286401, 2)],
  .big [(7, 4), (2467, 4), (2801, 2), (4933, 1), (10177286401, 4)],
  .big [(7, 4), (2467, 4), (2801, 2), (4933, 1)],
  .force 5244722549705267119 1 [(7, 4), (2467, 6), (2801, 2), (4933, 1)],
  .up 5244722549705267119 1,
  .rs 5244722549705267119 1 4,
  .par2 4933 5244722549705267119,
  .big [(7, 4), (2467, 6), (2801, 2), (4933, 1), (5244722549705267119, 2)],
  .big [(7, 4), (2467, 6), (2801, 2), (4933, 1)],
  .big [(7, 4), (2467, 10), (2801, 2), (4933, 1)],
  .big [(7, 4), (2467, 12), (2801, 2), (4933, 1)],
  .big [(7, 4), (2467, 16), (2801, 2), (4933, 1)],
  .big [(7, 4), (2467, 18), (2801, 2), (4933, 1)],
  .big [(7, 4), (2801, 2), (4933, 1)],
  .force 331 1 [(7, 4), (2801, 2), (4933, 2)],
  .up 331 1,
  .rs 331 1 23,
  .parS 331,
  .force 5233 1 [(7, 4), (331, 2), (2801, 2), (4933, 2)],
  .rs 5233 1 14,
  .force 2617 1 [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 1)],
  .up 2617 1,
  .rs 2617 1 14,
  .par2 5233 2617,
  .force 11833 1 [(7, 4), (331, 2), (2617, 2), (2801, 2), (4933, 2), (5233, 1)],
  .up 11833 1,
  .rs 11833 1 10,
  .par2 5233 11833,
  .force 18043 1 [(7, 4), (331, 2), (2617, 2), (2801, 2), (4933, 2), (5233, 1), (11833, 2)],
  .up 18043 1,
  .rs 18043 1 7,
  .par2 5233 18043,
  .force 15503233 1 [(7, 4), (331, 2), (2617, 2), (2801, 2), (4933, 2), (5233, 1), (11833, 2), (18043, 2)],
  .up 15503233 1,
  .big [(7, 4), (331, 2), (2617, 2), (2801, 2), (4933, 2), (5233, 1), (11833, 2), (18043, 2)],
  .big [(7, 4), (331, 2), (2617, 2), (2801, 2), (4933, 2), (5233, 1), (11833, 2), (18043, 4)],
  .big [(7, 4), (331, 2), (2617, 2), (2801, 2), (4933, 2), (5233, 1), (11833, 2)],
  .force 865622988431 1 [(7, 4), (331, 2), (2617, 2), (2801, 2), (4933, 2), (5233, 1), (11833, 4)],
  .up 865622988431 1,
  .big [(7, 4), (331, 2), (2617, 2), (2801, 2), (4933, 2), (5233, 1), (11833, 4)],
  .big [(7, 4), (331, 2), (2617, 2), (2801, 2), (4933, 2), (5233, 1), (11833, 6)],
  .big [(7, 4), (331, 2), (2617, 2), (2801, 2), (4933, 2), (5233, 1)],
  .force 46922470889141 1 [(7, 4), (331, 2), (2617, 4), (2801, 2), (4933, 2), (5233, 1)],
  .up 46922470889141 1,
  .rs 46922470889141 1 4,
  .par2 5233 46922470889141,
  .big [(7, 4), (331, 2), (2617, 4), (2801, 2), (4933, 2), (5233, 1), (46922470889141, 2)],
  .big [(7, 4), (331, 2), (2617, 4), (2801, 2), (4933, 2), (5233, 1)],
  .force 11627796440687491 1 [(7, 4), (331, 2), (2617, 6), (2801, 2), (4933, 2), (5233, 1)],
  .up 11627796440687491 1,
  .big [(7, 4), (331, 2), (2617, 6), (2801, 2), (4933, 2), (5233, 1)],
  .big [(7, 4), (331, 2), (2617, 10), (2801, 2), (4933, 2), (5233, 1)],
  .big [(7, 4), (331, 2), (2617, 12), (2801, 2), (4933, 2), (5233, 1)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 1)],
  .force 42073 1 [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2)],
  .rs 42073 1 10,
  .force 193 2 [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .rs 193 1 16,
  .par2 42073 193,
  .force 1783 1 [(7, 4), (193, 2), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .up 1783 1,
  .rs 1783 1 10,
  .par2 42073 1783,
  .force 1279 1 [(7, 4), (193, 2), (331, 2), (1783, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .up 1279 1,
  .rs 1279 1 8,
  .par2 42073 1279,
  .force 2383 1 [(7, 4), (193, 2), (331, 2), (1279, 2), (1783, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .up 2383 1,
  .rs 2383 1 4,
  .par2 42073 2383,
  .big [(7, 4), (193, 2), (331, 2), (1279, 2), (1783, 2), (2383, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .big [(7, 4), (193, 2), (331, 2), (1279, 2), (1783, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .big [(7, 4), (193, 2), (331, 2), (1279, 4), (1783, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .big [(7, 4), (193, 2), (331, 2), (1279, 6), (1783, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .big [(7, 4), (193, 2), (331, 2), (1783, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .force 4849081 1 [(7, 4), (193, 2), (331, 2), (1783, 4), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .up 4849081 1,
  .big [(7, 4), (193, 2), (331, 2), (1783, 4), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .big [(7, 4), (193, 2), (331, 2), (1783, 6), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .big [(7, 4), (193, 2), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .force 1394714501 1 [(7, 4), (193, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .up 1394714501 1,
  .rs 1394714501 1 4,
  .par2 42073 1394714501,
  .big [(7, 4), (193, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1), (1394714501, 2)],
  .big [(7, 4), (193, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .force 1208179545301 1 [(7, 4), (193, 6), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .up 1208179545301 1,
  .big [(7, 4), (193, 6), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .big [(7, 4), (193, 10), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .big [(7, 4), (193, 12), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 1)],
  .force 75931 1 [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2)],
  .up 75931 1,
  .rs 75931 1 7,
  .parS 75931,
  .force 787 1 [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2), (75931, 2)],
  .up 787 1,
  .rs 787 1 5,
  .parS 787,
  .big [(7, 4), (331, 2), (787, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2), (75931, 2)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2), (75931, 4)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 2)],
  .force 284860058207025151 1 [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 4)],
  .up 284860058207025151 1,
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 4)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2), (42073, 6)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 2)],
  .force 41213191 1 [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 4)],
  .up 41213191 1,
  .rs 41213191 1 5,
  .parS 41213191,
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 4), (41213191, 2)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 4)],
  .force 5522944621250897 1 [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 6)],
  .rs 5522944621250897 1 3,
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 6), (5522944621250897, 1)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 6)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 10)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2), (5233, 12)],
  .big [(7, 4), (331, 2), (2801, 2), (4933, 2)],
  .force 63601 1 [(7, 4), (331, 4), (2801, 2), (4933, 2)],
  .rs 63601 1 9,
  .force 37861 1 [(7, 4), (331, 4), (2801, 2), (4933, 2), (63601, 1)],
  .up 37861 1,
  .rs 37861 1 9,
  .par2 63601 37861,
  .force 10753 1 [(7, 4), (331, 4), (2801, 2), (4933, 2), (37861, 2), (63601, 1)],
  .up 10753 1,
  .rs 10753 1 7,
  .par2 63601 10753,
  .force 1201 1 [(7, 4), (331, 4), (2801, 2), (4933, 2), (10753, 2), (37861, 2), (63601, 1)],
  .up 1201 1,
  .rs 1201 1 4,
  .par2 63601 1201,
  .big [(7, 4), (331, 4), (1201, 2), (2801, 2), (4933, 2), (10753, 2), (37861, 2), (63601, 1)],
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2), (10753, 2), (37861, 2), (63601, 1)],
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2), (10753, 4), (37861, 2), (63601, 1)],
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2), (37861, 2), (63601, 1)],
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2), (37861, 4), (63601, 1)],
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2), (37861, 6), (63601, 1)],
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2), (63601, 1)],
  .force 612067 1 [(7, 4), (331, 4), (2801, 2), (4933, 2), (63601, 2)],
  .up 612067 1,
  .rs 612067 1 6,
  .parS 612067,
  .force 26010319 1 [(7, 4), (331, 4), (2801, 2), (4933, 2), (63601, 2), (612067, 2)],
  .up 26010319 1,
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2), (63601, 2), (612067, 2)],
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2), (63601, 2), (612067, 4)],
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2), (63601, 2)],
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2), (63601, 4)],
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2), (63601, 6)],
  .big [(7, 4), (331, 4), (2801, 2), (4933, 2)],
  .force 604842197 1 [(7, 4), (331, 6), (2801, 2), (4933, 2)],
  .rs 604842197 1 5,
  .force 2180921 1 [(7, 4), (331, 6), (2801, 2), (4933, 2), (604842197, 1)],
  .up 2180921 1,
  .rs 2180921 1 5,
  .par2 604842197 2180921,
  .big [(7, 4), (331, 6), (2801, 2), (4933, 2), (2180921, 2), (604842197, 1)],
  .big [(7, 4), (331, 6), (2801, 2), (4933, 2), (604842197, 1)],
  .big [(7, 4), (331, 6), (2801, 2), (4933, 2), (604842197, 2)],
  .big [(7, 4), (331, 6), (2801, 2), (4933, 2)],
  .force 703207451121161180833 1 [(7, 4), (331, 10), (2801, 2), (4933, 2)],
  .rs 703207451121161180833 1 3,
  .big [(7, 4), (331, 10), (2801, 2), (4933, 2), (703207451121161180833, 1)],
  .big [(7, 4), (331, 10), (2801, 2), (4933, 2)],
  .big [(7, 4), (331, 12), (2801, 2), (4933, 2)],
  .big [(7, 4), (331, 16), (2801, 2), (4933, 2)],
  .big [(7, 4), (331, 18), (2801, 2), (4933, 2)],
  .big [(7, 4), (2801, 2), (4933, 2)],
  .force 230329301 1 [(7, 4), (2801, 2), (4933, 4)],
  .rs 230329301 1 7,
  .force 111919 1 [(7, 4), (2801, 2), (4933, 4), (230329301, 1)],
  .up 111919 1,
  .rs 111919 1 9,
  .par2 230329301 111919,
  .force 7541 1 [(7, 4), (2801, 2), (4933, 4), (111919, 2), (230329301, 1)],
  .up 7541 1,
  .rs 7541 1 6,
  .par2 230329301 7541,
  .force 121267 1 [(7, 4), (2801, 2), (4933, 4), (7541, 2), (111919, 2), (230329301, 1)],
  .up 121267 1,
  .big [(7, 4), (2801, 2), (4933, 4), (7541, 2), (111919, 2), (230329301, 1)],
  .big [(7, 4), (2801, 2), (4933, 4), (7541, 4), (111919, 2), (230329301, 1)],
  .big [(7, 4), (2801, 2), (4933, 4), (111919, 2), (230329301, 1)],
  .big [(7, 4), (2801, 2), (4933, 4), (111919, 4), (230329301, 1)],
  .big [(7, 4), (2801, 2), (4933, 4), (111919, 6), (230329301, 1)],
  .big [(7, 4), (2801, 2), (4933, 4), (230329301, 1)],
  .force 237899493854161 1 [(7, 4), (2801, 2), (4933, 4), (230329301, 2)],
  .rs 237899493854161 1 3,
  .big [(7, 4), (2801, 2), (4933, 4), (230329301, 2), (237899493854161, 1)],
  .big [(7, 4), (2801, 2), (4933, 4), (230329301, 2)],
  .big [(7, 4), (2801, 2), (4933, 4), (230329301, 4)],
  .big [(7, 4), (2801, 2), (4933, 4)],
  .force 12400411646533 1 [(7, 4), (2801, 2), (4933, 6)],
  .rs 12400411646533 1 4,
  .force 77619973 1 [(7, 4), (2801, 2), (4933, 6), (12400411646533, 1)],
  .up 77619973 1,
  .rs 77619973 1 4,
  .par2 12400411646533 77619973,
  .big [(7, 4), (2801, 2), (4933, 6), (77619973, 2), (12400411646533, 1)],
  .big [(7, 4), (2801, 2), (4933, 6), (12400411646533, 1)],
  .big [(7, 4), (2801, 2), (4933, 6), (12400411646533, 2)],
  .big [(7, 4), (2801, 2), (4933, 6)],
  .big [(7, 4), (2801, 2), (4933, 10)],
  .big [(7, 4), (2801, 2), (4933, 12)],
  .big [(7, 4), (2801, 2), (4933, 16)],
  .big [(7, 4), (2801, 2)],
  .force 6294091 1 [(7, 4), (2801, 4)],
  .up 6294091 1,
  .rs 6294091 1 10,
  .parS 6294091,
  .force 13205195936791 1 [(7, 4), (2801, 4), (6294091, 2)],
  .up 13205195936791 1,
  .rs 13205195936791 1 5,
  .parS 13205195936791,
  .big [(7, 4), (2801, 4), (6294091, 2), (13205195936791, 2)],
  .big [(7, 4), (2801, 4), (6294091, 2)],
  .force 59376284620771 1 [(7, 4), (2801, 4), (6294091, 4)],
  .up 59376284620771 1,
  .big [(7, 4), (2801, 4), (6294091, 4)],
  .big [(7, 4), (2801, 4), (6294091, 6)],
  .big [(7, 4), (2801, 4)],
  .force 2884629032993 1 [(7, 4), (2801, 6)],
  .rs 2884629032993 1 5,
  .force 480771505499 1 [(7, 4), (2801, 6), (2884629032993, 1)],
  .up 480771505499 1,
  .rs 480771505499 1 4,
  .par2 2884629032993 480771505499,
  .big [(7, 4), (2801, 6), (480771505499, 2), (2884629032993, 1)],
  .big [(7, 4), (2801, 6), (2884629032993, 1)],
  .big [(7, 4), (2801, 6), (2884629032993, 2)],
  .big [(7, 4), (2801, 6)],
  .force 2033125998091 1 [(7, 4), (2801, 10)],
  .up 2033125998091 1,
  .big [(7, 4), (2801, 10)],
  .big [(7, 4), (2801, 12)],
  .big [(7, 4), (2801, 16)],
  .big [(7, 4), (2801, 18)],
  .big [(7, 4)],
  .force 4733 1 [(7, 6)],
  .rs 4733 1 21,
  .force 263 1 [(7, 6), (4733, 1)],
  .up 263 1,
  .rs 263 1 30,
  .par2 4733 263,
  .force 109 1 [(7, 6), (263, 2), (4733, 1)],
  .up 109 1,
  .rs 109 1 32,
  .par2 4733 109,
  .force 571 1 [(7, 6), (109, 2), (263, 2), (4733, 1)],
  .up 571 1,
  .rs 571 1 22,
  .par2 4733 571,
  .force 151 1 [(7, 6), (109, 2), (263, 2), (571, 2), (4733, 1)],
  .up 151 1,
  .rs 151 1 24,
  .par2 4733 151,
  .force 1093 1 [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (4733, 1)],
  .up 1093 1,
  .rs 1093 1 16,
  .par2 4733 1093,
  .force 398581 1 [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 2), (4733, 1)],
  .up 398581 1,
  .rs 398581 1 8,
  .par2 4733 398581,
  .force 32668561 1 [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 2), (4733, 1), (398581, 2)],
  .up 32668561 1,
  .rs 32668561 1 5,
  .par2 4733 32668561,
  .big [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 2), (4733, 1), (398581, 2), (32668561, 2)],
  .big [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 2), (4733, 1), (398581, 2)],
  .big [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 2), (4733, 1), (398581, 4)],
  .big [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 2), (4733, 1), (398581, 6)],
  .big [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 2), (4733, 1)],
  .force 4189129561 1 [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 4), (4733, 1)],
  .up 4189129561 1,
  .rs 4189129561 1 5,
  .par2 4733 4189129561,
  .big [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 4), (4733, 1), (4189129561, 2)],
  .big [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 4), (4733, 1)],
  .force 562731116179 1 [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 6), (4733, 1)],
  .up 562731116179 1,
  .big [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 6), (4733, 1)],
  .big [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 10), (4733, 1)],
  .big [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (1093, 12), (4733, 1)]]

/-- Instructions, part 3. -/
def tree7_3 : List Ins := [
  .big [(7, 6), (109, 2), (151, 2), (263, 2), (571, 2), (4733, 1)],
  .force 104670301 1 [(7, 6), (109, 2), (151, 4), (263, 2), (571, 2), (4733, 1)],
  .up 104670301 1,
  .rs 104670301 1 6,
  .par2 4733 104670301,
  .force 2357622555649 1 [(7, 6), (109, 2), (151, 4), (263, 2), (571, 2), (4733, 1), (104670301, 2)],
  .up 2357622555649 1,
  .big [(7, 6), (109, 2), (151, 4), (263, 2), (571, 2), (4733, 1), (104670301, 2)],
  .big [(7, 6), (109, 2), (151, 4), (263, 2), (571, 2), (4733, 1), (104670301, 4)],
  .big [(7, 6), (109, 2), (151, 4), (263, 2), (571, 2), (4733, 1)],
  .force 7960598843 1 [(7, 6), (109, 2), (151, 6), (263, 2), (571, 2), (4733, 1)],
  .up 7960598843 1,
  .rs 7960598843 1 5,
  .par2 4733 7960598843,
  .big [(7, 6), (109, 2), (151, 6), (263, 2), (571, 2), (4733, 1), (7960598843, 2)],
  .big [(7, 6), (109, 2), (151, 6), (263, 2), (571, 2), (4733, 1)],
  .force 18145704541823 1 [(7, 6), (109, 2), (151, 10), (263, 2), (571, 2), (4733, 1)],
  .up 18145704541823 1,
  .big [(7, 6), (109, 2), (151, 10), (263, 2), (571, 2), (4733, 1)],
  .big [(7, 6), (109, 2), (151, 12), (263, 2), (571, 2), (4733, 1)],
  .big [(7, 6), (109, 2), (151, 16), (263, 2), (571, 2), (4733, 1)],
  .big [(7, 6), (109, 2), (151, 18), (263, 2), (571, 2), (4733, 1)],
  .big [(7, 6), (109, 2), (151, 22), (263, 2), (571, 2), (4733, 1)],
  .big [(7, 6), (109, 2), (263, 2), (571, 2), (4733, 1)],
  .force 11631811 1 [(7, 6), (109, 2), (263, 2), (571, 4), (4733, 1)],
  .up 11631811 1,
  .rs 11631811 1 7,
  .par2 4733 11631811,
  .force 1831 1 [(7, 6), (109, 2), (263, 2), (571, 4), (4733, 1), (11631811, 2)],
  .up 1831 1,
  .rs 1831 1 7,
  .par2 4733 1831,
  .force 1237 1 [(7, 6), (109, 2), (263, 2), (571, 4), (1831, 2), (4733, 1), (11631811, 2)],
  .up 1237 1,
  .rs 1237 1 5,
  .par2 4733 1237,
  .big [(7, 6), (109, 2), (263, 2), (571, 4), (1237, 2), (1831, 2), (4733, 1), (11631811, 2)],
  .big [(7, 6), (109, 2), (263, 2), (571, 4), (1831, 2), (4733, 1), (11631811, 2)],
  .big [(7, 6), (109, 2), (263, 2), (571, 4), (1831, 4), (4733, 1), (11631811, 2)],
  .big [(7, 6), (109, 2), (263, 2), (571, 4), (4733, 1), (11631811, 2)],
  .big [(7, 6), (109, 2), (263, 2), (571, 4), (4733, 1), (11631811, 4)],
  .big [(7, 6), (109, 2), (263, 2), (571, 4), (4733, 1)],
  .force 41284013010997 1 [(7, 6), (109, 2), (263, 2), (571, 6), (4733, 1)],
  .up 41284013010997 1,
  .rs 41284013010997 1 4,
  .par2 4733 41284013010997,
  .big [(7, 6), (109, 2), (263, 2), (571, 6), (4733, 1), (41284013010997, 2)],
  .big [(7, 6), (109, 2), (263, 2), (571, 6), (4733, 1)],
  .force 3867675755483 1 [(7, 6), (109, 2), (263, 2), (571, 10), (4733, 1)],
  .up 3867675755483 1,
  .big [(7, 6), (109, 2), (263, 2), (571, 10), (4733, 1)],
  .big [(7, 6), (109, 2), (263, 2), (571, 12), (4733, 1)],
  .big [(7, 6), (109, 2), (263, 2), (571, 16), (4733, 1)],
  .big [(7, 6), (109, 2), (263, 2), (571, 18), (4733, 1)],
  .big [(7, 6), (109, 2), (263, 2), (4733, 1)],
  .force 24061 1 [(7, 6), (109, 4), (263, 2), (4733, 1)],
  .up 24061 1,
  .rs 24061 1 13,
  .par2 4733 24061,
  .force 46807 1 [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 2)],
  .up 46807 1,
  .rs 46807 1 10,
  .par2 4733 46807,
  .force 730314019 1 [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 2), (46807, 2)],
  .up 730314019 1,
  .rs 730314019 1 5,
  .par2 4733 730314019,
  .big [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 2), (46807, 2), (730314019, 2)],
  .big [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 2), (46807, 2)],
  .force 78690566287141541 1 [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 2), (46807, 4)],
  .up 78690566287141541 1,
  .big [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 2), (46807, 4)],
  .big [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 2), (46807, 6)],
  .big [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 2)],
  .force 3265059751 1 [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 4)],
  .up 3265059751 1,
  .rs 3265059751 1 4,
  .par2 4733 3265059751,
  .big [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 4), (3265059751, 2)],
  .big [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 4)],
  .big [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 6)],
  .big [(7, 6), (109, 4), (263, 2), (4733, 1), (24061, 10)],
  .big [(7, 6), (109, 4), (263, 2), (4733, 1)],
  .force 53306107 1 [(7, 6), (109, 6), (263, 2), (4733, 1)],
  .up 53306107 1,
  .rs 53306107 1 7,
  .par2 4733 53306107,
  .force 49851598189501 1 [(7, 6), (109, 6), (263, 2), (4733, 1), (53306107, 2)],
  .up 49851598189501 1,
  .rs 49851598189501 1 4,
  .par2 4733 49851598189501,
  .big [(7, 6), (109, 6), (263, 2), (4733, 1), (53306107, 2), (49851598189501, 2)],
  .big [(7, 6), (109, 6), (263, 2), (4733, 1), (53306107, 2)],
  .big [(7, 6), (109, 6), (263, 2), (4733, 1), (53306107, 4)],
  .big [(7, 6), (109, 6), (263, 2), (4733, 1)],
  .force 23971944503021153 1 [(7, 6), (109, 10), (263, 2), (4733, 1)],
  .up 23971944503021153 1,
  .rs 23971944503021153 1 4,
  .par2 4733 23971944503021153,
  .big [(7, 6), (109, 10), (263, 2), (4733, 1), (23971944503021153, 2)],
  .big [(7, 6), (109, 10), (263, 2), (4733, 1)],
  .force 9700639967080761011 1 [(7, 6), (109, 12), (263, 2), (4733, 1)],
  .up 9700639967080761011 1,
  .big [(7, 6), (109, 12), (263, 2), (4733, 1)],
  .big [(7, 6), (109, 16), (263, 2), (4733, 1)],
  .big [(7, 6), (109, 18), (263, 2), (4733, 1)],
  .big [(7, 6), (109, 22), (263, 2), (4733, 1)],
  .big [(7, 6), (109, 28), (263, 2), (4733, 1)],
  .big [(7, 6), (109, 30), (263, 2), (4733, 1)],
  .big [(7, 6), (263, 2), (4733, 1)],
  .force 4802611441 1 [(7, 6), (263, 4), (4733, 1)],
  .up 4802611441 1,
  .rs 4802611441 1 8,
  .par2 4733 4802611441,
  .force 208124989 1 [(7, 6), (263, 4), (4733, 1), (4802611441, 2)],
  .up 208124989 1,
  .rs 208124989 1 5,
  .par2 4733 208124989,
  .big [(7, 6), (263, 4), (4733, 1), (208124989, 2), (4802611441, 2)],
  .big [(7, 6), (263, 4), (4733, 1), (4802611441, 2)],
  .big [(7, 6), (263, 4), (4733, 1), (4802611441, 4)],
  .big [(7, 6), (263, 4), (4733, 1), (4802611441, 6)],
  .big [(7, 6), (263, 4), (4733, 1)],
  .force 192750517 1 [(7, 6), (263, 6), (4733, 1)],
  .up 192750517 1,
  .rs 192750517 1 7,
  .par2 4733 192750517,
  .force 78785754721 1 [(7, 6), (263, 6), (4733, 1), (192750517, 2)],
  .up 78785754721 1,
  .rs 78785754721 1 4,
  .par2 4733 78785754721,
  .big [(7, 6), (263, 6), (4733, 1), (192750517, 2), (78785754721, 2)],
  .big [(7, 6), (263, 6), (4733, 1), (192750517, 2)],
  .big [(7, 6), (263, 6), (4733, 1), (192750517, 4)],
  .big [(7, 6), (263, 6), (4733, 1)],
  .force 3124914562747294549 1 [(7, 6), (263, 10), (4733, 1)],
  .up 3124914562747294549 1,
  .rs 3124914562747294549 1 4,
  .par2 4733 3124914562747294549,
  .big [(7, 6), (263, 10), (4733, 1), (3124914562747294549, 2)],
  .big [(7, 6), (263, 10), (4733, 1)],
  .force 539093310059453790343 1 [(7, 6), (263, 12), (4733, 1)],
  .up 539093310059453790343 1,
  .big [(7, 6), (263, 12), (4733, 1)],
  .big [(7, 6), (263, 16), (4733, 1)],
  .big [(7, 6), (263, 18), (4733, 1)],
  .big [(7, 6), (263, 22), (4733, 1)],
  .big [(7, 6), (263, 28), (4733, 1)],
  .big [(7, 6), (4733, 1)],
  .force 22406023 1 [(7, 6), (4733, 2)],
  .up 22406023 1,
  .rs 22406023 1 10,
  .parS 22406023,
  .force 606538249 1 [(7, 6), (4733, 2), (22406023, 2)],
  .rs 606538249 1 7,
  .force 1283 1 [(7, 6), (4733, 2), (22406023, 2), (606538249, 1)],
  .up 1283 1,
  .rs 1283 1 11,
  .par2 606538249 1283,
  .force 1117 1 [(7, 6), (1283, 2), (4733, 2), (22406023, 2), (606538249, 1)],
  .up 1117 1,
  .rs 1117 1 9,
  .par2 606538249 1117,
  .force 59467 1 [(7, 6), (1117, 2), (1283, 2), (4733, 2), (22406023, 2), (606538249, 1)],
  .up 59467 1,
  .rs 59467 1 5,
  .par2 606538249 59467,
  .big [(7, 6), (1117, 2), (1283, 2), (4733, 2), (59467, 2), (22406023, 2), (606538249, 1)],
  .big [(7, 6), (1117, 2), (1283, 2), (4733, 2), (22406023, 2), (606538249, 1)],
  .big [(7, 6), (1117, 4), (1283, 2), (4733, 2), (22406023, 2), (606538249, 1)],
  .big [(7, 6), (1117, 6), (1283, 2), (4733, 2), (22406023, 2), (606538249, 1)],
  .big [(7, 6), (1283, 2), (4733, 2), (22406023, 2), (606538249, 1)],
  .force 337871 1 [(7, 6), (1283, 4), (4733, 2), (22406023, 2), (606538249, 1)],
  .up 337871 1,
  .big [(7, 6), (1283, 4), (4733, 2), (22406023, 2), (606538249, 1)],
  .big [(7, 6), (1283, 6), (4733, 2), (22406023, 2), (606538249, 1)],
  .big [(7, 6), (4733, 2), (22406023, 2), (606538249, 1)],
  .force 2635909 1 [(7, 6), (4733, 2), (22406023, 2), (606538249, 2)],
  .rs 2635909 1 4,
  .force 263591 1 [(7, 6), (4733, 2), (2635909, 1), (22406023, 2), (606538249, 2)],
  .up 263591 1,
  .big [(7, 6), (4733, 2), (2635909, 1), (22406023, 2), (606538249, 2)],
  .big [(7, 6), (4733, 2), (2635909, 2), (22406023, 2), (606538249, 2)],
  .big [(7, 6), (4733, 2), (22406023, 2), (606538249, 2)],
  .big [(7, 6), (4733, 2), (22406023, 2), (606538249, 4)],
  .big [(7, 6), (4733, 2), (22406023, 2)],
  .force 829007553280001 1 [(7, 6), (4733, 2), (22406023, 4)],
  .rs 829007553280001 1 3,
  .big [(7, 6), (4733, 2), (22406023, 4), (829007553280001, 1)],
  .big [(7, 6), (4733, 2), (22406023, 4)],
  .big [(7, 6), (4733, 2), (22406023, 6)],
  .big [(7, 6), (4733, 2)],
  .force 11018941331 1 [(7, 6), (4733, 4)],
  .up 11018941331 1,
  .rs 11018941331 1 7,
  .parS 11018941331,
  .force 8580759007 1 [(7, 6), (4733, 4), (11018941331, 2)],
  .up 8580759007 1,
  .rs 8580759007 1 4,
  .parS 8580759007,
  .big [(7, 6), (4733, 4), (8580759007, 2), (11018941331, 2)],
  .big [(7, 6), (4733, 4), (11018941331, 2)],
  .big [(7, 6), (4733, 4), (11018941331, 4)],
  .big [(7, 6), (4733, 4)],
  .force 329422297 1 [(7, 6), (4733, 6)],
  .rs 329422297 1 6,
  .force 69655517 1 [(7, 6), (4733, 6), (329422297, 1)],
  .up 69655517 1,
  .rs 69655517 1 5,
  .par2 329422297 69655517,
  .big [(7, 6), (4733, 6), (69655517, 2), (329422297, 1)],
  .big [(7, 6), (4733, 6), (329422297, 1)],
  .force 69655517 1 [(7, 6), (4733, 6), (329422297, 2)],
  .rs 69655517 1 3,
  .big [(7, 6), (4733, 6), (69655517, 1), (329422297, 2)],
  .big [(7, 6), (4733, 6), (329422297, 2)],
  .big [(7, 6), (4733, 6), (329422297, 4)],
  .big [(7, 6), (4733, 6)],
  .big [(7, 6), (4733, 10)],
  .big [(7, 6), (4733, 12)],
  .big [(7, 6), (4733, 16)],
  .big [(7, 6), (4733, 18)],
  .big [(7, 6)],
  .force 293459 1 [(7, 10)],
  .up 293459 1,
  .rs 293459 1 14,
  .parS 293459,
  .force 310897033 1 [(7, 10), (293459, 2)],
  .rs 310897033 1 8,
  .force 84437 1 [(7, 10), (293459, 2), (310897033, 1)],
  .up 84437 1,
  .rs 84437 1 10,
  .par2 310897033 84437,
  .force 23269 1 [(7, 10), (84437, 2), (293459, 2), (310897033, 1)],
  .up 23269 1,
  .rs 23269 1 8,
  .par2 310897033 23269,
  .force 6781 1 [(7, 10), (23269, 2), (84437, 2), (293459, 2), (310897033, 1)],
  .up 6781 1,
  .rs 6781 1 5,
  .par2 310897033 6781,
  .big [(7, 10), (6781, 2), (23269, 2), (84437, 2), (293459, 2), (310897033, 1)],
  .big [(7, 10), (23269, 2), (84437, 2), (293459, 2), (310897033, 1)],
  .big [(7, 10), (23269, 4), (84437, 2), (293459, 2), (310897033, 1)],
  .big [(7, 10), (23269, 6), (84437, 2), (293459, 2), (310897033, 1)],
  .big [(7, 10), (84437, 2), (293459, 2), (310897033, 1)],
  .force 5144408211938741 1 [(7, 10), (84437, 4), (293459, 2), (310897033, 1)],
  .up 5144408211938741 1,
  .big [(7, 10), (84437, 4), (293459, 2), (310897033, 1)],
  .big [(7, 10), (84437, 6), (293459, 2), (310897033, 1)],
  .big [(7, 10), (293459, 2), (310897033, 1)],
  .force 139017523 1 [(7, 10), (293459, 2), (310897033, 2)],
  .up 139017523 1,
  .rs 139017523 1 5,
  .parS 139017523,
  .big [(7, 10), (293459, 2), (139017523, 2), (310897033, 2)],
  .big [(7, 10), (293459, 2), (310897033, 2)],
  .big [(7, 10), (293459, 2), (310897033, 4)],
  .big [(7, 10), (293459, 2), (310897033, 6)],
  .big [(7, 10), (293459, 2)],
  .force 9875322243666178231 1 [(7, 10), (293459, 4)],
  .up 9875322243666178231 1,
  .rs 9875322243666178231 1 4,
  .parS 9875322243666178231,
  .big [(7, 10), (293459, 4), (9875322243666178231, 2)],
  .big [(7, 10), (293459, 4)],
  .force 60082728190583743 1 [(7, 10), (293459, 6)],
  .up 60082728190583743 1,
  .big [(7, 10), (293459, 6)],
  .big [(7, 10), (293459, 10)],
  .big [(7, 10), (293459, 12)],
  .big [(7, 10)],
  .force 16148168401 1 [(7, 12)],
  .rs 16148168401 1 8,
  .force 110563 1 [(7, 12), (16148168401, 1)],
  .up 110563 1,
  .rs 110563 1 12,
  .par2 16148168401 110563,
  .force 226741 1 [(7, 12), (110563, 2), (16148168401, 1)],
  .up 226741 1,
  .rs 226741 1 9,
  .par2 16148168401 226741,
  .force 17971 1 [(7, 12), (110563, 2), (226741, 2), (16148168401, 1)],
  .up 17971 1,
  .rs 17971 1 7,
  .par2 16148168401 17971,
  .force 415669 1 [(7, 12), (17971, 2), (110563, 2), (226741, 2), (16148168401, 1)],
  .up 415669 1,
  .rs 415669 1 4,
  .par2 16148168401 415669,
  .big [(7, 12), (17971, 2), (110563, 2), (226741, 2), (415669, 2), (16148168401, 1)],
  .big [(7, 12), (17971, 2), (110563, 2), (226741, 2), (16148168401, 1)],
  .big [(7, 12), (17971, 4), (110563, 2), (226741, 2), (16148168401, 1)],
  .big [(7, 12), (110563, 2), (226741, 2), (16148168401, 1)],
  .big [(7, 12), (110563, 2), (226741, 4), (16148168401, 1)],
  .big [(7, 12), (110563, 2), (226741, 6), (16148168401, 1)],
  .big [(7, 12), (110563, 2), (16148168401, 1)],
  .force 149431854123332538041 1 [(7, 12), (110563, 4), (16148168401, 1)],
  .up 149431854123332538041 1,
  .big [(7, 12), (110563, 4), (16148168401, 1)],
  .big [(7, 12), (110563, 6), (16148168401, 1)],
  .big [(7, 12), (110563, 10), (16148168401, 1)],
  .big [(7, 12), (16148168401, 1)],
  .force 200741603328100897 1 [(7, 12), (16148168401, 2)],
  .rs 200741603328100897 1 4,
  .force 412450637 1 [(7, 12), (16148168401, 2), (200741603328100897, 1)],
  .up 412450637 1,
  .rs 412450637 1 4,
  .par2 200741603328100897 412450637,
  .big [(7, 12), (412450637, 2), (16148168401, 2), (200741603328100897, 1)],
  .big [(7, 12), (16148168401, 2), (200741603328100897, 1)],
  .big [(7, 12), (16148168401, 2), (200741603328100897, 2)],
  .big [(7, 12), (16148168401, 2)],
  .big [(7, 12), (16148168401, 4)],
  .big [(7, 12), (16148168401, 6)],
  .big [(7, 12)],
  .force 2767631689 1 [(7, 16)],
  .rs 2767631689 1 8,
  .force 276763169 1 [(7, 16), (2767631689, 1)],
  .up 276763169 1,
  .rs 276763169 1 8,
  .par2 2767631689 276763169,
  .force 2263148233 1 [(7, 16), (276763169, 2), (2767631689, 1)],
  .up 2263148233 1,
  .rs 2263148233 1 4,
  .par2 2767631689 2263148233,
  .big [(7, 16), (276763169, 2), (2263148233, 2), (2767631689, 1)],
  .big [(7, 16), (276763169, 2), (2767631689, 1)],
  .big [(7, 16), (276763169, 4), (2767631689, 1)],
  .big [(7, 16), (276763169, 6), (2767631689, 1)],
  .big [(7, 16), (2767631689, 1)],
  .force 34199239 1 [(7, 16), (2767631689, 2)],
  .up 34199239 1,
  .rs 34199239 1 6,
  .parS 34199239,
  .force 14009 1 [(7, 16), (34199239, 2), (2767631689, 2)],
  .rs 14009 1 4,
  .force 4441 1 [(7, 16), (14009, 1), (34199239, 2), (2767631689, 2)],
  .up 4441 1,
  .big [(7, 16), (14009, 1), (34199239, 2), (2767631689, 2)],
  .big [(7, 16), (14009, 2), (34199239, 2), (2767631689, 2)],
  .big [(7, 16), (34199239, 2), (2767631689, 2)],
  .big [(7, 16), (34199239, 4), (2767631689, 2)],
  .big [(7, 16), (2767631689, 2)],
  .big [(7, 16), (2767631689, 4)],
  .big [(7, 16), (2767631689, 6)],
  .big [(7, 16)],
  .force 4534166740403 1 [(7, 18)],
  .up 4534166740403 1,
  .rs 4534166740403 1 6,
  .parS 4534166740403,
  .force 4721697244987 1 [(7, 18), (4534166740403, 2)],
  .up 4721697244987 1,
  .big [(7, 18), (4534166740403, 2)],
  .big [(7, 18), (4534166740403, 4)],
  .big [(7, 18)],
  .force 31479823396757 1 [(7, 22)],
  .rs 31479823396757 1 6,
  .force 826632619 1 [(7, 22), (31479823396757, 1)],
  .up 826632619 1,
  .rs 826632619 1 6,
  .par2 31479823396757 826632619,
  .force 401173 1 [(7, 22), (826632619, 2), (31479823396757, 1)],
  .up 401173 1,
  .big [(7, 22), (826632619, 2), (31479823396757, 1)],
  .big [(7, 22), (826632619, 4), (31479823396757, 1)],
  .big [(7, 22), (31479823396757, 1)],
  .force 1331399425301563 1 [(7, 22), (31479823396757, 2)],
  .up 1331399425301563 1,
  .big [(7, 22), (31479823396757, 2)],
  .big [(7, 22), (31479823396757, 4)],
  .big [(7, 22)],
  .force 71316922984999 1 [(7, 28)],
  .up 71316922984999 1,
  .rs 71316922984999 1 5,
  .parS 71316922984999,
  .big [(7, 28), (71316922984999, 2)],
  .big [(7, 28)],
  .force 3999088279399464409 1 [(7, 30)],
  .rs 3999088279399464409 1 4,
  .force 26677735199 1 [(7, 30), (3999088279399464409, 1)],
  .up 26677735199 1,
  .big [(7, 30), (3999088279399464409, 1)],
  .big [(7, 30), (3999088279399464409, 2)],
  .big [(7, 30)],
  .force 4805345109492315767981401 1 [(7, 36)],
  .rs 4805345109492315767981401 1 3,
  .big [(7, 36), (4805345109492315767981401, 1)],
  .big [(7, 36)],
  .force 4362139336229068656094783 1 [(7, 40)],
  .up 4362139336229068656094783 1,
  .big [(7, 40)],
  .force 2192537062271178641 1 [(7, 42)],
  .rs 2192537062271178641 1 3,
  .big [(7, 42), (2192537062271178641, 1)],
  .big [(7, 42)],
  .force 63681511996418550459487 1 [(7, 46)],
  .up 63681511996418550459487 1,
  .big [(7, 46)],
  .big [(7, 52)]]

/-- Instructions, part 4. -/
def tree7_4 : List Ins := [
  .big [(7, 58)],
  .big [(7, 60)],
  .big [(7, 66)],
  .big [(7, 70)],
  .big [(7, 72)],
  .big [(7, 78)],
  .big [(7, 82)],
  .big [(7, 88)],
  .big []]

/-- The tree for `7`. -/
def tree7 : List Ins := tree7_0 ++ tree7_1 ++ tree7_2 ++ tree7_3 ++ tree7_4

/-! ## Generated trees (END) -/

/-! ## The lower bound -/

/-- The tree for `3 ∣ N`. -/
theorem good3 : Good (10 ^ 79) [.pw 3 1] :=
  run_sound table_prime tree3 [[.pw 3 1]] (by decide +kernel) _ List.mem_cons_self

/-- The tree for `3 ∤ N`, `5 ∣ N`. -/
theorem good5 : Good (10 ^ 79) [.pw 5 1, .nd 3] :=
  run_sound table_prime tree5 [[.pw 5 1, .nd 3]] (by decide +kernel) _ List.mem_cons_self

/-- The tree for `3 ∤ N`, `5 ∤ N`, `7 ∣ N`. -/
theorem good7 : Good (10 ^ 79) [.pw 7 1, .nd 3, .nd 5] :=
  run_sound table_prime tree7 [[.pw 7 1, .nd 3, .nd 5]] (by decide +kernel) _ List.mem_cons_self

/-- If no prime below `11` divides an odd perfect number `N`, then `N` has at least `27`
distinct prime factors. -/
theorem card_primeFactors_of_no_prime_lt_11 {N : ℕ} (h : OddPerfect N)
    (hP : ∀ p, p.Prime → p < 11 → ¬ p ∣ N) : 27 ≤ N.primeFactors.card :=
  length_le_card_primeFactors h (P := 11) (L := 127)
    [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101,
    103, 107, 109, 113, 127]
    (by decide) hP (by decide) (by decide +kernel)
    (by norm_num [List.map, List.prod_cons])

/-- Every odd perfect number exceeds `10 ^ 79`. -/
theorem lower_bound {N : ℕ} (h : OddPerfect N) : 10 ^ 79 < N := by
  by_cases h3 : 3 ∣ N
  · refine good3 N h fun f hf => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl
    · exact ⟨by norm_num, by simpa using h3⟩
  by_cases h5 : 5 ∣ N
  · refine good5 N h fun f hf => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨by norm_num, by simpa using h5⟩
    · exact h3
  by_cases h7 : 7 ∣ N
  · refine good7 N h fun f hf => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact ⟨by norm_num, by simpa using h7⟩
    · exact h3
    · exact h5
  have hP : ∀ p, p.Prime → p < 11 → ¬ p ∣ N := by
    intro p hp hlt hd
    interval_cases p
    all_goals first
      | exact h.not_two_dvd hd
      | exact h3 hd
      | exact h5 hd
      | exact h7 hd
      | norm_num at hp
  have hc := card_primeFactors_of_no_prime_lt_11 h hP
  have hm : ∀ p ∈ N.primeFactors, 11 ≤ p := fun p hp => by
    by_contra hlt
    exact hP p (Nat.prime_of_mem_primeFactors hp) (by omega) (Nat.dvd_of_mem_primeFactors hp)
  calc 10 ^ 79 < 11 *
      [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
        101, 103, 107, 109, 113].prod ^ 2 := by
        norm_num
    _ ≤ N := le_of_card_primeFactors_consec h _ (by decide +kernel) hm (by simp; omega)

end OddPerfect.LowerBound

#print axioms OddPerfect.LowerBound.nbeq_iff
#print axioms OddPerfect.LowerBound.lowP_sound
#print axioms OddPerfect.LowerBound.hasPow_sound
#print axioms OddPerfect.LowerBound.compP_sound
#print axioms OddPerfect.LowerBound.oddP_sound
#print axioms OddPerfect.LowerBound.special_of_odd
#print axioms OddPerfect.LowerBound.gs_eq
#print axioms OddPerfect.LowerBound.nodupB_cons
#print axioms OddPerfect.LowerBound.Dv_dvd_sigma
#print axioms OddPerfect.LowerBound.compsOK_sound
#print axioms OddPerfect.LowerBound.half_dvd
#print axioms OddPerfect.LowerBound.base_dvd
#print axioms OddPerfect.LowerBound.Av_dvd
#print axioms OddPerfect.LowerBound.tdAux_sound
#print axioms OddPerfect.LowerBound.tdPrime_sound
#print axioms OddPerfect.LowerBound.tdAux_complete
#print axioms OddPerfect.LowerBound.tdPrime_complete
#print axioms OddPerfect.LowerBound.smallPrimes_check
#print axioms OddPerfect.LowerBound.mem_smallPrimes
#print axioms OddPerfect.LowerBound.mem_primesBelow
#print axioms OddPerfect.LowerBound.PT.allOK_mem
#print axioms OddPerfect.LowerBound.pm_eq_powModAux
#print axioms OddPerfect.LowerBound.pm_eq
#print axioms OddPerfect.LowerBound.mem_of_dvd_ppow
#print axioms OddPerfect.LowerBound.PT.prime_of_mem
#print axioms OddPerfect.LowerBound.coprime_dprod
#print axioms OddPerfect.LowerBound.dprod_sound
#print axioms OddPerfect.LowerBound.holds_cons
#print axioms OddPerfect.LowerBound.step_sound
#print axioms OddPerfect.LowerBound.run_sound
#print axioms OddPerfect.LowerBound.prod_range_le_prod
#print axioms OddPerfect.LowerBound.prod_consec_le_prod
#print axioms OddPerfect.LowerBound.le_of_card_primeFactors_consec
#print axioms OddPerfect.LowerBound.structural_lower_bound
#print axioms OddPerfect.LowerBound.le_of_card_primeFactors
#print axioms OddPerfect.LowerBound.length_le_card_primeFactors
#print axioms OddPerfect.LowerBound.table_ok
#print axioms OddPerfect.LowerBound.table_prime
#print axioms OddPerfect.LowerBound.good3
#print axioms OddPerfect.LowerBound.good5
#print axioms OddPerfect.LowerBound.good7
#print axioms OddPerfect.LowerBound.card_primeFactors_of_no_prime_lt_11
#print axioms OddPerfect.LowerBound.lower_bound
