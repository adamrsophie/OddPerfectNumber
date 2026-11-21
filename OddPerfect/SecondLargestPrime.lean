import OddPerfect.LargestPrimeFactor

/-!
# Two prime factors above a bound

Let `N` be an odd perfect number. We show that at least two distinct prime factors of `N`
exceed `58`, by a search whose every step is checked by the kernel.

By `exists_primeFactor_gt`, some prime factor `P0` of `N` exceeds `10000`; the search
only uses `3000 < P0`. Suppose every other
prime factor is at most `B`. Writing `S` for the part of `N` built from the odd primes up to
`B` and `a` for the exponent of `P0`, the abundancy satisfies `A(S) A(P0 ^ a) = 2` with
`1 + 1 / P0 ≤ A(P0 ^ a) < P0 / (P0 - 1)`. A search state holds:

* an entry `(q, c, k)` for each odd prime `q ≤ B`: undecided (`c = 0`), not dividing `N`
  (`c = 1`), dividing with exponent at least `k` (`c = 2`), or with exponent exactly `k`
  (`c = 3`);
* `g`: zero, or a number divisible by `P0` whose prime factors are all `P0`;
* bounds `lo ≤ P0 ≤ hi` (with `hi = 0` for no bound);
* `pin`: zero, or `P0` itself, with exponent at least `kP` (exactly `kP` when `xP`).

With `U` and `L` the upper and lower bounds for `A(S)` from the entries:

* `L (1 + 1 / P0) ≤ 2` gives a lower bound for `P0`, and `U P0 / (P0 - 1) > 2` an upper bound;
* an entry with `B < 2 k + 3` gives `2 k + 3 ≤ P0`, since some prime factor is at least
  `2 e + 3` for every exponent `e` (`exists_primeFactor_two_mul_factorization_add_three_le`);
* two primes with exact odd exponents contradict Euler's form;
* for an exact entry, the part of `σ (p ^ k)` coprime to the small primes is a power of `P0`,
  which updates `g`; when `g < lo ^ 2`, `g = P0`;
* when the window for `P0` is short, each candidate coprime to the small primes is tried as
  `pin`; with `pin = P0`, every component divisor sum is free of primes other than the small
  ones and `P0`, `σ (P0 ^ k)` is free of `P0`, and the factor of `P0` is bounded from its
  own entry;
* exact exponents that fail these forcing tests are skipped when a lower bound is raised.

`expand` computes the children of a state and `expand_sound` shows that a state holds only
if a child does. `run` processes a stack of states, and `run_sound` lifts this to stacks. The
search for `B = 58` is split into chunks whose intermediate stacks are written out, so each
chunk is a separate kernel computation.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace SLP

/-! ## Computable helpers

These are stated here so that this file does not depend on the internals of
`LargestPrimeFactor`. -/

/-- The divisor sum of `p ^ e` for prime `p`, in closed form. -/
def gs (p e : ℕ) : ℕ := (p ^ (e + 1) - 1) / (p - 1)

/-- Trial division of `n` by `d, d + 1, ...` while `d * d ≤ n`, for at most `f` steps. -/
def noDiv (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, d => n < d * d || (n % d != 0 && noDiv n f (d + 1))

/-- Primality by trial division up to the square root. -/
def isPrimeF (n : ℕ) : Bool := 2 ≤ n && noDiv n n 2

/-- The odd primes up to `B`. -/
def primesUpTo (B : ℕ) : List ℕ := (List.range (B + 1)).filter fun n => n != 2 && isPrimeF n

/-- Strip the prime factors of `M` from `m`, at most `f` rounds. -/
def cofree (M : ℕ) : ℕ → ℕ → ℕ
  | 0, m => m
  | f + 1, m => if Nat.gcd m M = 1 then m else cofree M f (m / Nat.gcd m M)

/-- Euler's parity condition for the exponent `e` of `p`. -/
def valid (p e : ℕ) : Bool := e % 2 == 0 || (p % 4 == 1 && e % 4 == 1)

/-- The least exponent above `k` allowed by Euler's parity condition. -/
def nextValid (p k : ℕ) : ℕ := if valid p (k + 1) then k + 1 else k + 2

/-- An entry `(q, c, k)` for a small prime `q`. Code `c`: `0` undecided, `1` does not divide,
`2` divides with exponent at least `k`, `3` exponent exactly `k`. -/
abbrev Ent := ℕ × ℕ × ℕ

/-- Numerator of the upper abundancy factor. -/
def un1 (e : Ent) : ℕ := if e.2.1 = 3 then gs e.1 e.2.2 else if e.2.1 = 1 then 1 else e.1
/-- Denominator of the upper abundancy factor. -/
def ud1 (e : Ent) : ℕ := if e.2.1 = 3 then e.1 ^ e.2.2 else if e.2.1 = 1 then 1 else e.1 - 1
/-- Numerator of the lower abundancy factor. -/
def ln1 (e : Ent) : ℕ := if 2 ≤ e.2.1 then gs e.1 e.2.2 else 1
/-- Denominator of the lower abundancy factor. -/
def ld1 (e : Ent) : ℕ := if 2 ≤ e.2.1 then e.1 ^ e.2.2 else 1

/-- Upper bound numerator. -/
def uN (st : List Ent) : ℕ := (st.map un1).prod
/-- Upper bound denominator. -/
def uD (st : List Ent) : ℕ := (st.map ud1).prod
/-- Lower bound numerator. -/
def lN (st : List Ent) : ℕ := (st.map ln1).prod
/-- Lower bound denominator. -/
def lD (st : List Ent) : ℕ := (st.map ld1).prod

/-- The bound `2 k + 3` on the large prime from an entry with `B < 2 k + 3`. -/
def loEnt (B : ℕ) (e : Ent) : ℕ := if 2 ≤ e.2.1 ∧ B < 2 * e.2.2 + 3 then 2 * e.2.2 + 3 else 0

/-- Minimum, with `0` standing for no bound. -/
def minz (a b : ℕ) : ℕ := if a = 0 then b else min a b

/-- The refined lower bound for the large prime. -/
def newLo (B : ℕ) (st : List Ent) (lo : ℕ) : ℕ :=
  if lN st < 2 * lD st then
    max (max lo ((st.map (loEnt B)).foldr max 0))
      ((lN st + (2 * lD st - lN st) - 1) / (2 * lD st - lN st))
  else max lo ((st.map (loEnt B)).foldr max 0)

/-- The upper bound for the large prime from the abundancy (`hi` when none). -/
def hiU (st : List Ent) (hi : ℕ) : ℕ :=
  if uN st < 2 * uD st then minz hi ((2 * uD st - 1) / (2 * uD st - uN st)) else hi

/-- The refined upper bound for the large prime (`0`: none). -/
def newHi (st : List Ent) (g hi : ℕ) : ℕ := if 0 < g then minz (hiU st hi) g else hiU st hi

/-- Numerator of the upper factor of the large prime. -/
def pun (pin kP : ℕ) (xP : Bool) : ℕ := if xP then gs pin kP else pin
/-- Denominator of the upper factor of the large prime. -/
def pud (pin kP : ℕ) (xP : Bool) : ℕ := if xP then pin ^ kP else pin - 1

/-- Two distinct primes with exact odd exponents. -/
def parityBad (st : List Ent) (pin kP : ℕ) (xP : Bool) : Bool :=
  let o := (st.filter fun e => e.2.1 == 3 && e.2.2 % 2 == 1).map Prod.fst ++
    (if pin != 0 && xP && kP % 2 == 1 then [pin] else [])
  o.any fun a => o.any fun b => a != b

/-- Everything is exact. -/
def allEx (st : List Ent) (xP : Bool) : Bool := xP && st.all fun e => e.2.1 == 1 || e.2.1 == 3

/-- The closing rules. -/
def closed (st : List Ent) (lo hi pin kP : ℕ) (xP : Bool) : Bool :=
  parityBad st pin kP xP || 2 * lD st ≤ lN st || (hi != 0 && hi < lo) ||
    (0 < lo && uN st * lo ≤ 2 * (lo - 1) * uD st) ||
    (pin != 0 &&
      (uN st * pun pin kP xP < 2 * (uD st * pud pin kP xP) ||
       (uN st * pun pin kP xP == 2 * (uD st * pud pin kP xP) && !allEx st xP) ||
       2 * (lD st * pin ^ kP) < lN st * gs pin kP))

/-- `m` has a prime factor not dividing `M` (sound test). -/
def hasOut (M m : ℕ) : Bool := cofree M 200 m != 1 && Nat.gcd (cofree M 200 m) M == 1

/-- The exact exponent `k` of `p` survives the forcing rules. -/
def okEx (M : ℕ) (st : List Ent) (g lo pin p k : ℕ) : Bool :=
  st.all (fun e => e.2.1 != 1 || gs p k % e.1 != 0) &&
    (if pin != 0 then !hasOut (M * pin) (gs p k) && !(p == pin && hasOut M (gs p k))
     else !hasOut M (gs p k) ||
       (lo ≤ cofree M 200 (gs p k) && (g == 0 || lo ≤ Nat.gcd g (cofree M 200 (gs p k)))))

/-- The least exponent from `k` on that survives the forcing rules (at most `40` steps). -/
def adv (M : ℕ) (st : List Ent) (g lo pin p : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | n + 1, k => if okEx M st g lo pin p k then k else adv M st g lo pin p n (nextValid p k)

/-- Mark the undecided primes dividing `s` as dividing. -/
def force (st : List Ent) (s : ℕ) : List Ent :=
  st.map fun e => if e.2.1 == 0 && s % e.1 == 0 then (e.1, 2, nextValid e.1 0) else e

/-- Set the entry of `p`. -/
def setE (st : List Ent) (p c k : ℕ) : List Ent :=
  st.map fun e => if e.1 == p then (p, c, k) else e

/-- The update of `g` from an exact entry. -/
def gUp (M g pin s : ℕ) : ℕ := if pin == 0 && hasOut M s then Nat.gcd g (cofree M 200 s) else g

/-- The gap `p / (p - 1)` over `σ (p ^ k) / p ^ k` exceeds `1 + 1 / 33`. -/
def gapBig (p k : ℕ) : Bool := p * p ^ k * 33 > (p - 1) * gs p k * 34

/-- `(p, k)` has a larger gap than `(q, l)`. -/
def gapGt (p k q l : ℕ) : Bool := p * p ^ k * ((q - 1) * gs q l) > q * q ^ l * ((p - 1) * gs p k)

/-- The small inexact entry of largest gap. -/
def pickBest : List Ent → Option (ℕ × ℕ)
  | [] => none
  | e :: l =>
    match pickBest l with
    | none => if e.2.1 == 2 then some (e.1, e.2.2) else none
    | some y => if e.2.1 == 2 && gapGt e.1 e.2.2 y.1 y.2 then some (e.1, e.2.2) else some y

/-- Some inexact entry still has a large gap. -/
def anyBig (st : List Ent) (pin kP : ℕ) (xP : Bool) : Bool :=
  (match pickBest st with
   | none => false
   | some y => gapBig y.1 y.2) || (pin != 0 && !xP && gapBig pin kP)

/-- The undecided prime to split on next, if any. -/
def chooseU (st : List Ent) (pin kP : ℕ) (xP : Bool) : Option Ent :=
  if anyBig st pin kP xP then none else st.find? fun e => e.2.1 == 0

/-- Split the exponent of the large prime next. -/
def useP (st : List Ent) (pin kP : ℕ) (xP : Bool) : Bool :=
  pin != 0 && !xP &&
    (match pickBest st with
     | none => true
     | some y => gapGt pin kP y.1 y.2)

/-- A search state `(st, g, lo, hi, pin, kP, xP)`. -/
abbrev State := List Ent × ℕ × ℕ × ℕ × ℕ × ℕ × Bool

/-- The children of a state; `none` when the search is stuck. -/
def expand (B M W : ℕ) : State → Option (List State)
  | (st, g, lo, hi, pin, kP, xP) =>
    if closed st (newLo B st lo) (newHi st g hi) pin kP xP then some []
    else if pin == 0 && 0 < g && g < newLo B st lo * newLo B st lo then
      some [(st, g, g, g, g, nextValid g 0, false)]
    else if pin == 0 && newHi st g hi != 0 && newHi st g hi ≤ newLo B st lo + W then
      some ((List.range' (newLo B st lo) (newHi st g hi + 1 - newLo B st lo)).filterMap fun c =>
        if Nat.gcd c M == 1 && (g == 0 || g % c == 0) then some (st, g, c, c, c, nextValid c 0, false)
        else none)
    else
      match chooseU st pin kP xP with
      | some e =>
        some [(setE st e.1 2 (adv M st g (newLo B st lo) pin e.1 40 (nextValid e.1 0)),
            g, newLo B st lo, newHi st g hi, pin, kP, xP),
          (setE st e.1 1 0, g, newLo B st lo, newHi st g hi, pin, kP, xP)]
      | none =>
        if useP st pin kP xP then
          some ((if okEx M st g (newLo B st lo) pin pin kP then
              [(force st (gs pin kP), g, newLo B st lo, newHi st g hi, pin, kP, true)] else []) ++
            [(st, g, newLo B st lo, newHi st g hi, pin,
              adv M st g (newLo B st lo) pin pin 40 (nextValid pin kP), false)])
        else
          match pickBest st with
          | none => none
          | some y =>
            some ((if okEx M st g (newLo B st lo) pin y.1 y.2 then
                [(force (setE st y.1 3 y.2) (gs y.1 y.2), gUp M g pin (gs y.1 y.2),
                  newLo B st lo, newHi st g hi, pin, kP, xP)] else []) ++
              [(setE st y.1 2 (adv M st g (newLo B st lo) pin y.1 40 (nextValid y.1 y.2)),
                g, newLo B st lo, newHi st g hi, pin, kP, xP)])

/-- Run the search on a stack of states for at most `f` steps; returns the remaining stack,
or `none` when stuck. -/
def run (B M W : ℕ) : ℕ → List State → Option (List State)
  | 0, L => some L
  | _ + 1, [] => some []
  | f + 1, s :: L =>
    match expand B M W s with
    | none => none
    | some cs => run B M W f (cs ++ L)

/-! ## Basic facts -/

private theorem sigma_eq_gs' {p : ℕ} (hp : p.Prime) (e : ℕ) : σ 1 (p ^ e) = gs p e := by
  rw [sigma_one_apply_prime_pow hp, gs, Nat.geomSum_eq hp.two_le]

private theorem gs_pos {p : ℕ} (hp : p.Prime) (e : ℕ) : 0 < gs p e := by
  rw [← sigma_eq_gs' hp]; exact sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)

private theorem noDiv_sound' {n : ℕ} : ∀ {f d : ℕ}, noDiv n f d = true →
    ∀ k, d ≤ k → k < d + f → k * k ≤ n → ¬ k ∣ n
  | 0, d, _, k, h1, h2, _ => by omega
  | f + 1, d, h, k, h1, h2, h3 => by
    simp only [noDiv, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at h
    rcases h with h | ⟨hd, h⟩
    · have := Nat.mul_le_mul h1 h1; omega
    · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact fun hk => hd (Nat.mod_eq_zero_of_dvd hk)
      · exact noDiv_sound' h k hlt (by omega) h3

private theorem noDiv_complete' {n : ℕ} : ∀ {f d : ℕ}, 2 ≤ d →
    (∀ k, d ≤ k → k < n → ¬ k ∣ n) → noDiv n f d = true
  | 0, _, _, _ => rfl
  | f + 1, d, hd, h => by
    simp only [noDiv, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq]
    by_cases hlt : n < d * d
    · exact Or.inl hlt
    · right
      have hdn : d < n := by nlinarith
      exact ⟨fun h0 => h d le_rfl hdn (Nat.dvd_of_mod_eq_zero h0),
        noDiv_complete' (by omega) fun k hk => h k (by omega)⟩

private theorem isPrimeF_iff' {n : ℕ} : isPrimeF n = true ↔ n.Prime := by
  simp only [isPrimeF, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h2, h⟩
    rw [Nat.prime_def_minFac]
    refine ⟨h2, ?_⟩
    by_contra hne
    have hsq := Nat.minFac_sq_le_self (by omega) (fun hp => hne (Nat.Prime.minFac_eq hp))
    have h2m := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
    have hle : n.minFac ≤ n := Nat.minFac_le (by omega)
    exact noDiv_sound' h n.minFac h2m (by omega) (by rw [← pow_two]; exact hsq)
      (Nat.minFac_dvd n)
  · intro hp
    refine ⟨hp.two_le, noDiv_complete' le_rfl fun k hk hkn hd => ?_⟩
    have := (Nat.prime_def_lt.mp hp).2 k hkn hd
    omega

private theorem mem_primesUpTo' {B q : ℕ} : q ∈ primesUpTo B ↔ q ≤ B ∧ q ≠ 2 ∧ q.Prime := by
  simp only [primesUpTo, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    isPrimeF_iff']
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h2, h3⟩

private theorem nodup_primesUpTo' (B : ℕ) : (primesUpTo B).Nodup :=
  (List.nodup_range).filter _

private theorem cofree_dvd' (M : ℕ) : ∀ f m, cofree M f m ∣ m
  | 0, m => dvd_rfl
  | f + 1, m => by
    unfold cofree
    split_ifs
    · exact dvd_rfl
    · exact (cofree_dvd' M f _).trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m M))

/-- What `hasOut` certifies. -/
private theorem hasOut_spec {M m : ℕ} (h : hasOut M m = true) :
    cofree M 200 m ≠ 1 ∧ Nat.gcd (cofree M 200 m) M = 1 := by
  simpa [hasOut] using h

private theorem hasOut_sound {M m : ℕ} (h : hasOut M m = true) :
    ∃ r, r.Prime ∧ r ∣ m ∧ ¬ r ∣ M := by
  obtain ⟨h1, h2⟩ := hasOut_spec h
  set c := cofree M 200 m
  have hc : c ∣ m := cofree_dvd' M 200 m
  refine ⟨c.minFac, Nat.minFac_prime h1, (Nat.minFac_dvd c).trans hc, fun hq => ?_⟩
  have := Nat.dvd_gcd (Nat.minFac_dvd c) hq
  rw [h2] at this
  exact (Nat.minFac_prime h1).one_lt.ne' (Nat.dvd_one.mp this)

private theorem valid_fact {N : ℕ} (h : OddPerfect N) {p : ℕ} (hp : p.Prime) :
    valid p (N.factorization p) = true := by
  obtain ⟨q, -, -, hq4, hqe, hev⟩ := exists_special_prime h
  simp only [valid, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
  by_cases hpq : p = q
  · subst hpq; exact Or.inr ⟨hq4, hqe⟩
  · exact Or.inl (Nat.even_iff.mp (hev p hp hpq))

private theorem nextValid_le {p k f : ℕ} (hk : k < f) (hf : valid p f = true) :
    nextValid p k ≤ f := by
  unfold nextValid
  split_ifs with h
  · omega
  · rcases Nat.lt_or_ge (k + 1) f with h1 | h1
    · omega
    · have : f = k + 1 := by omega
      subst this; exact absurd hf h

private theorem pickBest_mem : ∀ {l : List Ent} {y : ℕ × ℕ}, pickBest l = some y →
    ∃ e ∈ l, e.2.1 = 2 ∧ y = (e.1, e.2.2)
  | [], _, h => by simp [pickBest] at h
  | a :: l, y, h => by
    unfold pickBest at h
    split at h
    · split_ifs at h with ha
      · cases h; exact ⟨a, by simp, by simpa using ha, rfl⟩
    · rename_i z hz
      split_ifs at h with ha
      · cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at ha
        exact ⟨a, by simp, ha.1, rfl⟩
      · cases h
        obtain ⟨e, he, h2, rfl⟩ := pickBest_mem hz
        exact ⟨e, List.mem_cons_of_mem _ he, h2, rfl⟩

private theorem foldr_max_le {l : List ℕ} {b : ℕ} (h : ∀ a ∈ l, a ≤ b) : l.foldr max 0 ≤ b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

private theorem mem_setE {st : List Ent} {p c k : ℕ} {e : Ent} (he : e ∈ setE st p c k) :
    e = (p, c, k) ∨ e ∈ st := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr ha

private theorem fst_setE (st : List Ent) (p c k : ℕ) :
    (setE st p c k).map Prod.fst = st.map Prod.fst := by
  simp only [setE, List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp]
  split_ifs with h
  · simp only [beq_iff_eq] at h; simp [h]
  · rfl

private theorem fst_force (st : List Ent) (s : ℕ) :
    (force st s).map Prod.fst = st.map Prod.fst := by
  simp only [force, List.map_map]
  apply List.map_congr_left
  intro a _
  simp only [Function.comp]
  split_ifs <;> rfl

/-! ## Products of rationals -/

private theorem prod_le_prod' {l : List Ent} {x y : Ent → ℚ} (h : ∀ q ∈ l, 0 ≤ x q ∧ x q ≤ y q) :
    (l.map x).prod ≤ (l.map y).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha := h a (by simp)
    have ih' := ih (fun q hq => h q (by simp [hq]))
    have h0 : 0 ≤ (l.map x).prod := List.prod_nonneg (by
      intro z hz; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz; exact (h q (by simp [hq])).1)
    exact mul_le_mul ha.2 ih' h0 (ha.1.trans ha.2)

private theorem prod_lt_prod' {l : List Ent} {x y : Ent → ℚ} (h : ∀ q ∈ l, 0 < x q ∧ x q ≤ y q)
    (hs : ∃ q ∈ l, x q < y q) : (l.map x).prod < (l.map y).prod := by
  induction l with
  | nil => simp at hs
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha := h a (by simp)
    have hle := prod_le_prod' (l := l) (x := x) (y := y)
      (fun q hq => ⟨(h q (by simp [hq])).1.le, (h q (by simp [hq])).2⟩)
    have h0 : 0 < (l.map x).prod := List.prod_pos (by
      intro z hz; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz; exact (h q (by simp [hq])).1)
    obtain ⟨q, hq, hlt⟩ := hs
    rcases List.mem_cons.mp hq with rfl | hq'
    · calc x q * (l.map x).prod < y q * (l.map x).prod := mul_lt_mul_of_pos_right hlt h0
        _ ≤ y q * (l.map y).prod := mul_le_mul_of_nonneg_left hle (ha.1.le.trans ha.2)
    · have := ih (fun q hq => h q (by simp [hq])) ⟨q, hq', hlt⟩
      calc x a * (l.map x).prod < x a * (l.map y).prod := mul_lt_mul_of_pos_left this ha.1
        _ ≤ y a * (l.map y).prod := mul_le_mul_of_nonneg_right ha.2 (h0.le.trans this.le)

private theorem cast_prod_div (l : List Ent) (f g : Ent → ℕ) :
    (((l.map f).prod : ℕ) : ℚ) / (((l.map g).prod : ℕ) : ℚ) =
      (l.map fun q => (f q : ℚ) / (g q : ℚ)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    rw [mul_div_mul_comm, ih]

private theorem prod_pos_nat {l : List Ent} {f : Ent → ℕ} (h : ∀ q ∈ l, 0 < f q) :
    0 < (l.map f).prod := by
  apply List.prod_pos
  intro z hz
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
  exact h q hq

/-! ## The factors at one prime -/

/-- The meaning of an entry. -/
def EntOK (N : ℕ) (e : Ent) : Prop :=
  (e.2.1 = 1 → ¬ e.1 ∣ N) ∧ (2 ≤ e.2.1 → e.1 ∣ N ∧ e.2.2 ≤ N.factorization e.1) ∧
    (e.2.1 = 3 → N.factorization e.1 = e.2.2)

private theorem abund_eq_gs {p : ℕ} (hp : p.Prime) (k : ℕ) :
    abundancy (p ^ k) = (gs p k : ℚ) / ((p ^ k : ℕ) : ℚ) := by
  rw [abundancy, sigma_eq_gs' hp]

private theorem one_le_abund {p : ℕ} (hp : p.Prime) (k : ℕ) : 1 ≤ abundancy (p ^ k) := by
  have := abundancy_le_of_dvd (pow_ne_zero k hp.ne_zero) (one_dvd (p ^ k))
  simpa [abundancy] using this

private theorem ld1_pos {e : Ent} (hq : e.1.Prime) : 0 < ld1 e := by
  unfold ld1; split_ifs
  · exact pow_pos hq.pos _
  · exact Nat.one_pos

private theorem ud1_pos {e : Ent} (hq : e.1.Prime) : 0 < ud1 e := by
  have := hq.two_le
  unfold ud1; split_ifs
  · exact pow_pos hq.pos _
  · exact Nat.one_pos
  · omega

private theorem ln1_pos {e : Ent} (hq : e.1.Prime) : 0 < ln1 e := by
  unfold ln1; split_ifs
  · exact gs_pos hq _
  · exact Nat.one_pos

private theorem low_le {N : ℕ} {e : Ent} (he : EntOK N e) (hq : e.1.Prime) :
    (ln1 e : ℚ) / (ld1 e : ℚ) ≤ abundancy (e.1 ^ N.factorization e.1) := by
  unfold ln1 ld1
  split_ifs with h
  · rw [← abund_eq_gs hq]
    exact abundancy_prime_pow_mono hq (he.2.1 h).2
  · simp only [Nat.cast_one, div_one]; exact one_le_abund hq _

private theorem fact_zero {N : ℕ} {e : Ent} (he : EntOK N e) (h1 : e.2.1 = 1) :
    N.factorization e.1 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (he.1 h1)

private theorem lt_up {N : ℕ} {e : Ent} (hq : e.1.Prime) (h1 : e.2.1 ≠ 1) (h3 : e.2.1 ≠ 3) :
    abundancy (e.1 ^ N.factorization e.1) < (un1 e : ℚ) / (ud1 e : ℚ) := by
  unfold un1 ud1
  simp only [h1, h3, if_false]
  rw [Nat.cast_sub hq.one_lt.le, Nat.cast_one]
  exact abundancy_prime_pow_lt hq _

private theorem le_up {N : ℕ} {e : Ent} (he : EntOK N e) (hq : e.1.Prime) :
    abundancy (e.1 ^ N.factorization e.1) ≤ (un1 e : ℚ) / (ud1 e : ℚ) := by
  by_cases h3 : e.2.1 = 3
  · unfold un1 ud1
    simp only [h3, if_true]
    rw [he.2.2 h3, abund_eq_gs hq]
  · by_cases h1 : e.2.1 = 1
    · unfold un1 ud1
      simp only [h1, if_true]
      rw [fact_zero he h1]; simp [abundancy]
    · exact (lt_up hq h1 h3).le

/-! ## The context -/

/-- The setting: `P0` is the only prime factor of `N` above `B`. -/
structure Ctx (N B P0 : ℕ) : Prop where
  /-- `N` is an odd perfect number. -/
  h : OddPerfect N
  /-- `P0` is prime. -/
  hp : P0.Prime
  /-- `P0` divides `N`. -/
  hdvd : P0 ∣ N
  /-- `P0` exceeds `B`. -/
  hB : B < P0
  /-- Every other prime factor of `N` is at most `B`. -/
  hrest : ∀ r ∈ N.primeFactors, r ≠ P0 → r ≤ B

/-- The meaning of the data on the large prime. -/
def PinOK (N P0 pin kP : ℕ) (xP : Bool) : Prop :=
  pin = 0 ∨ (pin = P0 ∧ kP ≤ N.factorization P0 ∧ (xP = true → N.factorization P0 = kP))

/-- The meaning of a search state. -/
def Holds (N B P0 : ℕ) (st : List Ent) (g lo hi pin kP : ℕ) (xP : Bool) : Prop :=
  st.map Prod.fst = primesUpTo B ∧ (∀ e ∈ st, EntOK N e) ∧
    (g = 0 ∨ (P0 ∣ g ∧ ∀ r, r.Prime → r ∣ g → r = P0)) ∧
    lo ≤ P0 ∧ (hi = 0 ∨ P0 ≤ hi) ∧ PinOK N P0 pin kP xP

variable {N B P0 : ℕ}

private theorem mem_st {st : List Ent} (hst : st.map Prod.fst = primesUpTo B) {e : Ent}
    (he : e ∈ st) : e.1 ≤ B ∧ e.1 ≠ 2 ∧ e.1.Prime := by
  rw [← mem_primesUpTo', ← hst]; exact List.mem_map_of_mem he

private theorem eq_P0 (c : Ctx N B P0) {r : ℕ} (hr : r.Prime) (hrN : r ∣ N)
    (hrM : ¬ r ∣ 2 * (primesUpTo B).prod) : r = P0 := by
  by_contra hne
  have hle := c.hrest r (Nat.mem_primeFactors.mpr ⟨hr, hrN, c.h.ne_zero⟩) hne
  have hr2 : r ≠ 2 := by rintro rfl; exact c.h.not_two_dvd hrN
  exact hrM (Dvd.dvd.mul_left (List.dvd_prod (mem_primesUpTo'.mpr ⟨hle, hr2, hr⟩)) 2)

private theorem P0_not_dvd_M (c : Ctx N B P0) : ¬ P0 ∣ 2 * (primesUpTo B).prod := by
  intro hd
  rcases (Nat.Prime.dvd_mul c.hp).mp hd with h2 | hpr
  · have := (Nat.prime_dvd_prime_iff_eq c.hp Nat.prime_two).mp h2
    subst this; exact c.h.not_two_dvd c.hdvd
  · obtain ⟨a, ha, hda⟩ := (Prime.dvd_prod_iff c.hp.prime).mp hpr
    obtain ⟨hle, -, hap⟩ := mem_primesUpTo'.mp ha
    have := (Nat.prime_dvd_prime_iff_eq c.hp hap).mp hda
    have := c.hB; omega

/-- A prime factor of an exact component divisor sum not dividing `M` is `P0`. -/
private theorem out_eq_P0 (c : Ctx N B P0) {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hd : r ∣ gs p (N.factorization p)) (hrM : ¬ r ∣ 2 * (primesUpTo B).prod) : r = P0 := by
  have hr2 : r ≠ 2 := by rintro rfl; exact hrM (dvd_mul_right 2 _)
  exact eq_P0 c hr (OPNStarter.force_prime c.h.perfect hp rfl hr hr2 (by rwa [sigma_eq_gs' hp]))
    hrM

/-! ## The abundancy identity -/

private theorem decomp (c : Ctx N B P0) {st : List Ent} (hst : st.map Prod.fst = primesUpTo B) :
    (st.map fun e => abundancy (e.1 ^ N.factorization e.1)).prod *
      abundancy (P0 ^ N.factorization P0) = 2 := by
  have hab := (perfect_iff_abundancy_eq_two c.h.pos).mp c.h.perfect
  rw [abundancy_eq_prod_primeFactors c.h.ne_zero] at hab
  set L := primesUpTo B with hL
  have hnodup : L.Nodup := nodup_primesUpTo' B
  have hP0L : P0 ∉ L := fun hm => by
    have := (mem_primesUpTo'.mp hm).1
    have := c.hB; omega
  have hsub : N.primeFactors ⊆ insert P0 L.toFinset := by
    intro q hq
    rw [Finset.mem_insert, List.mem_toFinset]
    by_cases hqP : q = P0
    · exact Or.inl hqP
    · right
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqN := Nat.dvd_of_mem_primeFactors hq
      have hq2 : q ≠ 2 := by rintro rfl; exact c.h.not_two_dvd hqN
      exact mem_primesUpTo'.mpr ⟨c.hrest q hq hqP, hq2, hqp⟩
  have h1 : ∏ p ∈ N.primeFactors, abundancy (p ^ N.factorization p) =
      ∏ p ∈ insert P0 L.toFinset, abundancy (p ^ N.factorization p) := by
    apply Finset.prod_subset hsub
    intro q _ hq
    have : N.factorization q = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hq
    rw [this]; simp [abundancy]
  rw [h1, Finset.prod_insert (by simpa using hP0L), List.prod_toFinset _ hnodup] at hab
  have e : (st.map fun e => abundancy (e.1 ^ N.factorization e.1)) =
      L.map fun q => abundancy (q ^ N.factorization q) := by
    rw [← hst, List.map_map]; rfl
  rw [e, mul_comm]; exact hab

/-- The bounds on the two parts of the abundancy. -/
private theorem facts (c : Ctx N B P0) {st : List Ent} (hst : st.map Prod.fst = primesUpTo B)
    (hok : ∀ e ∈ st, EntOK N e) :
    (st.map fun e => abundancy (e.1 ^ N.factorization e.1)).prod *
      abundancy (P0 ^ N.factorization P0) = 2 ∧
    (lN st : ℚ) / (lD st : ℚ) ≤ (st.map fun e => abundancy (e.1 ^ N.factorization e.1)).prod ∧
    (st.map fun e => abundancy (e.1 ^ N.factorization e.1)).prod ≤ (uN st : ℚ) / (uD st : ℚ) ∧
    1 + (P0 : ℚ)⁻¹ ≤ abundancy (P0 ^ N.factorization P0) ∧
    abundancy (P0 ^ N.factorization P0) < (P0 : ℚ) / ((P0 : ℚ) - 1) ∧
    0 < lD st ∧ 0 < uD st ∧ 0 < lN st := by
  have hLp : ∀ e ∈ st, e.1.Prime := fun e he => (mem_st hst he).2.2
  refine ⟨decomp c hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lN, lD, cast_prod_div]
    exact prod_le_prod' fun e he => ⟨by positivity, low_le (hok e he) (hLp e he)⟩
  · rw [uN, uD, cast_prod_div]
    exact prod_le_prod' fun e he => ⟨by unfold abundancy; positivity, le_up (hok e he) (hLp e he)⟩
  · exact one_add_inv_le_abundancy_prime_pow c.hp
      ((c.hp.dvd_iff_one_le_factorization c.h.ne_zero).mp c.hdvd)
  · exact abundancy_prime_pow_lt c.hp _
  · exact prod_pos_nat fun e he => ld1_pos (hLp e he)
  · exact prod_pos_nat fun e he => ud1_pos (hLp e he)
  · exact prod_pos_nat fun e he => ln1_pos (hLp e he)

/-- The two integer inequalities behind the closing rules. -/
private theorem ints (c : Ctx N B P0) {st : List Ent} (hst : st.map Prod.fst = primesUpTo B)
    (hok : ∀ e ∈ st, EntOK N e) :
    2 * (P0 - 1) * uD st < uN st * P0 ∧ lN st * (P0 + 1) ≤ 2 * P0 * lD st := by
  obtain ⟨h2, hlw, hup, hp1, hp2, hld, hud, -⟩ := facts c hst hok
  set As := (st.map fun e => abundancy (e.1 ^ N.factorization e.1)).prod
  set Ap := abundancy (P0 ^ N.factorization P0)
  have hP2 : (2 : ℚ) ≤ P0 := by exact_mod_cast c.hp.two_le
  have hudq : (0 : ℚ) < uD st := by exact_mod_cast hud
  have hldq : (0 : ℚ) < lD st := by exact_mod_cast hld
  have hP1 : (0 : ℚ) < (P0 : ℚ) - 1 := by linarith
  have hAp0 : 0 < Ap := by
    have : (0 : ℚ) < (P0 : ℚ)⁻¹ := by positivity
    linarith
  have hAs0 : 0 ≤ As := by
    by_contra hneg; push Not at hneg; nlinarith
  constructor
  · have hU0 : (0 : ℚ) < (uN st : ℚ) / uD st := by
      by_contra hneg; push Not at hneg; nlinarith
    have h3 : (2 : ℚ) < (uN st : ℚ) / uD st * ((P0 : ℚ) / ((P0 : ℚ) - 1)) := by
      calc (2 : ℚ) = As * Ap := h2.symm
        _ ≤ (uN st : ℚ) / uD st * Ap := mul_le_mul_of_nonneg_right hup hAp0.le
        _ < _ := mul_lt_mul_of_pos_left hp2 hU0
    rw [div_mul_div_comm, lt_div_iff₀ (by positivity)] at h3
    have h4 : ((2 * (P0 - 1) * uD st : ℕ) : ℚ) < ((uN st * P0 : ℕ) : ℚ) := by
      push_cast [Nat.cast_sub c.hp.one_lt.le]; linarith
    exact_mod_cast h4
  · have h3 : (lN st : ℚ) / lD st * (1 + (P0 : ℚ)⁻¹) ≤ 2 := by
      calc (lN st : ℚ) / lD st * (1 + (P0 : ℚ)⁻¹) ≤ As * Ap :=
            mul_le_mul hlw hp1 (by positivity) hAs0
        _ = 2 := h2
    have hP0 : (0 : ℚ) < P0 := by linarith
    have h4 : (lN st : ℚ) * (P0 + 1) ≤ 2 * P0 * lD st := by
      have e : (lN st : ℚ) / lD st * (1 + (P0 : ℚ)⁻¹) = (lN st : ℚ) * (P0 + 1) /
          (P0 * lD st) := by field_simp
      rw [e, div_le_iff₀ (by positivity)] at h3
      linarith
    exact_mod_cast h4

/-! ## The refined bounds -/

private theorem loEnt_le (c : Ctx N B P0) {st : List Ent} (hok : ∀ e ∈ st, EntOK N e)
    (hLp : ∀ e ∈ st, e.1.Prime) : ∀ e ∈ st, loEnt B e ≤ P0 := by
  intro e he
  unfold loEnt
  split_ifs with hb
  · obtain ⟨hpN, hk⟩ := (hok e he).2.1 hb.1
    have hpm : e.1 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hLp e he, hpN, c.h.ne_zero⟩
    obtain ⟨r, hr, hle⟩ := exists_primeFactor_two_mul_factorization_add_three_le c.h hpm
    by_cases hrP : r = P0
    · subst hrP; omega
    · have := c.hrest r hr hrP; omega
  · exact Nat.zero_le _

private theorem minz_ok {hi x : ℕ} (hhi : hi = 0 ∨ P0 ≤ hi) (hx : P0 ≤ x) :
    minz hi x = 0 ∨ P0 ≤ minz hi x := by
  right
  unfold minz
  split_ifs with h
  · exact hx
  · rcases hhi with hhi | hhi
    · exact absurd hhi h
    · exact le_min hhi hx

/-- The refined bounds are valid. -/
private theorem refine_ok (c : Ctx N B P0) {st : List Ent} {g lo hi : ℕ}
    (hst : st.map Prod.fst = primesUpTo B) (hok : ∀ e ∈ st, EntOK N e)
    (hg : g = 0 ∨ (P0 ∣ g ∧ ∀ r, r.Prime → r ∣ g → r = P0)) (hlo : lo ≤ P0)
    (hhi : hi = 0 ∨ P0 ≤ hi) :
    newLo B st lo ≤ P0 ∧ (newHi st g hi = 0 ∨ P0 ≤ newHi st g hi) := by
  obtain ⟨I1, I2⟩ := ints c hst hok
  have hLp : ∀ e ∈ st, e.1.Prime := fun e he => (mem_st hst he).2.2
  have hfold : (st.map (loEnt B)).foldr max 0 ≤ P0 := foldr_max_le fun a ha => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact loEnt_le c hok hLp x hx
  have hlo1 : max lo ((st.map (loEnt B)).foldr max 0) ≤ P0 := max_le hlo hfold
  have hP1 := c.hp.one_lt
  constructor
  · unfold newLo
    split_ifs with h
    · refine max_le hlo1 ?_
      set d := 2 * lD st - lN st with hd
      have hd0 : 0 < d := by omega
      have hsum : lN st + d = 2 * lD st := by omega
      have key : lN st ≤ P0 * d := by
        have : lN st * (P0 + 1) ≤ P0 * (lN st + d) := by rw [hsum]; linarith
        nlinarith
      have : (lN st + d - 1) / d < P0 + 1 := by
        rw [Nat.div_lt_iff_lt_mul hd0]
        have : (P0 + 1) * d = P0 * d + d := by ring
        omega
      omega
    · exact hlo1
  · have hb1 : hiU st hi = 0 ∨ P0 ≤ hiU st hi := by
      unfold hiU
      split_ifs with h
      · refine minz_ok hhi ?_
        set d := 2 * uD st - uN st with hd
        have hd0 : 0 < d := by omega
        have hsum : uN st + d = 2 * uD st := by omega
        rw [Nat.le_div_iff_mul_le hd0]
        have h1 : 2 * (P0 - 1) * uD st + 2 * uD st = 2 * P0 * uD st := by
          have : P0 - 1 + 1 = P0 := by omega
          nlinarith
        have : P0 * d < 2 * uD st := by nlinarith
        omega
      · exact hhi
    unfold newHi
    split_ifs with hg0
    · rcases hg with hg | ⟨hPg, -⟩
      · omega
      · exact minz_ok hb1 (Nat.le_of_dvd hg0 hPg)
    · exact hb1

/-! ## The closing rules -/

private theorem parity_sound (c : Ctx N B P0) {st : List Ent} {pin kP : ℕ} {xP : Bool}
    (hok : ∀ e ∈ st, EntOK N e) (hLp : ∀ e ∈ st, e.1.Prime) (hpin : PinOK N P0 pin kP xP)
    (hb : parityBad st pin kP xP = true) : False := by
  -- every member of the list has an odd exponent
  have hodd : ∀ a ∈ ((st.filter fun e => e.2.1 == 3 && e.2.2 % 2 == 1).map Prod.fst ++
      (if pin != 0 && xP && kP % 2 == 1 then [pin] else [])),
      a.Prime ∧ Odd (N.factorization a) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      obtain ⟨he, hc⟩ := List.mem_filter.mp he
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      refine ⟨hLp e he, ?_⟩
      rw [(hok e he).2.2 hc.1]; exact Nat.odd_iff.mpr hc.2
    · split_ifs at ha with hc
      · simp only [List.mem_singleton] at ha
        subst ha
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
        rcases hpin with h0 | ⟨rfl, -, hx⟩
        · exact absurd h0 hc.1.1
        · exact ⟨c.hp, by rw [hx hc.1.2]; exact Nat.odd_iff.mpr hc.2⟩
      · simp at ha
  simp only [parityBad, List.any_eq_true, bne_iff_ne, ne_eq] at hb
  obtain ⟨a, ha, b, hb, hab⟩ := hb
  obtain ⟨q, -, hu⟩ := existsUnique_odd_exponent c.h
  exact hab ((hu a (hodd a ha)).trans (hu b (hodd b hb)).symm)

private theorem pin_sound (c : Ctx N B P0) {st : List Ent} {kP : ℕ} {xP : Bool}
    (hst : st.map Prod.fst = primesUpTo B) (hok : ∀ e ∈ st, EntOK N e)
    (hk : kP ≤ N.factorization P0) (hx : xP = true → N.factorization P0 = kP)
    (hb : (uN st * pun P0 kP xP < 2 * (uD st * pud P0 kP xP) ||
       (uN st * pun P0 kP xP == 2 * (uD st * pud P0 kP xP) && !allEx st xP) ||
       2 * (lD st * P0 ^ kP) < lN st * gs P0 kP) = true) : False := by
  obtain ⟨h2, hlw, hup, -, -, hld, hud, hln⟩ := facts c hst hok
  have hLp : ∀ e ∈ st, e.1.Prime := fun e he => (mem_st hst he).2.2
  set As := (st.map fun e => abundancy (e.1 ^ N.factorization e.1)).prod
  set Ap := abundancy (P0 ^ N.factorization P0)
  have hudq : (0 : ℚ) < uD st := by exact_mod_cast hud
  have hldq : (0 : ℚ) < lD st := by exact_mod_cast hld
  have hlnq : (0 : ℚ) < lN st := by exact_mod_cast hln
  have hP2 := c.hp.two_le
  have hpud : 0 < pud P0 kP xP := by
    unfold pud; split_ifs
    · exact pow_pos c.hp.pos _
    · omega
  have hpudq : (0 : ℚ) < pud P0 kP xP := by exact_mod_cast hpud
  have hpow : (0 : ℚ) < ((P0 ^ kP : ℕ) : ℚ) := by exact_mod_cast pow_pos c.hp.pos kP
  have hgsq : (0 : ℚ) < (gs P0 kP : ℚ) := by exact_mod_cast gs_pos c.hp kP
  -- the factor of `P0`
  have hApL : (gs P0 kP : ℚ) / ((P0 ^ kP : ℕ) : ℚ) ≤ Ap := by
    rw [← abund_eq_gs c.hp]; exact abundancy_prime_pow_mono c.hp hk
  have hApU : Ap ≤ (pun P0 kP xP : ℚ) / (pud P0 kP xP : ℚ) := by
    unfold pun pud
    change abundancy (P0 ^ N.factorization P0) ≤ _
    split_ifs with hxP
    · rw [hx hxP, abund_eq_gs c.hp]
    · rw [Nat.cast_sub c.hp.one_lt.le, Nat.cast_one]; exact (abundancy_prime_pow_lt c.hp _).le
  have hApS : xP = false → Ap < (pun P0 kP xP : ℚ) / (pud P0 kP xP : ℚ) := by
    intro hxP
    unfold pun pud
    simp only [hxP, Bool.false_eq_true, if_false]
    rw [Nat.cast_sub c.hp.one_lt.le, Nat.cast_one]; exact abundancy_prime_pow_lt c.hp _
  have hAp0 : 0 < Ap := lt_of_lt_of_le (by positivity) hApL
  have hAs0 : 0 < As := lt_of_lt_of_le (by positivity) hlw
  have hU : (2 : ℚ) ≤ (uN st : ℚ) / uD st * ((pun P0 kP xP : ℚ) / pud P0 kP xP) := by
    rw [← h2]; exact mul_le_mul hup hApU hAp0.le (hAs0.le.trans hup)
  have hLo : (lN st : ℚ) / lD st * ((gs P0 kP : ℚ) / ((P0 ^ kP : ℕ) : ℚ)) ≤ 2 := by
    rw [← h2]; exact mul_le_mul hlw hApL (by positivity) hAs0.le
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hb
  rcases hb with (hb | hb) | hb
  · rw [div_mul_div_comm, le_div_iff₀ (by positivity)] at hU
    have : ((2 * (uD st * pud P0 kP xP) : ℕ) : ℚ) ≤ ((uN st * pun P0 kP xP : ℕ) : ℚ) := by
      push_cast; linarith
    have := (Nat.cast_le (α := ℚ)).mp this
    omega
  · obtain ⟨heq, hne⟩ := hb
    have hstrict : (2 : ℚ) < (uN st : ℚ) / uD st * ((pun P0 kP xP : ℚ) / pud P0 kP xP) := by
      rw [← h2]
      by_cases hxP : xP = true
      · rw [hxP] at hne
        simp only [allEx, Bool.true_and, List.all_eq_false] at hne
        obtain ⟨e, he, hne'⟩ := hne
        have h1 : e.2.1 ≠ 1 := fun h => hne' (by simp [h])
        have h3 : e.2.1 ≠ 3 := fun h => hne' (by simp [h])
        have hlt : As < (uN st : ℚ) / uD st := by
          rw [uN, uD, cast_prod_div]
          apply prod_lt_prod'
          · intro q hq
            exact ⟨by unfold abundancy; have := (hLp q hq).pos; positivity,
              le_up (hok q hq) (hLp q hq)⟩
          · exact ⟨e, he, lt_up (hLp e he) h1 h3⟩
        calc As * Ap < (uN st : ℚ) / uD st * Ap := mul_lt_mul_of_pos_right hlt hAp0
          _ ≤ _ := mul_le_mul_of_nonneg_left hApU (hAs0.le.trans hlt.le)
      · exact mul_lt_mul' hup (hApS (by simpa using hxP)) hAp0.le (hAs0.trans_le hup)
    rw [div_mul_div_comm, lt_div_iff₀ (by positivity)] at hstrict
    have : ((2 * (uD st * pud P0 kP xP) : ℕ) : ℚ) < ((uN st * pun P0 kP xP : ℕ) : ℚ) := by
      push_cast; linarith
    have := (Nat.cast_lt (α := ℚ)).mp this
    omega
  · rw [div_mul_div_comm, div_le_iff₀ (by positivity)] at hLo
    have : ((lN st * gs P0 kP : ℕ) : ℚ) ≤ ((2 * (lD st * P0 ^ kP) : ℕ) : ℚ) := by
      push_cast at hLo ⊢; linarith
    have := (Nat.cast_le (α := ℚ)).mp this
    omega

private theorem closed_sound (c : Ctx N B P0) {st : List Ent} {lo hi pin kP : ℕ} {xP : Bool}
    (hst : st.map Prod.fst = primesUpTo B) (hok : ∀ e ∈ st, EntOK N e)
    (hlo : lo ≤ P0) (hhi : hi = 0 ∨ P0 ≤ hi) (hpin : PinOK N P0 pin kP xP)
    (hc : closed st lo hi pin kP xP = true) : False := by
  obtain ⟨I1, I2⟩ := ints c hst hok
  obtain ⟨-, -, -, -, -, hld, hud, -⟩ := facts c hst hok
  have hLp : ∀ e ∈ st, e.1.Prime := fun e he => (mem_st hst he).2.2
  have hP1 := c.hp.one_lt
  unfold closed at hc
  simp only [Bool.or_eq_true] at hc
  rcases hc with (((hc | hc) | hc) | hc) | hc
  · exact parity_sound c hok hLp hpin hc
  · simp only [decide_eq_true_eq] at hc
    nlinarith
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
    rcases hhi with hhi | hhi
    · exact hc.1 hhi
    · omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hl0, hc⟩ := hc
    have hu : uN st < 2 * uD st := by
      by_contra hge; push Not at hge
      have : 2 * (lo - 1) * uD st < 2 * uD st * lo := by
        have : lo - 1 < lo := by omega
        nlinarith
      nlinarith
    obtain ⟨a, rfl⟩ : ∃ a, lo = a + 1 := ⟨lo - 1, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, P0 = b + 1 := ⟨P0 - 1, by omega⟩
    rw [hb] at I1 hlo
    simp only [Nat.add_sub_cancel] at hc I1
    have hab : a ≤ b := by omega
    nlinarith
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    rcases hpin with hpin | ⟨rfl, hk, hx⟩
    · exact hc.1 hpin
    · exact pin_sound c hst hok hk hx hc.2

/-! ## Branch lemmas -/

private theorem gpin_eq {g lo : ℕ} (hg0 : 0 < g)
    (hg : g = 0 ∨ (P0 ∣ g ∧ ∀ r, r.Prime → r ∣ g → r = P0)) (hlo : lo ≤ P0)
    (hlt : g < lo * lo) : g = P0 := by
  rcases hg with hg | ⟨⟨m, rfl⟩, hall⟩
  · omega
  · have hm0 : m ≠ 0 := by rintro rfl; simp at hg0
    by_cases hm1 : m = 1
    · subst hm1; ring
    · have hmp := Nat.minFac_prime hm1
      have := hall _ hmp ((Nat.minFac_dvd m).trans (dvd_mul_left m P0))
      have hPm : P0 ≤ m := this ▸ Nat.minFac_le (Nat.pos_of_ne_zero hm0)
      have : lo * lo ≤ P0 * m := Nat.mul_le_mul hlo (hlo.trans hPm)
      omega

/-- The part of an exact component divisor sum coprime to `M` is a power of `P0`. -/
private theorem cofree_ok (c : Ctx N B P0) {p : ℕ} (hp : p.Prime)
    (h : hasOut (2 * (primesUpTo B).prod) (gs p (N.factorization p)) = true) :
    P0 ∣ cofree (2 * (primesUpTo B).prod) 200 (gs p (N.factorization p)) ∧
      0 < cofree (2 * (primesUpTo B).prod) 200 (gs p (N.factorization p)) ∧
      ∀ r, r.Prime → r ∣ cofree (2 * (primesUpTo B).prod) 200 (gs p (N.factorization p)) →
        r = P0 := by
  set M := 2 * (primesUpTo B).prod
  set s := gs p (N.factorization p)
  obtain ⟨h1, h2⟩ := hasOut_spec h
  set cf := cofree M 200 s
  have hcs : cf ∣ s := cofree_dvd' M 200 s
  have hs0 : s ≠ 0 := (gs_pos hp _).ne'
  have hcf0 : cf ≠ 0 := by rintro h0; rw [h0, zero_dvd_iff] at hcs; exact hs0 hcs
  have hall : ∀ r, r.Prime → r ∣ cf → r = P0 := by
    intro r hr hrc
    refine out_eq_P0 c hp hr (hrc.trans hcs) fun hrM => ?_
    have := Nat.dvd_gcd hrc hrM
    rw [h2] at this
    exact hr.one_lt.ne' (Nat.dvd_one.mp this)
  have hPc : P0 ∣ cf := by
    have := hall _ (Nat.minFac_prime h1) (Nat.minFac_dvd cf)
    rw [← this]; exact Nat.minFac_dvd cf
  exact ⟨hPc, Nat.pos_of_ne_zero hcf0, hall⟩

private theorem gUp_ok (c : Ctx N B P0) {g pin p : ℕ} (hp : p.Prime)
    (hg : g = 0 ∨ (P0 ∣ g ∧ ∀ r, r.Prime → r ∣ g → r = P0)) :
    gUp (2 * (primesUpTo B).prod) g pin (gs p (N.factorization p)) = 0 ∨
      (P0 ∣ gUp (2 * (primesUpTo B).prod) g pin (gs p (N.factorization p)) ∧
        ∀ r, r.Prime → r ∣ gUp (2 * (primesUpTo B).prod) g pin (gs p (N.factorization p)) →
          r = P0) := by
  unfold gUp
  split_ifs with hcond
  · simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨hPc, -, hall⟩ := cofree_ok c hp hcond.2
    right
    rcases hg with rfl | ⟨hPg, hgall⟩
    · rw [Nat.gcd_zero_left]; exact ⟨hPc, hall⟩
    · exact ⟨Nat.dvd_gcd hPg hPc, fun r hr hrd => hgall r hr (hrd.trans (Nat.gcd_dvd_left _ _))⟩
  · exact hg

/-- The forcing rules pass at the true exponent. -/
private theorem okEx_true (c : Ctx N B P0) {st : List Ent} {g lo pin kP : ℕ} {xP : Bool}
    (hok : ∀ e ∈ st, EntOK N e) (hLp : ∀ e ∈ st, e.1.Prime ∧ e.1 ≠ 2)
    (hg : g = 0 ∨ (P0 ∣ g ∧ ∀ r, r.Prime → r ∣ g → r = P0)) (hlo : lo ≤ P0)
    (hpin : PinOK N P0 pin kP xP) {p : ℕ} (hp : p.Prime) :
    okEx (2 * (primesUpTo B).prod) st g lo pin p (N.factorization p) = true := by
  set M := 2 * (primesUpTo B).prod
  set s := gs p (N.factorization p)
  have hs0 : s ≠ 0 := (gs_pos hp _).ne'
  unfold okEx
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro e he
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq]
    by_cases h1 : e.2.1 = 1
    · right
      intro h0
      exact (hok e he).1 h1 (OPNStarter.force_prime c.h.perfect hp rfl (hLp e he).1
        (hLp e he).2 (by rw [sigma_eq_gs' hp]; exact Nat.dvd_of_mod_eq_zero h0))
    · left; exact h1
  · split_ifs with hp0
    · simp only [bne_iff_ne, ne_eq] at hp0
      rcases hpin with h0 | ⟨rfl, -, -⟩
      · exact absurd h0 hp0
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      constructor
      · cases hh : hasOut (M * pin) s
        · rfl
        · obtain ⟨r, hr, hrs, hrM⟩ := hasOut_sound hh
          have hrM' : ¬ r ∣ M := fun hd => hrM (hd.mul_right _)
          have := out_eq_P0 c hp hr hrs hrM'
          subst this; exact absurd (dvd_mul_left _ _) hrM
      · cases hh : (p == pin && hasOut M s)
        · rfl
        · simp only [Bool.and_eq_true, beq_iff_eq] at hh
          obtain ⟨hxP, hh⟩ := hh
          obtain ⟨r', hr, hrs, hrM⟩ := hasOut_sound hh
          have hr'P := out_eq_P0 c hp hr hrs hrM
          have hcop := coprime_sigma_prime_pow hp (N.factorization p)
          rw [sigma_eq_gs' hp] at hcop
          have hrp : r' ∣ p := by rw [hr'P, hxP]
          exact (hr.one_lt.ne' ((Nat.coprime_self _).mp
            ((Nat.Coprime.coprime_dvd_left hrs hcop).coprime_dvd_right hrp))).elim
    · simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq]
      cases hh : hasOut M s
      · left; rfl
      · right
        obtain ⟨hPc, hc0, -⟩ := cofree_ok c hp hh
        have hPle : P0 ≤ cofree M 200 s := Nat.le_of_dvd hc0 hPc
        refine ⟨hlo.trans hPle, ?_⟩
        rcases hg with hg | ⟨hPg, -⟩
        · left; exact hg
        · right
          by_cases hg0 : g = 0
          · subst hg0; rw [Nat.gcd_zero_left]; exact hlo.trans hPle
          · exact hlo.trans (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hg0))
              (Nat.dvd_gcd hPg hPc))

/-- The advanced exponent is still a lower bound. -/
private theorem adv_le {M : ℕ} {st : List Ent} {g lo pin p f : ℕ}
    (hf : valid p f = true) (hok : okEx M st g lo pin p f = true) :
    ∀ (n k : ℕ), k ≤ f → adv M st g lo pin p n k ≤ f
  | 0, k, hk => hk
  | n + 1, k, hk => by
    unfold adv
    split_ifs with h
    · exact hk
    · have hkf : k ≠ f := by rintro rfl; exact h hok
      exact adv_le hf hok n _ (nextValid_le (by omega) hf)

private theorem force_ok (c : Ctx N B P0) {st : List Ent} (hok : ∀ e ∈ st, EntOK N e)
    (hLp : ∀ e ∈ st, e.1.Prime ∧ e.1 ≠ 2) {p : ℕ} (hp : p.Prime) :
    ∀ e ∈ force st (gs p (N.factorization p)), EntOK N e := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  split_ifs with h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    have haN : a.1 ∣ N := OPNStarter.force_prime c.h.perfect hp rfl (hLp a ha).1 (hLp a ha).2
      (by rw [sigma_eq_gs' hp]; exact Nat.dvd_of_mod_eq_zero (by simpa using h.2))
    refine ⟨fun h1 => by simp at h1, fun _ => ⟨haN, ?_⟩, fun h3 => by simp at h3⟩
    exact nextValid_le ((hLp a ha).1.dvd_iff_one_le_factorization c.h.ne_zero |>.mp haN)
      (valid_fact c.h (hLp a ha).1)
  · exact hok a ha

/-! ## Soundness -/

/-- The meaning of a search state. -/
def HoldsS (N B P0 : ℕ) (s : State) : Prop :=
  Holds N B P0 s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2.1 s.2.2.2.2.2.2

/-- Soundness of one step: if no child holds, the state does not hold. -/
theorem expand_sound (c : Ctx N B P0) {W : ℕ} {st : List Ent} {g lo hi pin kP : ℕ} {xP : Bool}
    {cs : List State} (he : expand B (2 * (primesUpTo B).prod) W (st, g, lo, hi, pin, kP, xP) =
      some cs)
    (hcs : ∀ t ∈ cs, ¬ HoldsS N B P0 t) (H : Holds N B P0 st g lo hi pin kP xP) : False := by
  obtain ⟨hst, hok, hg, hlo, hhi, hpin⟩ := H
  have hR := refine_ok c hst hok hg hlo hhi
  have hLp : ∀ e ∈ st, e.1.Prime ∧ e.1 ≠ 2 := fun e he =>
    ⟨(mem_st hst he).2.2, (mem_st hst he).2.1⟩
  simp only [expand] at he
  set lo2 := newLo B st lo with hlo2
  set hi2 := newHi st g hi with hhi2
  have hP0pin : PinOK N P0 P0 (nextValid P0 0) false :=
    Or.inr ⟨rfl, nextValid_le ((c.hp.dvd_iff_one_le_factorization c.h.ne_zero).mp c.hdvd)
      (valid_fact c.h c.hp), fun h => by simp at h⟩
  by_cases hcl : closed st lo2 hi2 pin kP xP = true
  · exact closed_sound c hst hok hR.1 hR.2 hpin hcl
  rw [if_neg hcl] at he
  by_cases h1 : (pin == 0 && decide (0 < g) && decide (g < lo2 * lo2)) = true
  · -- the large prime is `g`
    rw [if_pos h1, Option.some_inj] at he
    subst he
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    have hgP := gpin_eq h1.1.2 hg hR.1 h1.2
    subst hgP
    exact hcs _ (List.mem_singleton_self _) ⟨hst, hok, hg, le_rfl, Or.inr le_rfl, hP0pin⟩
  rw [if_neg h1] at he
  by_cases h2 : (pin == 0 && hi2 != 0 && decide (hi2 ≤ lo2 + W)) = true
  · -- the window for the large prime is short
    rw [if_pos h2, Option.some_inj] at he
    subst he
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h2
    have hP : P0 ≤ hi2 := hR.2.resolve_left h2.1.2
    have hmem : P0 ∈ List.range' lo2 (hi2 + 1 - lo2) := by
      rw [List.mem_range'_1]; have := hR.1; omega
    have hcond : (Nat.gcd P0 (2 * (primesUpTo B).prod) == 1 && (g == 0 || g % P0 == 0)) =
        true := by
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
      refine ⟨(c.hp.coprime_iff_not_dvd).mpr (P0_not_dvd_M c), ?_⟩
      rcases hg with hg | ⟨hPg, -⟩
      · exact Or.inl hg
      · exact Or.inr (Nat.mod_eq_zero_of_dvd hPg)
    refine hcs (st, g, P0, P0, P0, nextValid P0 0, false) (List.mem_filterMap.mpr ⟨P0, hmem, ?_⟩)
      ⟨hst, hok, hg, le_rfl, Or.inr le_rfl, hP0pin⟩
    rw [if_pos hcond]
  rw [if_neg h2] at he
  rcases hcu : chooseU st pin kP xP with _ | e
  rotate_left
  · -- split on an undecided prime
    rw [hcu, Option.some_inj] at he
    subst he
    have hem : e ∈ st ∧ e.2.1 = 0 := by
      unfold chooseU at hcu
      split_ifs at hcu
      exact ⟨List.mem_of_find?_eq_some hcu, by simpa using List.find?_some hcu⟩
    obtain ⟨hep, he2⟩ := hLp e hem.1
    by_cases heN : e.1 ∣ N
    · refine hcs _ (List.mem_cons_self ..) ⟨by rw [fst_setE]; exact hst, ?_, hg, hR.1, hR.2,
        hpin⟩
      intro x hx
      rcases mem_setE hx with rfl | hx
      · refine ⟨fun h => by simp at h, fun _ => ⟨heN, ?_⟩, fun h => by simp at h⟩
        exact adv_le (valid_fact c.h hep)
          (okEx_true c hok hLp hg hR.1 hpin hep) 40 _
          (nextValid_le ((hep.dvd_iff_one_le_factorization c.h.ne_zero).mp heN)
            (valid_fact c.h hep))
      · exact hok x hx
    · refine hcs _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
        ⟨by rw [fst_setE]; exact hst, ?_, hg, hR.1, hR.2, hpin⟩
      intro x hx
      rcases mem_setE hx with rfl | hx
      · exact ⟨fun _ => heN, fun h => by simp at h, fun h => by simp at h⟩
      · exact hok x hx
  rw [hcu] at he
  dsimp only at he
  by_cases hu : useP st pin kP xP = true
  · -- split the exponent of the large prime
    rw [if_pos hu, Option.some_inj] at he
    subst he
    simp only [useP, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hu
    obtain ⟨⟨hpin0, hxP⟩, -⟩ := hu
    rcases hpin with h0 | ⟨rfl, hk, -⟩
    · exact absurd h0 hpin0
    by_cases hke : N.factorization pin = kP
    · have hokP := okEx_true (xP := true) c hok hLp hg hR.1 (Or.inr ⟨rfl, hk, fun _ => hke⟩) c.hp
      rw [hke] at hokP
      refine hcs (force st (gs pin kP), g, lo2, hi2, pin, kP, true) (List.mem_append_left _ ?_)
        ⟨by rw [fst_force]; exact hst, ?_, hg, hR.1, hR.2, Or.inr ⟨rfl, hk, fun _ => hke⟩⟩
      · rw [if_pos hokP]; exact List.mem_singleton_self _
      · rw [← hke]; exact force_ok c hok hLp c.hp
    · refine hcs _ (List.mem_append_right _ (List.mem_singleton_self _))
        ⟨hst, hok, hg, hR.1, hR.2, Or.inr ⟨rfl, ?_, fun h => by simp at h⟩⟩
      exact adv_le (valid_fact c.h c.hp) (okEx_true (xP := false) c hok hLp hg hR.1
        (Or.inr ⟨rfl, hk, fun h => absurd h (by decide)⟩) c.hp) 40 _
        (nextValid_le (by omega) (valid_fact c.h c.hp))
  rw [if_neg hu] at he
  rcases hpb : pickBest st with _ | y
  · rw [hpb] at he; simp at he
  rw [hpb, Option.some_inj] at he
  subst he
  -- split the exponent of a small prime
  obtain ⟨e, hem, he2, rfl⟩ := pickBest_mem hpb
  obtain ⟨hep, -⟩ := hLp e hem
  obtain ⟨heN, hk⟩ := (hok e hem).2.1 (by omega)
  by_cases hke : N.factorization e.1 = e.2.2
  · have hokE := okEx_true c hok hLp hg hR.1 hpin hep
    rw [hke] at hokE
    have hok' : ∀ x ∈ setE st e.1 3 e.2.2, EntOK N x := by
      intro x hx
      rcases mem_setE hx with rfl | hx
      · exact ⟨fun h => by simp at h, fun _ => ⟨heN, hke.ge⟩, fun _ => hke⟩
      · exact hok x hx
    have hLp' : ∀ x ∈ setE st e.1 3 e.2.2, x.1.Prime ∧ x.1 ≠ 2 := by
      intro x hx
      rcases mem_setE hx with rfl | hx
      · exact hLp e hem
      · exact hLp x hx
    have hfo := force_ok c hok' hLp' hep
    have hgu := gUp_ok c hep hg (pin := pin)
    rw [hke] at hfo hgu
    refine hcs (force (setE st e.1 3 e.2.2) (gs e.1 e.2.2),
        gUp (2 * (primesUpTo B).prod) g pin (gs e.1 e.2.2), lo2, hi2, pin, kP, xP)
      (List.mem_append_left _ ?_) ⟨by rw [fst_force, fst_setE]; exact hst, hfo, hgu, hR.1,
        hR.2, hpin⟩
    rw [if_pos hokE]; exact List.mem_singleton_self _
  · refine hcs _ (List.mem_append_right _ (List.mem_singleton_self _))
      ⟨by rw [fst_setE]; exact hst, ?_, hg, hR.1, hR.2, hpin⟩
    intro x hx
    rcases mem_setE hx with rfl | hx
    · refine ⟨fun h => by simp at h, fun _ => ⟨heN, ?_⟩, fun h => by simp at h⟩
      exact adv_le (valid_fact c.h hep) (okEx_true c hok hLp hg hR.1 hpin hep) 40 _
        (nextValid_le (by omega) (valid_fact c.h hep))
    · exact hok x hx

/-- Soundness of a run: if no state left on the stack holds, no state on the initial stack
holds. -/
theorem run_sound (c : Ctx N B P0) {W : ℕ} : ∀ (f : ℕ) (L L' : List State),
    run B (2 * (primesUpTo B).prod) W f L = some L' → (∀ t ∈ L', ¬ HoldsS N B P0 t) →
      ∀ t ∈ L, ¬ HoldsS N B P0 t
  | 0, L, L', h, h', t, ht => by
    simp only [run, Option.some_inj] at h
    subst h; exact h' t ht
  | _ + 1, [], _, _, _, t, ht => by simp at ht
  | f + 1, s :: L, L', h, h', t, ht => by
    simp only [run] at h
    split at h
    · simp at h
    · rename_i cs hcs
      have hall := run_sound c f _ _ h h'
      have hs : ¬ HoldsS N B P0 s := by
        obtain ⟨st, g, lo, hi, pin, kP, xP⟩ := s
        exact fun H => expand_sound c hcs (fun u hu => hall u (List.mem_append_left _ hu)) H
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hs
      · exact hall t (List.mem_append_right _ ht)

/-- No state of `L` holds for an odd perfect number whose only prime factor above `B` is
`P0`. -/
def Cert (B : ℕ) (L : List State) : Prop :=
  ∀ N P0, Ctx N B P0 → ∀ t ∈ L, ¬ HoldsS N B P0 t

/-- The empty stack is certified. -/
theorem cert_nil (B : ℕ) : Cert B [] := fun _ _ _ _ ht => by simp at ht

/-- A checked run certifies its initial stack from its final stack. -/
theorem cert_step {B M W K : ℕ} {L L' : List State} (hM : 2 * (primesUpTo B).prod = M)
    (h : run B M W K L = some L') (h' : Cert B L') : Cert B L := by
  subst hM
  exact fun N P0 c => run_sound c K L L' h (h' N P0 c)

/-- A certified initial stack for `B` gives two distinct prime factors above `B`. The initial
entries `st` are given explicitly and checked. -/
theorem exists_two_of_cert {B : ℕ} {st : List Ent}
    (hst : (primesUpTo B).map (fun q => (q, 0, 0)) = st) (hB : B ≤ 3000)
    (hc : Cert B [(st, 0, 3001, 0, 0, 0, false)]) {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, ∃ r ∈ N.primeFactors, p ≠ r ∧ B < p ∧ B < r := by
  subst hst
  obtain ⟨P0, hP0, hgt⟩ := exists_primeFactor_gt h
  by_contra hne
  have c : Ctx N B P0 :=
    ⟨h, Nat.prime_of_mem_primeFactors hP0, Nat.dvd_of_mem_primeFactors hP0, by omega,
      fun r hr hrP => le_of_not_gt fun hlt => hne ⟨P0, hP0, r, hr, Ne.symm hrP, by omega, hlt⟩⟩
  refine hc N P0 c _ (List.mem_singleton_self _) ⟨by rw [List.map_map]; exact List.map_id _,
    ?_, Or.inl rfl, show 3001 ≤ P0 by omega, Or.inl rfl, Or.inl rfl⟩
  intro e he
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp he
  exact ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩

/-! ## The certificate for `B = 58`

The stacks below were produced by running `run` itself, 1000 steps at a time, from the initial
stack; the kernel checks every step. -/

/-- Decidable equality of search states. -/
private instance : DecidableEq State := fun a b => instDecidableEqProd a b

private def st58 : List Ent :=
  [(3, 0, 0), (5, 0, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)]

private theorem st58_eq : (primesUpTo 58).map (fun q => (q, 0, 0)) = st58 := by decide +kernel

private theorem M58_eq : 2 * (primesUpTo 58).prod = 32589158477190044730 := by decide +kernel

private def S0 : List State := [(st58, 0, 3001, 0, 0, 0, false)]

private def S1 : List State :=
  [([(3, 3, 2), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 2, 1), (17, 2, 1), (19, 1, 0), (23, 1, 0), (29, 2, 4), (31, 1, 0), (37, 2, 4), (41, 2, 6), (43, 1, 0), (47, 1, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 3, 2), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 2, 1), (17, 2, 1), (19, 1, 0), (23, 1, 0), (29, 2, 4), (31, 1, 0), (37, 2, 4), (41, 1, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 3, 2), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 2, 1), (17, 2, 1), (19, 1, 0), (23, 1, 0), (29, 2, 4), (31, 1, 0), (37, 1, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 3, 2), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 2, 1), (17, 2, 1), (19, 1, 0), (23, 1, 0), (29, 1, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 3, 2), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 2, 1), (17, 1, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 3, 2), (5, 1, 0), (7, 1, 0), (11, 1, 0), (13, 2, 1), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 0, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 0, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false)]

private def S2 : List State :=
  [([(3, 2, 12), (5, 3, 1), (7, 1, 0), (11, 1, 0), (13, 1, 0), (17, 3, 4), (19, 1, 0), (23, 2, 4), (29, 1, 0), (31, 1, 0), (37, 1, 0), (41, 1, 0), (43, 1, 0), (47, 1, 0), (53, 1, 0)], 88741, 88741, 88741, 88741, 1, false), ([(3, 2, 12), (5, 3, 1), (7, 1, 0), (11, 1, 0), (13, 1, 0), (17, 2, 6), (19, 1, 0), (23, 2, 4), (29, 1, 0), (31, 1, 0), (37, 1, 0), (41, 1, 0), (43, 1, 0), (47, 1, 0), (53, 1, 0)], 0, 3501, 3519, 0, 0, false), ([(3, 2, 4), (5, 3, 1), (7, 1, 0), (11, 1, 0), (13, 1, 0), (17, 2, 1), (19, 1, 0), (23, 1, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 3, 1), (7, 1, 0), (11, 1, 0), (13, 1, 0), (17, 1, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 2, 2), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 0, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false)]

private def S3 : List State :=
  [([(3, 2, 12), (5, 1, 0), (7, 3, 2), (11, 1, 0), (13, 1, 0), (17, 3, 1), (19, 2, 4), (23, 1, 0), (29, 1, 0), (31, 1, 0), (37, 1, 0), (41, 1, 0), (43, 2, 4), (47, 1, 0), (53, 1, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 12), (5, 1, 0), (7, 2, 10), (11, 1, 0), (13, 1, 0), (17, 3, 1), (19, 2, 4), (23, 1, 0), (29, 1, 0), (31, 1, 0), (37, 1, 0), (41, 1, 0), (43, 2, 4), (47, 1, 0), (53, 1, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 12), (5, 1, 0), (7, 2, 2), (11, 1, 0), (13, 1, 0), (17, 2, 4), (19, 2, 4), (23, 1, 0), (29, 1, 0), (31, 1, 0), (37, 1, 0), (41, 1, 0), (43, 2, 4), (47, 1, 0), (53, 1, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 2, 2), (11, 1, 0), (13, 1, 0), (17, 2, 1), (19, 2, 4), (23, 1, 0), (29, 1, 0), (31, 1, 0), (37, 1, 0), (41, 1, 0), (43, 1, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 2, 2), (11, 1, 0), (13, 1, 0), (17, 2, 1), (19, 1, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 2, 2), (11, 1, 0), (13, 1, 0), (17, 1, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 0, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false)]

private def S4 : List State :=
  [([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 2, 4), (17, 1, 0), (19, 2, 4), (23, 1, 0), (29, 1, 0), (31, 1, 0), (37, 2, 1), (41, 1, 0), (43, 1, 0), (47, 2, 8), (53, 2, 1)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 2, 4), (17, 1, 0), (19, 2, 4), (23, 1, 0), (29, 1, 0), (31, 1, 0), (37, 2, 1), (41, 1, 0), (43, 1, 0), (47, 2, 8), (53, 1, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 2, 4), (17, 1, 0), (19, 2, 4), (23, 1, 0), (29, 1, 0), (31, 1, 0), (37, 2, 1), (41, 1, 0), (43, 1, 0), (47, 1, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 2, 4), (17, 1, 0), (19, 2, 4), (23, 1, 0), (29, 1, 0), (31, 1, 0), (37, 1, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 2, 4), (17, 1, 0), (19, 1, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 1, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 1, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 0, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false)]

private def S5 : List State :=
  [([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 1, 0), (17, 1, 0), (19, 2, 4), (23, 2, 4), (29, 1, 0), (31, 2, 6), (37, 2, 1), (41, 1, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 1, 0), (17, 1, 0), (19, 2, 4), (23, 2, 4), (29, 1, 0), (31, 2, 6), (37, 1, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 1, 0), (17, 1, 0), (19, 2, 4), (23, 2, 4), (29, 1, 0), (31, 1, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 1, 0), (17, 1, 0), (19, 2, 4), (23, 1, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 2, 6), (13, 1, 0), (17, 1, 0), (19, 1, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 1, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 0, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false)]

private def S6 : List State :=
  [([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 1, 0), (13, 1, 0), (17, 2, 1), (19, 2, 4), (23, 2, 4), (29, 1, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 1, 0), (13, 1, 0), (17, 2, 1), (19, 2, 4), (23, 1, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 1, 0), (13, 1, 0), (17, 2, 1), (19, 1, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 2, 4), (5, 1, 0), (7, 1, 0), (11, 1, 0), (13, 1, 0), (17, 1, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 0, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false)]

private def S7 : List State :=
  [([(3, 1, 0), (5, 3, 2), (7, 2, 6), (11, 2, 2), (13, 2, 1), (17, 1, 0), (19, 1, 0), (23, 2, 4), (29, 1, 0), (31, 2, 4), (37, 1, 0), (41, 1, 0), (43, 2, 4), (47, 2, 4), (53, 2, 4)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 6), (7, 2, 6), (11, 2, 2), (13, 2, 1), (17, 1, 0), (19, 1, 0), (23, 2, 4), (29, 1, 0), (31, 2, 4), (37, 1, 0), (41, 1, 0), (43, 2, 4), (47, 2, 4), (53, 2, 4)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 2, 2), (13, 2, 1), (17, 1, 0), (19, 1, 0), (23, 2, 4), (29, 1, 0), (31, 2, 4), (37, 1, 0), (41, 1, 0), (43, 2, 4), (47, 2, 4), (53, 1, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 2, 2), (13, 2, 1), (17, 1, 0), (19, 1, 0), (23, 2, 4), (29, 1, 0), (31, 2, 4), (37, 1, 0), (41, 1, 0), (43, 2, 4), (47, 1, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 2, 2), (13, 2, 1), (17, 1, 0), (19, 1, 0), (23, 2, 4), (29, 1, 0), (31, 2, 4), (37, 1, 0), (41, 1, 0), (43, 1, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 2, 2), (13, 2, 1), (17, 1, 0), (19, 1, 0), (23, 2, 4), (29, 1, 0), (31, 1, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 2, 2), (13, 2, 1), (17, 1, 0), (19, 1, 0), (23, 1, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 2, 2), (13, 1, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 1, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 1, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 1, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false)]

private def S8 : List State :=
  [([(3, 1, 0), (5, 3, 2), (7, 2, 6), (11, 1, 0), (13, 3, 1), (17, 2, 4), (19, 2, 4), (23, 1, 0), (29, 2, 4), (31, 2, 6), (37, 1, 0), (41, 2, 4), (43, 1, 0), (47, 2, 10), (53, 2, 6)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 3, 2), (7, 2, 6), (11, 1, 0), (13, 2, 4), (17, 2, 4), (19, 2, 4), (23, 1, 0), (29, 2, 4), (31, 2, 6), (37, 1, 0), (41, 2, 4), (43, 1, 0), (47, 2, 10), (53, 2, 6)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 6), (7, 2, 6), (11, 1, 0), (13, 2, 1), (17, 2, 4), (19, 2, 4), (23, 1, 0), (29, 2, 4), (31, 2, 6), (37, 1, 0), (41, 2, 4), (43, 1, 0), (47, 2, 10), (53, 2, 6)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 1, 0), (13, 2, 1), (17, 2, 4), (19, 2, 4), (23, 1, 0), (29, 2, 4), (31, 2, 6), (37, 1, 0), (41, 2, 4), (43, 1, 0), (47, 2, 10), (53, 1, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 1, 0), (13, 2, 1), (17, 2, 4), (19, 2, 4), (23, 1, 0), (29, 2, 4), (31, 2, 6), (37, 1, 0), (41, 2, 4), (43, 1, 0), (47, 1, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 1, 0), (13, 2, 1), (17, 2, 4), (19, 2, 4), (23, 1, 0), (29, 2, 4), (31, 2, 6), (37, 1, 0), (41, 1, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 1, 0), (13, 2, 1), (17, 2, 4), (19, 2, 4), (23, 1, 0), (29, 2, 4), (31, 1, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 1, 0), (13, 2, 1), (17, 2, 4), (19, 2, 4), (23, 1, 0), (29, 1, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 1, 0), (13, 2, 1), (17, 2, 4), (19, 1, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 1, 0), (13, 2, 1), (17, 1, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 2, 6), (11, 1, 0), (13, 1, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 2, 2), (7, 1, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false), ([(3, 1, 0), (5, 1, 0), (7, 0, 0), (11, 0, 0), (13, 0, 0), (17, 0, 0), (19, 0, 0), (23, 0, 0), (29, 0, 0), (31, 0, 0), (37, 0, 0), (41, 0, 0), (43, 0, 0), (47, 0, 0), (53, 0, 0)], 0, 3001, 0, 0, 0, false)]

private def S9 : List State :=
  []

set_option maxRecDepth 100000 in
private theorem run0 : run 58 32589158477190044730 10 1000 S0 = some S1 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem run1 : run 58 32589158477190044730 10 1000 S1 = some S2 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem run2 : run 58 32589158477190044730 10 1000 S2 = some S3 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem run3 : run 58 32589158477190044730 10 1000 S3 = some S4 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem run4 : run 58 32589158477190044730 10 1000 S4 = some S5 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem run5 : run 58 32589158477190044730 10 1000 S5 = some S6 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem run6 : run 58 32589158477190044730 10 1000 S6 = some S7 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem run7 : run 58 32589158477190044730 10 1000 S7 = some S8 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem run8 : run 58 32589158477190044730 10 1000 S8 = some S9 := by
  decide +kernel

private theorem cert58 : Cert 58 S0 :=
  cert_step M58_eq run0 (cert_step M58_eq run1 (cert_step M58_eq run2 (cert_step M58_eq run3 (cert_step M58_eq run4 (cert_step M58_eq run5 (cert_step M58_eq run6 (cert_step M58_eq run7 (cert_step M58_eq run8 (cert_nil 58)))))))))

end SLP

/-- An odd perfect number has two distinct prime factors above `58`. -/
theorem exists_two_primeFactors_gt {N : ℕ} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, ∃ r ∈ N.primeFactors, p ≠ r ∧ 58 < p ∧ 58 < r :=
  SLP.exists_two_of_cert SLP.st58_eq (by norm_num) SLP.cert58 h

end OddPerfect

#print axioms OddPerfect.SLP.expand_sound
#print axioms OddPerfect.SLP.run_sound
#print axioms OddPerfect.SLP.cert_nil
#print axioms OddPerfect.SLP.cert_step
#print axioms OddPerfect.SLP.exists_two_of_cert
#print axioms OddPerfect.exists_two_primeFactors_gt
