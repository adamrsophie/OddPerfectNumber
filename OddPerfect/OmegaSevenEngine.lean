import OddPerfect.OmegaSeven

namespace OddPerfect.OmegaSevenEngine

open OmegaSixSearch (Ent Holds lnum lden unum uden strip remove isPrimeQ kmin nextValid valid
  bsearch bounds bU minB chainList allEx deadAbund deadParity deadChain solve_sound enum_sound
  kmin_le lowB)
open Cert (geom)

noncomputable section

/-- Closed form of `1 + p + ... + p ^ k`. -/
def geomN (p k : ℕ) : ℕ := Nat.div (Nat.sub (Nat.pow p (Nat.succ k)) 1) (Nat.sub p 1)

/-- Numerator of the lower abundancy bound. -/
def lnumR (l : List Ent) : ℕ :=
  List.rec (motive := fun _ => ℕ) 1 (fun e _ ih => Nat.mul (geomN e.p e.k) ih) l
/-- Denominator of the lower abundancy bound. -/
def ldenR (l : List Ent) : ℕ :=
  List.rec (motive := fun _ => ℕ) 1 (fun e _ ih => Nat.mul (Nat.pow e.p e.k) ih) l
/-- Numerator of the upper abundancy bound. -/
def unumR (l : List Ent) : ℕ :=
  List.rec (motive := fun _ => ℕ) 1 (fun e _ ih => Nat.mul (cond e.ex (geomN e.p e.k) e.p) ih) l
/-- Denominator of the upper abundancy bound. -/
def udenR (l : List Ent) : ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun e _ ih => Nat.mul (cond e.ex (Nat.pow e.p e.k) (Nat.sub e.p 1)) ih) l

/-- Remove all factors `y` from `g` (fuel `n`). -/
def removeR (y n g : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun g => g)
    (fun _ ih g => cond (Nat.beq (Nat.mod g y) 0) (ih (Nat.div g y)) g) n g

/-- Remove all factors of a list. -/
def stripR (g : ℕ) (ys : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun g => g) (fun y _ ih g => ih (removeR y g g)) ys g

/-- The listed primes. -/
def psR (l : List Ent) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun e _ ih => e.p :: ih) l

/-- Prepend `c` unless it is `1`. -/
def consC (c : ℕ) (t : List ℕ) : List ℕ := cond (Nat.beq c 1) t (c :: t)

/-- The cofactors, coprime to `ps`, of the exact component divisor sums, without ones. -/
def chainAux (ps : List ℕ) (l : List Ent) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) []
    (fun e _ ih => cond e.ex (consC (stripR (geomN e.p e.k) ps) ih) ih) l

/-- The cofactors of the exact component divisor sums that are not one. -/
def chainR (l : List Ent) : List ℕ := chainAux (2 :: psR l) l

/-- Maximum. -/
def maxN (a b : ℕ) : ℕ := cond (Nat.ble a b) b a

/-- Lower bound for every unlisted prime: `m + 1`, and `q (2 - L) ≥ L` with `L = ln / ld`. -/
def lowE (ln ld m : ℕ) : ℕ :=
  cond (Nat.blt ln (Nat.mul 2 ld))
    (maxN (Nat.succ m) (Nat.div (Nat.sub (Nat.add ln (Nat.sub (Nat.mul 2 ld) ln)) 1)
      (Nat.sub (Nat.mul 2 ld) ln)))
    (Nat.succ m)

/-- The last ladder entry `(X, P)` with `X < lo` (scanning a sorted ladder), or `b`. -/
def pickP (lad : List (ℕ × ℕ)) (lo : ℕ) (b : ℕ × ℕ) : ℕ × ℕ :=
  List.rec (motive := fun _ => ℕ × ℕ → ℕ × ℕ) (fun b => b)
    (fun x _ ih b => cond (Nat.blt x.1 lo) (ih x) b) lad b

/-- A cofactor certified prime: below `lo ^ 2`, or below `(Y + 1) ^ 2` and coprime to `Q`. -/
def forceOK (lo Y Q c : ℕ) : Bool :=
  Nat.blt c (Nat.mul lo lo) ||
    (Nat.blt c (Nat.mul (Nat.succ Y) (Nat.succ Y)) && Nat.beq (Nat.gcd c Q) 1)

/-- The first certified prime cofactor, or `0`. -/
def firstForce (lo Y Q : ℕ) (cs : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun c _ ih => cond (forceOK lo Y Q c) c ih) cs

/-- The chain test: a cofactor is impossible. -/
def deadC (j lo P : ℕ) (cs : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun c _ ih => (Nat.beq j 0 || Nat.blt c lo || Nat.blt 1 (Nat.gcd c P)) || ih) cs

/-- The condition `U (q/(q-1))^j > 2` with `U = un/ud`. -/
def condR (un ud j q : ℕ) : Bool :=
  Nat.blt (Nat.mul (Nat.mul 2 ud) (Nat.pow (Nat.sub q 1) j)) (Nat.mul un (Nat.pow q j))

/-- Bisection for the last `q` satisfying `condR`. -/
def bsearchR (un ud j n a b : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun a _ => a)
    (fun _ ih a b => cond (Nat.ble b (Nat.succ a)) a
      (cond (condR un ud j (Nat.div (Nat.add a b) 2)) (ih (Nat.div (Nat.add a b) 2) b)
        (ih a (Nat.div (Nat.add a b) 2)))) n a b

/-- Upper bounds for the next prime, from the bisection result `b`. -/
def boundsW (un ud j b : ℕ) (cs : List ℕ) : List ℕ :=
  cond (Nat.blt un (Nat.mul 2 ud) && Nat.ble 1 b && !condR un ud j (Nat.succ b)) (b :: cs) cs

/-- Upper bounds for the next prime. -/
def boundsR (un ud j m : ℕ) (cs : List ℕ) : List ℕ :=
  boundsW un ud j (bsearchR un ud j 200 m
    (Nat.add (Nat.add m (Nat.div (Nat.mul (Nat.mul 2 j) un) (Nat.sub (Nat.mul 2 ud) un))) 2)) cs

/-- Minimum of a list (`0` for the empty list). -/
def minR (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun a t ih => List.rec (motive := fun _ => ℕ) a (fun _ _ _ => cond (Nat.ble a ih) a ih) t) l

/-- All entries are exact. -/
def allExR (l : List Ent) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => e.ex && ih) l

/-- Some exact entry other than `p` has an odd exponent. -/
def oddOther (l : List Ent) (p : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun b _ ih => (b.ex && Nat.beq (Nat.mod b.k 2) 1 && !Nat.beq b.p p) || ih) l

/-- Some exact entry of `l'` with an odd exponent has an exact odd partner in `L`. -/
def parAux (L l' : List Ent) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ ih => (a.ex && Nat.beq (Nat.mod a.k 2) 1 && oddOther L a.p) || ih) l'

/-- The parity test: two exact entries with odd exponents. -/
def parC (l : List Ent) : Bool := parAux l l

/-- Some inexact entry has `p ^ k < T`. -/
def lowInexact (l : List Ent) (T : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun e _ ih => (!e.ex && Nat.blt (Nat.pow e.p e.k) T) || ih) l

/-- Scan for the inexact entry (with `p ^ k < T`, when `T ≠ 0`) of largest abundancy gap,
starting from the best entry `be` so far with gap `bn / bd`. -/
def pickAuxR (T : ℕ) (l : List Ent) (be : Ent) (bn bd : ℕ) : Ent :=
  List.rec (motive := fun _ => Ent → ℕ → ℕ → Ent) (fun be _ _ => be)
    (fun e _ ih be bn bd =>
      cond (!e.ex && (Nat.beq T 0 || Nat.blt (Nat.pow e.p e.k) T) &&
          Nat.blt (Nat.mul bn (Nat.mul (Nat.sub e.p 1) (geomN e.p e.k)))
            (Nat.mul (Nat.mul e.p (Nat.pow e.p e.k)) bd))
        (ih e (Nat.mul e.p (Nat.pow e.p e.k)) (Nat.mul (Nat.sub e.p 1) (geomN e.p e.k)))
        (ih be bn bd)) l be bn bd

/-- The inexact entry (with `p ^ k < T`, when `T ≠ 0`) of largest abundancy gap; the first on
ties; `⟨0, 0, true⟩` if there is none. -/
def pickR (l : List Ent) (T : ℕ) : Ent := pickAuxR T l ⟨0, 0, true⟩ 0 1

/-- An exponent admissible by Euler's theorem. -/
def validR (p e : ℕ) : Bool :=
  Nat.beq (Nat.mod e 2) 0 || (Nat.beq (Nat.mod p 4) 1 && Nat.beq (Nat.mod e 4) 1)

/-- The next admissible exponent above `k`. -/
def nextValidR (p k : ℕ) : ℕ := cond (validR p (Nat.succ k)) (Nat.succ k) (Nat.succ (Nat.succ k))

/-- The least admissible positive exponent of `q`. -/
def kminR (q : ℕ) : ℕ := cond (Nat.beq (Nat.mod q 4) 1) 1 2

/-- The exact case `p ^ k` with cofactor `c` is impossible by the local chain or parity test. -/
def advDeadC (l : List Ent) (j lo P p k c : ℕ) : Bool :=
  (!Nat.beq c 1 && (Nat.beq j 0 || Nat.blt c lo || Nat.blt 1 (Nat.gcd c P))) ||
  (Nat.beq (Nat.mod k 2) 1 && oddOther l p)

/-- Skip exponents whose exact case is impossible (fuel `n`). -/
def advR (l : List Ent) (j lo P p : ℕ) (ps : List ℕ) (n k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun k => k)
    (fun _ ih k => cond (advDeadC l j lo P p k (stripR (geomN p k) ps)) (ih (nextValidR p k)) k)
    n k

/-- Replace the entries with prime `p` by `e`. -/
def replP (l : List Ent) (p : ℕ) (e : Ent) : List Ent :=
  List.rec (motive := fun _ => List Ent) [] (fun a _ ih => cond (Nat.beq a.p p) (e :: ih) (a :: ih)) l

/-- Split the prime `p` at exponent `k` (exact) and above (inexact). -/
def splitK (rec : List Ent → ℕ → ℕ → Bool) (l : List Ent) (j m p k : ℕ) : Bool :=
  rec (replP l p ⟨p, k, true⟩) j m && rec (replP l p ⟨p, nextValidR p k, false⟩) j m

/-- Split the entry `e`, skipping impossible exact exponents first. -/
def splitR (rec : List Ent → ℕ → ℕ → Bool) (l : List Ent) (j m lo P : ℕ) (e : Ent) : Bool :=
  splitK rec l j m e.p (advR l j lo P e.p (2 :: psR l) 20 e.k)

/-- `q` is a listed prime. -/
def listedR (l : List Ent) (q : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ ih => Nat.beq e.p q || ih) l

/-- The enumeration filter: true on every prime `q > X` that is not listed. -/
def candQ (l : List Ent) (X P q : ℕ) : Bool :=
  !listedR l q && Nat.beq (Nat.gcd q P) 1 &&
    (Nat.blt q (Nat.mul (Nat.succ X) (Nat.succ X)) || isPrimeQ q)

/-- Enumerate the candidates `q, q + 1, ..., q + n - 1` for the next prime. -/
def enumR (rec : List Ent → ℕ → ℕ → Bool) (l : List Ent) (j' X P n q : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih q => (!candQ l X P q || rec (⟨q, kminR q, false⟩ :: l) j' q) && ih (Nat.succ q)) n q

/-- Node, last step: `j' + 1` further primes and the least upper bound `B`. -/
def nodeG (rec : List Ent → ℕ → ℕ → Bool) (T : ℕ) (l : List Ent) (j' m lo X P pm B : ℕ) : Bool :=
  cond (Nat.ble 1 j' && Nat.ble j' 8 && lowInexact l T && !Nat.ble B (Nat.add lo 10))
    (splitR rec l (Nat.succ j') m lo pm (pickR l T))
    (cond (Nat.ble B (Nat.add lo 10) || allExR l || Nat.ble 1 j')
      (enumR rec l j' X P (Nat.sub (Nat.succ B) lo) lo)
      (!allExR l && splitR rec l (Nat.succ j') m lo pm (pickR l 0)))

/-- Node: `j' + 1` further primes and the list of upper bounds `bs`. -/
def nodeF (rec : List Ent → ℕ → ℕ → Bool) (T : ℕ) (l : List Ent) (j' m lo X P pm : ℕ)
    (bs : List ℕ) : Bool :=
  match bs with
  | [] => !allExR l && splitR rec l (Nat.succ j') m lo pm (pickR l 0)
  | b :: bs' => nodeG rec T l j' m lo X P pm (minR (b :: bs'))

/-- Node: `j' + 1` further primes, after the forcing test. -/
def nodeE (rec : List Ent → ℕ → ℕ → Bool) (T : ℕ) (l : List Ent) (j' m un ud lo X P pm : ℕ)
    (cs : List ℕ) (fc : ℕ) : Bool :=
  match fc with
  | 0 => nodeF rec T l j' m lo X P pm (boundsR un ud (Nat.succ j') m cs)
  | c + 1 => rec (⟨c + 1, kminR (c + 1), false⟩ :: l) j' m

/-- Node: the closing tests for `j = 0`, forcing and the step for `j > 0`. -/
def nodeD (rec : List Ent → ℕ → ℕ → Bool) (Y Q T : ℕ) (l : List Ent) (j m ln ld un ud lo X P
    pm : ℕ) (cs : List ℕ) : Bool :=
  match j with
  | 0 => cond (allExR l) (!Nat.beq ln (Nat.mul 2 ld))
      (Nat.ble un (Nat.mul 2 ud) || splitR rec l 0 m lo pm (pickR l 0))
  | j' + 1 => nodeE rec T l j' m un ud lo X P pm cs (firstForce lo Y Q cs)

/-- Node: the abundancy, parity and chain tests. -/
def nodeC (rec : List Ent → ℕ → ℕ → Bool) (Y Q T : ℕ) (l : List Ent) (j m ln ld un ud lo X P
    pm : ℕ) (cs : List ℕ) : Bool :=
  (Nat.blt (Nat.mul 2 ld) ln || (Nat.blt 0 j && Nat.ble (Nat.mul 2 ld) ln)) || parC l ||
  deadC j lo P cs || nodeD rec Y Q T l j m ln ld un ud lo X P pm cs

/-- Node: the ladder entries. -/
def nodeB (lad : List (ℕ × ℕ)) (rec : List Ent → ℕ → ℕ → Bool) (Y Q T : ℕ) (l : List Ent)
    (j m ln ld un ud lo : ℕ) (xp : ℕ × ℕ) : Bool :=
  nodeC rec Y Q T l j m ln ld un ud lo xp.1 xp.2 (pickP lad (Nat.succ m) (0, 1)).2 (chainR l)

/-- Node: the lower bound for the unlisted primes. -/
def nodeA (lad : List (ℕ × ℕ)) (rec : List Ent → ℕ → ℕ → Bool) (Y Q T : ℕ) (l : List Ent)
    (j m ln ld un ud : ℕ) : Bool :=
  nodeB lad rec Y Q T l j m ln ld un ud (lowE ln ld m) (pickP lad (lowE ln ld m) (0, 1))

/-- The search with fuel `f`. `true` means no odd perfect number satisfies the state. -/
def solve (lad : List (ℕ × ℕ)) (Y Q T f : ℕ) : List Ent → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => List Ent → ℕ → ℕ → Bool) (fun _ _ _ => false)
    (fun _ rec l j m => nodeA lad rec Y Q T l j m (lnumR l) (ldenR l) (unumR l) (udenR l)) f


/-! ### The fast functions agree with the reference functions of `OmegaSixSearch` -/

private theorem beqF {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.mpr fun h' => h (Nat.eq_of_beq_eq_true h')

private theorem bleF {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false :=
  Bool.eq_false_iff.mpr fun h' => h (Nat.le_of_ble_eq_true h')

private theorem bltD (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff]; simp

private theorem bleD (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff]; simp

@[simp] private theorem natDiv (a b : ℕ) : Nat.div a b = a / b := rfl
@[simp] private theorem natMod (a b : ℕ) : Nat.mod a b = a % b := rfl

private theorem beq_false_iff {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b :=
  ⟨fun h h' => by rw [h', Nat.beq_refl] at h; exact absurd h (by decide), beqF⟩

private theorem geomN_eq {p : ℕ} (hp : 2 ≤ p) (k : ℕ) : geomN p k = geom p k := by
  rw [Cert.geom_eq, Nat.geomSum_eq hp]; rfl

section Eqs

variable {l : List Ent}

private theorem lnumR_eq (hl : ∀ e ∈ l, 2 ≤ e.p) : lnumR l = lnum l := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    show geomN e.p e.k * lnumR t = _
    rw [ih (fun x hx => hl x (by simp [hx])), geomN_eq (hl e (by simp))]
    simp [lnum]

private theorem ldenR_eq : ldenR l = lden l := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    show e.p ^ e.k * ldenR t = _
    rw [ih]; simp [lden]

private theorem unumR_eq (hl : ∀ e ∈ l, 2 ≤ e.p) : unumR l = unum l := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    show cond e.ex (geomN e.p e.k) e.p * unumR t = _
    rw [ih (fun x hx => hl x (by simp [hx])), geomN_eq (hl e (by simp))]
    obtain ⟨p, k, ex⟩ := e
    cases ex <;> simp [unum]

private theorem udenR_eq : udenR l = uden l := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    show cond e.ex (e.p ^ e.k) (e.p - 1) * udenR t = _
    rw [ih]
    obtain ⟨p, k, ex⟩ := e
    cases ex <;> simp [uden]

private theorem remove_zero (y : ℕ) : ∀ n, remove y n 0 = 0
  | 0 => rfl
  | n + 1 => by simp [remove]

private theorem removeR_eq {y : ℕ} (hy : 2 ≤ y) : ∀ n g, removeR y n g = remove y n g
  | 0, g => rfl
  | n + 1, g => by
    show cond (Nat.beq (g % y) 0) (removeR y n (g / y)) g = _
    rw [removeR_eq hy n]
    by_cases hg : g = 0
    · subst hg; simp [remove_zero, remove]
    · by_cases hm : g % y = 0
      · simp [remove, hm, hg, hy]
      · rw [beqF hm]; simp [remove, hm]

private theorem stripR_eq : ∀ (ys : List ℕ) (g : ℕ), (∀ y ∈ ys, 2 ≤ y) → stripR g ys = strip g ys
  | [], _, _ => rfl
  | y :: ys, g, h => by
    show stripR (removeR y g g) ys = strip (remove y g g) ys
    rw [removeR_eq (h y (by simp))]
    exact stripR_eq ys _ (fun x hx => h x (by simp [hx]))

private theorem psR_eq : psR l = l.map Ent.p := by
  induction l with
  | nil => rfl
  | cons e t ih => show e.p :: psR t = _; rw [ih]; rfl

private theorem chainAux_eq {ps : List ℕ} (hps : ∀ y ∈ ps, 2 ≤ y) (hl : ∀ e ∈ l, 2 ≤ e.p) :
    chainAux ps l = ((l.filter (·.ex)).map fun e => strip (geom e.p e.k) ps).filter
      (· != 1) := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    show cond e.ex (consC (stripR (geomN e.p e.k) ps) (chainAux ps t)) (chainAux ps t) = _
    rw [ih (fun x hx => hl x (by simp [hx])), stripR_eq ps _ hps, geomN_eq (hl e (by simp))]
    cases hx : e.ex
    · simp [hx]
    · simp only [cond_true, consC, List.filter_cons, hx, if_true, List.map_cons]
      by_cases h1 : strip (geom e.p e.k) ps = 1
      · simp [h1]
      · simp [beqF h1, h1]

private theorem chainR_eq (hl : ∀ e ∈ l, 2 ≤ e.p) : chainR l = chainList l := by
  unfold chainR chainList
  rw [psR_eq, chainAux_eq _ hl]
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact le_rfl
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy; exact hl e he

private theorem minR_eq : ∀ l : List ℕ, minR l = minB l
  | [] => rfl
  | [a] => rfl
  | a :: b :: t => by
    show cond (Nat.ble a (minR (b :: t))) a (minR (b :: t)) = min a (minB (b :: t))
    rw [minR_eq (b :: t)]
    by_cases h : a ≤ minB (b :: t)
    · rw [Nat.ble_eq_true_of_le h]; simp [h]
    · rw [bleF h]; simp [Nat.min_def, h]

private theorem condR_eq (un ud j q : ℕ) : condR un ud j q = OmegaSixSearch.cond un ud j q := by
  simp [condR, OmegaSixSearch.cond, bltD]

private theorem bsearchR_eq (un ud j : ℕ) : ∀ n a b, bsearchR un ud j n a b = bsearch un ud j n a b
  | 0, _, _ => rfl
  | n + 1, a, b => by
    show cond (Nat.ble b (a + 1)) a
      (cond (condR un ud j ((a + b) / 2)) (bsearchR un ud j n ((a + b) / 2) b)
        (bsearchR un ud j n a ((a + b) / 2))) = _
    rw [bsearchR_eq un ud j n, bsearchR_eq un ud j n, condR_eq]
    by_cases h : b ≤ a + 1
    · rw [Nat.ble_eq_true_of_le h]; simp [bsearch, h]
    · rw [bleF h]; simp only [bsearch, h, if_false]
      cases OmegaSixSearch.cond un ud j ((a + b) / 2) <;> rfl

private theorem boundsR_eq (j m : ℕ) :
    boundsR (unum l) (uden l) j m (chainList l) = bounds l j m := by
  unfold boundsR boundsW bounds bU
  rw [bsearchR_eq, condR_eq, bltD, bleD]
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, natDiv, Nat.succ_eq_add_one]
  generalize bsearch (unum l) (uden l) j 200 m (m + 2 * j * unum l / (2 * uden l - unum l) + 2) = b
  by_cases h1 : unum l < 2 * uden l <;> by_cases h2 : 1 ≤ b <;>
    cases OmegaSixSearch.cond (unum l) (uden l) j (b + 1) <;> simp [h1, h2]

private theorem allExR_eq : allExR l = allEx l := by
  induction l with
  | nil => rfl
  | cons e t ih => show (e.ex && allExR t) = _; rw [ih]; simp [allEx]

private theorem kminR_eq (q : ℕ) : kminR q = kmin q := by
  unfold kminR kmin
  simp only [natMod]
  by_cases h : q % 4 = 1
  · rw [h]; simp
  · rw [beqF h]; simp [h]

private theorem validR_eq (p e : ℕ) : validR p e = valid p e := by
  rw [Bool.eq_iff_iff]; simp [validR, valid, natMod]

private theorem nextValidR_eq (p k : ℕ) : nextValidR p k = nextValid p k := by
  unfold nextValidR nextValid
  rw [validR_eq]
  cases valid p (k + 1) <;> rfl

private theorem maxN_eq (a b : ℕ) : maxN a b = max a b := by
  unfold maxN
  by_cases h : a ≤ b
  · rw [Nat.ble_eq_true_of_le h]; simp [h]
  · rw [bleF h]; simp [max_def, h]

private theorem listedR_iff (q : ℕ) : listedR l q = true ↔ q ∈ l.map Ent.p := by
  induction l with
  | nil => simp [listedR]
  | cons e t ih =>
    show (Nat.beq e.p q || listedR t q) = true ↔ _
    rw [Bool.or_eq_true, ih]
    simp only [List.map_cons, List.mem_cons, Nat.beq_eq]
    exact ⟨fun h => h.elim (fun h => Or.inl h.symm) Or.inr,
      fun h => h.elim (fun h => Or.inl h.symm) Or.inr⟩

end Eqs
/-! ### Facts about states -/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

section Facts

variable {N : ℕ} {l : List Ent} {j m : ℕ}

private theorem remove_dvd (y : ℕ) : ∀ n g, remove y n g ∣ g
  | 0, g => by simp [remove]
  | n + 1, g => by
    unfold remove
    split_ifs with h
    · exact (remove_dvd y n (g / y)).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h.2.2))
    · exact dvd_rfl

private theorem remove_ne_zero (y : ℕ) : ∀ n g, g ≠ 0 → remove y n g ≠ 0
  | 0, g, hg => by simpa [remove] using hg
  | n + 1, g, hg => by
    unfold remove
    split_ifs with h
    · apply remove_ne_zero y n
      have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hg) (Nat.dvd_of_mod_eq_zero h.2.2))
        (by omega : 0 < y)
      omega
    · exact hg

private theorem not_dvd_remove {y : ℕ} (hy : 2 ≤ y) :
    ∀ n g, g ≠ 0 → g < 2 ^ n → ¬ y ∣ remove y n g
  | 0, g, hg, hlt => by simp at hlt; omega
  | n + 1, g, hg, hlt => by
    unfold remove
    split_ifs with h
    · apply not_dvd_remove hy n
      · have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hg)
          (Nat.dvd_of_mod_eq_zero h.2.2)) (by omega : 0 < y)
        omega
      · have h1 : g / y ≤ g / 2 := Nat.div_le_div_left hy (by norm_num)
        have h2 : g / 2 < 2 ^ n := by rw [pow_succ] at hlt; omega
        omega
    · intro hd
      exact h ⟨hy, hg, Nat.mod_eq_zero_of_dvd hd⟩

private theorem strip_dvd : ∀ (ys : List ℕ) (g : ℕ), strip g ys ∣ g
  | [], g => by simp [strip]
  | y :: ys, g => (strip_dvd ys _).trans (remove_dvd y g g)

private theorem strip_ne_zero : ∀ (ys : List ℕ) (g : ℕ), g ≠ 0 → strip g ys ≠ 0
  | [], _, hg => hg
  | y :: ys, g, hg => strip_ne_zero ys _ (remove_ne_zero y g g hg)

private theorem not_dvd_strip : ∀ (ys : List ℕ) (g : ℕ) {y : ℕ}, y ∈ ys → 2 ≤ y → g ≠ 0 →
    ¬ y ∣ strip g ys
  | [], _, _, hy, _, _ => by simp at hy
  | z :: ys, g, y, hy, h2, hg => by
    intro hd
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact not_dvd_remove h2 g g hg Nat.lt_two_pow_self (hd.trans (strip_dvd ys _))
    · exact not_dvd_strip ys _ hy' h2 (remove_ne_zero z g g hg) hd

private theorem geom_pos (p k : ℕ) : 0 < geom p k := by
  rw [Cert.geom_eq]; exact Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨0, by simp, by simp⟩

private theorem prime_of_holds (H : Holds N l j m) : ∀ e ∈ l, e.p.Prime :=
  fun e he => Nat.prime_of_mem_primeFactors (H.2.2.1 e he).1

private theorem two_le_of_holds (H : Holds N l j m) : ∀ e ∈ l, 2 ≤ e.p :=
  fun e he => (prime_of_holds H e he).two_le

/-- With no further primes, every prime factor is listed. -/
private theorem mem_of_holds_zero (H : Holds N l 0 m) {q : ℕ} (hq : q ∈ N.primeFactors) :
    q ∈ l.map Ent.p := by
  obtain ⟨h, hnd, hent, hcard, -⟩ := H
  have hK : (l.map Ent.p).toFinset ⊆ N.primeFactors := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact (hent e he).1
  have heq := Finset.eq_of_subset_of_card_le hK (by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hcard]; omega)
  rw [← heq] at hq
  exact List.mem_toFinset.mp hq

private theorem pos_of_unlisted (H : Holds N l j m) {q : ℕ} (hq : q ∈ N.primeFactors)
    (hn : q ∉ l.map Ent.p) : 0 < j := by
  rcases Nat.eq_zero_or_pos j with rfl | h
  · exact absurd (mem_of_holds_zero H hq) hn
  · exact h

/-- Adding an unlisted prime factor, with the same bound `m`. -/
private theorem holds_cons (H : Holds N l j m) {q : ℕ} (hq : q ∈ N.primeFactors)
    (hn : q ∉ l.map Ent.p) : Holds N (⟨q, kmin q, false⟩ :: l) (j - 1) m := by
  have hj := pos_of_unlisted H hq hn
  obtain ⟨h, hnd, hent, hcard, hbig⟩ := H
  refine ⟨h, List.nodup_cons.mpr ⟨hn, hnd⟩, ?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨hq, kmin_le h hq, fun h => by simp at h⟩
    · exact hent e he
  · simp only [List.length_cons]; omega
  · intro r hr hrn
    exact hbig r hr (fun hh => hrn (by simp [hh]))

/-- The child state of the enumeration, with the new entry in front. -/
private theorem holds_cons_of_append {x : Ent} {j' m' : ℕ} (H : Holds N (l ++ [x]) j' m') :
    Holds N (x :: l) j' m' := by
  obtain ⟨h, hnd, hent, hcard, hbig⟩ := H
  have hp : (l ++ [x]).Perm (x :: l) := List.perm_append_singleton x l
  refine ⟨h, (hp.map Ent.p).nodup_iff.mp hnd, fun e he => hent e (hp.mem_iff.mpr he), ?_,
    fun r hr hn => hbig r hr (fun hh => hn ((hp.map Ent.p).mem_iff.mp hh))⟩
  rw [hcard, hp.length_eq]

private theorem solve_one_of_abund {l : List Ent} {j m : ℕ} (h : deadAbund l j = true) :
    OmegaSixSearch.solve 1 l j m = true := by
  simp [OmegaSixSearch.solve, h]

/-- Every unlisted prime factor `q` satisfies `L (1 + 1/q) ≤ 2`, so it is at least `lowE`. -/
private theorem lowE_le (H : Holds N l j m) {q : ℕ} (hq : q ∈ N.primeFactors) (hn : q ∉ l.map Ent.p) :
    lowE (lnum l) (lden l) m ≤ q := by
  have H' := holds_cons H hq hn
  have hd : deadAbund (⟨q, kmin q, false⟩ :: l) (j - 1) = false := by
    by_contra hc
    exact solve_sound 1 _ _ _ (solve_one_of_abund (m := m) (by simpa using hc)) H'
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hq2 := hqp.two_le
  have hm : m < q := H.2.2.2.2 q hq hn
  simp only [deadAbund, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hd
  have key : lnum l * (q + 1) ≤ 2 * q * lden l := by
    have h1 := hd.1
    simp only [lnum, lden, List.map_cons, List.prod_cons] at h1
    change geom q (kmin q) * lnum l ≤ 2 * (q ^ kmin q * lden l) at h1
    unfold kmin at h1
    split_ifs at h1
    · simp [geom] at h1; nlinarith
    · simp [geom] at h1
      have : q * (lnum l * (q + 1)) ≤ q * (2 * q * lden l) := by nlinarith
      exact Nat.le_of_mul_le_mul_left this (by omega)
  unfold lowE
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq, natDiv]
  cases hc : Nat.blt (lnum l) (2 * lden l)
  · show m + 1 ≤ q; omega
  · have hlt : lnum l < 2 * lden l := by simpa using hc
    show maxN (m + 1) _ ≤ q
    rw [maxN_eq]
    refine max_le (by omega) ?_
    have hD : 0 < 2 * lden l - lnum l := by omega
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul hD]
    have : lnum l ≤ q * (2 * lden l - lnum l) := by
      rw [Nat.mul_sub]
      have e1 : lnum l * (q + 1) = q * lnum l + lnum l := by ring
      have e2 : 2 * q * lden l = q * (2 * lden l) := by ring
      omega
    have : q.succ * (2 * lden l - lnum l) = q * (2 * lden l - lnum l) + (2 * lden l - lnum l) := by
      rw [Nat.succ_eq_add_one]; ring
    omega

/-- A prime factor of the cofactor of `σ(p^k)`, for a listed prime `p` of exact exponent `k`,
is an unlisted prime factor of `N`. -/
private theorem cof_prime (H : Holds N l j m) {p k r : ℕ} (hpl : p ∈ l.map Ent.p)
    (hk : N.factorization p = k) (hr : r.Prime) (hrc : r ∣ strip (geom p k) (2 :: l.map Ent.p)) :
    r ∈ N.primeFactors ∧ r ∉ l.map Ent.p := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hpl
  have hp := prime_of_holds H e he
  have hg := (geom_pos e.p k).ne'
  have hr2 : r ≠ 2 := by
    rintro rfl; exact not_dvd_strip _ _ (by simp) le_rfl hg hrc
  have hrg : r ∣ σ 1 (e.p ^ N.factorization e.p) := by
    rw [hk, Cert.sigma_eq_geom hp]; exact hrc.trans (strip_dvd _ _)
  have hrN := OPNStarter.force_prime H.1.perfect hp rfl hr hr2 hrg
  refine ⟨Nat.mem_primeFactors.mpr ⟨hr, hrN, H.1.ne_zero⟩, ?_⟩
  intro hm
  exact not_dvd_strip _ _ (List.mem_cons_of_mem _ hm) hr.two_le hg hrc

private theorem mem_chainList {c : ℕ} (hc : c ∈ chainList l) :
    ∃ e ∈ l, e.ex = true ∧ c = strip (geom e.p e.k) (2 :: l.map Ent.p) ∧ c ≠ 1 := by
  simp only [chainList, List.mem_filter, List.mem_map, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨e, ⟨he, hex⟩, rfl⟩, hc1⟩ := hc
  exact ⟨e, he, by simpa using hex, rfl, hc1⟩

/-- A cofactor's prime factors are unlisted prime factors of `N`, hence at least `lo`. -/
private theorem chain_factor (H : Holds N l j m) {c r : ℕ} (hc : c ∈ chainList l) (hr : r.Prime)
    (hrc : r ∣ c) : r ∈ N.primeFactors ∧ r ∉ l.map Ent.p ∧ lowE (lnum l) (lden l) m ≤ r := by
  obtain ⟨e, he, hex, rfl, -⟩ := mem_chainList hc
  obtain ⟨h1, h2⟩ := cof_prime H (List.mem_map_of_mem he) ((H.2.2.1 e he).2.2 hex) hr hrc
  exact ⟨h1, h2, lowE_le H h1 h2⟩

private theorem chain_pos {c : ℕ} (hc : c ∈ chainList l) : 0 < c := by
  obtain ⟨e, -, -, rfl, -⟩ := mem_chainList hc
  exact Nat.pos_of_ne_zero (strip_ne_zero _ _ (geom_pos _ _).ne')

end Facts
/-! ### Soundness of the node tests -/

/-- Every prime factor of the second component of a ladder entry is at most the first. -/
def LadGood (lad : List (ℕ × ℕ)) : Prop := ∀ x ∈ lad, ∀ r : ℕ, r.Prime → r ∣ x.2 → r ≤ x.1

/-- Every prime up to `Y` divides `Q`. -/
def QGood (Y Q : ℕ) : Prop := ∀ r : ℕ, r.Prime → r ≤ Y → r ∣ Q

section Sound

variable {N : ℕ} {l : List Ent} {j m : ℕ}

private theorem pickP_good {lad : List (ℕ × ℕ)} (hlad : LadGood lad) (lo : ℕ) :
    ∀ b : ℕ × ℕ, (∀ r : ℕ, r.Prime → r ∣ b.2 → r < lo) →
      ∀ r : ℕ, r.Prime → r ∣ (pickP lad lo b).2 → r < lo := by
  induction lad with
  | nil => intro b hb; exact hb
  | cons x t ih =>
    intro b hb
    show ∀ r : ℕ, r.Prime → r ∣ (cond (Nat.blt x.1 lo) (pickP t lo x) b).2 → r < lo
    cases hx : Nat.blt x.1 lo
    · exact hb
    · have hx' : x.1 < lo := by simpa using hx
      exact ih (fun y hy => hlad y (by simp [hy])) x
        (fun r hr hrd => lt_of_le_of_lt (hlad x (by simp) r hr hrd) hx')

private theorem pickP_zero_good {lad : List (ℕ × ℕ)} (hlad : LadGood lad) (lo : ℕ) :
    ∀ r : ℕ, r.Prime → r ∣ (pickP lad lo (0, 1)).2 → r < lo :=
  pickP_good hlad lo (0, 1) (fun r hr hd => absurd (Nat.le_of_dvd one_pos hd) (by
    have := hr.two_le; omega))

private theorem deadC_iff (j lo P : ℕ) : ∀ cs : List ℕ, deadC j lo P cs = true ↔
    ∃ c ∈ cs, j = 0 ∨ c < lo ∨ 1 < Nat.gcd c P
  | [] => by simp [deadC]
  | c :: cs => by
    show ((Nat.beq j 0 || Nat.blt c lo || Nat.blt 1 (Nat.gcd c P)) || deadC j lo P cs) = true ↔ _
    rw [Bool.or_eq_true, deadC_iff j lo P cs]
    simp [or_assoc]

/-- A cofactor `c ≠ 1` of `σ(p^k)`, where `k` is the exponent of the listed prime `p`, with
`j = 0`, `c < lo` or a common factor with `P`, is impossible. -/
private theorem cof_dead (H : Holds N l j m) {p k P : ℕ} (hpl : p ∈ l.map Ent.p)
    (hk : N.factorization p = k)
    (hP : ∀ r : ℕ, r.Prime → r ∣ P → r < lowE (lnum l) (lden l) m)
    (hc1 : strip (geom p k) (2 :: l.map Ent.p) ≠ 1)
    (hcase : j = 0 ∨ strip (geom p k) (2 :: l.map Ent.p) < lowE (lnum l) (lden l) m ∨
      1 < Nat.gcd (strip (geom p k) (2 :: l.map Ent.p)) P) : False := by
  set c := strip (geom p k) (2 :: l.map Ent.p) with hcdef
  have hc0 : 0 < c := Nat.pos_of_ne_zero (strip_ne_zero _ _ (geom_pos _ _).ne')
  have hr := Nat.minFac_prime hc1
  obtain ⟨hrN, hrl⟩ := cof_prime H hpl hk hr (Nat.minFac_dvd c)
  have hlo := lowE_le H hrN hrl
  rcases hcase with hj | hlt | hg
  · subst hj; exact hrl (mem_of_holds_zero H hrN)
  · have := Nat.minFac_le hc0; omega
  · have hg1 : Nat.gcd c P ≠ 1 := by omega
    have hr' := Nat.minFac_prime hg1
    have hd' := Nat.minFac_dvd (Nat.gcd c P)
    obtain ⟨hrN', hrl'⟩ := cof_prime H hpl hk hr' (hd'.trans (Nat.gcd_dvd_left c P))
    have hlo' := lowE_le H hrN' hrl'
    have := hP _ hr' (hd'.trans (Nat.gcd_dvd_right c P))
    omega

/-- The chain test of a node. -/
private theorem deadC_sound (H : Holds N l j m) {P : ℕ}
    (hP : ∀ r : ℕ, r.Prime → r ∣ P → r < lowE (lnum l) (lden l) m)
    (hd : deadC j (lowE (lnum l) (lden l) m) P (chainList l) = true) : False := by
  obtain ⟨c, hc, hcase⟩ := (deadC_iff _ _ _ _).mp hd
  obtain ⟨e, he, hex, rfl, hc1⟩ := mem_chainList hc
  exact cof_dead H (List.mem_map_of_mem he) ((H.2.2.1 e he).2.2 hex) hP hc1 hcase

private theorem oddOther_iff (p : ℕ) : ∀ l : List Ent, oddOther l p = true ↔
    ∃ b ∈ l, b.ex = true ∧ b.k % 2 = 1 ∧ b.p ≠ p
  | [] => by simp [oddOther]
  | b :: t => by
    show ((b.ex && Nat.beq (Nat.mod b.k 2) 1 && !Nat.beq b.p p) || oddOther t p) = true ↔ _
    rw [Bool.or_eq_true, oddOther_iff p t]
    simp [beq_false_iff, and_assoc]

private theorem parAux_iff (L : List Ent) : ∀ l' : List Ent, parAux L l' = true ↔
    ∃ a ∈ l', a.ex = true ∧ a.k % 2 = 1 ∧ oddOther L a.p = true
  | [] => by simp [parAux]
  | a :: t => by
    show ((a.ex && Nat.beq (Nat.mod a.k 2) 1 && oddOther L a.p) || parAux L t) = true ↔ _
    rw [Bool.or_eq_true, parAux_iff L t]
    simp [and_assoc]

/-- Two exact entries with odd exponents contradict Euler's theorem. -/
private theorem odd_pair_false (H : Holds N l j m) {a b : Ent} (ha : a ∈ l) (hb : b ∈ l)
    (hak : N.factorization a.p % 2 = 1) (hbk : N.factorization b.p % 2 = 1) (hab : b.p ≠ a.p) :
    False := by
  obtain ⟨q, -, hu⟩ := existsUnique_odd_exponent H.1
  have h1 := hu a.p ⟨prime_of_holds H a ha, Nat.odd_iff.mpr hak⟩
  have h2 := hu b.p ⟨prime_of_holds H b hb, Nat.odd_iff.mpr hbk⟩
  exact hab (h2.trans h1.symm)

private theorem parC_sound (H : Holds N l j m) (hd : parC l = true) : False := by
  obtain ⟨a, ha, hax, hak, ho⟩ := (parAux_iff l l).mp hd
  obtain ⟨b, hb, hbx, hbk, hab⟩ := (oddOther_iff _ _).mp ho
  exact odd_pair_false H ha hb (by rw [(H.2.2.1 a ha).2.2 hax]; exact hak)
    (by rw [(H.2.2.1 b hb).2.2 hbx]; exact hbk) hab

private theorem firstForce_spec (lo Y Q : ℕ) : ∀ (cs : List ℕ) (c : ℕ),
    firstForce lo Y Q cs = c + 1 → c + 1 ∈ cs ∧ forceOK lo Y Q (c + 1) = true
  | [], c, h => by simp [firstForce] at h
  | d :: cs, c, h => by
    change cond (forceOK lo Y Q d) d (firstForce lo Y Q cs) = c + 1 at h
    cases hd : forceOK lo Y Q d
    · rw [hd] at h
      obtain ⟨h1, h2⟩ := firstForce_spec lo Y Q cs c h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rw [hd] at h
      change d = c + 1 at h
      subst h
      exact ⟨by simp, hd⟩

/-- A forced cofactor is prime. -/
private theorem force_prime {Y Q : ℕ} (H : Holds N l j m) (hQ : QGood Y Q) {c : ℕ}
    (hc : c ∈ chainList l) (hf : forceOK (lowE (lnum l) (lden l) m) Y Q c = true) : c.Prime := by
  by_contra hnp
  have hc0 := chain_pos hc
  have hc1 : c ≠ 1 := (mem_chainList hc).choose_spec.2.2.2
  have hr := Nat.minFac_prime hc1
  obtain ⟨-, -, hlo⟩ := chain_factor H hc hr (Nat.minFac_dvd c)
  have hsq := Nat.minFac_sq_le_self hc0 hnp
  simp only [forceOK, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    Nat.mul_eq, Nat.succ_eq_add_one] at hf
  rcases hf with hf | ⟨hf, hg⟩
  · have : lowE (lnum l) (lden l) m * lowE (lnum l) (lden l) m ≤ c.minFac ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul hlo hlo
    omega
  · have hY : c.minFac ≤ Y := by
      by_contra hY
      have : (Y + 1) * (Y + 1) ≤ c.minFac ^ 2 := by
        rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
      omega
    have h1 := Nat.dvd_gcd (Nat.minFac_dvd c) (hQ _ hr hY)
    rw [hg] at h1
    exact hr.one_lt.ne' (Nat.dvd_one.mp h1)

private theorem valid_fact (h : OddPerfect N) {p : ℕ} (hp : p.Prime) :
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
    · exact absurd (show f = k + 1 by omega ▸ hf) h

/-- A skipped exact exponent is not the exponent of `N`. -/
private theorem adv_skip (H : Holds N l j m) {e : Ent} (he : e ∈ l) {P k : ℕ}
    (hP : ∀ r : ℕ, r.Prime → r ∣ P → r < lowE (lnum l) (lden l) m)
    (hd : advDeadC l j (lowE (lnum l) (lden l) m) P e.p k
      (strip (geom e.p k) (2 :: l.map Ent.p)) = true) : N.factorization e.p ≠ k := by
  intro hk
  have hpl : e.p ∈ l.map Ent.p := List.mem_map_of_mem he
  simp only [advDeadC, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq,
    Nat.blt_eq, natMod] at hd
  rcases hd with ⟨hc1, hcase⟩ | ⟨hk2, ho⟩
  · exact cof_dead H hpl hk hP (beq_false_iff.mp hc1) (by simpa [or_assoc] using hcase)
  · obtain ⟨b, hb, hbx, hbk, hbp⟩ := (oddOther_iff _ _).mp ho
    exact odd_pair_false H he hb (by rw [hk]; exact hk2) (by rw [(H.2.2.1 b hb).2.2 hbx]; exact hbk)
      hbp

/-- The split exponent stays at most the exponent of `N`. -/
private theorem advR_le (H : Holds N l j m) {e : Ent} (he : e ∈ l) {P : ℕ}
    (hP : ∀ r : ℕ, r.Prime → r ∣ P → r < lowE (lnum l) (lden l) m) :
    ∀ n k, k ≤ N.factorization e.p →
      advR l j (lowE (lnum l) (lden l) m) P e.p (2 :: psR l) n k ≤ N.factorization e.p
  | 0, k, hk => hk
  | n + 1, k, hk => by
    have hl2 := two_le_of_holds H
    have hps : ∀ y ∈ 2 :: psR l, 2 ≤ y := by
      intro y hy
      rw [psR_eq] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact le_rfl
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hl2 x hx
    show cond (advDeadC l j _ P e.p k (stripR (geomN e.p k) (2 :: psR l)))
      (advR l j _ P e.p (2 :: psR l) n (nextValidR e.p k)) k ≤ _
    rw [stripR_eq _ _ hps, geomN_eq (hl2 e he), psR_eq]
    cases hd : advDeadC l j (lowE (lnum l) (lden l) m) P e.p k
      (strip (geom e.p k) (2 :: l.map Ent.p))
    · exact hk
    · have hne := adv_skip H he hP hd
      rw [← psR_eq]
      apply advR_le H he hP n
      rw [nextValidR_eq]
      exact nextValid_le (by omega) (valid_fact H.1 (prime_of_holds H e he))

private theorem replP_map {p : ℕ} {x : Ent} (hx : x.p = p) : ∀ l : List Ent,
    (replP l p x).map Ent.p = l.map Ent.p
  | [] => rfl
  | a :: t => by
    show (cond (Nat.beq a.p p) (x :: replP t p x) (a :: replP t p x)).map Ent.p = _
    cases h : Nat.beq a.p p
    · simp [replP_map hx t]
    · have : a.p = p := by simpa using h
      simp [replP_map hx t, hx, this]

private theorem replP_mem {p : ℕ} {x y : Ent} : ∀ l : List Ent, y ∈ replP l p x → y = x ∨ y ∈ l
  | [], h => by simp [replP] at h
  | a :: t, h => by
    change y ∈ cond (Nat.beq a.p p) (x :: replP t p x) (a :: replP t p x) at h
    cases hc : Nat.beq a.p p <;> rw [hc] at h <;> simp only [cond_true, cond_false] at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (by simp)
      · rcases replP_mem t h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl rfl
      · rcases replP_mem t h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem replP_self {p : ℕ} {x : Ent} : ∀ l : List Ent, p ∉ l.map Ent.p → replP l p x = l
  | [], _ => rfl
  | a :: t, h => by
    show cond (Nat.beq a.p p) (x :: replP t p x) (a :: replP t p x) = a :: t
    have hne : a.p ≠ p := fun e => h (by simp [e])
    rw [beqF hne, replP_self t (fun h' => h (List.mem_cons_of_mem _ h'))]
    rfl

private theorem holds_replP (H : Holds N l j m) {p : ℕ} {x : Ent} (hx : x.Holds N) (hxp : x.p = p) :
    Holds N (replP l p x) j m := by
  obtain ⟨h, hnd, hent, hcard, hbig⟩ := H
  have hmap := replP_map hxp l
  have hlen : (replP l p x).length = l.length := by
    rw [← List.length_map (f := Ent.p), hmap, List.length_map]
  refine ⟨h, hmap ▸ hnd, ?_, by rw [hlen]; exact hcard, fun q hq hn => hbig q hq (hmap ▸ hn)⟩
  intro e he
  rcases replP_mem l he with rfl | he
  · exact hx
  · exact hent e he

private theorem pickR_aux (T : ℕ) : ∀ (l : List Ent) (be : Ent) (bn bd : ℕ),
    pickAuxR T l be bn bd ∈ l ∨ pickAuxR T l be bn bd = be
  | [], _, _, _ => Or.inr rfl
  | e :: t, be, bn, bd => by
    show cond _ (pickAuxR T t e _ _) (pickAuxR T t be bn bd) ∈ e :: t ∨
      cond _ (pickAuxR T t e _ _) (pickAuxR T t be bn bd) = be
    generalize (!e.ex && (Nat.beq T 0 || Nat.blt (Nat.pow e.p e.k) T) &&
          Nat.blt (Nat.mul bn (Nat.mul (Nat.sub e.p 1) (geomN e.p e.k)))
            (Nat.mul (Nat.mul e.p (Nat.pow e.p e.k)) bd)) = c
    cases c
    · simp only [cond_false]
      rcases pickR_aux T t be bn bd with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
    · simp only [cond_true]
      rcases pickR_aux T t e (Nat.mul e.p (Nat.pow e.p e.k))
          (Nat.mul (Nat.sub e.p 1) (geomN e.p e.k)) with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · left; rw [h]; exact List.mem_cons_self

private theorem pickR_mem (l : List Ent) (T : ℕ) : pickR l T ∈ l ∨ pickR l T = ⟨0, 0, true⟩ :=
  pickR_aux T l _ _ _

/-- A split: one of the two children holds. -/
private theorem splitR_sound (H : Holds N l j m) {rec : List Ent → ℕ → ℕ → Bool}
    (hrec : ∀ l', rec l' j m = true → ¬ Holds N l' j m) {P : ℕ}
    (hP : ∀ r : ℕ, r.Prime → r ∣ P → r < lowE (lnum l) (lden l) m) {e : Ent}
    (he : e ∈ l ∨ e = ⟨0, 0, true⟩)
    (hs : splitR rec l j m (lowE (lnum l) (lden l) m) P e = true) : False := by
  unfold splitR splitK at hs
  rw [Bool.and_eq_true] at hs
  obtain ⟨h1, h2⟩ := hs
  rcases he with he | rfl
  · have hE := H.2.2.1 e he
    have hle := advR_le H he hP 20 e.k hE.2.1
    generalize advR l j (lowE (lnum l) (lden l) m) P e.p (2 :: psR l) 20 e.k = k at h1 h2 hle
    by_cases hka : N.factorization e.p = k
    · exact hrec _ h1 (holds_replP H ⟨hE.1, hle, fun _ => hka⟩ rfl)
    · rw [nextValidR_eq] at h2
      refine hrec _ h2 (holds_replP H ⟨hE.1, ?_, fun h => by simp at h⟩ rfl)
      show nextValid e.p k ≤ N.factorization e.p
      exact nextValid_le (by omega) (valid_fact H.1 (prime_of_holds H e he))
  · have h0 : (0 : ℕ) ∉ l.map Ent.p := by
      intro h0
      obtain ⟨x, hx, hx0⟩ := List.mem_map.mp h0
      have := two_le_of_holds H x hx; omega
    rw [replP_self l h0] at h1
    exact hrec _ h1 H

private theorem enumR_spec {rec : List Ent → ℕ → ℕ → Bool} {l : List Ent} {j' X P : ℕ} :
    ∀ n q0, enumR rec l j' X P n q0 = true → ∀ q, q0 ≤ q → q < q0 + n →
      candQ l X P q = true → rec (⟨q, kminR q, false⟩ :: l) j' q = true
  | 0, q0, _, q, h1, h2, _ => by omega
  | n + 1, q0, h, q, h1, h2, hc => by
    change ((!candQ l X P q0 || rec (⟨q0, kminR q0, false⟩ :: l) j' q0) &&
      enumR rec l j' X P n (q0 + 1)) = true at h
    rw [Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rw [hc, Bool.not_true, Bool.false_or] at h; exact h.1
    · exact enumR_spec n (q0 + 1) h.2 q hlt (by omega) hc

private theorem solve_one_full (hall : allEx l = true) (hne : lnum l ≠ 2 * lden l) :
    OmegaSixSearch.solve 1 l 0 m = true := by
  simp [OmegaSixSearch.solve, hall, hne]

private theorem solve_one_ufull (hall : allEx l = false) (hu : unum l ≤ 2 * uden l) :
    OmegaSixSearch.solve 1 l 0 m = true := by
  simp [OmegaSixSearch.solve, hall, hu]

end Sound
/-! ### Soundness of the search -/

section Main

variable {N : ℕ}

/-- One node of the search is sound, given that the recursive calls are. -/
private theorem nodeA_sound {lad : List (ℕ × ℕ)} {Y Q T : ℕ} (hlad : LadGood lad) (hQ : QGood Y Q)
    {rec : List Ent → ℕ → ℕ → Bool} (hrec : ∀ l j m, rec l j m = true → ∀ N, ¬ Holds N l j m)
    {l : List Ent} {j m : ℕ} (H : Holds N l j m)
    (h : nodeA lad rec Y Q T l j m (lnumR l) (ldenR l) (unumR l) (udenR l) = true) : False := by
  have hl2 := two_le_of_holds H
  rw [lnumR_eq hl2, ldenR_eq, unumR_eq hl2, udenR_eq] at h
  unfold nodeA nodeB nodeC at h
  rw [chainR_eq hl2] at h
  have hP := pickP_zero_good hlad (lowE (lnum l) (lden l) m)
  have hlo1 : m + 1 ≤ lowE (lnum l) (lden l) m := by
    unfold lowE
    cases Nat.blt (lnum l) (Nat.mul 2 (lden l))
    · exact le_rfl
    · show m + 1 ≤ maxN (m + 1) _
      rw [maxN_eq]; exact le_max_left _ _
  have hPm : ∀ r : ℕ, r.Prime → r ∣ (pickP lad (Nat.succ m) (0, 1)).2 →
      r < lowE (lnum l) (lden l) m :=
    fun r hr hd => lt_of_lt_of_le (pickP_zero_good hlad (m + 1) r hr hd) hlo1
  simp only [Bool.or_eq_true] at h
  rcases h with ((habund | hpar) | hdead) | hD
  · have hd : deadAbund l j = true := by
      simpa [deadAbund, bltD, bleD] using habund
    exact solve_sound 1 l j m (solve_one_of_abund hd) H
  · exact parC_sound H hpar
  · exact deadC_sound H hP hdead
  · cases j with
    | zero =>
      change cond (allExR l) (!Nat.beq (lnum l) (Nat.mul 2 (lden l)))
        (Nat.ble (unum l) (Nat.mul 2 (uden l)) ||
          splitR rec l 0 m _ (pickP lad (Nat.succ m) (0, 1)).2 (pickR l 0)) = true at hD
      rw [allExR_eq] at hD
      cases hall : allEx l
      · rw [hall] at hD
        simp only [cond_false, Bool.or_eq_true] at hD
        rcases hD with hu | hs
        · exact solve_sound 1 l 0 m (solve_one_ufull hall (by simpa using hu)) H
        · exact splitR_sound H (fun l' h' => hrec l' 0 m h' N) hPm (pickR_mem l 0) hs
      · rw [hall] at hD
        simp only [cond_true, Bool.not_eq_true', Nat.mul_eq] at hD
        exact solve_sound 1 l 0 m (solve_one_full hall (beq_false_iff.mp hD)) H
    | succ j' =>
      change nodeE rec T l j' m (unum l) (uden l) (lowE (lnum l) (lden l) m)
        (pickP lad (lowE (lnum l) (lden l) m) (0, 1)).1
        (pickP lad (lowE (lnum l) (lden l) m) (0, 1)).2 (pickP lad (Nat.succ m) (0, 1)).2
        (chainList l) (firstForce (lowE (lnum l) (lden l) m) Y Q (chainList l)) = true at hD
      cases hf : firstForce (lowE (lnum l) (lden l) m) Y Q (chainList l) with
      | succ c =>
        rw [hf] at hD
        change rec (⟨c + 1, kminR (c + 1), false⟩ :: l) j' m = true at hD
        obtain ⟨hc, hok⟩ := firstForce_spec _ _ _ _ _ hf
        have hcp := force_prime H hQ hc hok
        obtain ⟨hcN, hcl, -⟩ := chain_factor H hc hcp dvd_rfl
        have H' := holds_cons H hcN hcl
        rw [kminR_eq] at hD
        exact hrec _ _ _ hD N H'
      | zero =>
        rw [hf] at hD
        change nodeF rec T l j' m (lowE (lnum l) (lden l) m)
          (pickP lad (lowE (lnum l) (lden l) m) (0, 1)).1
          (pickP lad (lowE (lnum l) (lden l) m) (0, 1)).2 (pickP lad (Nat.succ m) (0, 1)).2
          (boundsR (unum l) (uden l) (Nat.succ j') m (chainList l)) = true at hD
        rw [boundsR_eq] at hD
        have hsplit : ∀ T', splitR rec l (j' + 1) m (lowE (lnum l) (lden l) m)
            (pickP lad (Nat.succ m) (0, 1)).2 (pickR l T') = true → False :=
          fun T' hs => splitR_sound H (fun l' h' => hrec l' _ m h' N) hPm (pickR_mem l T') hs
        cases hb : bounds l (j' + 1) m with
        | nil =>
          rw [hb] at hD
          change (!allExR l && splitR rec l (Nat.succ j') m _ _ (pickR l 0)) = true at hD
          rw [Bool.and_eq_true] at hD
          exact hsplit 0 hD.2
        | cons b bs =>
          rw [hb] at hD
          change nodeG rec T l j' m (lowE (lnum l) (lden l) m)
            (pickP lad (lowE (lnum l) (lden l) m) (0, 1)).1
            (pickP lad (lowE (lnum l) (lden l) m) (0, 1)).2 (pickP lad (Nat.succ m) (0, 1)).2
            (minR (b :: bs)) = true at hD
          rw [minR_eq, ← hb] at hD
          unfold nodeG at hD
          cases hh : (Nat.ble 1 j' && Nat.ble j' 8 && lowInexact l T &&
              !Nat.ble (minB (bounds l (j' + 1) m)) (Nat.add (lowE (lnum l) (lden l) m) 10))
          · rw [hh] at hD
            simp only [cond_false] at hD
            cases he : (Nat.ble (minB (bounds l (j' + 1) m)) (Nat.add (lowE (lnum l) (lden l) m) 10)
                || allExR l || Nat.ble 1 j')
            · rw [he] at hD
              simp only [cond_false, Bool.and_eq_true] at hD
              exact hsplit 0 hD.2
            · rw [he] at hD
              simp only [cond_true] at hD
              obtain ⟨q, -, hqB, hqp, H'⟩ := enum_sound H (by omega) (by rw [hb]; simp)
              have H'' := holds_cons_of_append H'
              have hqN : q ∈ N.primeFactors := (H''.2.2.1 ⟨q, kmin q, false⟩ List.mem_cons_self).1
              have hql : q ∉ l.map Ent.p := (List.nodup_cons.mp H''.2.1).1
              have hlo := lowE_le H hqN hql
              have hq := Nat.prime_of_mem_primeFactors hqN
              have hcand : candQ l (pickP lad (lowE (lnum l) (lden l) m) (0, 1)).1
                  (pickP lad (lowE (lnum l) (lden l) m) (0, 1)).2 q = true := by
                simp only [candQ, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                  Nat.beq_eq]
                refine ⟨⟨?_, ?_⟩, Or.inr hqp⟩
                · cases hl : listedR l q
                  · rfl
                  · exact absurd ((listedR_iff q).mp hl) hql
                · rcases Nat.coprime_or_dvd_of_prime hq
                    (pickP lad (lowE (lnum l) (lden l) m) (0, 1)).2 with hc | hc
                  · exact hc
                  · have := hP q hq hc; omega
              have hr := enumR_spec _ _ hD q hlo (by simp only [Nat.sub_eq, Nat.succ_eq_add_one]; omega) hcand
              rw [kminR_eq] at hr
              exact hrec _ _ _ hr N H''
          · rw [hh] at hD
            simp only [cond_true] at hD
            exact hsplit T hD

/-- Soundness of the search: if it returns `true` on a state, no number satisfies the state. -/
theorem solve_sound' {lad : List (ℕ × ℕ)} {Y Q : ℕ} (hlad : LadGood lad) (hQ : QGood Y Q)
    (T : ℕ) : ∀ (f : ℕ) (l : List Ent) (j m : ℕ), solve lad Y Q T f l j m = true →
      ∀ N, ¬ Holds N l j m := by
  intro f
  induction f with
  | zero => intro l j m h; exact absurd h (by simp [solve])
  | succ f ih =>
    intro l j m h N H
    exact nodeA_sound hlad hQ ih H h

end Main
/-! ### Tables -/

/-- Sieve: from `acc`, multiply in every `r, r + 1, ..., r + n - 1` coprime to the product so
far. Started at `r = 2`, `acc = 1`, it computes the product of the primes below `n + 2`. -/
def sieveR (n r acc : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih r acc => cond (Nat.beq (Nat.gcd r acc) 1) (ih (Nat.succ r) (Nat.mul acc r))
      (ih (Nat.succ r) acc)) n r acc

private theorem sieveR_acc : ∀ n r acc, acc ∣ sieveR n r acc
  | 0, _, _ => dvd_rfl
  | n + 1, r, acc => by
    change acc ∣ cond (Nat.beq (Nat.gcd r acc) 1) (sieveR n (r + 1) (acc * r))
      (sieveR n (r + 1) acc)
    cases Nat.beq (Nat.gcd r acc) 1
    · exact sieveR_acc n (r + 1) acc
    · exact (Dvd.intro r rfl).trans (sieveR_acc n (r + 1) (acc * r))

private theorem sieveR_factor : ∀ n r acc, 1 ≤ r → ∀ p : ℕ, p.Prime → p ∣ sieveR n r acc →
    p ∣ acc ∨ p < r + n
  | 0, _, _, _, _, _, h => Or.inl h
  | n + 1, r, acc, hr, p, hp, h => by
    change p ∣ cond (Nat.beq (Nat.gcd r acc) 1) (sieveR n (r + 1) (acc * r))
      (sieveR n (r + 1) acc) at h
    cases hc : Nat.beq (Nat.gcd r acc) 1 <;> rw [hc] at h
    · rcases sieveR_factor n (r + 1) acc (by omega) p hp h with h | h
      · exact Or.inl h
      · right; omega
    · rcases sieveR_factor n (r + 1) (acc * r) (by omega) p hp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact Or.inl h
        · right; have := Nat.le_of_dvd (by omega) h; omega
      · right; omega

private theorem sieveR_prime : ∀ n r acc (p : ℕ), p.Prime → r ≤ p → p < r + n → p ∣ sieveR n r acc
  | 0, _, _, _, _, h1, h2 => by omega
  | n + 1, r, acc, p, hp, h1, h2 => by
    change p ∣ cond (Nat.beq (Nat.gcd r acc) 1) (sieveR n (r + 1) (acc * r))
      (sieveR n (r + 1) acc)
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · cases hc : Nat.beq (Nat.gcd r acc) 1
      · have hg : Nat.gcd r acc ≠ 1 := beq_false_iff.mp hc
        rcases Nat.coprime_or_dvd_of_prime hp acc with h | h
        · exact absurd h hg
        · exact h.trans (sieveR_acc n (r + 1) acc)
      · exact (Dvd.intro_left acc rfl).trans (sieveR_acc n (r + 1) (acc * r))
    · cases Nat.beq (Nat.gcd r acc) 1
      · exact sieveR_prime n (r + 1) acc p hp hlt (by omega)
      · exact sieveR_prime n (r + 1) (acc * r) p hp hlt (by omega)

/-- Every prime factor of `P` is at most `X`. -/
def EntGood (X P : ℕ) : Prop := ∀ r : ℕ, r.Prime → r ∣ P → r ≤ X

theorem entGood_one : EntGood 1 1 := fun r hr hd =>
  absurd (Nat.le_of_dvd one_pos hd) (by have := hr.two_le; omega)

/-- A sieve step from a certified entry `(Y, Py)` certifies `(X, P)`. -/
theorem entGood_step {Y Py X P : ℕ} (hY : EntGood Y Py) (hYX : Y ≤ X)
    (h : Nat.beq (sieveR (X - Y) (Y + 1) Py) P = true) : EntGood X P := by
  intro r hr hd
  rw [← (Nat.beq_eq ▸ h : sieveR (X - Y) (Y + 1) Py = P)] at hd
  rcases sieveR_factor _ _ Py (by omega) r hr hd with h1 | h1
  · exact (hY r hr h1).trans hYX
  · omega

/-- A table `Q` certified by the sieve. -/
private theorem qGood_of {Y Q : ℕ} (hY : 1 ≤ Y) (h : Nat.beq (sieveR (Y - 1) 2 1) Q = true) :
    QGood Y Q := by
  intro r hr hrY
  rw [← (Nat.beq_eq ▸ h : sieveR (Y - 1) 2 1 = Q)]
  exact sieveR_prime _ 2 1 r hr hr.two_le (by omega)

/-- The product of the primes up to `2` (script `gen_tables.py`). -/
def L1 : ℕ := 2

/-- The product of the primes up to `4` (script `gen_tables.py`). -/
def L2 : ℕ := 6

/-- The product of the primes up to `8` (script `gen_tables.py`). -/
def L3 : ℕ := 210

/-- The product of the primes up to `16` (script `gen_tables.py`). -/
def L4 : ℕ := 30030

/-- The product of the primes up to `32` (script `gen_tables.py`). -/
def L5 : ℕ := 200560490130

/-- The product of the primes up to `64` (script `gen_tables.py`). -/
def L6 : ℕ := 117288381359406970983270

/-- The product of the primes up to `128` (script `gen_tables.py`). -/
def L7 : ℕ := 4014476939333036189094441199026045136645885247730

/-- The product of the primes up to `256` (script `gen_tables.py`). -/
def L8 : ℕ := 64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230

/-- The product of the primes up to `512` (script `gen_tables.py`). -/
def L9 : ℕ := 31964081287196888554640742530273949712805599189441373009521636182430667982828077742788853029807931798207106885718293402541861369758591699412090677759187666930105491469725350718941073722934985042092154205321144030

/-- The product of the primes up to `1024` (script `gen_tables.py`). -/
def L10 : ℕ := 20832554441869718052627855920402874457268652856889007473404900784018145718728624430191587286316088572148631389379309284743016940885980871887083026597753881317772605885038331625282052311121306792193540483321703645630071776168885357126715023250865563442766366180331200980711247645589424056809053468323906745795726223468483433625259000887411959197323973613488345031913058775358684690576146066276875058596100236112260054944287636530

/-- The product of the primes up to `2048` (script `gen_tables.py`). -/
def L11 : ℕ := 19715709508360953114374661372140832573527668916105872794926333060297871449651734582409991668843441820266278378118728485148168052527337670919674223469012969178672977227072795398306263493830356381829963553984977106476223553289236874490965490814683907479774989742598973059492724655933525009014366770606113797909787756429946279379148422779873023509692425578789431844457340362331184484513003069790241825471100067435615791316203952602424495432459080705440658240652502007397553198195118594362221080000427604407098288753451636312836956904634164235592657407712347190431248214702715894315629036857892557110457128346323257946583100638693178044822811318079790804932655795200315297303921003642387711141261860563345607520337980150595956420269786329953669494070024182468864254588770792312987994835613679486548183532710482875782243678422568782859055176331229157823021755575280190

/-- The product of the primes up to `4096` (script `gen_tables.py`). -/
def L12 : ℕ := 1203914594293071947027859878588534472710996843355561850008714936932493122716058548993681173695214007103209640253414271055512275013812954973284983748123889548756867132787002962025393760304108479036240027207974200954446015030713121721243894717674810318073260170091267295656918827216831511361604639538713700822981636245151463207541784909327485329149774091398436645530969812113940049385388758729878655956582822688730136895519226934682254377010799453120336612037247767859331311284957451163389106480393405712715976385749209909249159316540861734793182311253035165594833153385348300441152504290832724153505048124175621107035375435262770194816302091434597711666798897674364261583030107119033138212110956062888666113566783294152431824045531848558046621648807342973220362317375323219496422314824084846622503125154821026247955026662525482755381826272358269469160145068062455724356876533304403463637906391633612222610863145441779899494959630077492123499253599733489847429144788640200992682192404085835653560292502805178604325584812465701837943420761452535692233224879813968943516869212625984782664303785176111487814414757602918732692756244537976752509560706440586112581760113922696175340682657545311951868927766672143299915528080417165822902526811292288168986895072939171876177359720739881760245963313420929915871477959173502859145145471669357495827273283672758028500165371848642604827171256762148357097918430088955731073776960447076634186306738209760103349302030423090436147097180660135306558298332952255202815029248435980640982412467393370803158427382465041038794618973312066730307466724656856504254334276221965307101039125575493234571983245748615492409025401499971934486222185720070988132252215199568024119074497556388084447761509381108623156788854266062940790

/-- The product of the primes up to `8192` (script `gen_tables.py`). -/
def L13 : ℕ := 16255178265053877384476057227203628360596426037712774238424901128382017272219718481680189944001603471361614497372026729071330276912666363905596937518451126264972166011215972518559136741738897083235675474633868732995335758866861881163272621901774166694814870499590268768968879145866618265294908328048113038869956550810611564107105605254604030808978555419838586876734612530993245604520077477858923073371640650665958734995577575314691979535074165021966765788768541058686364449086549124285976623209800850818847019225689360302265339395286248947605587045759434740073815282762189528414642504325605258289017326737679479990447260662939568930356828898799801647788083107178503742043976388972409835326468665417347658330163101456059365867331563801537462941685419893087707841254162921593613458604254612933964356300319288272776886587522371491308172906302038530486868082642950736829404992163662386988338568594329153458366132216390288298553213377389661351859584498644023931367739939674166403623325502067183846343629783651668929439887137020271570745611693110128996936952901897797159691665592631415531720210670582235794632053040945388096911228491550318039769504381975888755388432712659174066991213500517981813858989891897157745845267754190409169624829943727380155411917553612104019794378090124209597839277942193194598065201765781835968137879748000120393702721235572023796950662531803202935629184807053110378168317417682544516947721446491933324718474306684593011184736424097521846845138717107687104317495106765982941270054059761630950806097626439061696535501990066206453115955157514128671355118122714667438226942214955830541816620531067132522842907031465554017639496189289065899219793121626770457387105917377982731476348097083815709107484265710980565777236399104537865740351479267529615464505935271771997054365397019968177584200153592841649549373019524975351033560635001313054382445406358946736336819539068781450641914321187111958007863012829683076030767536938852214813317547870487964376903074285610560893230570665753348322493277432676481958657366185328074024907316968260695405502183553266811407879635266685429868894808136357932080246516714012606646316036916104315572111849176810796651720756120619468564791066810993618401839920064015042687995052187760241651508318572750675783064422411292927360618268844539118675316874865174360542447454584126237161412776127380324165951338325247226202212446423012582191528575321784117520230880388631228840165858563091023244864638851277814112751018782589055988345739237020951050218598888227833540010861599458893312578411457219026794056059197902656042194910219620637249105638327388342489041686681179980011859025368822604399806811534335486244738477024671776834662085994389150996627532935296047233514106131891076500508563985803602955458864466773912863370462608437306709273873707446148287830072103827576762937763360669584655797918069727017050331462505290184616306726894376828381198026409151185939162154691298356758070101783073039865184250604512019248733601709724912114448481184011039949291166425404786230718331247891911805125193879073101221707971734501593011162285929335931904039292661800813826651321625084468171508501867827160832607679511473282258856724826178724246868776920970482596550443277328522413635502598663652248369343022592222713629659282806128273654229865485861315089469126983291209348314202417004645676220196954138466343596836847312709608667801185237001319385724657760263230183318266553836195685030467438807572622451027429885228383543608531294475879343639676125007180695485871042482210

/-- The product of the primes up to `16384` (script `gen_tables.py`). -/
def L14 : ℕ := 3126264614264423984510948012165371829813506977707636184734915655275234754050978322149794800222250253117891792946422409650042085491858804614371183481926187941837978720503250160769805618075243231534016811153175676303309506091917101911472463045634738380129232160224803254274725975034737837471263775250222065704069320441014364649112566905569145427456200426496913380198797919909148513949297629511523781151617240288755050813674739062101007142325953196455556484118090916168260591811166364277490424120374002836390268208284528104485343475133897914970316030539480402237823284078461977256270195674657497638674069141795739125397411547163485078057138019104603861734378366976363629047808515296234334807119755284336993190772042073583601209478728228762606028316858422227339841493648464405190854835344569913318743735541949319612956005960106174973652671825870621287073592515520846491234018733466971533169707017784925131959804509164127584609819661341882208736951123875758768299481468279912009529332800040790313464263777261100198871248201822021662893756220114145882646712475220374101100207051499936003946507418700792126717592590756442884270834333105238147175589814755338042974228095919016926844894425229564553177140266234404709212417606309285903330101775810071692596574886727804035521288848347066748367947919109612346931574784234195752640791753457744090615474020494366921812118583664063833842942393783030608381543882253903873387894303323816299341669823556218881081950796074019086586131266407021075526875383362628355418681854720485622884677894662277237043412990235853519239713467545504273362206870047159650674606505308093660173375523695921639489874685148449747123531272126936440778930276877047693093283935761047444432764294183965328618136917524751547474953117798121821759207790167004380840687186444274781573609474941709969482413942205959043712833979682980125281703398446013411987169740889386641179217060728327017134763580481264523019298402448596201954078899660023311705053539775211522698790664762532862665516125369424079861382862914351192561444684121912023592522986716972139249730860278443475896273513885890963000723589878261853611305663803994771086811353531070113331475699681877713440965913809184483271834467012223944662108762729064229714515873028480090956944164009926466605508728150012158775754093593393603622318495565410065617220241853641891100253345606583468494131355716111310686292600776492143175881992308804283764615904043494326187275594801981065162576583051758930103160381308851265061890477464795073743991781443760820401785714018641569459392025798288010588498623307609514728413442914828883664415288581214271471475386943342691300716297262009231290472450244203415901192755675753750020063259779127473192386984246039668347225668672227294476806614648818578393564152058398235798198086657493240600610483700002779038607136046048013766185299824144295845120455070058216682446259519333349236789086490962497916335610878846678310246529676285744633577275617709011643471363083253705235455594193592381014952881919125337370663831101527792459074229443013944461075673493697658202098812839573067855617134239161793541100732635198325917369742712444975009642737195116280732877996051158001826754337110196379445147983413194598626610296838918160016938881968507147852743855431810207361862084883828256459702373231444785548601969796840982778130981474842278540672183760182713292664991979915718410551391006612928951682145311700695549330936161442131345480552881914522507643462307289174798886863339622385218436675062997165498859786733465418662246733640550435189418164694306576659352454022735456646763786426066181328857658483747736453145468182348327565713508832905199461131621161505005161326904942953536843926602116393235144383389413021242258368278840698969528417377210147583652249108624845943662808735017041481974838744950712776248489585652633903828580372043464898714150461621924393648531199264488465142988379750473981085312837613400204262125092364743473847578426462925855856543828923427113847617175741295471221606493208662010481424352482915310581854173719655598171101407847463550750219188232433545027590968662397778559420674693246385582254559105355643599296127250330374909435751701150455202006978781310841318721701660267419173429291467186532402446155724001945221020476144636093845809218098696856251466101873484114780963513881714200361406064845552789680433047641533391477820168926409504262907919389747977927992139218920289970047414729151887380009142618876558279819137139375991907859170106625417380897168494768756952183782476975077763642677256303466025935812017540131721968780130950147846325797354908935516741323572846771515166650893755392935066549952030764796119804978418345686264738963445451733144132443185365511707781905682878065612051509650684306829984351506779000295001968937884375322199914261973031009669394115682268041561736298641940846172859337805484212355684236283603669044394622080210181929785454337641254814995203796523353493557357498631800599673748631666666653760961791378301959670959493633136138462014702912040796044715006349748528028399584494745361359660872359960671877485732773517593136883344778570127724396391880864833689239288831276582141681913395107217862803268943562486557782679500023738175223251436257084893480773970209139479310185469874421379191696967779282386676227105688380786388529105510220589167150365251804769335976219842224650316476574953929884349529925520225506870363548253488957939120492744154467529249822870602269829412221714849847879348689875810022696450086437725942925177777174002954697841558301760368185858659716270645050799570347754888362587668136893776660739703433385618374540477850568099690088086097973924177064261250273326794952850213404309055453975457198261845467346223442984294890121373096500919393132843234303057094098620158435115433620114539851778832880078461652901177022467961925020558553523434999664728827395581600889054722766228375909061887928009048221521115869303138266730742681150747754433177010140862539351987595188725015966320467957701296825986155412660098302954936942287459080798071172259248055161715867650794292210885157005719598479298860290882789022220985800744043683573026950577426087211997775379386649766986356596963831171055121159659665369212634046985573043469608284899368726716656213171118898072768287790837459952253231058675989982061296663840681476074433868655488610001735745878895799492089922286563724177238027335540041748523326274616279553470883404097395965587556871777832182088803174833973475958452447785049004924161494735600418988175749449381217688162758845753598849008323699771618171943081853938155713484586335084511064907053251523138368408960526260657953859639999707936318708803099632713731837026133908208621945021314176821459606549506175406436396577902993495674724640894877297402805145745946283708555937078722049431405413076345728832220469561541491282830078608312957574769368767559693376452243924381692774782821360077553437130821487397804703011286985401014048918868229697583740537982675973471805836929227459432561616455954609248595782099283462869738303704999238532316324167328036814309215833704774299364061562825581857234264765627206162017588210

/-- The product of the primes up to `32768` (script `gen_tables.py`). -/
def L15 : ℕ := 1026908085893382159909787546924611076811433264008489592067573499469001226964801066785995318564696061455909533850372339816859104053106274946148620439102844860182636143138476311538601500311263057727618984120024462087874096184881331254555006992222008713086622530128286617304783333481752765203861183753936211735593385317227233327108474064162847620454941720700353956508609883180627667596094268338045586784797559995121385934805822299294585616952174930549553043317265762406417760810662971093535286306819812587144534932243118521694182078365244421429647627442219562866558866971472186086389567085386305956670477211124017215837246117726165537056464711249566088812454102490196908123801578957648794633084217590947299628916332692543966901785549038371237098251184652822926472965831964496875584390047392391166969549879619543776160500926789567682064145108722134053262285148311192556830922353970241890806253436115972148164269465092468743403781528901567826090658979493005005332194784283899736307510032738110525110236701840987421217932348297653679247476591734311477416301819497883829972911356746253365229640769763247851518646078004879740189193244003781796939290437795735401053817629988301919821138574467747442896771175005671699799580377080153235152381555079299715581078015877422395938235026463423404059416716330262966143406249673129003350063132110743320952149879768625125829838056783526572829125643142626657564004929634669478835943661462579126394991213866507721871570222907055377428222334976543836695452930115592678557787476379787173290259531677816566767043833138806407966984284189662696351391456872592924566486818970959381567549239785036393399414582208097000280385306446807558329797305662849245169728662626068331088639941486482356917341073452590560186505020934184505238899084539470402540302365536057049447236666185091622023326977045558422980069089216630819169299119525278294745621463087328013942392273795648002083417911357891632155457523367865255621730081436624998094322241731510230467725153238140642286770381890223329278836165329057676721215838435144477708936379534618878387541204530185668277831080377741895322217828772534625033347256059147996894585216427255458673279044446340342557128396466474567168777218119210382448957180387761736169155125728567224164039308579537427587591715983253484632878970036120683652743254047025239425922769825147557299980206287735946182044795637184081785435959972779444593019063097819610540682808787512645725056487212148571079270085890742116263168256471661011612042268389738229827597719011544196214346406550515280670718498883667859657934038317628320950942778899056835224473156781485244862152143872863576404999565027804775629219475634073673687710085973507220448620664930032846802701262903748972415471006744691268434279614158378939996055858349809444592152750435854741261589608806086960800021384129170360584428545403127745668559177873680028677522248962815457255375664162353440811619924656642791203268085328906157003109727928992420623308258897472671074523493602877227333645298465836093204217830503343036733467155743576659211395606989650341736796863263774574815982381574883459598712102803911518122807117060257287025321676184442267321412562157748811345840562249042611775547883186918793982260483379226171563756025093167948811700576307210720384238908024961982041679598353345542550858620392305832821102414471840306140327892592391314271145572971674496473077708323972123592659070003225155370522693942521619595383968972792264092306065054994255836244465123326000321602549838130394476490440156323694017674620450041366341030732769883266495366383188781996986226738797376004721746766439982636510433158114914486916986586680406155303361612875116433152458728436306376698844194220357555019160772269067459627884070217483257187412878699363969012555458082174463615909116971581486050214389437647366560879324923788735420329851204619428496941637245141096232340981148812580419290666279549366546695864540382282486449156760949782744079450986724297923918389352230909555092573614883341190160649797342034549466376912353243038046652707882160584694724754368045659009242850177162778209296448647113153197427282641539596971084665655193408240491750247778322549323155668029820380817693229758497873203294911127296074853151178544926914221449382052499800631832526848632577845988649332260687595918345094497210064745334045947529394605966836009697452953341965818573838756427154700717439336582579352911554310074132589157235984103837966987999963050696091481898804677338242528217960645456204986689467099361937850304063814190742910996936395743329727392801770476931845130565401696966857981413150870971744723052650138446120086558080338467278875172717705731054878378256327056901826107247148057214044838743182478906719581454161065851599359562404677150546377362279840295528461114485786158254524262431401437681392122286236572806124690326620305758063269034141888813512558747727466954839059760190143944516648861417934489034981469152008624904392264282040391263922829312847878712370700158704407597012813644254158947720978944040711658765171597394171759550900601577812812158211361529460842666747176811044243013427653021607579078575799911833734977524125191197415188417981457106933953295734573322877202377850922123333285095884339077674958527132008562726468598162915994419913894765642713004832575795714063482535870235767980101302421837644607588261770926783319623604360845643675749853220758255201336465454972245546860327761356822004057897913123706291678553120738446720997864825919655304801921939574355935124279780464507202078571250507285180163881778390217422288445572545507144711560446411516053785985823667473158876814559150827251725973597424316106404061298196478738359075332030558466712748179943271921463555219493927842785712828078383085358001587381252879648188190710926264942904106551202073362455790899564562445949619804392599268376201072358874196721456593922548822145030529063800233049305080426078288773338269043611873906337117094429030516386324255478833102652486105492271826105766745719022812979518891378953881231571286750691644311584177234831247314726430761050514851443226759077413993444670085043326062950908151195118750035263474860770723790630128717570351223687873506124318954256056336428132528661658244704561747518807004679889230389720660975084324971731252881058793367502859473879285695179104763358519425775379379803902871366639231766428206368711710449291695553560758875767905547493069523703651680081324224146482690449681030928265511958402348772528579753433085315671370223185088016399864809370592485947969912486463255656934098127960493703343733056434290969410166576543611233846747812563789686477056876650881877895535451366447805189206121124304396805204306378597440149784084478384183415423735264539403344397013151462671515344592220712082189676257890011527855724304366208829847374259221045539804741696721186146658583823223840930386563512604176229916913545882142451826063252667618338871803378805997869626076559393837255485879525118560311192173246122776730047100754298460574349563073495946091118157297441507760386749051022173522086650151496673358063398224646489991064265546386685484846695124596842218534210452056082888796487498450370302230813107468783416257709259238664996045680101007441378219347424874361106668422101271462143129410714245250651812391229616069118135446024329171297751916621397083666590743841218553224595321475292582206128075371011564420115614370437218551751915197758867776665291673734544322470767889951710646285422433886369449078845159926963409154227421289672768516748335928700493362053806819652272244978044945367804255677443245457763894859300502140495140373999975171407205245723441586243618248920406660055100293665064997162560877401710059618826937355391796655811473911852324302081079758605964076614115050234704038732831574407858830836276472454752839479674760424074060856713288910720624117693495670804592989185947964855185366425903591448548655731481793708542352037407473124963885101982293703131144416569151958328083260384528214263669847298437248895880183146326629569327154191774288370480611865569039778975915780593509987874274945858792847018974556201409002766061334919615357966718452849720475826607564694339236714729941781607569224211320477001428990222444579981320109221136707963830679918878617755696940767226315946082926985003054946044873213288158302400132175692064785114301596064610317473496580445134652323882345953195739767290688656739613014234059085071545464881363475366910259237429072288749781602974112919540265757010604350463480735221596445361408410687152037879049568420356976978952435808023611119309735947009381201374915257963765728137256058587907872063621418405923094688111938383556881163753586317648045501541627403315004843725428250748755717188665934937175258804461288720972731444402257251458304416084254801853080394024487837113441826160150104015478615643923556348632383215604950830491905767155918034162776400709225448553911274841554880717054838890476606857882954348986699102133492074092727261215681923907658953988225056263069851398819204050078722001320058068444411795790975106908271253842638346503659484801715926753942997509980384061531872042730656358261459207564517092464181770775690310920989858870116427373909991044152806408234254719097016021855859334851811793412748717899425126842339164747717670777649854746756112453067855713913441231146248842085853498251642121045538816201486615448198967719743303686493088330724876987394116647048539387430982649263457208443330315095568180852565744967613462017711588220255356712071445122202876121478224763924701398136356518032290402513727949964726637161394855693238800227485895745892062076510300036074126587602694145594280267945516521684641603697130148320318053331598802888472847170505359225124515144155581025569433998157745806947396177292465145715441404632647180880673402040994163535196667194256316274690039545598381387055841319928719535044533799200914115991653694240687357296456070550821416414727384989365350805324614505745958224943772554178263042809834849549145558467820605427280841617808628911746142746090687853119271245514433500855317912756798990843661093792697800731262361178155523138987561676469879290491911678680668949283603032407275270489263475427250351455426413852231738976085049208202142221550349799327392043190934827468335537974449985886040094187651086830502508547707444362516699039346298186347499912131120232372147787988816690899442177431573512163953689605755361818019288848049253769591318601135210601429481638981847111878664185728209546233834816141495705668575774821403349899465926059124475573771535144834770350464843022099896817932370514943551851097590888632860846179086571127744368853070644246013632536002711745637061730854658216368985478872777114165452534390091915440832901671981155661812944389216162979007209561212806034078349337942621612141732832633565675355221835893237694536647815162914428707498553846729757143522191637914766665999893228434328819405115634707218051644881366052093087950102455141447011022661545057387537520565280682984279765231247329082926899355749824626673189855597946980616315134889859498376592991974809378396765404490643417972121734134947333468936080181450918876368509200321796351771061998228359712439024657796408348497624159046645583834597959617269782783064145890934622609683826041364165014870302432068512285731938293578998269663730421000733887248844650064949662751709380886026390490830782386500611624617410405724902835041922591222378623916322472374499001066399725546386714218206888328646421970852026275473153322993581466580850759451211262119107253179774657180284934183374567378118228106644805965006922642872398675539667219759705660996004509705052158192917930229042409614130456613606835695195343835392927794901753760562210439074373771797680970881615820404549274534575822107759321334018835741199177492166321652156875610154315649444414078747934118100074353395324642707600648924787788608130633119187807728830783646631560018735638798259434670361636056737812245374748895633485902062963227128553443303313965291419708761030860298811153148854027236505253117367890406842890296324908159538338386711149332113508012722715748466062758802769754457700822192361349781097216931865737672957432490650672153686465760150999283074605807851595568802983655989002278907214490122782042378443898573930951140927030412402159640640187231845561689410280448272226040123291626295461615954764013910424318789025818475485447446746860341796946800800114688590831990539116400960448711603699059632888734849384971087357762660914455314223171230536931965361530603724586292613528743320126169056807940807816943543371137517534282853632399911149252430913003575416480281297970676561527698228538542104677298993205922778544522285126346891634115918041471645420310525851320706659979609611364191831309358993371136626880141549750255820540047851610778439283891159638249205567592283203248547832614804924052469317013327551829439350510247028780382670219507461947410317771203126304652432100017124174248116702492377685715827715608026990128572160398659523754372156615683054146502909456897362853292332064341655596032419200960942944164776997925265604460779374367312196926362090643937832685584490697143301781646113631407165631824577232120459669935560424412005401543437149061081466468524124900499714178945668561092652351522759018196475796035543242687117194205832373809882210353142126091055679420794243980506628306634409542517422479563030776091004261537387479271955759430461752633528113489880386932691715335149742316818880021141346527210411997300319281593648759349315128114753478099880551742697055009225405485848711468627911570585494220392314196812642836952238342651276043868005879919807361945760263959954477234092162361761599379413510429499283892810783990723287665076948355792977713891824039435954230907860347951575379837540683992664255604032660315254341294345675095910250851270425743673666250877550620835392366851092090604857623610807575475457695973425653135841834031191106593908897370217736039833556162831331006941275471089697021887813444638179642803159968333218246610147453031189943527278009828408144607736792199068046111520980176235987759507007058818093699708444769122646497835630227270684358943100188529890990945600650125045851057425001444518853795033564729152880689291943777287447770440515746929913981706700614684202917049411725218230

/-- The product of the primes up to `65536` (script `gen_tables.py`). -/
def L16 : ℕ := 664294312873588591557696282245080384613808600692072289299106734227519427216562269334647365766239130550478814511606893741397102226899229592648042029334009556195606460038548885243012915724086088933150947844648962127227057503685079074520504204641963637568361509564712554731536709093444200873839578014224997581169606987447005891344530361460695481120350492676281066779643313109845937291835830591238181827151151009778678653674198023449317675178043403160690141565712372806288424521963746776431503438964269820990956342782943941245756580810070290909721207921954876543302091151500005637335463840825814644905229649471756751774157609378642831029380081200989980353728995541571528925052067362528008067901786017910320792470370151712638151335422778326714762560890693857620024107975928964781885832717455143331405615508597701432765328412505887470069746527021920202101980042621921604651206895349245634289423213589870994260996904587945567230817159685332345157307873149533560650747529443816913977810088613335551696421967060900485074173948223212787591719152643895516542754302832861025566397679248767980266219420088389364921524056865561832550898752972463827420254261530230107015695110085159942966938284125453441755512045631601058463705839402331786978011511368593018893495969673193789487884349043804363893603032439809879528794823699444136334925932775766686462902840219206553505420500787934642762298323250592086676640222475394674271267116860123143569636394655071922810862471281342670274405520839394000581029373614876384970097679583676205241282770396713388372294002336419808334454967731304490047458465850619525334828990220030656514586982922714610380252772562653135748569019447122144172164961237868814662061782747322200821818832983236531382728161662178309119563343907186381636138067332727535000940784288177101379969575459314289879627738887094933551102262431855758698190052637562011986602071795574857043303039012474926807434439622321558963528649034285925435997441831708915415773485726592216610202570714152758526418056016320210052924093410212199195453446505961754151852060011774457149961236225092743843593049944390631939484170018037044109733742758364190603936125976650870671196062166809111303562926769367041542166826254045509351778984612311316113036931134710079520197202939872029521910739793914535494900852576235513115535205380678254679480307251516766015561622253162370971111707774400393555728035248327261471675598308082375085566624652206859385659162599560708706589313218953035895648881232468167835282942812310109644190932631317216459772285012553786651505120584093823556467259089406884580804215987672169800883405635229136692628023346037432853813750699205036645927199680972899730049233786061510506991051767522945656882092048610690370686018161946135554340718155042881568841237660787454623322527657649459803574801185536290290335300349119994684824732883661000279969799448344906653948043799692165755551821190733925750529611505079781810225445140081734860862607451848855201041443235296598763449654724274807790092660859848753247911152279717109087244465315454843071252834684645507160978263085650060942260143649007252087087535805128978768646330786459536763690151459924294540940629804851648609224178040344534198618935247234971003399865635966830179984624511507000141511833561347083906383130270583249191676236594179003054046521411052858474915669400849346802108310685936670799144910681949029403544827528870351225084740137353440618102775874749079664878862337856067677303616881465358178344303826220727210018063619605120248022656291747612076001179773701499464124912398569284842596735444087685676543348180766411961621913021801290613547627050675798613875721520337314378232164888855603985152156633162995365492424343525505160584545850917066555725654187891394643557248934242125562341297812500258976625107570954003005078964710094221537596675582449215422350113033673032302021449178312454146636551468488089554448846020015229659659125012535031334823696801414530680581877031292162021717624813609083857726832665379804087697211736196728082798252877268606854398792014447627818256914135435080802869147937186498936605413587665437694206319708734860840102992161368005469878139970614695966448362643459139734741026870821379333637514741873508643268526549390230049621554284739523981559565888380088714171424070743935802934425784977050871138890082606778867856831184727627483718457828475588931039581072518760026638403474684267559589790677695223639464661138392586948618466033541277993994432170170732988676147989110855243778319793544063046443934398759300064382143503056023724594670575516914848065409579027286596438917806270299022787187631671330373195967229372020388375954736032894605418643681648233666465483900022587964685549626653085121649784269215722370363539265551701815949145100808081546739371033735231679425973084198405370140757474797405568728635390261000361420285506786559745895776289537128532036568297140921356493641214832054120858789188923597402396811491641859042452190516144025067157829889027899893806212446820586432611396134741679937867280073191979037922395607960573228550985455116161949034680686656276778698036650418980675523924458963526663373961188436818078730574993091503591378733453477091927566930903605515852348892894322368244785224640325702228728298769204460646306299360773679636760190255412883113708371922916075381269175130281806558014693121129368998826062105026840194294760670145052955003567579381592325678974210003310584510905499233233948199003994485352256729755236197523149427182288506751320539420561438855892397327899026880420346504889193917381376567663219965664987034302057619727078592452800522469288645711228947391323760436210555285175203710334154439166491832955761218738128987172013543245811842830794301151294365193163883205838246123151349183299505510897780294653923300487243920029283388793566973043681803684534421564433320478122124334210776731222840772956021054992644215340909109144930588768397379079944174218807676647661195559728867082913826093201306627807196372037814388090767237608805211423900490148103660683504725434949294804621065002411351123155188941519337946271565900759148269714070479931958007654875996200018333522412285609348600015658908568659639651605797093913094648095300006128032468823394700675866488446601764198998854941135906257600829031038817543423714012512387403134706445546599831907947848366925768881462793505714533465140085934287153817556972979012209541725386679679467534705238992617741786573451729715208512631141479638929152245134088610842129790690654777954254122968888044232433720820658645354913014067750663734578940389806908422789535863232112670302448227390374402541792436564002238049353781067735822721158257465370774093857129867913194888402480862529300116346326410873844494013125126028948887986812840925223918190431729765779981807516721218568325029274537225593365818431346356057605076348161317939641503820032479488678594116830114490937289321850267635594909298973549485892248884363252688981942378249850615745100062739331823399505125561578978028790597055446302357223884855262903092671803265041917435810797263160910523930611419590805856593501445058735203411287873518993304245936542118427628253484903531193177858967194655806557220517994525313017105242577695085899625593401121802544864421349380744052181027372406762526619232100168105610989758220268058576179265165669820366077906223425710890636377053362518664338478118860672730612991089013070390021262202769850561419150147818875557439272306377254706632049908724234682311229113789588524990286021956586530108801610654838309179432857985106433451343452718852493538324132638385035502401433757119057736617171252268728111662190151374012450518240779320639540825441090052832893890190715149097198092137999376656457355224070054413858765323481639607028873585328145422239507781614599526008062691652972424396427635447038371025303941403687153868443183378672823746358960756341503989381911488566401530543016852425348053040323206825891705250310230733979394773130617599940829698719033044130037195840838527365298185064654627611230844705984829801978439390355396839809435534339062888679415545906606734022383195356775142962315065299947625932191670241413973273164008610600201045749664824990651907553907130570096006437716626401356036795375061828368148611973619946813391106730324377245440073013588311671023329922649590361780844791839538152072200774760656738252907981914652085993357640400728582850032282137963570971127997236386394063385938599603501616725677991070724098016897878576292527570479766742488860531961680268175142248696205024928006369016953979975574446086984288304815564993718422132801681662848757216138370352100546467265894499599810777023040106090956939360205102341837125808216363561496302579047467115433312193526032433473049227686454052899784685239549459570017109132339647505630252362256416268562776960966450788733643952160049874388557364228396316703153356302775556574717685954912494186960687301295955349564465936672972517353238273843350246935627982005490928983022112191286677442471971688459800808151640700382974940735281498538957941406064086758211792446973227012359006757619811249325043520756958160881744407644537687773305522453464648546246980839120932961906479810579992604003925182955177568142728637678201254336636775482618247836012067003718320906308518776846710376691736975906480061966960671465939511304918060667470883759335227645064190635181955846702450508710696313254040397931131910367224897483800020814667811832142807079496752690554517760104731964827978955929796545291174876759541236874829668692373746382544570559877377178222695746537012557434295976025096224840421015707597083477571943727697908413919493466630363138008172775057475724937161399489679718879207853769830602575187380867963064017752875956359919372612254865068251997369802167164727494739196637440380136083213759959756168506524448697856931861823426899375561340594250311117175626560502212975134218933371507185012057908678174740829527231718849182171212618185902701976255473639682682193866390204112318653159881206635080273849087204037452070356151568836266699256547072235405318412029000212971842988963323619209197928129798560238311845474478123752566394637764640111276394364066008328278034434436088823487201656220824441942716398777083395651720337955421125505974290550781144256189716188419605113266908611999363700391165353395544956313967092633332576920676837635323665383259569657108760693383051358661804267812089074212255182455950995724641046445251906472130970634835513585028345196999885899919623620068306804954147643931128121285499031044222614000018122280740206190739971318469248294888175062562597847733572308365883295089095958392992159624821271605094659589964144682562256655815280678194123111003153540035406422184474948064807116583793041955537592653053170579409020463025652507167816738078533166436925024281323204920762811258998126295848640176845220369880460982009612718757026949261762735396132238459476656569359440096479979319322665461398177084961810056266497330037083924122483181203844731969755963746516469275741310134139339764967899492852240394394992011589632377807369658499359012554914152049352562982594923062856064938413304845515399900840953277276484100294808921572202603877097054867593433006299527912532255884422367391569631183657004659476684415089230796724891809050019877380402159419292222556285656740801284217624086521804846051410358789571108307489630840734317492313012276550156536374147008229496488943022777110008717032917784298160861420429323145783350435922349649219923929639645588712872910758148909370758763355492357839767241570538349012881803617609322740176309640673906292805569650024237925375410655273386981919796042253807962000335170723082618116859018841006994771021638707207416591125897439672948846025568807277346080919077218889565195094251076769625260279843666975558127182175512308565153713735868022914164138027926571544697555872055566223771183570164360969474356239979610632184781699843195723155057490392875676408811265880366026870389479882823026685587633995439044451828461599691342523914140658642201065238808161895388927197540274286290388441079773795713914129856097046647308979089500288248052552045176373625547820513368519704923321523336419483713007182303983629846421083985981983227874765938761084075023053552025104561453924332532802703950678448532590341265489638501844007757673237845545704058388944360199567992046152816423349292094460610817604849154339971661416429077621226997140385778241117584159017223716027629919384543141572776445743216566854828289329033505560704305809845117522359041619010694205202180274672425551157234916189120590335438592695348077206747901566332615514571246887538494039864626435879092689308240216450285320916861702211775231150910442741501764746591583679757851883395300274025895076029431785490680853572349427606082135723506556576242185289628445913508234483729133702949926376828556914112996554071919731333168244406411137172502584078060715416089419374874246595508917143139424102006079437352771564871980461005593179976712782681308108983803462650155524290998349066707151609480422663558526137222489860962404543023729071936057752156724539796643214283350028104748649293132524177358848808898679761408581795279986248704368996755383335042815190444801149798994399173844251337176165373294730089311563101921387245553706272562871972101631505626029531281265636898327687654386641347934541600716235239424321567282095337213388154668179649042671282149452250178302556713617925149076157975608660104117497745478630746137768983792767227610123340230249642942271500949482005048251629220368713601598889009855251373093262853121661619293476871970423827248378838575196071570875266928109921767411279018971250869273246141591024126216603928846308588171404054622518963489795339749330145860013482630173111793324970751164162339998279168331981139778275816134002066946775714182441854594574833720088569567271220970894254058039629170442303427140210505880769660246489772027705923640689863592829268057307062748988009213839652198308587672018242192687577958377014493721281789118537938059332982468051363814271219580965715701225840205892056663649186647570686011248969692754665893127052481120105490224843340832693462622486381657950827408457119726738933004938619930986459902082414825300423434452294034701292409389849313136551114787397453034123804027309700966747275034402594145097426437310406303543309486196103112312482689999344927079260295916440910894287061992498221832981765439717537537418404517085348313098506258603675113197703630992548192332222355605379985700145191410695566570970861684120434424763472833005541417496986936349014284155952122808191084477807901000897093914585153994748310344054629200843565235486056185181291807447602370696283559757973955819818036960076087708973898147501044257245737748617050536834808249122396008226451682633567515969322854229341898331649905487297845022267995548639359857252212418150217916575283369073620651286212620770099737873000131776038152474387216827946498926630138184828398105537722704285720668779573105520116548900190128938943156929289691666932009383443424611137920502288688536902203729265089728473270467826147818908192302919315430743204863660113035983622209876287271712663730728093828384684924643972441681563387743093160076500750426203874717594917709288467672091410632453770876886692447916546224556401979112191017816214307476267241688635504982225897351604727151462072597001238750487503189924018046780899353822522872934837906965577811804238997040803639156716899576856340610307940672647612659108084730908966769605220054404681682073091901366033583452314288918552747005605069854632911992069010705941095827991410047765317599793911921410118507984027993252709742864924546570324637485135449085648792908915050548752660214939831176602163460379590026069682508553343367472245007888181689705859201059112622196881749373229231178423273522109670408671385689377905307618398334393054722637717905954572252180024792826969123413997463630852421412771735202235625734056465592392253174069423938057505538585148455550463223934607157195385216180116709867998248114821503868617751717236328325851468490663864617925872063227947753541597100258262424125689829467248164441892370167593638783770915002648585973728637344621885039387931002066148080977120641252756963070650418703987550857674404715880865486453521763749792426178204389329742119587983440659171480766476638571515713797114270426034975955735856216003410678987148299203434465565587902734860994278977802745935157374771975082600485308849366811809083666269657397385564480749152424271533637737619370092492112859716548602679146696368223520621426508466813605849535863432658539111169964454700572679123640881298901479737438663506606718997663409456162963961946789982369669920356795136359370826525096985798852216586677138221720852371302932232314036929616221751933837728824951894304752018652622755235280030187651243509908516408245327847845699344401793488664461766052485889198917790775740520580095507556235643771617667533631498360651833572162037267990789146096512080153617850656354769670079583297835477164758357699859803242406121432623199446274024377084832848345149764306752655113847775328674813074562178410934883238205136877860895895897662960924322177990614731553581656015589023785181185050397652800241558890519582117708790171732770130758589058627412849268752594264564205145712352621071300970239806561850273242632509804642718946039199042400927136024594646694144981625367156547923081741184575382166294448874297998249728962938479455605114711694863189707921123831989228203648389461254979027199058335991086397957087697340046043291415882382645057356724730227602372245949552955044743570584254228818446040195423076449932488878340092658314381349551221277231706771355655906617008946490847931146944010231257653816011625003912147969540473005614133711548298577917287187356166528808667159115600048009484303128457083267002430560368054331411226948694778751048375354955910176154449234547461247906949232139616752778529454389832858552293467274514214324612254227095659572861032989173178402791394811027909197154919868910649140846456104456241890305312020529627466299170188638061325041514398522803102886939869794123473311022316868245992179242235376195752839615130530249724046073299317019108791875222952444985845914372143360741088251879966555258951772271643935209568706637493112406767231434704835866197272043714224662278006779814946420104596176954230904973430004387084550546216953419184320651250310502973340922755106009115911324680620825807518699507256350344157122069938636092348715365347355636785634592446845473946919543042611361788474698088641718353502244134149673540739804289550909657002599809964771375950487824072580625963950910832510484392026058309095400753025666689663223577221772707269039016003455054676875931732258974874335718753212637136000972760100177014849858944064819914411247937057392195535188178210612579550070062342254099734236642794136940803786598147927969917910991173412533742393318640278966041817842071949499833602876898484009877005846091648784303958620423992696825695420585797274706139223577943675630958952204606774362658988203835608332843680993487690768820910251364139805366229254058959336582162751580073391235753133998207964096682273088160327027563502857827262465590376854499248662915244783003208631626403159597521012882544189456540178377521502561288183808961798070047828171930219980197282332284809781293643445347490754364000265786963373833699661116488712174587843591756970094657020099965809581192295276046445722468525959503365296201077764162189861384396935117676495180594620827777146189179627126867996206790537424004263050550285251044226316335571661968524878900722111469690634668586186269698491084173244528083841419254530257785827747752063841384528721812658922395887990771423271363165779858190609563508359385787253326007062480638105878397497635122081818126613287890702999857546167487288197642752888098713811185772852028205296864702603732620320934102956963679627478548893131040823463724127504547623762209947157801873869575765968120510873530780857796213377479585253570996069567960340039066382507777661393304035597543383611953229587693755724055240420569999615720013526971058558807388718926043166327869235700488647092205871157506130392494591153796275066788502655237145515211791516868783162898671797072840600703992886823839067090146741044025342375552241472381791130496073431468235797278043442398956777177331132701681272800946894727526573642278717579954910620300186695543482826919944823280947144969696185419001446085963305645862546814302269906347634585627278025360824543492913974235994128894254456461392932360993114292041777511408636555875272324303550127444596771988495556269981577578373446621990214146367200752468343165319043237854375398036697914401508259787296984105433614565151519127130900350104465445439674599436782684736924314044213714896681092274040821576871223939400959395293200546907992400155964439742098839365377630833871047820577388754296464724424983426887739941409918997102834629161564506458727439111095135095607958142354047124215638003540049117298352621107371805021821484399001460784992399083761439987571460097901878784724632495084948385881041181029990032334269318420318297692948807093179484787958518732404784912664409951202297325301740886819807830607639412651774325731394741120154231167727312022320401760761704142746798955500497729451189263005876635511914958341823512238844142738694030538523827376638135729705862985076052443102740369185124066401390577448469975588461453236068796148279516824805088083454678297574225003696052227100814231622203745539086687483745091805222033187261998135209444684147516848044861456238200516368245178340965941544853740139910091965250262390875272105460220844604100091971067207150540894960002681527071675093508717863950217765653743378222764882759804177907471138543113314901458812404056429604630301854616482364079106863729290433801803094407865518820889557697000969382657479810507061834513145682226491520411425600801138942117205286353864522652891736635859690344105791222622884576951167266464094334065903766226076997495873629650078110873966118563672894138009593830529432722973606539094778183549690023170132503974202196193101897961445753399207786459841233878900015361701854566344559388306703842860162183426849322514117414039688067847794576448615129708059802201011558417953764824462641224694976227154055963781419135475801956351995246430051978323266418593847927185038795396067544671067696788030301161567848254262376070198986984079682748474156686727210343814829105122951553059248946959644355444080793148259782572527795780377277433262979748716422111584432861740046686325344529942093673227401778097354012152228087856595609372619023093974160767468149994341257906008896849656519268101290468989535118841704737516999062007482585837300577903207437646743711636614621149277453517403977068112131481153615835733541791394994128684780704150786489514585375774275472071052102801178845353948843851827128907410092404497097238915704857829842724727098765052064299612821038107743687754533967434665155978932348853728367766634213096041046598016880415037615332762817159889851909195401134113009448844452662847658058185998099816735635046315135952857516661744101190207392875066435993329117314942619586466993507649551395600581442742053981943295116933363629192281613410275630728738574325207653660381993424868126488009605276634444570973974480359009671552506778428622905305381034490527059839607072347185390676415447157287128277640431462541702416258729739300689099989247957163888988396842024453188496616667060577956969729816471263598925676887837433351101167856213657788796977262895203971619229647870888213953604782564620166456513200120993900353856097984356120962255281119747991464126955057779179237209020451420449588371636477443847288081690115895099954100616650087457936451989258546538949999759725495510764871913555640297130622344943550948493082187067222834256531405860524745460403830413246116294620669656505542275112456207053507075832547244334953197240091705575631491858104970269302190979079355153344409022730259607517544890998694900591906196092810589873020020207709480295568398307205856732578177962598575122254864704873301759057185750808390711478927160449198993719510330397950270011322408611807510358407090870982196169758555291156197966503116563731272439508998347894077354452026104038066763480739932722904019724106327855878455154324443054074032067722398486488954282656923435195936796030559291433239495600739734214703097439052976350169863544241404275379208526828757492571153526043036094635389861581225789233542247393143126744239520501470197385068533741568846238967073468256559058944490656237070794540710244913278273174207396143308020037195129061131834769786305993490155611402276164453657856393540045852546355309981096405988576375641516867290819018887992060992199123862788617338379668129544250735525575799179545965619445966336476097586834512653962122586469617159374612912867954428403242046437843669300865377304623779155351909473846083687600506515355120130881540602724893988614460141671984992234689279387898104223614639168437444684757434862677234407590845577371971867556413066206108453671946728847072126664539851233779214076440878266602701326956757187941047361369556060567151704355983472310040483505954563314740826857022901442311110434923094228526155417002621895165947591696024864098202481527668884537780859895771546470946667087153660198088201758074434215073185619166625606974415889865025563821583140571517973227612497783143059596248347730603455085310987021407353300725495395026101091338975615172767453516111415896338936863465803681872949017213075717966348603204750350526970137129169025195744124218189228693268118190504587256901526135379736270761655504404107271534838475925745668397252797420175505536088866265711824848237514668945508715691027970766747476971438848981395638034922452191891308724914739992456210955254328034845562270648919301548917694036591962425231118116682489572353365902592213249747459415732892003950179922417155986755331814522252395301718873888654382279580286539188656794476802262105997931908138880816180564962057992715671459843319116701623431953490187633372924396145481176984540384005449901590257029697306859996661824210004220723076659649199765656938349576933008025048876217648974488891827153497589496979206154016315113715728406362171120811623383542403328246843546897781936087783263224902048994087591744299596319307715804783088026189436126826271453873042340461036876010629622163728951605077172865143796434605378995927691303607532890040257105406083855237766600696570242669043171649870026555915352607734066974786477938422947340990558653689514297739439624168612786364927034790844229400428821395795141436281392539376824884789948239956204422631857471944516505509754315246163970029261184705102039568268143608503808081500341516242039925808978673002092472680931205935583916194952653347069583408312342483683607437834787494057668780128983670226611733485013719224129103290173239000915885780125782177215657014120981039708229620293954125392995052697849493081824323037998937387603443104891451033090814778525166139459590088570811882102319791159541245418774279972439641256238846081704326918088204835276178934844447970335046949966150943821760774232463876683175564866610819906405524007493430802842231265828358893303162219189249632914422988936438023095614794104135636117346798676643506793571232185803731061296936825753017407290952263996592880054531611742636198807985944805503748467395111166943712708419069942180221648102371364401016464543921100017727757640622993458272198767387757509082505188935936602307389686763332950645394420318554436731949799875209802343321511813608175754777973982638648140832753642478983074912247774260664675316893669846328278980512353405075868999953402374527461317464455828955652323303859794060362726582011704673839505109906018723799492664927299515371609115980452598386918768023976825862098730091328970285038993534324743833527242175212764602503941269463699715183737330047386865729936717772223305457496325472139921267293499475482110580161120226082001641936370548258101980180687636368515462221387533201666311976635059444312098313333969033663185244946352213904073391092225613588649094311902640165412251003822818123803185090719972539439387377028273138809036455803628506913054785929999365662180861760862629497881821469376262322259867519865886855831033323338892937995274142868666194031660996553099801614561392137616163500790739367549208735211355053090149525494811478456524713156908659381923847878828774348384601311628132659001952699717198097476373698986863518977662652068625085394429304307205151173081606193200759438215154910545614152249435189420125300017493549011770233814380300227887570

/-- The product of the primes up to `131072` (script `gen_tables.py`). -/
def L17 : ℕ := 1072453133089165880732835696216062554740583642351682978151748916044668363371902813746865743614117363225352793507632563200644292809818805069012833526985209715850853640451085196309340416352926681082319836786101662951102773396914259164798259497776750449031859173227606747431497915761932184649912199393052902663444659875867423718743531039727071641936897921431141772931168952291616913023362601213039400970538493820308172139240669257468839313780298984009782758662173696298120083604255254925112633421943446411319111526151364342014971286141127973367836063569078571767472937158906011982055891262897454559176575466579789106916245325133977801170857977274282317066057101455356903260424570072512329203533553271596743083579957381434608182633356070801063642788911268521499154304676425396772373354547896882205224188365712137449714971295812049071858525545151188081463086534305032350895195221214541815439379750293347215971715047433516301076186559500436803859899282834419465596990733743769713706393729663990933570831939975867332988536609342690381579237698579509635067364932529832357056270210760113641236317117250290591199543662900072565914704452687301131712181048035083730116710329758433556249130918375946654211843782203862977566903077440456938219080697201180274739631974926921608336261889904764474239926066665615816365377815717188341884034547951749881308274114319227519995235937042556935212887279317098900645796340804010504664137538694688052915942632875830672900119418452423112830469880704315611983882450952186625816430432898638942305953795943994967692026933938681334367721049239822749194298385105073923242748870240540998953321112564233346546604918517283291328775132398359605434431639774318751530258009276531945066189628727971408570946277005910401853921940145738285805976253685667281874858309285650891608678871567028502932593591340339553719532543066232678833294309307480511279192296588472685609371522351394855444522783789898746373933382700198054855725093641362625480429384685257211606795054979508018838420866756155771176176742748250082889084820526037350903836443321929255937295689905269461636273926055974916895997329281785745882330336154518422834382520955874485434946143650366676328450435867879587304718096665869160876599683517256344415029217894453657300301292690901090302992598944133743922684752758475065012159134985086232636612501140136153974130326105889746168169748247602412762273205368867177565901984336406046997035374845632296796903843383499022024834050575375986939883523373329637806694957734524240263144383481544303431229241135818415139271629247648805762898312437407552274321515326071404222176177798112283518542363387067308390255066176756706342690126061108146845917148550578567735172800068803922107505785274115822890313650486383182336655409263611443167289633807541952659072812129824406995771370948617190876438306844232079865569762526953103445154774031024753732772442905910695741614294787833496637753945857338772324408524626394485653616042063972781644558568155250774369242242992902753016562820373546889597245266888010388029440908935006878284226798434275645474919657058573661968766477991043705715556382627696800027963470243869796332204271617412632013619807037506251278980341721435326295390607987953525051089489718923602601643241962461204352037164314955370549665479441585705708033196487860344831104635060979699485552365088874115065671801410727187012546651219652119223642785606956287386320391317732082553894371026532196625124333452344613097606592743645770814996075507456753296482490684647936833575762646497498973809144150048134807061664317835037748944606860970099723620306224673294134801918529873958137977720346190500619234499756064865692555455448895187617174802266250275171296194193035515006679513851984671674200834793694814630926866870843534582356855422138202700193780926918288321407799370482071032653311918330546705513420447994921989761981020682114602267826181077758039922714833417690412378816596961537625992816532757544618054889834348967955174756624728661741980998518635968314249592423834466185148911123560866741088666716949244127336277476268268966974050471605650232291528049375810291947909677497088165734784139198586491161489324049332709000930488957960910753758665829394134405038788778268649509639041187783482774992004317867363329576183296565650279704893949150102089677864488591134150516948606463052420293990449208466735437854300248730637943689923876154782879212735049587108224810469282721636538968054655247572768889190783546979609264196888097468325975298679162384962745998185907075195638657885832387954908060056263913281778224732355511319015169199218626212563768753606828789875185933722481179233290545356616135956725525472608406445776731451699354265530836875218478495456202660789720699890033909882998335061943001010743943640858291027452311824610189167823000557291569235668353985450229770621786302181363235136343352967033636126777677068953196373140153534307707813369341499670993251414084987057886686148153383249573591001508938716674252333317971541603359188402997549100085223437156181367244640252499172899148798271861904393145734454920026594865423581149867430923752749647664474728113920370872417727777914721436972635044123644500260854673226565771951134683686900579307376818525009414819746354186298160329541917476137408396701014074610896556087847363751131454592008085656804439475452030233874897722983847786672072424404555552813432546791243215596805247754267127127438955397267040264493751338532225324064398090501521261601721681524905040232098530830555269756747725914511382201530558584657543521179275427487628173227340334059668969405314720656379791315734571481870877270937935427051867115729529796996740253949415336063471680989001674014977441453830016421735832493369339684760211107972412835796696559091663996197810696951728089746426280612683894788799172738439632096964806839460455781950835148046245927782432003480494970304584957019137934343692080979950797246309397345759580829707165855332116876618368888826389176173055899625095580338084631265379550402396191772910119922388822583068773202510119861019978999769102034530686079106607281926098998799605934725120159899576571349321784267814350821888262766532508851365027029061659803412752078737895115617912672695714470371710176300688263379720842630606680711866902090969534021153457813508698472855817587741616615950733593619455887324072172994645133451446403760545430908899235871009710547298055848902917434089245563680138798826026033532572339545839892366540544022561040535555123524485795962633278763994846010536629404595123447398958089800509610472267693855653482753503354767708524053750351963919101266573208978941719108170034829872967426477946710263382181540511855051028892517382402236904570511927230915600704883774165096296225148342999762927574296628407313192775612264402358883829522846952036344979604024881867675626179659849419025255246367133523035827385879797456856639778734136038186962219362883421186676064722161621570278777392898051533037153217444313083528075110620548174504384650107213536930224872208613262710180167776321813355769356021506754524112929648351781895207611246973061871215310579782664003701053166679441335304029395382690548084712602445008352738589955668876427446531605470728415662132127012596189981117453920410164277413519318105129612476688027602435755855187109262089161764831014216904463137616977869386127742464030059144454435322619296993642071080057677002841612577508036252035984907872395592756036882010273571557511880104003932712406596100038686219831108001185832331731023717772368750141631601691224192552653626116761178812348611581180424968623732889131107371666728393178327986545123396882025194839433510559045419939213787900612615094612778234392970363129271488534210792537470296872468460250429837952239299815948357106304303325587673899608210702874311880279326066315320743822565392049165493283533410445533769651070330536520550145454660598616311315716214092327115456082863500771442548996134629117353080529709039475458895871331725162222235824296061216034456168734599284848597676901751563067528907919697111712247253858648453826408284437162626958914285673951494199731930975894216957897266414834799645933830747399483718441412526657885130741521191003083518674963881246476819143017937984894786671101243498217227945321253970369358979785226737587799073076041825178956535160187270791563109271893249196648676934245770169007767684838012612218443368278373319412255470245416948817198816932312208116052907378912412116074826901673418097970992896181891115419308545183245816523676392374900268800728963399557991335264573078652160889138634976470331863323442441609464235061802565374866033351976448869226528883916459131820491216116684842042364782150329650150370297136810180743085533405472929402832060333052530608013994785303408433893389453549859215374548369792635423361306528852122105153343313837890584836514466630919456039464072546785802463858393789951506112575225029359947215362072049684437555889874641999518809077691057231834576633213065050475372859032531484775424935495086962782646581932013321640293421660615536411653453094048561790237162496801714618054520212931881064006578426779101719996827644639732578016176846228992986471274574592709314128398313085146834703690412571361890270879312948504678647568920966324422589039056299281584020823610325142383280737764230568950821017938544716634613291878099291433854389934386211078134658986183317644177027976509584526601397889956718026671375892247431121789208740446293004141989220556995707632271270102019758315217750185616355832967919134513545708237877040421277208896502238275293461180315902991042123938666109207576044106057647086905475192424679094050708436133015986851082824643582583732651726083530491608324075383345663168080654686609352320542891152067814541655944822261294310729069690551920879431825472738399721932412143712120635718856549387478726946964669480120662219061537646472835474680146094476402112469021286777433940061154485357495258826464294270548567063787559115697353107484129826988114832834334725430917455671072740154192227191989387247738587663864484583329215215595358962580904936306514808912311281191524334538354212345051492127131077015681046994244349091084592151799818535442098769467205380295623000361361046295574184526710420611840297966159030459883621432664155844943611383513339704621612881925789980793237500770590442945045606777660479467035900820138242908489035301704630852006846359981087767295756571030688290665622657743804198669294591439298472202504951245333056291278144057387964458627077928371182456770292824731784924795134414510474166810451480784415311943874847809507166000947119056289622097946966541826575987316124226466033940069133895839201460180268501333255300692455592512022955492615847652773332173114474086502591012791933368260012728876645703325722971059442137194099720677735449951272710238666376390436330181190751266772054988808329190928484787866150940088200956014913962003332319528856541392562652401178604512597306972211571900913708794617306339858892158997627064720382892724180855882175157976043693748911689230781469594284313629847476546271101555017499713497907788319259124600407653723558990555450988208884828611433281283500671993807730728143922474759489758297668383254440032636004395295301928287540794423798590771369527992933800845382391178819288585343197766932892344099090806815230790578569724000701483522964721217088474205847366583509791981713529605054487585842831976254739223776276634951593349925519065176838539275059486010794757692899068669680684133354491165985095857223241137190166726429308622898102736522863844698378955674631980767069788659342649426460467363695662500787953323127371496201095514118107120150299556880482803319486794174551852060556066848214122481028924421336985740755058673646165704487330423420350672110179645685441614227072310332913272947436037525018042360838619619553771454304522308244804464317872827542848704470859254346948504035117071195211243888508080511140879281708393472116266724163155875249116618725433489627845822157431015607494028176531467807493711414016791492931490657270076816448381053545103437432611729273952852474444756539775005030383702108201958824579399788180544537213471219114288161196322256421209817999696377874673422420830951920691083311979725820002218299446341373013721041999765300465052710633527886624741506369237982862237120086207623065511294435035777576298573638833733090778088997019230278800899466658707873836615472517081301760176903625539557798534405663929637707612168867774691359990356849561362820667406962537962116049219737755453943392234455810441100184368015688381441097983218228984981669870453263671752550199334401836354776662811224115329537638809511919293539950753191052165392482833037227717057656286047591271911236670004486924924494503784740804185416779594370423619171163617728373341292705349882308501479736996442839818465265117073103061734679465961339634059603045792572030991403186284641506086631476440305087444905659944225456994562346677129906479780621009097429637321526527337680144909587123078190353636269264168293171199236222357519895995326289536901527302033342743119348773028568228200668471775701393720483037684893797362748575880640124426432652850210781880862547667601121711522037054495852031028769099161514448063343937250440500407324267988077029986005783436388850275555760092730797137001614978148724546274365577694705861249014315838271772507895840819226410263136388344335467749571686468387470131058763369349441053469768468463543951324661888698313887863444602100961537442130564936314494812497381707241479461445690018576719757992616245526053279632572779697514689956806501385096873535267449862487349361282503625945219570069763357891725771750398700511240302925625331192401365111379088359992165948936227173628245908618483497542427832242911804443099751893757366432612531217788501472525821786276269861662962817532394119229523982562117040125638771109549534508734866385120172011687543612789626710856237813406778382407471130444935892559924854586555135076022419826783032593864085125445297333744021788121607157333903336423049534602350003122921129084179769166444140456567454847445612724362961587740855315508010098388257967838324712232839311106827683559490769348320504972822650324153533209857422673239995859119192206030841095553166588013889330485160073893669646231926819680656277986101620598760008941830637291928497459329184473853979261503965581590265359790603694376935476121103544411910827751211878667014983601245278218985499902078492605494407387508341512832459517283726901933577480112035429256629644648859677541195950673414237331752328965404204053160160314443413884399228008913666841705634510932935332925000336761711717615337716514733665742251711467393725573219808038099306902617758317872889181047475787464734308603804422168889915436292333441969841344059750167398768505818895483982366534204486574509671923411690953395860653810557268345455867168702417034583422927972973152289798292968672445820480466613067569762552427298201440830636864337969604850104882787070037030869440765244068816691175026713946607090029332315705723302189255100756909678443889454811106027574978096912190980288856958760198960163085245110571325193801600068994829331113746619752532558696559658666805793762917587736029447023447434285433658880968719823330858886276602483274186858777385022467593235538402919210424196957568260869389349594817633645628876124350545630052341423545681531763117142630635598223327418716504860092985533071236574274478110835130864736345249240146764757848498453854565788581779828304150520022093414880722939653158717149393551253407605063315113113657057028152800860623973726300177840438880562524629237375150726120567613072369363151892080703239181619058535547716662659008023172025386819537218132336485362687545720111885259995692601799365846523630286716318418765259448322789751128286676208350673714504226404035144285514769110326493477243772902518623883523345771087629072649485171595948321040956409216247303918032353430877479783014950756925498247236053165696016749178620516663101915976815447774445967623249642990960092239744450302694424467259455561626393135420529263137634466495022281774997141229552541804119266265262725037997833762637107560647100981271602545940090883159117009335174638199939762453081719093104824004889102876868467523963887354220019025039529922198050579029666530648098624823797692790441444207401206141925828178630791503964663437672261615756740349423291833387205443472757736372056612377487743440653645543513052494449253809130504988731634145559690891556928782386179801762264328522886767919404015907772317698670528904962767581279837923655516728303731773987997017915544985369595217510162102390006999775710546978918913138777727114944272460295585339390814774702169810678540309895294548471042125470155048980589253928797722318274786927860283246226706527493730869942438646885960655816999123310793662290661815821048534028994895904068891010287623385910147332253508243359879994799386908319457370737943967502821088991510640125937413263028964494149942638634945743085816352718483914492040540728578311657400768801288829290363297920547595636556746531719865196299346267562252988008931108852801401470377461211781711823447873104366355810256055017321644418348866648641578282318870992478888781356788288643117059660932293588026400026177943492963452980826550005747165856258684741319703071008574126451619834262193988303005466868193400967815554683500367102736357677502851787778779164815836468443498245462405851239590319505769595186878902244372916502832762102758928357093839384020526878622233813993945229914384092485139859281016511917885956735084463641851542735835895492854180352507915277826842471810772278045037810178985202008217959318861870571594012408681995217160477986021886125529481300830107849006713440772515226015343813802683647208175502311999569767002788826394497775005588336533964550169292737227546488931273877324404861203114518894632960345898040111772563359489435319913015494696278301983255842096209671537997281904542763456041194542278065265527430387720335998591430574125763982827633440674469668435722857189997068971141407692629316407308204828851406386321997261133154071708477941674700602026661824037461414852196167772226764210100914660273399582911430771411230432620563451595068722036941144254935553608558007458866271988076799742733753819474841203196303653553031426049435339001923164545485735092412704854002584594969006001427317486469987570651887206300575686705472660612998866857559630305787349834848361895934416619244700650308061775639941174345153507374674256218057593839478361104026213220776012229820055453841204770952108689499834308472530154361921295735755306013996801604545513342676394962931086438690344215578519341974950697224160747193752162990014437360287005565793330466626561615223922523500513148738141886981802025570619594865091754631494719185694910237163774684503998136032082783699727573471820830523979447887040114550611571888913210296171905647188675760154912817372806046937040678260761633657311192111603053896127078214044164565419114682263965296318603209573636166441881983176225413584111066574937666699791823454881927759370076335535728830521362120653787644724282763904282686082057361824744048679200299396913831366659676936914156880514470528968617068660085639243354256920108150106853541484038625351591403987147264107321789335374480306771873085322832975817199233921258287395262008200398786527633089361159243244828277570273708583809928191692942335651546265071241051274465408028596667378151671375608179764112229581861669171909138204086887111333384402217678956261885986615054768276789870531782132763307701322382956575253562816726126049626642558513816155568752280238102898839100593709677240828699221871663702184567505429955383301290765326122116673624642643995808577303505691383681611934767750821967146681511842918301863878681841063751376758482904813607571774396307708772345323659342595894631473058928774858032313410513308078617011296985022145991398830589475406418075295727159126993653733368139224749165145391785194428211300628305721141179592455887586271715904664381702259678726471665095914184171792382522645554669075716559810868351110166922610827803580080535649474180735856190477398878085545290050543184655427569958309668570921624646100113289021937913749448495578236018969618291615424885715862044068069644579321229902680935917393337036845776092065519915668067668466647337941645451470282139631541642836967322521469340607172783116923653915316658109575221573050578109423895142035455457652036025839489913765182766721229221786192745328318280878921578016865582565195128908440852586886290715405198107948441516076783916113926482838707309020112668128807659984634776186126029704583964430755377275531581336702463531410354652782625379742536663316202517458928590786202474725399173408227212421508494164605703121037485917341213312934503627425358859044277476670047117813100067638156119198629114468674033244340362777210360912739954857217366280589965555403314046987093007646352691607959315790168897385549940361866979196070209906047360121638356245960346094752230828575802588314598383193781052543956878044534933014507949839638776260162803568384010749972668467757250298134046823811034621449856074019484308605218237816850803122767671216338190416106920966283961049527161730525834839854382678062895936288073873310744441301607369790791454073852546207614027080895292210628117413481939335344252841110138928655285635381002142709525411934833624989071114036188928001147204127182972179416288479806259152805060185313077846088164762800999073865263081542724366556327248158712804918580786216125453521864639306088427812640004660170684336309135897658698104786281504987300827836005818448574129588562859555676689247891857206474203703085436498545559559586797241003844217108267169435300032256919412557781805276913023349558385628695230062492061081289995148866006935963844017994660610254107303797903983270169391112180672985025329569205092133084976483014238428241665714504463721352201249710046912893356688698202014228470020377632072441074118453547019671636460312662381734506289185897895320091118256307261338741356411162755349684842738960205460325244126852461432422235106838486058934641476005697265879014260176021453372430471686608418141433184678800821888213923731734246835169875260530456440770312763440008132741450738045248069433238846983060845217868640082374393990419579110327199613590884514607189178108711006916037888327153243324937707011788936410373263663995811365967590783577684142364623110874832028591731585449614239375762294835089629504280058604869211288538932750786798002672485294335169665474775378025230053438813320816748959391715023993640452201691417569142116239274219411647427479996357814328026746967959522689574233410066616752622088878302234841259082472009399534021851521477648259127632316803979489279487621972443872151678888496867836609191283564916869951803942551547002895368782267261351397212172077579704286474818667815017735581767342235705364197513283166035417844820812596778299974662411633354128340345263279829528570812437018988990056862679814529520317124375884381435605864123044054449258062569141264877027173028405197488736858082139796036681211868075072449764388804978433585454586699314428342878335561230543642389733033998203568344590977878639043436724824334205932011524646467161592368109452855630028586092661859967964564758077703211787545064059632939414820097595694273306468161079816796811936802867691844278207925602488906265189394132269309036196085746244902076955175441059616127403874653495434206603052811158027856036834468279582891715825746811128481191830265653202648279763036021157244398163218769838867614752688746438596634421208713596321137506762287398700776461987371684199774856841821656846703399442628776183172319997075453825020225058754662666118501728621329505651092690021852421578910736450594890513021320959174224281842106675752802967509367690552673463780554726110368312213117434091939431556938504465137660884079165755022368001865443980887266434960182144635533413704579343188089831687931781488843315675086003327460230759577758110458745346408425403418302356651766486828687215518044380006309179250133708288401584871318023968252783019457221635584750456952520011084250202823356745633039278192266034710801884844636297473627927129499429612128952730663792776075946036123683279545073176428826081283198479481159071732873685856225304889713860461416600470456732630624430666336278190777733470983876824988912597906901125421168710158541799538116031711678356657435639679734679377367245005876531556875618189198584474382687023660898331381081180787326131115858025219528864906504146135200741915151861330900423281848811936597826285637136190888511444805492406673940520016481298951625090170713265592574875694703672744669076553658777053386070017625751424383026422869399073544206942840997830137036285835105468776283924738513172339102098941001410871215305263270235418503327811685978582155500038131545735912831894390632812870713424472124810791888722116047850083093966285099293512736411992072760532404504849187238082643425202665118595357006096598294602971022414321901547587869925632281042654938430794686243314807257506112294124529316381038135048840853692888706495840310932572531360001445700217080236493746648947788553195048251909256387019780613388023258888895002812290825038043913921888798242877364362812215383760694090869130958605789690920677526202394545786207492867904702347121033505759605465719327038612173476595987371185794193703234053275847644679863526275889181167566083611189525246175123620195015609093436086274804007539182131435623465842536403510791638670653631736029581793612255068427811098848370423360577813843456064910544725654849687931410183246145202542987272490300733051188687232907779915521077616878519083744388471301472372595617723763400076860430797119449824730960720591916257105123663098752457078289214281608656926879878019990138405703680384970789855631327625039185510482407860611868875643879540483642620143739904425913364081015272304660686584536115979825168045191025403682687956742045909882069271706613282169761459858124475902923835343353072873559354148618821710649098973663824309202189940200827279698160240083758602751742632800522446049317355248940237069767293721776723360030809447620050418325093112859724438355231051121706598081193464612155336883135681681890442371685561972666277062294600856558296604938223502755287097879065786354933132079820912878679012730572764748406303677876289697102550518390849905094803791986087617199048054054032165092649004145964429694944111104885496847102366961422195066410346644590961721475600786614363816583772947732442016666654463166577446459826987045184933963746208830833123722852044623635310433525577504571636258747659568764735019926208955432401375285281833328561213254182990224067798410709811985073691369506279383506570869722505887949189946871680549072441914062943033203322967198419264696954317670052314317960271173096680373431114562341973063986863175899254218934089394974858943112933454604305777867811446226143405626740199814726381752936819276250346356894442330964523740997966816035113293779237575067656135854880719049468407056933356609863752506870149630332786801930546623255956071107595118458509519270261621637693168755020468050552193197643791188266400963618102895545302039097344894851388755424062254089864849840500848340082663203572866068861663863589153118183130985508026920667855357668738941452049177200514700043064631116438715576551759674620862869870501288817611437781354894416048151478449304335133157789114463236464589232083165327544044639814099323985404639655842175499411300242172709016978419910284064395794402899138197182284308440254283212031396288704795422549829213997115935527532059105490405514516402467117301988638205061825683121319632835818472118098983854467194594271832419528592768322453585402884941905947862955630562637824562967010827145949132071069808557075700791109278579771808052269905614020686553650399716919408051364117018925649692638452284878498436549560181725638386320457806278780906366035035853821207644574756441705630171630843644909771848322505334290860515818969790711974130591507523635022448597851005197173178770545170512858069156533987475492216056823691266268174646324476087495060690666260430582440324813715618456763193954355983827647075450965588934959439495404474416931261877140159188548841119515643827383145690406414144627596403828098853532872771631380872436266501910743108976200610993719840662577730855764823061450572539604714583768332190009362889434608093632231788265706956629744746689680091156394664561087470084841018694504236156092059885600082016153602770046672368500623556161747326891116890008423803635601178812533696194032249691886690215101058716167470327507082902702373401975123587163174329582237833918494604253857167998493159655652425916061716539086553801107201852723403410259354003409493959518154269865114352221822999351681876641363952028572242469999756410130906857029976227464798315203068646430735173195962622428574724145790744686378843798260740676690358821075835813619599672004238864498856687003393220272989753196945689770067033343143603612071838218213995697307350951983313651466442260602120073951866390670680804426020814353665099184044609658668343832317601289086896656195514182489525001451688327832418467446496099828902840469092159225039056654159236927257704733143130419126217997361245496091119710092144175893864587229120947624395035735187186344546908343853766143992631621113208955402622682163493649338048982700618773550486363102608594717783673842791916793321642270825208685667042839132405747088421073812517382276103779387281551227984178572842623033192247894128393680061079479493063379657052490525803512098612253733172850737496236983505369535583394585291717798163725655299625545380498570361825231439906213378796924787604818823415853397915252107504773642417073713766054972520568712903888417134645700101972770998594542128719906301023460082879459901418669725284101110106627355606969546531203287170697979999808193976129525575457641026532108119040184046119980488189101321020811538698064710001345406534078332738173251484902975597873092836192701117509362898659104985932601389058802833173084833652520498041400596716794721247506245195172010753122963492260472315365947328647297944224142704246461157752006614486991589302223836472179876791694390749048132809357195735971845273295538364643354024906689748352103205588206378150148982812167533011538421750116420691690351543131967656404793283462181978935580451024424662898495836470742017539408654318148665463274245293825398180311851871931914956410554340340173004959752475521763265732836325124450749937153069044836962179368144126473069724506492730600606005686025524696824838390485848251571538989711367445770866954004058869933235895087129550523391018773093663028232184888027826121107834731526525702701859457276919182845401828238985026976122189047193860135390370760635006819531451153040596432892056031940610369835794663629854927607828058006574880960363717143268645087061583152505435564868619011446983833663471861820437721380388626384085668850348925253286175130572805749524599828056309894098146121391701634119055434015036181348120881075901283771954771308809276843382390802019666307118329000673930937104528760140643863773196138721665979562709602698747457201109175544951776916088823053437078849039643843327626467149920472090350233330834751977198596471201058028890202441364400526844113642889336228201867303954114334853316647391255312021766808811074342217482413807586226561396100353702565425362312874671241963155530783015696970788105260886273038765276552530837402734142525478360953171713614757827022823899832727473315733750264898983907978075546320239101871754264396089643219947197649780069175491683319671795758450126606123950908123195244155965190722517930104879188080773059503596634086155108282961899717511976423715645848823150982839665425100888700880899778103315617730324118559529189976147682192914374697759565376877832583106352506170930697436998326054964639182737632465305524693043709949888760165035409363099825018652855226743925101710675252921575941142872449067743713376927645743785955125030585404318608391020582978112383489680999880095074894565481739044665159548471358864284563610938254109737008476739809267781919559852889855094013618694564105858794814481093113474751373379239262263363195240634323104583623577882116674881965827808030451659507483841821008434567871335745095358015348385237852014952092221608180160882207566301564139006405266682692765756860932002312881774655999082239193891481529010335533757981572370590470522462281769337312710995544303478015120643417469115913710455563396429857480863568993813618830668652592314407535622974857972021313641046814076928841185115304502779189481098408577783475341283638452317235947274689390300434708880634422946827425612782032332075382031344515683600902566117195721721144427138794516968207264698556571438065696175584944205453789073712424981430130105873960569584667144705445440834691840190819578781998559603765855602046276222053462398557553613362062374592628682202108889482729860182981819214953239842870008479967291865528069971037149365785535464141327795015603663592090589182337822766241512373213612490753649001483112033901969882961584289294194318800037707956646560060523392065306244959098555569958457830196943110654320905512085940433745809196516325501362188634998923178920931725794513466135928394348573650379900745887542296844940540257554981590521752688937492929987705644305104032613424674755733239784311982361001743128663087632925264139401296396079847524357133028793980218262069336463818901028106605549516376206456558725750110666411807116899334815585752314623409612931775795645745667983964445215314499633739393476065157559505290715687108922318088749158209235178348626132154924632785328556829166269074534682332995702110063848105105280770904729551306087217764606057826895852261695704324521528797076996793587904057079035659221988452901355909530057153912623239680415893023033375483609676286133394038846963851049667176031114104331548821996671764414608464454286908917807388848248358281235940779446995390376730026008797192649635904818097678686983731726055986522562803570296653174409725246039029431110546304022439339196523763438044862152701325109632720226865134912836326123308820607608428302730447760902859470980745961377700284737481273544009775310035106554417371228265921398110839698350740584950981194340938357313411356301829203920909357801784308433257063985061850281834542939013875263893406092404467334305283438788376733552312479231523811830326067298817703868086602370987265531206043979461816223889679131638075245153412654873555929313207666334826902885379762090511542285054801388508043148350061432229453149137158560645272647612800197329983887363517724088105158384869657444732873113724038366253765642798076490933507479763787109522753225033940331310698981916323299717715284378652618393567059567765953642237150136077567349442534565487380464843978572764601634769431600826271382689074172325510840665353521933029250837772860553724779673259935869900574881308066666628155971645847251437404105883059819972306172760175949017288435232033449056826955334292167646703550125766245816033073697131870810723214226566203908388814595481380342238244101340321631924418749951993504368092674130271463038872855640492541710783869749999638527674996041418730628532985054256658018714804239162723595700452675781154861587636814873459009388747974173793110250226727831492482599815608761071377053888525831291588319814816033997434358855964983011370045146686391412139227238134979393125497140519228143679536711027971281175365663111490635612892647812463934053992127407431606868588072113038550329891379782798415776914681381304215362486354199505229570939101750108741488451796230172678320353933313172167662637442716377808958901366106578919472795140979103646045273137193191375698409527406796796583053272883920405065528532896560529160302516086169294379537278453096291951149035546841833207491488637368079801206178276383767916347270402930714516293522086988190565400541278669060019026173916316225980295508289003261059585345275020189174850276037408999837885786999278518747124893867123256705369217726830900414725774185873439982908209560097224384987386314613579069102451989123979686801670324336544199125565530422035708850781707581933495240737743161642853041783787619840668850228329582493203685936733912763616881343276563815315578803262830053064193904315504340478815241786877741703885363488555733584916930125410141333317133660237172467392930349141796556521365700181858457868127961295912375237261442685643552591111240981805910389679555836770378690512752419751050366213479237238657651882030735496266983088134404201929715860816197676556848365230052146444253665905827600168377567697254404834582401040850457764449785836866733211475086435249755297906648400721420684175752383970655796917814159104346256763029635811040391608595133241947622290087192235404896890891645991930746514366131135646145332213828957896723313469238024195489844071822650866391536265317824746517828942319392876925908218323992281372096052872449112377065100551909064211460687033239628244823224731286372147303358474644830716975461263141684453016388197265391660058618582571052786441001739467677101013839000611839586350126687056152081654747394357426009743249540201512709774649545143033540935597258214698978829095205730148317391589571128761645824906631820066136379638972129888977204008652555390904093928859173593852473522478383001203438002996813855662367774961627762818142309126923590860704943229072196011289814507804628753137383362962312386990682281163557832715829363107140936394106606137756711594106471724513494755029837816926617903868763889416233631757183360230196856827181973274921646366286603429662263116938402718325571902013267545375733029601981026846415437463462385170531844183931784585849705948240424292834024634447457390896116581848052903639647707305724179896588220236948636070181265443177553542252022043774036473496321769182014525516625260096255596550431994003875099732617883947865541024176130253121194908126175814852328726488492216785274945876138889921044712080178384482831607329110716138333038556915667420457551797050738157191644807041079495660118835169661896721791676203217940004845441762665635330213810984528742430151938193762894708927729180170340322894068794836497808052723342937947826297169704487555768221917949005361750725279431994285525592392478394901893965853538103938422453937145205312171050971721237483031705531969852934987785603240189302252201841490560975251426750466205104374148878881719219162243948841133396039690218599485994664969566584272931559445208664570400869186007874024748187770060241656259478246271276454681784839663543743147423155779204716475587050033560462170806715531373742002442356388927853010258252323101321899755508754259904001038041989041748113956072539176401417620524273787093829037843245733013643268872519664965667915636517969609806930192331818932689997399027787887771068008417434347791129458638945014614284955163418078693893061872799544473339265133884832602280509910940865050608116083547075452736583032799300650619886583996785629737068951545673446346643056180877770529912349516571489988184115603456668586590727804703374176314647394858978503787426679407967532922371443561959259654754576594986174884977861855702211741859904401967591048168579570248530241607458957694306871236602477143260821651699525141209044406847517855404633295866364826195513289543824795667151366727254429534526048300907981196279069626662368636649519060680706893518154575203915740010434056066566535901551969356002106753488167420129467655829966870104653619993702398142120162806625164230131116102811818992536217857722018719952285250010017622282667058043942717960513687013389487346108203262787102003143770115307456194693808085244525260582858271036765748427526995748471189086205001247721856398675337511740048750358241393395102760734266421615602419158934186548219782135246304219281093247812597588859254312053754493892601241670858624148210517210506006973152867898636301518047447003855700672556966480126599072531326820848377089149779431067796764169851894022689848780412460578741770319533330669934681389743599074953291277789059837114085348364605311109145701028544052487724809452693788910387603818958891705081745280127841489310236122053547302476464239651121377505367960229933107573840443853009936362499373136067045136332051002172370262048309216122152016120191010898678609509586093955624717717639163819268073206719575529326130838277873575732806827564862157320003508353959128849682373985305213360791749266564800661303541913504039270278181933421592579489646470858374139441686287970056013539283907728603709867806538812334013511033278141436961582032040806829295686247215602771778034954762826688128057373464374479572969254205472080092565348812049832546568133556855940658648247851134861259179706521385962264026158924335274609170708123537211715507858496753888990298201065007064826274200362076546094379857842446230323591067624603692997388927645903280863672880494063385620634842327163155712165382165789029599962616275463758866935434205360124110911360464045761684416070975697906507085890918277780062803369827352160022479852746706620394367235735660439788088697384600423859685838893911138557867681547636024614529232913451322981243658005166572403807142586175002433518383159516621779747573900153120439218728564937739805521399365998057423702439325733203513365307851085853150804736448039770479091919142390102864548492031274490693691214092968657133633956339921508297631361080510950708804064460782357582805944198482808005075483324312489572217649547998930483197876043501978726402032602517166772956405116253303212170387899324201284474997719414316886692579438046444177057050525395938038784967599352159175227669670089702951393554629997897395220112732329355728890771271749053276729268711295733220469808132229651659506291314085526561517062190648001911289228453545191858302658245119158510377942430317114501086581620746451303007257860105804619354603000388472341539559211948303796552932442899927044016099452177274168705564728217254026197009668269776959009689790509367013935875154965807760373503546667493448609105318980499076336099431477539025871626109866691889806215559111236673956241152009027682922129311104078231863603808879047618514275100694071390694377267109151253047903650164415793344983302124866914719357486575520286888178886602758843614288571699724789804289565349516742590634009799837035088825569729063203069078623188552356966668704055715696673955148357303503443436147456053809615347023594243072185252329603061367875522605394778905546120164858820234931758511661451591733275906101416032498704780200439529352870273719558440160483376120943585041660700755622845199245744419322867481179890367439396863833325782048106214044049271830281232529596969717363534027646645117825948251856075969225758411985898271543410818890999114525805822041782988958282010493590895286270551691649060928707144041914646891221401911695436543589619855883687924873906407246121684656185818353833267000195911429055260057782460543613665218674358231239067661962630655607168862335344823255153458530190111961104621674428194601097266315898609464789345430056487799307074935473740870765275305729573928215568830009036840025928200907331031489401211417463042925218046614979647012595200234138920349482646448842969861257388029911819268260517781118446489230578043889535765045361739976883629676966603664970726755191059244271511885250480977171457845943842115706423810637691792834627702012541218536394046770322495918894050191127271090225303379762154217575669476296173414509265931909545368918829704232003512906990999697429765126645839773992824182951824221375311707831526684812738447995310148281976768600084105621810982695385508997422019493191055381749498641855764580276044567056730857275989984913143551120784403313774697258656429999558103274129566253021130626376221801599076869978863007760423821960510080329486597982110301399145876447311137596990955720965281780156615859220669806143459278308265445512560996326937550777648744384660361722933594410806838774061857754675400108785729906101817767487106153233881548699267130315345853020072951395394064719033673401099852720822561997016429179475813220960160824031313262528892124470721612136112923226275644076938456390281866281169229473333025109881442304291494245838320958390534325286627032944807860681441636995676161594962234782276854323934202976756283250743304775255274877920679764210000230091557811839570978367145146951245127508070478321756457308096971483946032130993742119568074730320004424842434135130424726697541295289903325567292872607123885225285454779314789341918644275147660324858925751797663913412369027353723675144740697612713951318759037478311199733664378696458650986498219583067164011106744083371642578223489110750475572252734868049939080961202427128888133741491917964482924148184303740774376824448738908233246879364409611448761177031101526452790939283877702837935381515543741747984392786130814263874165770835767087465437693616025080935852498479399890160325821816974065162708407581969411576544328382741781896514074555847503845950397056843638590344558376548756010290205905625757796102750311029022198144550157312995949235300022985103116619068499447483132503843105634417862057201916930410191798996533123145780207341414945820305153530811017886330643451477406391322437029649472117560266623359351580093817524175220295659706100819445886778242750087515848326077892547902604864354351204099283369884475442357762135297896518354777884778946919296006206798713005328699271904553966125772512953514213280810917940275722548985845192857961676141574162289561707934418481060164619185383651017465095503472090943024818389435294068377396060912898712970087030241209664745599703294747986849192409122350275935909826353403026604710915737342093882540431637795129088427424160680576390339173539513385399869564693379419039379289152258379940273693971000926682431376232130387185196258004410607211560306227360789750023426013019619885316215603413363082533131569156284107220001180734439545042352318227912576584338645272319903874209212484594592059485604590699687533674680496645373405800810068334972603330382250467584669268849507605141181036453655810876837063857961591626017603006677763631857127149149447416211105975622533830257972107950258915088951750126829550289330317997602465803139029264166874782622440715824489998572544678657123877980769219969480933593150223499161068798786916788162733426976447546967980767720227981260086197457487938745257263511010843548508948901401933060054560994060733330797462219584159264152959917330786119896667724993557004918663121506411789674142292898153071637839658702364477704293258462936785301828163151092451401131795711879423337180320823723633725813557846327835806534885705987800265665789993383179477621683004664774804046629503399847430221596790413328504928933568801210463419703488022215523981854158967747175522066782657495674513872679401611610284449240506821690275443806776853751042480582682747885498663747436856039200372407935205630027168679788113644042885279399902302918469084782541089093361715534541996357481580912413035621640075791634547294871205635754570325441421946574153614595774256918793213729426286820266044586154476145708497296124989721276071960740811197755579975503985068743683092937593186344179684255648867734271717548286313163087324917141831287350009600114625760921471413888652196824738182879323374433532937028564422357436563079450312293183181691558241022486046976562734364779581846536124264723200869549774500073302870844679056238545643942468892657185019145917623812756574407118509723927691863256319551368614093319066784551692792053327155992483430740115903629064054859490361356798015467005512362035235351915986497438126622059387060026494243870072637019299871211421418838769034602224279124414913169008014086996043585654948864082635152713688504379865647078549298098853528272195591550494926690294035126252483763070393884341371287394093226630113552064951149973730757272762241241424456089526482680565278346770937452830379394450202296125623517198649990344621908431829642643753907646339271094727504874537741267814115943117323003582557161345086181663226861399676263756473802641672874027086738953875161061814579739785093180983441266855920231224636732191927912553374801111001032031344105759393238727712201315461624820092840684799220552397897751058516091818504683994004503712094403875551561260226306096872439487940279632420708865417105880788590191374379294935108187809507953193042057206862519016299678490711697295191179689592544152887760744179687047642966755598519324963472121188508781818126711623514320583653786741129337756997115655251601926037712636446508921248588533731892711973749354213484200827813256823435250379641153669517185340681079542004804595019609410269508862875966853970036440088103526841996156597511373134064400194003192243206660848718655435836802368189624213950150457557237312042754261620974205773407076050849985906734630611842850846412688633125229010010230280004162562820841074212240164102418871593501231416640162669803742972001646483979745683198628205640654263500931140489516330323158148365821920810604205226536046430945522248087778231567956103154757353181685989473545865436217134860783889718200284337451455878551134209496662998285791767391816839447144666883054788274770859542953558974323681953674378430289840097053205574847964776704379415753573829388458645713700321766129945403581375477071021655744926568193647401095320993269450359051138756530628950217078025133975357208669349519880026212752844392125753591115937752142228460646895231458070036112291456071967847038437705590399206730014222227617521262860270295418151231651766708762797725638468570136972912889280006514815601160749865032417898716479129236640044230712093886819433480009204353945556802135162199830089465268131868334370482452150407461136082279636890740454619987998762048596961181012257131385710860940858060725636225498213603621269082716005485680204485521184152392029851904911709374430747353899766460579196984272742172417694871241612065532421316086934763080317381766827209654293853316232514591477263606564906670197202733213614314010617105600198154831212191207677067026501810378937249592610819686843043393839906604515864979982668302868761371424783609011778839590828053955479748807156433497772155148222876891387694049462840389744661437055783117046740715811321267177251687789420486197941844194206821531185220811742909960211153516613181029855382994630593384307355347065706636625655467555510546163699313740952248712648728933844914654430524555780677972107869167664409010034209379832931755815572453153368455716845847906517344767929812778092740674029527997067613153821297471074044893834773685666506746460369453792242493261073755393191063068641052669614899109247182755788911768968833427629158252955425494789954520983109503293467862424700201649585533270620163535947524870640861541064500217887677510002026512790062321338308967598697847301432412682134615448314763396681535590380502504658139358668481218022508403065646236363527902677132571588341733977902084803190516752948039876548441113642607823979822676006257798491808653256103103224547645335090614960151292220735621259883176405609069370399879396738764274229718176271123840322937585980483709799790962415968175408273088627944945543831392422594153018780437583765813854032874173910611821666151942738963449159292230928551237297439307611746664055902841571019937629948218792953182175960462325212600515270537660340593154829969045132901495659706304292624540917027064057065810950652195575844170267633365994885900313790176173525630428025900440699086379797382725250323834477343313277858266718519153788505629915916508184196005543095894185222761435442262092653843595450867382789300391331078731333202544092866286451543191462643950191451204508802104291435864768125347930223634246009681582807125746201227810862841145995249901315300352321242380989415692507347744999906790573749411926014677837757955200698221412827438864510850000189970972368783790431301440632520155171187425694123222077108144188762870870356660418791452106789602123366129479101256130849309771886076109107572011648291716959775886051231317130045077710566424237990620382158747952015661774944197992433417152584725390355546798064124873531705509276051281526465513255353670013440765534717675146099411911003911475168743097688398863055816108365946134637174921370541239353194154006722451634873122343211847110254537700270922787417900722619858958654051697923521916077215476754182180744330154286424076378122293045799692873657126077437354337251622422786883423724577288330899138086911910981597146604462272435110053749317167865190041231504786214288140054058626485455627974475113685542314107299622925248477013202997449464955407344785003709400905500329757910191688937366454228543547867739407440725931456178642535848623789150126189561338548486634418484056211186084572970421787362040973377481923076393315220069396138096401012923071837944066527194809393672088460666129007894041449756392268792082097251552311225464751038402009541534844525125441409820079120800918190220621060007270553870446532523723269968843699846926983542888565266624801492946951906201573574432177999425737018150353002714541577812424749856061336206185867189849508848371454843034121501660716623127836700883816851793609451315751354691690568714913745468717603101737127221163235865081395514066489292376384558447763103399462790143726529254227401460167844682625652287701185363247363274827604629100687178204069839266623288633693081183846442891577796706495653065335275727736671716121531320077284565629626844748536633134530404942102088782287200104651898159807312455000897657160257363756247079939275566998245199034369559616726480740092067968634442583129586211399811127028455596344906226888611505495206159334243389860122566414095139019204198935379031309539451073131969452011009861081824351663969934869648101813657683417003527719525779836590148564307312828752546173580530663495714921374488031539310808113205839313159868715510405753484578784072312789722843037785766890455046249415509944224737874130197383067996172044236879291221432651646595761355101574981642001043350106705795445935203467619377073545796132663339060460231522458109348973901026706286618858877824799636084075518602533720548961082647256770725517896419998903115711064404324186935823566858884873412016439697401365458295478498506746142335992995292670539171842147454846461625353460493895896429163294497914542798108778511282580202531198762538461892136439900073900776841711956576242799016414802178365653098736323275390382994245642559650721743307100009126599014188899719403247029699850864815452023992073485802632815626648110300077712515715741206884494728050238787972916230901449110144176979025752066289450963243910476354755464262405124825131487011234075186133025142327871169090116714324474448837054172888018782268035597924882908143091390723683810977590509944376096419377604412235242829847522750338420106142972345352501271435209872395414032266984962995364723992644524054633599491150598674190349078114105777339596453667658842453132504067598203644228724477552753602074051369933005133680233944850732009303475650500322268923732550654277555980780092804284016961636050640862662400885926081709389669420543881087688746288416268694551088898566485387241887807457598515884960342532426611524815974039467792859885599444068238651834073783820107103404298560552554296948573875688809661255931237669026379678362936786914098528505018355025708154915770658053789690799050963135988140802462390541267016707487559534436510606497345275267161841682276303268660886382045158803133583270713502706555486309107570364571608934968251311096210402188620454253064112195414400711179625811759679799081233424751657277383808832184027215505639635033335910428222767191407084287517052360925758910654921002869164527352312273355527069552182735644248871675299519588189379795717421067788150938812806451955877493530914646649290717170907820354538245511621039262389398008972706832929801490687204855169201284502881485244769093336267728772040326396345636475063511771835686078767037302233703895749301057616727448110701500372937001088482904454457397112655347843950806506578874234440144468821668963504432424379203659555666785080890276885129345951583693088036780461316952692902842634073712696242955559244021351003506928341765467861017734139693696161178198548434247029064358029427750934064668080318203768789854179079917936937442669044033720907679691282206723221529905917188259176400814204278864876462414786287939233541536690609781254710763956858907526833933256697469256109002545908923099743992761839780267120291853191509459738560492471181061294985064640815776030219656694122275406657263317759114894828630028315145052109734748396910416269222344224691476091106437909019712325272439434551845475292442571863891677887909170457860968496807487165508455690865771300912444253423264841406068036783082011067208387307820141999090600324206598889000924404631182316862681110041428428020704677201933946733554029616190781213524693457776411958117219066493957262695338055017831917974105805869671653005168620284104116834190038894192823688884735324707775918622462221257043726670243731128549006272223939417351723330042382527009324899358748596032819227415536477635850464886327611227738087106083811134744603937214754734354310376054297910504019523454814685180491805732899562074522364055621322585294897302519478908664673669091866246325044864730097363285707407934811845410

/-- The product of the primes up to `10000` (script `gen_tables.py`). -/
def Q4 : ℕ := 59490679579998635868564022242503445659680322440679327938309703916140405638383434744833220555452130558140772894046169700747186409941317550665821619479140098743288335106272856533978719769677794737287419461899922456614256826709727133515885581878614846298251428096512495590545989536239739285290509870860732435109794045491640561011775744617218426011793283330497878491137999673760740717904979730106994180691956740996319139767941335979146924614249205862051182094081815447356600355657858936442589201739350474320966093143098768914226528498860747050474426418211313776073365498029087492308102876323562641651940555529817223923967479711293692697592800750806084802623966596666156361791014935954720420383555300213829134029560826306201326905674141090667002959274513478562033467485802590354539887133866434256562999666615074220857502563011098759348850149774083443643246907501430076141377431759984926248272553982527014011245310690986644461251576837779050124866641531488351016070300247918750613207952783437248236577750579092103591540592540838395240861443615842939673889972504776455114767522430347610500271801944701491874649306605557851914677316523034726044356368337787113190245601235705959816327016988315321850324065292964680148884818699916224411245926491625245571963741062587277736372090007125908660590314049976206281064703285728879581199596401313352724403492043120507597057004633720111008838673185885941472392623805512709896864520875740497617898566981218781313900004406341154884180472153171064617953661517880143988867189622824081729539392205701820144922307223627345876707465251206005262622236311161449785941834002795854996108322186230425179217618301526151712928790928933798369678844576216735378555233905935973195721247604933753363412045618703247367192610615234835041956551569232557323060407648325565048712478527583315981204846341857095134567470182330491262285172727037299211391244340592936174221176781260586188162350081192408213470101717320475998863222409777310443027421196981193126541663212124245716187453863438039402316877152286468198891603632606578778749292403571792687832081974134637014026451921536576338243322267400651083805535119025415817887075652758045539565968044552126338330231434466204888993650859153585380124240540573308417330478048240203241631072371322849430883727355239704116556046700749530006852187064160849175332758172150251213637470549781080491037088372092203085237973008861896576796238915011886636658033019385943299986285181723378096425117379056207797455963451889971988904466449319007760192467211209692128894691704353648198130409333996534250878389064152054828983825841234644875996912485916827004219887033833599723481903489316488764021700996686817244736947119285629049355809027206179193628292018441744552168286541735687924729198455883895791600170372255284216915442808139396541702893732917062958054499525549626455191658842064247047426187897146172971001949767308335268505414284088528125611263685734457560292833389995980698745893243832547007166243476192958601735336260255598581701267151224204461879782815468518040925292817115377696676461775120750971210951527384637825092221708015393564320979357698186262039029460777050248162599194429941464248920952161182024344007059684970270762248243899640259750891406957836740989312390963091260380990901672119736141666856448171380781556117025832312710039041398538035351795267732240730608951176127282191528457681241590895740457571038936173983449289126574141189374690274057472401359482497502067814596008557725079835212621242944853319496441084441343866446380876967613370281793088540430288658573281302876742323336651987699532240686371751448290351615451932054274752105688318766958111191822471878078268490672607804265064578569581247796205593441336042254502454646980009177290888726099355974892680373341371214123450598691915802122913613669446370194221846225597401405625536693874723700374068542217340621938985167525416725638580266200550048001242788847319217369432802469735271132107428204697172144851088692772696511622350096452418244968500432645305761138012204888798724453956720733374364721511323104353496583927094760495687785031050687852300161433757934364774351673531859394855389527851678630166084819717354779333605871648837631164630550613112327670353108353791304451834904017538583880634608113426156225757314283269948216017294095002859515842577481167417167637534527111130468710

/-- The ladder: `(X, P)` with `P` the product of the primes up to `X = 2 ^ i`. -/
def ladT : List (ℕ × ℕ) :=
  [(2, L1), (4, L2), (8, L3), (16, L4), (32, L5), (64, L6), (128, L7), (256, L8), (512, L9), (1024, L10), (2048, L11), (4096, L12), (8192, L13), (16384, L14), (32768, L15), (65536, L16), (131072, L17)]

set_option maxRecDepth 200000 in
private theorem good_L1 : EntGood 2 L1 :=
  entGood_step entGood_one (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L2 : EntGood 4 L2 :=
  entGood_step good_L1 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L3 : EntGood 8 L3 :=
  entGood_step good_L2 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L4 : EntGood 16 L4 :=
  entGood_step good_L3 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L5 : EntGood 32 L5 :=
  entGood_step good_L4 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L6 : EntGood 64 L6 :=
  entGood_step good_L5 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L7 : EntGood 128 L7 :=
  entGood_step good_L6 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L8 : EntGood 256 L8 :=
  entGood_step good_L7 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L9 : EntGood 512 L9 :=
  entGood_step good_L8 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L10 : EntGood 1024 L10 :=
  entGood_step good_L9 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L11 : EntGood 2048 L11 :=
  entGood_step good_L10 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L12 : EntGood 4096 L12 :=
  entGood_step good_L11 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L13 : EntGood 8192 L13 :=
  entGood_step good_L12 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L14 : EntGood 16384 L14 :=
  entGood_step good_L13 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L15 : EntGood 32768 L15 :=
  entGood_step good_L14 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L16 : EntGood 65536 L16 :=
  entGood_step good_L15 (by norm_num) (by decide +kernel)

set_option maxRecDepth 200000 in
private theorem good_L17 : EntGood 131072 L17 :=
  entGood_step good_L16 (by norm_num) (by decide +kernel)

/-- Every ladder entry is certified. -/
theorem ladT_good : LadGood ladT := by
  intro x hx
  simp only [ladT, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [good_L1, good_L2, good_L3, good_L4, good_L5, good_L6, good_L7, good_L8, good_L9, good_L10, good_L11, good_L12, good_L13, good_L14, good_L15, good_L16, good_L17]


set_option maxRecDepth 200000 in
/-- Every prime up to `10000` divides `Q4`. -/
theorem Q4_good : QGood 10000 Q4 := qGood_of (by norm_num) (by decide +kernel)

/-- The search with the tables `ladT`, `Q4` and the hoisting threshold `3 * 10 ^ 6`. -/
def run (f : ℕ) (l : List Ent) (j m : ℕ) : Bool := solve ladT 10000 Q4 3000000 f l j m

/-- Soundness of `run`, in the shape of `OmegaSixSearch.solve_sound`. -/
theorem run_sound (f : ℕ) (l : List Ent) (j m : ℕ) (h : run f l j m = true) {N : ℕ} :
    ¬ Holds N l j m :=
  solve_sound' ladT_good Q4_good 3000000 f l j m h N

/-- An accepted state is closed. -/
theorem closed_of_run {f : ℕ} {l : List Ent} {j m : ℕ} (h : run f l j m = true) :
    OmegaSevenSearch.Closed l j m := fun _ => run_sound f l j m h

end

end OddPerfect.OmegaSevenEngine

#print axioms OddPerfect.OmegaSevenEngine.solve_sound'
#print axioms OddPerfect.OmegaSevenEngine.entGood_one
#print axioms OddPerfect.OmegaSevenEngine.entGood_step
#print axioms OddPerfect.OmegaSevenEngine.ladT_good
#print axioms OddPerfect.OmegaSevenEngine.Q4_good
#print axioms OddPerfect.OmegaSevenEngine.run_sound
#print axioms OddPerfect.OmegaSevenEngine.closed_of_run
