import OddPerfect.Pratt

/-!
# A certificate checker for factor chain trees with the defect ledger: code

This module holds only the computable part of the checker: the parameters, the search state,
the certificate term and the Boolean checker `check`. It imports nothing but `OddPerfect.Pratt`,
so that data modules that only evaluate the checker load quickly. The meaning of a state and the
soundness theorem `check_sound` live in `OddPerfect.DefectTreeCheck`. The checker is a tool: an
accepted certificate refutes exactly the hypotheses of `check_sound`, nothing more.

## The setting

`N` is an odd perfect number, `q` its special prime, `D = supportDefect N q` and `T` the total
excess. The parameters `P` give the hypotheses carried by the whole tree: `P.w * ω(N) + D ≤ P.K`,
every prime factor of `N` is at least `P.u`, the prime `P.root` divides `N`, and, when
`P.cap = some c`, `T ≤ c`.

## The state

A state has a list `os` of ordinary entries `(p, e, exact)` and a number `sp`. An entry with
`exact = true` says that `p` is a prime factor of `N`, `p ≠ q` and `v_p(N) = e`; with
`exact = false` it says `p ≠ q` and `4 ≤ e ≤ v_p(N)`. The number `sp` is `0` (the special prime
is not assigned) or the special prime `q`.

## Rows and facts

The row of an exact entry `(p, e)` is `σ(p ^ e) = gs p e`, the row of the special prime is
`q + 1 = gs q 1`. The rows are never factored by the checker. A table `tab` lists for some pairs
`(p, m)` facts `(r, k)` with `r ^ k ∣ gs p m`, `r` an odd prime (trial division below 200, a
Pratt certificate above) and `k ≥ 1`; `tabOK` checks the whole table once. Each fact makes `r` a
prime factor of `N` (a forced prime) and gives weight at least `k` from `p` to `r`.

## Leaves

* `cap r`: capacity at an exact entry `r`: the facts of distinct sources give weight above
  `v_r(N)`.
* `small r`: a forced prime below `P.u`.
* `budget`: the entries alone give `T > c` when `P.cap = some c`.
* `ledger ks`: for every candidate `c` of the special prime, `P.w * #ks` plus the lower bound
  `bound P tab st c` for `D` exceeds `P.K`, where `ks` lists distinct known primes.
* `abund ws`: a list of prime powers `p ^ f` below the exact powers with
  `∏ σ(p ^ f) > 2 * ∏ p ^ f`.

## Branches

`br r sp ch` branches on a forced prime `r` that is not assigned (at the root: on `P.root`).
The child `sp` is the case `r = q`; it is checked only when no special prime is assigned and
`r % 4 = 1`, which covers every possible case since `q % 4 = 1`. The chain `ch` lists the
exponents `2, 4, 6, …` with `ord kid rest` (the exponent is exactly the current one, or at
least two more) and ends with `high kid` (the exponent is at least the current one, which must
be at least 4).
-/

namespace OddPerfect

namespace DefectTree

/-- The parameters: the bound `K` for `w * ω(N) + D`, the weight `w`, the lower bound `u` for the
prime factors, the root prime, and the optional cap for the total excess. -/
structure Params where
  K : ℕ
  w : ℕ
  u : ℕ
  root : ℕ
  cap : Option ℕ
  deriving DecidableEq, Repr

/-- A state: ordinary entries `(p, e, exact)` and the special prime (`0` when not assigned). -/
structure St where
  os : List (ℕ × ℕ × Bool)
  sp : ℕ
  deriving DecidableEq, Repr

/-- The leaf rules with their witnesses. -/
inductive Leaf where
  /-- Capacity at the exact entry `r`. -/
  | cap (r : ℕ) : Leaf
  /-- The forced prime `r` is below the lower bound `u`. -/
  | small (r : ℕ) : Leaf
  /-- The exponents of the entries alone exceed the cap for the total excess. -/
  | budget : Leaf
  /-- The ledger, with a list of distinct known primes for the term `w * ω(N)`. -/
  | ledger (ks : List ℕ) : Leaf
  /-- An abundant divisor `∏ p ^ f` given by the pairs `(p, f)`. -/
  | abund (ws : List (ℕ × ℕ)) : Leaf
  deriving DecidableEq, Repr

/-- The certificate term. -/
inductive Cert where
  /-- A leaf. -/
  | leaf (l : Leaf) : Cert
  /-- Branch on the prime `r`: the child for `r = q` and the chain of exponents. -/
  | br (r : ℕ) (sp ch : Cert) : Cert
  /-- In a chain: the current exponent exactly, then the rest of the chain. -/
  | ord (kid rest : Cert) : Cert
  /-- In a chain: the exponent is at least the current one. -/
  | high (kid : Cert) : Cert
  /-- No child. -/
  | nil : Cert
  deriving Repr

/-- Where a certificate node sits: an ordinary node, the root, or a chain for the prime `r` at
the exponent `e`. -/
inductive Mode where
  | node : Mode
  | root : Mode
  | chain (r e : ℕ) : Mode

/-- The fact table: entries `(p, m, facts)`. -/
abbrev Tab := List (ℕ × ℕ × List (ℕ × ℕ))

/-- A flat Pratt certificate. -/
abbrev PCert := List (ℕ × ℕ × List ℕ)

/-- `gs p m = 1 + p + ... + p ^ m`. -/
def gs (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => gs p m + p ^ (m + 1)

/-- No repeated element. -/
def nodupB : List ℕ → Bool
  | [] => true
  | a :: l => !(l.contains a) && nodupB l

/-- The number paired with `r` in a list of pairs (the first one), or `0`. -/
def kOf (fs : List (ℕ × ℕ)) (r : ℕ) : ℕ :=
  match fs.find? (fun y => y.1 == r) with
  | some y => y.2
  | none => 0

/-- Primality: trial division below 200, membership in the Pratt certificate above. -/
def isPr (pc : PCert) (r : ℕ) : Bool :=
  (decide (r < 200) && Pratt.trialPrime r) || (pc.map Prod.fst).contains r

/-- The facts of the table for the row `gs p m` (none when the pair is absent). -/
def look (tab : Tab) (p m : ℕ) : List (ℕ × ℕ) :=
  match tab.find? (fun t => t.1 == p && t.2.1 == m) with
  | some t => t.2.2
  | none => []

/-- The check of the table: distinct primes in each entry, each an odd prime with a positive
exponent whose power divides the row. -/
def tabOK (pc : PCert) (tab : Tab) : Bool :=
  tab.all fun t => nodupB (t.2.2.map Prod.fst) && t.2.2.all fun y =>
    isPr pc y.1 && y.1 != 2 && decide (1 ≤ y.2) && gs t.1 t.2.1 % y.1 ^ y.2 == 0

/-- The facts of an entry: those of its row when it is exact, none otherwise. -/
def factsE (tab : Tab) (x : ℕ × ℕ × Bool) : List (ℕ × ℕ) :=
  if x.2.2 then look tab x.1 x.2.1 else []

/-- The facts of the special prime: those of `q + 1`. -/
def spFacts (tab : Tab) (st : St) : List (ℕ × ℕ) :=
  if st.sp = 0 then [] else look tab st.sp 1

/-- All facts of the state. -/
def allFacts (tab : Tab) (st : St) : List (ℕ × ℕ) :=
  spFacts tab st ++ st.os.flatMap (factsE tab)

/-- `r` is a forced prime. -/
def forcedB (tab : Tab) (st : St) (r : ℕ) : Bool :=
  (allFacts tab st).any fun y => y.1 == r

/-- `r` is not assigned. -/
def freshB (st : St) (r : ℕ) : Bool :=
  !(st.os.any fun x => x.1 == r) && r != st.sp

/-- The weight of the facts at receivers `r % 3 = 1` other than `c`. -/
def recvL (fs : List (ℕ × ℕ)) (c : ℕ) : ℕ :=
  ((fs.filter fun y => y.1 % 3 == 1 && y.1 != c).map Prod.snd).sum

/-- The lower bound for the terms of one entry in the support defect, with candidate `c`. -/
def entB (tab : Tab) (c : ℕ) (x : ℕ × ℕ × Bool) : ℕ :=
  if x.2.1 = 2 then recvL (factsE tab x) c - 1
  else if 4 ≤ x.2.1 then
    (if x.1 = 3 then 0 else 3 * (x.2.1 / 2 - 2)) + (if x.1 % 3 = 2 then x.2.1 else 0) +
      2 * kOf (factsE tab x) 3 + recvL (factsE tab x) c
  else 0

/-- The lower bound for `v_3(N) / 2 - 2`. -/
def threeT (st : St) : ℕ :=
  match st.os.find? (fun x => x.1 == 3) with
  | some x => x.2.1 / 2 - 2
  | none => 0

/-- The lower bound for the support defect with candidate `c` for the special prime. -/
def bound (P : Params) (tab : Tab) (st : St) (c : ℕ) : ℕ :=
  threeT st + (if 3 < P.u then 4 else 0) +
    (if st.sp = 0 then 0 else recvL (spFacts tab st) c) + (st.os.map (entB tab c)).sum

/-- The candidates for the special prime: the assigned one, or `0` (none of the forced primes)
and every forced prime that is 1 modulo 4. -/
def cands (tab : Tab) (st : St) : List ℕ :=
  if st.sp = 0 then 0 :: ((allFacts tab st).map Prod.fst).filter (fun r => r % 4 == 1)
  else [st.sp]

/-- `p` is a known prime factor: an entry, the special prime or a forced prime. -/
def knownB (tab : Tab) (st : St) (p : ℕ) : Bool :=
  (st.os.any fun x => x.1 == p) || (p == st.sp && p != 0) || forcedB tab st p

/-- The exponent `f` of `p` is allowed in an abundant divisor. -/
def allowB (tab : Tab) (st : St) (p f : ℕ) : Bool :=
  match st.os.find? (fun x => x.1 == p) with
  | some x => decide (f ≤ x.2.1)
  | none =>
    if p = st.sp ∧ p ≠ 0 then decide (f ≤ 1)
    else forcedB tab st p && (decide (f ≤ 1) || (decide (f ≤ 2) && (st.sp != 0 || p % 4 != 1)))

/-- The leaf checks. -/
def leafB (P : Params) (tab : Tab) (st : St) : Leaf → Bool
  | .cap r =>
    match st.os.find? (fun x => x.1 == r && x.2.2) with
    | some x => decide (x.2.1 < kOf (spFacts tab st) r +
        (st.os.map fun y => kOf (factsE tab y) r).sum)
    | none => false
  | .small r => forcedB tab st r && decide (r < P.u)
  | .budget =>
    match P.cap with
    | some c => decide (c < (st.os.map fun x => x.2.1 / 2 - 1).sum)
    | none => false
  | .ledger ks => nodupB ks && ks.all (knownB tab st) &&
      (cands tab st).all fun c => decide (P.K < bound P tab st c + P.w * ks.length)
  | .abund ws => nodupB (ws.map Prod.fst) &&
      (ws.map Prod.fst).all (fun p => allowB tab st p (kOf ws p)) &&
      decide (2 * ((ws.map Prod.fst).map fun p => p ^ kOf ws p).prod <
        ((ws.map Prod.fst).map fun p => gs p (kOf ws p)).prod)

/-- The condition on the branch prime: forced and not assigned at a node, the root prime at
the root. -/
def brHead (P : Params) (pc : PCert) (tab : Tab) (st : St) : Mode → ℕ → Bool
  | .node, r => forcedB tab st r && freshB st r
  | .root, r => r == P.root && isPr pc r && freshB st r
  | .chain _ _, _ => false

/-- `true` at an ordinary node. -/
def isNode : Mode → Bool
  | .node => true
  | _ => false

/-- The tree check. -/
def go (P : Params) (pc : PCert) (tab : Tab) : Cert → St → Mode → Bool
  | .leaf l, st, m => isNode m && leafB P tab st l
  | .br r spk ch, st, m =>
    brHead P pc tab st m r &&
      (if st.sp = 0 ∧ r % 4 = 1 then go P pc tab spk ⟨st.os, r⟩ .node else true) &&
      go P pc tab ch st (.chain r 2)
  | .ord kid rest, st, m =>
    match m with
    | .chain r e => go P pc tab kid ⟨(r, e, true) :: st.os, st.sp⟩ .node &&
        go P pc tab rest st (.chain r (e + 2))
    | _ => false
  | .high kid, st, m =>
    match m with
    | .chain r e => decide (4 ≤ e) && go P pc tab kid ⟨(r, e, false) :: st.os, st.sp⟩ .node
    | _ => false
  | .nil, _, _ => false

/-- The full check: the Pratt certificate, the table and the tree from the empty state at the
root. -/
def check (P : Params) (pc : PCert) (tab : Tab) (c : Cert) : Bool :=
  Pratt.check pc && tabOK pc tab && go P pc tab c ⟨[], 0⟩ .root

end DefectTree

end OddPerfect
