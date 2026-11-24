import OddPerfect.DefectTreeCode

/-!
# A certificate checker for the special component `5 ^ 1` with bounded components: code

This module holds only the computable part of the checker. It imports nothing but
`OddPerfect.DefectTreeCode` (and through it `OddPerfect.Pratt`), whose geometric sums `gs`,
fact tables `Tab`, Pratt certificates `PCert` and table check `tabOK` it reuses, so that data
modules that only evaluate the checker load quickly. The soundness theorem `check_sound` lives
in `OddPerfect.SpecialFiveCheck`. The checker is a tool: an accepted certificate for the bound
`B` refutes an odd perfect number `N` with `v_5(N) = 1` all of whose components
`p ^ v_p(N)` are at most `B`, nothing more.

## The setting

`N` is an odd perfect number with `v_5(N) = 1`, so `5` is the special prime and every other
prime factor has an even exponent, at least 2. Every component `p ^ v_p(N)` is assumed to be
at most `B`.

## The state

A state is a list of entries `(p, e)`: `p` is a prime factor of `N` with `v_p(N) = e`, and the
primes of the entries are distinct. The root state is `[(5, 1)]`.

## Facts

The row of an entry `(p, e)` is `σ(p ^ e) = gs p e`. The table `tab` (checked once by `tabOK`)
lists for some rows facts `(r, k)`: `r` an odd prime, `k ≥ 1` and `r ^ k ∣ gs p e`. A fact makes
`r` a prime factor of `N` (a forced prime) and says that the row sends at least `k` factors of
`r` to `σ(N) = 2 N`.

## Leaves and branches

* `cap r`: `r` is an entry `(r, e)` and the facts at `r` of all entries sum to more than `e`.
* `abund`: the entries give `∏ σ(p ^ e) > 2 * ∏ p ^ e`.
* `br r ch`: `r` is a forced prime, not an entry and not `5`, so its exponent is even and at
  least 2. The chain `ch` lists the exponents `2, 4, 6, …` with `ord kid rest` (the exponent is
  exactly the current one, or at least two more) and ends with `stop`, which checks
  `B < r ^ e` for the current exponent `e`. A chain that is a bare `stop` is a size leaf.
-/

namespace OddPerfect

namespace SpecialFive

open DefectTree (gs kOf look tabOK Tab PCert)

/-- The certificate term. -/
inductive Cert where
  /-- Capacity at the entry `r`. -/
  | cap (r : ℕ) : Cert
  /-- The entries form an abundant divisor. -/
  | abund : Cert
  /-- Branch on the forced prime `r` with the chain `ch` of its exponents. -/
  | br (r : ℕ) (ch : Cert) : Cert
  /-- In a chain: the current exponent exactly, then the rest of the chain. -/
  | ord (kid rest : Cert) : Cert
  /-- In a chain: the current power of the branch prime exceeds the bound. -/
  | stop : Cert
  deriving Repr

/-- Where a certificate node sits: an ordinary node, or a chain for the prime `r` at the
exponent `e`. -/
inductive Mode where
  | node : Mode
  | chain (r e : ℕ) : Mode

/-- All facts of the state. -/
def allFacts (tab : Tab) (st : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  st.flatMap fun x => look tab x.1 x.2

/-- `r` is a forced prime. -/
def forcedB (tab : Tab) (st : List (ℕ × ℕ)) (r : ℕ) : Bool :=
  (allFacts tab st).any fun y => y.1 == r

/-- `r` is not an entry. -/
def freshB (st : List (ℕ × ℕ)) (r : ℕ) : Bool :=
  !(st.any fun x => x.1 == r)

/-- The capacity leaf at `r`. -/
def capB (tab : Tab) (st : List (ℕ × ℕ)) (r : ℕ) : Bool :=
  match st.find? (fun x => x.1 == r) with
  | some x => decide (x.2 < (st.map fun y => kOf (look tab y.1 y.2) r).sum)
  | none => false

/-- The abundance leaf. -/
def abundB (st : List (ℕ × ℕ)) : Bool :=
  decide (2 * (st.map fun x => x.1 ^ x.2).prod < (st.map fun x => gs x.1 x.2).prod)

/-- The tree check. -/
def go (B : ℕ) (tab : Tab) : Cert → List (ℕ × ℕ) → Mode → Bool
  | .cap r, st, .node => capB tab st r
  | .abund, st, .node => abundB st
  | .br r ch, st, .node =>
    forcedB tab st r && freshB st r && r != 5 && go B tab ch st (.chain r 2)
  | .ord kid rest, st, .chain r e =>
    go B tab kid ((r, e) :: st) .node && go B tab rest st (.chain r (e + 2))
  | .stop, _, .chain r e => decide (B < r ^ e)
  | _, _, _ => false

/-- The full check: the Pratt certificate, the table and the tree from the root state
`[(5, 1)]`. -/
def check (B : ℕ) (pc : PCert) (tab : Tab) (c : Cert) : Bool :=
  Pratt.check pc && tabOK pc tab && go B tab c [(5, 1)] .node

end SpecialFive

end OddPerfect
