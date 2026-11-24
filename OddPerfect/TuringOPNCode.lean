/-!
# A 24 state Turing machine for odd perfect numbers: the definitions

This file holds only the definitions that a reader must trust. The machine is the 24 state,
2 symbol Turing machine published on P. Ochem's page on odd perfect numbers
(https://www.lirmm.fr/~ochem/opn/ , file `opn24.py`); the bbchallenge project lists machines of
this kind among its "Cryptids". In the standard bbchallenge text format (one block per state,
`A` to `X`, each block the action on reading 0 and then on reading 1) the machine is

`1RO0LT_0RI0RC_0RD1RC_1RE1RD_0LG0LF_0LH1LF_0RE1LG_1RB1LH_`
`0LK1RJ_1LS1RJ_0LL1LK_0LM1LL_1RN1LM_0RU0RO_0RP1RO_0RQ1RP_`
`1RR1RQ_0LS0LK_0LA1LS_0RB1LT_0RV0RW_---1RX_1RX1RW_1LK1RX`

(one string, shown on three lines). The table `table` below is this string, entry by entry.

Semantics (the standard one): two symbols, `false` for 0 and `true` for 1; a two way infinite
tape indexed by `Int`, initially all 0; the head starts at position 0 in state `A`. In state `q`
reading `b`, the entry `table q b = some (w, d, q')` writes `w` at the head, moves the head
(`L` subtracts one from the position, `R` adds one) and enters `q'`. The only undefined entry
is state `V` reading 0 (`table .V false = none`); the machine halts when it reaches it.

The statement proved about this machine (`OddPerfect.TuringOPN.halts_iff_exists_oddPerfect` in
`OddPerfect/TuringOPN.lean`) concerns this machine only. It gives no information on whether an
odd perfect number exists; that question is open.
-/

namespace OddPerfect

namespace TuringOPN

/-- The 24 states `A` to `X` of the machine; `A` is the start state. -/
inductive St
  | A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X
  deriving DecidableEq, Repr

/-- Head moves: `L` subtracts one from the head position, `R` adds one. -/
inductive Dir
  | L | R
  deriving DecidableEq, Repr

/-- A head move as a change of the head position. -/
def Dir.delta : Dir → Int
  | .L => -1
  | .R => 1

/-- The transition table: `table q b = some (w, d, q')` means that in state `q`, reading `b`,
the machine writes `w`, moves in direction `d` and enters state `q'`. The value `none` (only at
state `V` reading 0) means that the machine halts. -/
def table : St → Bool → Option (Bool × Dir × St)
  | .A, false => some (true, .R, .O)
  | .A, true => some (false, .L, .T)
  | .B, false => some (false, .R, .I)
  | .B, true => some (false, .R, .C)
  | .C, false => some (false, .R, .D)
  | .C, true => some (true, .R, .C)
  | .D, false => some (true, .R, .E)
  | .D, true => some (true, .R, .D)
  | .E, false => some (false, .L, .G)
  | .E, true => some (false, .L, .F)
  | .F, false => some (false, .L, .H)
  | .F, true => some (true, .L, .F)
  | .G, false => some (false, .R, .E)
  | .G, true => some (true, .L, .G)
  | .H, false => some (true, .R, .B)
  | .H, true => some (true, .L, .H)
  | .I, false => some (false, .L, .K)
  | .I, true => some (true, .R, .J)
  | .J, false => some (true, .L, .S)
  | .J, true => some (true, .R, .J)
  | .K, false => some (false, .L, .L)
  | .K, true => some (true, .L, .K)
  | .L, false => some (false, .L, .M)
  | .L, true => some (true, .L, .L)
  | .M, false => some (true, .R, .N)
  | .M, true => some (true, .L, .M)
  | .N, false => some (false, .R, .U)
  | .N, true => some (false, .R, .O)
  | .O, false => some (false, .R, .P)
  | .O, true => some (true, .R, .O)
  | .P, false => some (false, .R, .Q)
  | .P, true => some (true, .R, .P)
  | .Q, false => some (true, .R, .R)
  | .Q, true => some (true, .R, .Q)
  | .R, false => some (false, .L, .S)
  | .R, true => some (false, .L, .K)
  | .S, false => some (false, .L, .A)
  | .S, true => some (true, .L, .S)
  | .T, false => some (false, .R, .B)
  | .T, true => some (true, .L, .T)
  | .U, false => some (false, .R, .V)
  | .U, true => some (false, .R, .W)
  | .V, false => none
  | .V, true => some (true, .R, .X)
  | .W, false => some (true, .R, .X)
  | .W, true => some (true, .R, .W)
  | .X, false => some (true, .L, .K)
  | .X, true => some (true, .R, .X)

/-- A configuration: the state, the head position and the tape (`true` is the symbol 1). -/
structure Cfg where
  /-- The current state. -/
  state : St
  /-- The head position. -/
  pos : Int
  /-- The tape contents. -/
  tape : Int → Bool

/-- One step of the machine: `none` when the table entry for the current state and the symbol
under the head is undefined, otherwise the next configuration. -/
def step (c : Cfg) : Option Cfg :=
  match table c.state (c.tape c.pos) with
  | none => none
  | some (w, d, q) => some ⟨q, c.pos + d.delta, fun x => if x = c.pos then w else c.tape x⟩

/-- The initial configuration: state `A`, head at position 0, blank tape (all 0). -/
def init : Cfg := ⟨.A, 0, fun _ => false⟩

/-- `run k c` is the configuration after `k` steps from `c`, or `none` if the machine halts
(reaches the undefined entry) before `k` steps have been made. -/
def run : Nat → Cfg → Option Cfg
  | 0, c => some c
  | k + 1, c => (step c).bind (run k)

/-- The machine halts from the blank tape: some configuration reached after finitely many steps
has no successor. -/
def Halts : Prop := ∃ k c, run k init = some c ∧ step c = none

end TuringOPN

end OddPerfect
