import OddPerfect.SecondLargestPrime

/-!
# A faster form of the search for two prime factors above a bound

The search of `OddPerfect.SecondLargestPrime` is checked by the kernel one step at a time. Most
of the cost of a step is spent reading the entries of the state: the four abundancy products,
the lower bound from the exponents, the parity test, the entry of largest gap, the first
undecided prime and the excluded primes are each computed by a separate pass, and every pass
reads the entries through several layers of definitions.

This file defines `expandF` and `runF`, which compute exactly the same values as `expand` and
`run`, but gather everything they need from the entries in one pass (`info`), with one test of
the code of each entry. We prove `expandF_eq` and `runF_eq`, so a run checked with `runF`
certifies its stack exactly as a run checked with `run` does (`cert_stepF`). Nothing new is
proved about odd perfect numbers here; the gain is only in the cost of the kernel checks.
-/

namespace OddPerfect

namespace SLP

/-! ## The one pass summary -/

/-- What a step needs from the entries of a state, gathered in one pass. -/
structure Info where
  /-- The product `uN`. -/
  un : ℕ
  /-- The product `uD`. -/
  ud : ℕ
  /-- The product `lN`. -/
  ln : ℕ
  /-- The product `lD`. -/
  ld : ℕ
  /-- The largest bound `loEnt`. -/
  mlo : ℕ
  /-- The primes with an exact odd exponent, in order. -/
  odd : List ℕ
  /-- Every entry is excluded or exact. -/
  ax : Bool
  /-- The result of `pickBest`. -/
  pb : Option (ℕ × ℕ)
  /-- The first undecided entry. -/
  fu : Option Ent
  /-- The excluded primes, in order. -/
  ex : List ℕ

/-- One step of `pickBest` for an entry `(q, 2, k)`. -/
def pbStep (q k : ℕ) : Option (ℕ × ℕ) → Option (ℕ × ℕ)
  | none => some (q, k)
  | some y => if gapGt q k y.1 y.2 then some (q, k) else some y

/-- The summary of a list of entries. -/
def info (B : ℕ) : List Ent → Info
  | [] => ⟨1, 1, 1, 1, 0, [], true, none, none, []⟩
  | (q, c, k) :: l =>
    let I := info B l
    if Nat.beq c 0 then
      ⟨q * I.un, (q - 1) * I.ud, I.ln, I.ld, I.mlo, I.odd, false, I.pb, some (q, c, k), I.ex⟩
    else if Nat.beq c 1 then
      ⟨I.un, I.ud, I.ln, I.ld, I.mlo, I.odd, I.ax, I.pb, I.fu, q :: I.ex⟩
    else
      let s := gs q k
      let t := q ^ k
      let m := max (if B < 2 * k + 3 then 2 * k + 3 else 0) I.mlo
      if Nat.beq c 3 then
        ⟨s * I.un, t * I.ud, s * I.ln, t * I.ld, m,
          if Nat.beq (k % 2) 1 then q :: I.odd else I.odd, I.ax, I.pb, I.fu, I.ex⟩
      else
        ⟨q * I.un, (q - 1) * I.ud, s * I.ln, t * I.ld, m, I.odd, false,
          if Nat.beq c 2 then pbStep q k I.pb else I.pb, I.fu, I.ex⟩

/-- The primes with an exact odd exponent, as listed by `parityBad`. -/
def oddL (st : List Ent) : List ℕ :=
  (st.filter fun e => e.2.1 == 3 && e.2.2 % 2 == 1).map Prod.fst

/-- The excluded primes. -/
def exL (st : List Ent) : List ℕ := (st.filter fun e => e.2.1 == 1).map Prod.fst

/-! ## The fast step -/

/-- `parityBad` from the list of primes with an exact odd exponent. -/
def parityBadL (o : List ℕ) (pin kP : ℕ) (xP : Bool) : Bool :=
  let o := o ++ (if pin != 0 && xP && kP % 2 == 1 then [pin] else [])
  o.any fun a => o.any fun b => a != b

/-- `closed` from the summary. -/
def closedF (lo hi pin kP : ℕ) (xP : Bool) (I : Info) : Bool :=
  parityBadL I.odd pin kP xP || 2 * I.ld ≤ I.ln || (hi != 0 && hi < lo) ||
    (0 < lo && I.un * lo ≤ 2 * (lo - 1) * I.ud) ||
    (pin != 0 &&
      (I.un * pun pin kP xP < 2 * (I.ud * pud pin kP xP) ||
       (I.un * pun pin kP xP == 2 * (I.ud * pud pin kP xP) && !(xP && I.ax)) ||
       2 * (I.ld * pin ^ kP) < I.ln * gs pin kP))

/-- `newLo` from the summary. -/
def newLoF (lo : ℕ) (I : Info) : ℕ :=
  if I.ln < 2 * I.ld then
    max (max lo I.mlo) ((I.ln + (2 * I.ld - I.ln) - 1) / (2 * I.ld - I.ln))
  else max lo I.mlo

/-- `hiU` from the summary. -/
def hiUF (hi : ℕ) (I : Info) : ℕ :=
  if I.un < 2 * I.ud then minz hi ((2 * I.ud - 1) / (2 * I.ud - I.un)) else hi

/-- `newHi` from the summary. -/
def newHiF (g hi : ℕ) (I : Info) : ℕ := if 0 < g then minz (hiUF hi I) g else hiUF hi I

/-- `anyBig` from the result of `pickBest`. -/
def anyBigP (pb : Option (ℕ × ℕ)) (pin kP : ℕ) (xP : Bool) : Bool :=
  (match pb with
   | none => false
   | some y => gapBig y.1 y.2) || (pin != 0 && !xP && gapBig pin kP)

/-- `chooseU` from the summary. -/
def chooseUF (pin kP : ℕ) (xP : Bool) (I : Info) : Option Ent :=
  if anyBigP I.pb pin kP xP then none else I.fu

/-- `useP` from the result of `pickBest`. -/
def usePF (pin kP : ℕ) (xP : Bool) (pb : Option (ℕ × ℕ)) : Bool :=
  pin != 0 && !xP &&
    (match pb with
     | none => true
     | some y => gapGt pin kP y.1 y.2)

/-- `okEx` from the list of excluded primes. -/
def okExF (M : ℕ) (ex : List ℕ) (g lo pin p k : ℕ) : Bool :=
  ex.all (fun q => gs p k % q != 0) &&
    (if pin != 0 then !hasOut (M * pin) (gs p k) && !(p == pin && hasOut M (gs p k))
     else !hasOut M (gs p k) ||
       (lo ≤ cofree M 200 (gs p k) && (g == 0 || lo ≤ Nat.gcd g (cofree M 200 (gs p k)))))

/-- `adv` from the list of excluded primes. -/
def advF (M : ℕ) (ex : List ℕ) (g lo pin p : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | n + 1, k => if okExF M ex g lo pin p k then k else advF M ex g lo pin p n (nextValid p k)

/-- `setE`, by direct recursion. -/
def setEF (p c k : ℕ) : List Ent → List Ent
  | [] => []
  | e :: l => (if Nat.beq e.1 p then (p, c, k) else e) :: setEF p c k l

/-- The children of a state, computed as `expand` does, from the summary. -/
def expandF (B M W : ℕ) : State → Option (List State)
  | (st, g, lo, hi, pin, kP, xP) =>
    let I := info B st
    let lo2 := newLoF lo I
    let hi2 := newHiF g hi I
    if closedF lo2 hi2 pin kP xP I then some []
    else if pin == 0 && 0 < g && g < lo2 * lo2 then
      some [(st, g, g, g, g, nextValid g 0, false)]
    else if pin == 0 && hi2 != 0 && hi2 ≤ lo2 + W then
      some ((List.range' lo2 (hi2 + 1 - lo2)).filterMap fun c =>
        if Nat.gcd c M == 1 && (g == 0 || g % c == 0) then some (st, g, c, c, c, nextValid c 0, false)
        else none)
    else
      match chooseUF pin kP xP I with
      | some e =>
        some [(setEF e.1 2 (advF M I.ex g lo2 pin e.1 40 (nextValid e.1 0)) st,
            g, lo2, hi2, pin, kP, xP),
          (setEF e.1 1 0 st, g, lo2, hi2, pin, kP, xP)]
      | none =>
        if usePF pin kP xP I.pb then
          some ((if okExF M I.ex g lo2 pin pin kP then
              [(force st (gs pin kP), g, lo2, hi2, pin, kP, true)] else []) ++
            [(st, g, lo2, hi2, pin, advF M I.ex g lo2 pin pin 40 (nextValid pin kP), false)])
        else
          match I.pb with
          | none => none
          | some y =>
            some ((if okExF M I.ex g lo2 pin y.1 y.2 then
                [(force (setEF y.1 3 y.2 st) (gs y.1 y.2), gUp M g pin (gs y.1 y.2),
                  lo2, hi2, pin, kP, xP)] else []) ++
              [(setEF y.1 2 (advF M I.ex g lo2 pin y.1 40 (nextValid y.1 y.2)) st,
                g, lo2, hi2, pin, kP, xP)])

/-- `run` with `expandF` in place of `expand`. -/
def runF (B M W : ℕ) : ℕ → List State → Option (List State)
  | 0, L => some L
  | _ + 1, [] => some []
  | f + 1, s :: L =>
    match expandF B M W s with
    | none => none
    | some cs => runF B M W f (cs ++ L)

/-! ## The summary is correct -/

private theorem nbeq (a b : ℕ) : Nat.beq a b = (a == b) := by
  by_cases h : a = b
  · subst h; simp [Nat.beq_refl]
  · have hf : Nat.beq a b = false := by
      cases hb : Nat.beq a b
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h
    simp [hf, h]

private theorem info_cons (B q c k : ℕ) (l : List Ent) :
    info B ((q, c, k) :: l) =
      ⟨un1 (q, c, k) * (info B l).un, ud1 (q, c, k) * (info B l).ud,
        ln1 (q, c, k) * (info B l).ln, ld1 (q, c, k) * (info B l).ld,
        max (loEnt B (q, c, k)) (info B l).mlo,
        if (c == 3 && k % 2 == 1) = true then q :: (info B l).odd else (info B l).odd,
        (c == 1 || c == 3) && (info B l).ax,
        if (c == 2) = true then pbStep q k (info B l).pb else (info B l).pb,
        if (c == 0) = true then some (q, c, k) else (info B l).fu,
        if (c == 1) = true then q :: (info B l).ex else (info B l).ex⟩ := by
  rcases Nat.lt_or_ge c 4 with h | h
  · interval_cases c <;> simp [info, un1, ud1, ln1, ld1, loEnt, nbeq]
  · have h0 : c ≠ 0 := by omega
    have h1 : c ≠ 1 := by omega
    have h2 : c ≠ 2 := by omega
    have h3 : c ≠ 3 := by omega
    simp [info, un1, ud1, ln1, ld1, loEnt, nbeq, h0, h1, h2, h3, show 2 ≤ c by omega]

private theorem info_un (B : ℕ) : ∀ st : List Ent, (info B st).un = uN st
  | [] => rfl
  | (q, c, k) :: l => by
    have ih := info_un B l
    rw [info_cons]
    simp only [uN, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

private theorem info_ud (B : ℕ) : ∀ st : List Ent, (info B st).ud = uD st
  | [] => rfl
  | (q, c, k) :: l => by
    have ih := info_ud B l
    rw [info_cons]
    simp only [uD, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

private theorem info_ln (B : ℕ) : ∀ st : List Ent, (info B st).ln = lN st
  | [] => rfl
  | (q, c, k) :: l => by
    have ih := info_ln B l
    rw [info_cons]
    simp only [lN, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

private theorem info_ld (B : ℕ) : ∀ st : List Ent, (info B st).ld = lD st
  | [] => rfl
  | (q, c, k) :: l => by
    have ih := info_ld B l
    rw [info_cons]
    simp only [lD, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

private theorem info_mlo (B : ℕ) :
    ∀ st : List Ent, (info B st).mlo = (st.map (loEnt B)).foldr max 0
  | [] => rfl
  | (q, c, k) :: l => by
    rw [info_cons, List.map_cons, List.foldr_cons, ← info_mlo B l]

private theorem info_odd (B : ℕ) : ∀ st : List Ent, (info B st).odd = oddL st
  | [] => rfl
  | (q, c, k) :: l => by
    rw [info_cons, info_odd B l]
    simp only [oddL, List.filter_cons]
    split <;> simp_all

private theorem info_ax (B : ℕ) :
    ∀ st : List Ent, (info B st).ax = st.all fun e => e.2.1 == 1 || e.2.1 == 3
  | [] => rfl
  | (q, c, k) :: l => by
    rw [info_cons, info_ax B l, List.all_cons]

private theorem pickBest_cons (q c k : ℕ) (l : List Ent) :
    pickBest ((q, c, k) :: l) =
      if (c == 2) = true then pbStep q k (pickBest l) else pickBest l := by
  simp only [pickBest]
  cases pickBest l <;> by_cases h : c = 2 <;> simp [h, pbStep]

private theorem info_pb (B : ℕ) : ∀ st : List Ent, (info B st).pb = pickBest st
  | [] => rfl
  | (q, c, k) :: l => by
    rw [info_cons, info_pb B l, pickBest_cons]

private theorem info_fu (B : ℕ) :
    ∀ st : List Ent, (info B st).fu = st.find? fun e => e.2.1 == 0
  | [] => rfl
  | (q, c, k) :: l => by
    rw [info_cons, info_fu B l, List.find?_cons]
    by_cases h : c = 0
    · simp [h]
    · have h' : (c == 0) = false := by simpa using h
      simp [h']

private theorem info_ex (B : ℕ) : ∀ st : List Ent, (info B st).ex = exL st
  | [] => rfl
  | (q, c, k) :: l => by
    rw [info_cons, info_ex B l]
    simp only [exL, List.filter_cons]
    split <;> simp_all

private theorem all_exL (s : ℕ) : ∀ st : List Ent,
    (exL st).all (fun q => s % q != 0) = st.all (fun e => e.2.1 != 1 || s % e.1 != 0)
  | [] => rfl
  | (q, c, k) :: l => by
    have ih := all_exL s l
    simp only [exL, List.filter_cons, List.all_cons] at ih ⊢
    by_cases h : c = 1 <;> simp_all

/-! ## The fast step is the step -/

private theorem closedF_eq (B lo hi pin kP : ℕ) (xP : Bool) (st : List Ent) :
    closedF lo hi pin kP xP (info B st) = closed st lo hi pin kP xP := by
  simp only [closedF, closed, info_un, info_ud, info_ln, info_ld, info_odd, info_ax, allEx]
  rfl

private theorem newLoF_eq (B lo : ℕ) (st : List Ent) : newLoF lo (info B st) = newLo B st lo := by
  simp only [newLoF, newLo, info_ln, info_ld, info_mlo]

private theorem newHiF_eq (g hi : ℕ) (B : ℕ) (st : List Ent) :
    newHiF g hi (info B st) = newHi st g hi := by
  simp only [newHiF, hiUF, newHi, hiU, info_un, info_ud]

private theorem chooseUF_eq (pin kP : ℕ) (xP : Bool) (B : ℕ) (st : List Ent) :
    chooseUF pin kP xP (info B st) = chooseU st pin kP xP := by
  simp only [chooseUF, chooseU, info_pb, info_fu]
  rfl

private theorem usePF_eq (pin kP : ℕ) (xP : Bool) (st : List Ent) :
    usePF pin kP xP (pickBest st) = useP st pin kP xP := rfl

private theorem okExF_eq (M g lo pin p k B : ℕ) (st : List Ent) :
    okExF M (info B st).ex g lo pin p k = okEx M st g lo pin p k := by
  simp only [okExF, okEx, info_ex, all_exL]

private theorem advF_eq (M g lo pin p B : ℕ) (st : List Ent) :
    ∀ n k, advF M (info B st).ex g lo pin p n k = adv M st g lo pin p n k
  | 0, k => rfl
  | n + 1, k => by
    simp only [advF, adv, okExF_eq, advF_eq M g lo pin p B st n]

private theorem setEF_eq (p c k : ℕ) : ∀ st : List Ent, setEF p c k st = setE st p c k
  | [] => rfl
  | e :: l => by
    simp only [setEF, setE, List.map_cons, nbeq] at *
    rw [setEF_eq p c k l, setE]

/-- `expandF` computes exactly the children computed by `expand`. -/
theorem expandF_eq (B M W : ℕ) (s : State) : expandF B M W s = expand B M W s := by
  obtain ⟨st, g, lo, hi, pin, kP, xP⟩ := s
  simp only [expandF, expand, newLoF_eq, newHiF_eq, closedF_eq, chooseUF_eq, info_pb, usePF_eq,
    okExF_eq, advF_eq, setEF_eq]
  rfl

/-- `runF` computes exactly what `run` computes. -/
theorem runF_eq (B M W : ℕ) : ∀ (f : ℕ) (L : List State), runF B M W f L = run B M W f L
  | 0, L => rfl
  | _ + 1, [] => rfl
  | f + 1, s :: L => by
    simp only [runF, run, expandF_eq]
    cases expand B M W s with
    | none => rfl
    | some cs => exact runF_eq B M W f (cs ++ L)

/-- A run checked with `runF` certifies its initial stack from its final stack. -/
theorem cert_stepF {B M W K : ℕ} {L L' : List State} (hM : 2 * (primesUpTo B).prod = M)
    (h : runF B M W K L = some L') (h' : Cert B L') : Cert B L :=
  cert_step hM (by rw [← runF_eq]; exact h) h'

end SLP

end OddPerfect

#print axioms OddPerfect.SLP.expandF_eq
#print axioms OddPerfect.SLP.runF_eq
#print axioms OddPerfect.SLP.cert_stepF
