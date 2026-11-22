# Untrusted helper script for the OddPerfect Lean library.
# Generates OddPerfect/SecondLargestPrimeFastData1.lean .. SecondLargestPrimeFastData<NMOD>.lean
# and OddPerfect/SecondLargestPrimeTwo.lean: the search of OddPerfect.SecondLargestPrime for the
# bound B, started from the lower bound LO for the large prime, split into theorems of K steps
# checked with SLP.runF (OddPerfect/SecondLargestPrimeFast.lean); Two assembles the chain and
# derives the bound 58 as a corollary. The stacks come from slp.py.
# Used by: the modules named above.
# Run: python3 -I mkfast.py 72 500 10001 9 OUTDIR [TWO_NAME] [DATA_PREFIX]
#   (writes into OUTDIR; the landed modules are reproduced byte for byte with these arguments).
# Requires: Python 3.8 or later, standard library only. Deterministic; about 10 seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: imports slp.py from the folder of this script; writes only into OUTDIR.
# License: GPL 3, same as the repository.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from slp import init, run, Mof, fmt_stack, primesUpTo

B, K, LO, NMOD = map(int, sys.argv[1:5])
OUT = sys.argv[5]
TWO = sys.argv[6] if len(sys.argv) > 6 else 'SecondLargestPrimeTwo'
PRE = sys.argv[7] if len(sys.argv) > 7 else 'SecondLargestPrimeFastData'
NS = PRE.replace('SecondLargestPrime', '')
W = 10
M = Mof(B)
L = init(B, LO)
S = [L]
while L:
    L = run(B, M, W, K, L)
    assert L is not None, 'the search is stuck'
    S.append(L)
n = len(S) - 1
cuts = [round(i * n / NMOD) for i in range(NMOD + 1)]
os.makedirs(OUT, exist_ok=True)
for m in range(NMOD):
    a, b = cuts[m], cuts[m + 1]
    s = f'''import OddPerfect.SecondLargestPrimeFast

/-!
# Certificate data for two prime factors above `{B}`, part {m + 1} of {NMOD}

Steps {a * K} to {b * K} of the search of `OddPerfect.SecondLargestPrime` for `B = {B}`, started
from the lower bound `{LO}` for the large prime, in theorems of {K} steps checked with `SLP.runF`
(`OddPerfect.SecondLargestPrimeFast`), which computes exactly what `SLP.run` computes. The
stacks were found outside Lean by a program that reproduces `SLP.run`; the kernel checks every
step again.
-/

namespace OddPerfect.SLP.{NS}{m + 1}

/-- Decidable equality of search states. -/
private instance : DecidableEq State := fun a b => instDecidableEqProd a b

private theorem M_eq : 2 * (primesUpTo {B}).prod = {M} := by decide +kernel

/-- The stack at the start of this part. -/
def first : List State :=
  {fmt_stack(S[a])}

/-- The stack at the end of this part. -/
def last : List State :=
  {fmt_stack(S[b])}
'''
    for i in range(a + 1, b):
        s += f'\nprivate def S{i} : List State :=\n  {fmt_stack(S[i])}\n'
    name = lambda i: 'first' if i == a else ('last' if i == b else f'S{i}')
    for i in range(a, b):
        s += (f'\nset_option maxRecDepth 100000 in\nprivate theorem run{i} : runF {B} {M} {W} {K} {name(i)} = '
              f'some {name(i + 1)} := by\n  decide +kernel\n')
    chain = 'h'
    for i in reversed(range(a, b)):
        chain = f'cert_stepF M_eq run{i} ({chain})'
    s += f'''
/-- No state of `first` holds, given that no state of `last` holds. -/
theorem cert_first (h : Cert {B} last) : Cert {B} first :=
  {chain}

end OddPerfect.SLP.{NS}{m + 1}

#print axioms OddPerfect.SLP.{NS}{m + 1}.cert_first
'''
    open(f'{OUT}/{PRE}{m + 1}.lean', 'w').write(s)

imports = '\n'.join(f'import OddPerfect.{PRE}{m + 1}' for m in range(NMOD))
chain = f'cert_nil {B}'
for m in reversed(range(NMOD)):
    chain = f'{NS}{m + 1}.cert_first ({chain})'
st = '[' + ', '.join(f'({q}, 0, 0)' for q in primesUpTo(B)) + ']'
# the bound 58 of the former certificate in OddPerfect/SecondLargestPrime.lean, as a corollary
COR = '' if B <= 58 else f'''
/-- An odd perfect number has two distinct prime factors above `58`. -/
theorem exists_two_primeFactors_gt {{N : ℕ}} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, ∃ r ∈ N.primeFactors, p ≠ r ∧ 58 < p ∧ 58 < r := by
  obtain ⟨p, hp, r, hr, hpr, h1, h2⟩ := exists_two_primeFactors_gt_{B} h
  exact ⟨p, hp, r, hr, hpr, by omega, by omega⟩
'''
CORAX = '' if B <= 58 else '#print axioms OddPerfect.exists_two_primeFactors_gt\n'
open(f'{OUT}/{TWO}.lean', 'w').write(f'''{imports}

/-!
# Two prime factors above `{B}`

A formalization of a known type of result: lower bounds for the second largest prime factor
of an odd perfect number. Iannucci proved such bounds with far larger constants (the second
largest prime factor exceeds `10 ^ 4`); those published bounds are not proved here. We show that
an odd perfect number has two distinct prime factors above `{B}`, with the search engine of
`OddPerfect.SecondLargestPrime`, started from the lower bound `{LO}` for the large prime given
by `exists_primeFactor_gt`. The steps of the search were found outside Lean and are checked
again by the kernel in the modules `{PRE}1` to
`{PRE}{NMOD}`, with the fast step of `OddPerfect.SecondLargestPrimeFast`.
-/

namespace OddPerfect

namespace SLP

/-- A certified initial stack, with lower bound `{LO}` for the large prime, gives two distinct
prime factors above `B`. The initial entries `st` are given explicitly and checked. -/
theorem exists_two_of_cert_from {{B : ℕ}} {{st : List Ent}}
    (hst : (primesUpTo B).map (fun q => (q, 0, 0)) = st) (hB : B ≤ {LO - 1})
    (hc : Cert B [(st, 0, {LO}, 0, 0, 0, false)]) {{N : ℕ}} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, ∃ r ∈ N.primeFactors, p ≠ r ∧ B < p ∧ B < r := by
  subst hst
  obtain ⟨P0, hP0, hgt⟩ := exists_primeFactor_gt h
  by_contra hne
  have c : Ctx N B P0 :=
    ⟨h, Nat.prime_of_mem_primeFactors hP0, Nat.dvd_of_mem_primeFactors hP0, by omega,
      fun r hr hrP => le_of_not_gt fun hlt => hne ⟨P0, hP0, r, hr, Ne.symm hrP, by omega, hlt⟩⟩
  refine hc N P0 c _ (List.mem_singleton_self _) ⟨by rw [List.map_map]; exact List.map_id _,
    ?_, Or.inl rfl, show {LO} ≤ P0 by omega, Or.inl rfl, Or.inl rfl⟩
  intro e he
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp he
  exact ⟨fun h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩

private def st{B} : List Ent :=
  {st}

private theorem st{B}_eq : (primesUpTo {B}).map (fun q => (q, 0, 0)) = st{B} := by decide +kernel

private theorem cert{B} : Cert {B} [(st{B}, 0, {LO}, 0, 0, 0, false)] :=
  {chain}

end SLP

/-- An odd perfect number has two distinct prime factors above `{B}`. -/
theorem exists_two_primeFactors_gt_{B} {{N : ℕ}} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, ∃ r ∈ N.primeFactors, p ≠ r ∧ {B} < p ∧ {B} < r :=
  SLP.exists_two_of_cert_from SLP.st{B}_eq (by norm_num) SLP.cert{B} h
{COR}
end OddPerfect

#print axioms OddPerfect.SLP.exists_two_of_cert_from
#print axioms OddPerfect.exists_two_primeFactors_gt_{B}
{CORAX}''')
print(n, 'chunks', cuts)
