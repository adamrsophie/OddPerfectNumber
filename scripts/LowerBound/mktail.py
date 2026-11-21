# Untrusted helper script for the OddPerfect Lean library.
# Writes the final section of LowerBound.lean for a bound B with trees for the primes below P:
# the theorems good<p>, card_primeFactors_of_no_prime_lt_P and lower_bound.
# Used by: OddPerfect/LowerBound.lean (the section after "Generated trees (END)").
# Run: python3 mktail.py 79 11 tail.lean
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

"""Write the final section of LowerBound.lean for a bound B with trees for the primes below P."""
import sys
from fractions import Fraction as F

def isp(n): return n > 1 and all(n % d for d in range(2, int(n ** .5) + 1))

def wrap(xs, ind):
    import textwrap
    return textwrap.fill('[' + ', '.join(map(str, xs)) + ']', 96 - ind, subsequent_indent=' ' * ind)

import os
SPLIT = os.environ.get('SPLIT')

def main(B, P, out):
    roots = [p for p in range(3, P) if isp(p)]
    # T: maximal list of consecutive primes from P with prod t/(t-1) < 2 L/(L-1)
    pr = [p for p in range(P, 20000) if isp(p)]
    x, k = F(1), 0
    for i, q in enumerate(pr):
        x *= F(q, q - 1)
        if x < 2 * F(q, q - 1): k = i + 1
        else: break
    T = pr[:k]; L = T[-1]
    l = pr[:k - 1]
    import math
    assert P * math.prod(l) ** 2 > 10 ** B, 'final bound too weak'
    o = ['/-! ## The lower bound -/\n']
    for i, p in enumerate(roots if not SPLIT else []):
        st = ', '.join(['.pw %d 1' % p] + ['.nd %d' % q for q in roots[:i]])
        cond = ', '.join(['`%d ∤ N`' % q for q in roots[:i]] + ['`%d ∣ N`' % p])
        o.append('/-- The tree for %s. -/\ntheorem good%d : Good (10 ^ %d) [%s] :=\n'
                 '  run_sound table_prime tree%d [[%s]] (by decide +kernel) _ List.mem_cons_self\n' % (cond, p, B, st, p, st))
    o.append('/-- If no prime below `%d` divides an odd perfect number `N`, then `N` has at least `%d`\n'
             'distinct prime factors. -/\n'
             'theorem card_primeFactors_of_no_prime_lt_%d {N : ℕ} (h : OddPerfect N)\n'
             '    (hP : ∀ p, p.Prime → p < %d → ¬ p ∣ N) : %d ≤ N.primeFactors.card :=\n'
             '  length_le_card_primeFactors h (P := %d) (L := %d)\n'
             '    %s\n    (by decide) hP (by decide) (by decide +kernel)\n'
             '    (by norm_num [List.map, List.prod_cons])\n' % (P, k, P, P, k, P, L, wrap(T, 4)))
    o.append('/-- Every odd perfect number exceeds `10 ^ %d`. -/\n'
             'theorem lower_bound {N : ℕ} (h : OddPerfect N) : 10 ^ %d < N := by' % (B, B))
    for i, p in enumerate(roots):
        o.append('  by_cases h%d : %d ∣ N' % (p, p))
        o.append('  · refine good%d N h fun f hf => ?_' % p)
        o.append('    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf')
        o.append('    rcases hf with %s' % ' | '.join(['rfl'] * (i + 1)))
        o.append('    · exact ⟨by norm_num, by simpa using h%d⟩' % p)
        for q in roots[:i]: o.append('    · exact h%d' % q)
    o.append('  have hP : ∀ p, p.Prime → p < %d → ¬ p ∣ N := by' % P)
    o.append('    intro p hp hlt hd')
    o.append('    interval_cases p')
    o.append('    all_goals first')
    o.append('      | exact h.not_two_dvd hd')
    for q in roots: o.append('      | exact h%d hd' % q)
    o.append('      | norm_num at hp')
    o.append('  have hc := card_primeFactors_of_no_prime_lt_%d h hP' % P)
    o.append('  have hm : ∀ p ∈ N.primeFactors, %d ≤ p := fun p hp => by' % P)
    o.append('    by_contra hlt')
    o.append('    exact hP p (Nat.prime_of_mem_primeFactors hp) (by omega) (Nat.dvd_of_mem_primeFactors hp)')
    o.append('  calc 10 ^ %d < %d *\n      %s.prod ^ 2 := by\n        norm_num' % (B, P, wrap(l, 8)))
    o.append('    _ ≤ N := le_of_card_primeFactors_consec h _ (by decide +kernel) hm (by simp; omega)')
    o.append('\nend OddPerfect.LowerBound\n')
    open(out, 'w').write('\n'.join(o))

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3])
