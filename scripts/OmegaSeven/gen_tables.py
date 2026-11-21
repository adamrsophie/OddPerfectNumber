# Untrusted helper script for the OddPerfect Lean library.
# Generates the table section of OddPerfect/OmegaSevenEngine.lean: the ladder entries L1..L17
# (products of the primes up to 2^i), Q4 (product of the primes up to 10^4), and one kernel
# certificate per ladder step.
# Used by: OddPerfect/OmegaSevenEngine.lean (L1 .. L17, Q4, ladT, good_L1 .. good_L17,
# ladT_good).
# Run: python3 gen_tables.py out.txt
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: the output file is written relative to the current folder.
# License: GPL 3, same as the repository.
import sys
from math import gcd
sys.set_int_max_str_digits(0)
def primorial(x):
    r = 1
    for d in range(2, x + 1):
        if gcd(d, r) == 1: r *= d
    return r
out = []
for i in range(1, 18):
    out.append('/-- The product of the primes up to `%d` (script `gen_tables.py`). -/' % 2**i)
    out.append('def L%d : ℕ := %d\n' % (i, primorial(2**i)))
out.append('/-- The product of the primes up to `10000` (script `gen_tables.py`). -/')
out.append('def Q4 : ℕ := %d\n' % primorial(10**4))
out.append('/-- The ladder: `(X, P)` with `P` the product of the primes up to `X = 2 ^ i`. -/')
out.append('def ladT : List (ℕ × ℕ) :=\n  [' + ', '.join('(%d, L%d)' % (2**i, i) for i in range(1, 18)) + ']\n')
prev = ('1', '1')
for i in range(1, 18):
    X = 2**i
    out.append('set_option maxRecDepth 200000 in')
    out.append('private theorem good_L%d : EntGood %d L%d :=' % (i, X, i))
    pg = 'entGood_one' if i == 1 else 'good_L%d' % (i - 1)
    out.append('  entGood_step %s (by norm_num) (by decide +kernel)\n' % pg)
    prev = (str(X), 'L%d' % i)
out.append('/-- Every ladder entry is certified. -/')
out.append('theorem ladT_good : LadGood ladT := by')
out.append('  intro x hx')
out.append('  simp only [ladT, List.mem_cons, List.not_mem_nil, or_false] at hx')
out.append('  rcases hx with ' + ' | '.join(['rfl'] * 17))
out.append('  ' + ' <;> '.join([]) + 'exacts [' + ', '.join('good_L%d' % i for i in range(1, 18)) + ']\n')
open(sys.argv[1], 'w').write('\n'.join(out) + '\n')
