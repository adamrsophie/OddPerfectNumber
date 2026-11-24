#!/usr/bin/env python3
# Untrusted helper script for the OddPerfect Lean library.
# Paired fixtures for the low level helpers of the two exception engine: a fixed list of input
# vectors, the value that the Python mirror engine.py (in this folder) computes on each, and the
# Lean file CheckerControls/PairedControls.lean, in which the kernel checks that the helper of
# OddPerfect/TwoExcEngineCode.lean has that same value on the same input. The pairs are
# findDiv / find_div, smallPrime and primeB / small_prime, powModE / pow_mod_e, pfacs / pfacs,
# ordOK / ord_ok, findKey / key_find, lookupW / lookup_w, lookupP / lookup_p, qrTable and
# qrPass / QR_MODS, QR_SETS and qr_pass, newton / newton, sqrtIfSq / square_root_if_square.
# Run (any folder):
#     python3 -I paired.py emit         print the Lean file
#     python3 -I paired.py check FILE   compare FILE with that text, byte for byte
# Exit status: 0 for emit, and for check when the texts are equal; 1 when they differ (or when
# a generated line would exceed 100 characters); 2 for a usage error or an unreadable file.
# Requires: Python 3 standard library only. Running time: about a second.
# Untrusted: the Lean kernel checks every value, and the check mode only compares text.
# License: GPL 3, same as the repository.

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import engine  # noqa: E402

# The product of the moduli of the square filter: adding it keeps every residue of the filter.
Q = 92990138354449826827902565

# ---------------------------------------------------------------- numbers

def num(v):
    """A number of the vectors as (value, Lean text). A plain int, ('pow', a, b) for 2^a + b,
    or ('sq', a, b, c) for (2^a + b)^2 + c, where b and c may be negative."""
    def plus(t, b):
        return t if b == 0 else f'{t} + {b}' if b > 0 else f'{t} - {-b}'
    if type(v) is int:
        return v, str(v)
    if v[0] == 'pow':
        _, a, b = v
        return 2 ** a + b, plus(f'2 ^ {a}', b)
    _, a, b, c = v
    return (2 ** a + b) ** 2 + c, plus(f'({plus(f"2 ^ {a}", b)}) ^ 2', c)


def arg(v):
    """Lean text of an argument: parenthesized unless it is a plain number."""
    val, t = num(v)
    return val, t if type(v) is int else f'({t})'


def nat(n):
    """Lean text of a result: the numeral, or 2^a + b for a long number with a small b."""
    if len(str(n)) <= 40:
        return str(n)
    for a in (n.bit_length(), n.bit_length() - 1):
        b = n - 2 ** a
        if abs(b) < 10 ** 12:
            return num(('pow', a, b))[1]
    raise SystemExit(f'paired.py: no short Lean text for a result of {len(str(n))} digits')


def boolean(b):
    return 'true' if b else 'false'


def nats(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def key_text(k):
    return '⟨%d, %s, [%s]⟩' % (k[0], engine.lean_role(k[1]),
                               ', '.join('(%d, %d)' % tuple(e) for e in k[2]))

# ---------------------------------------------------------------- vectors

# Key lists, defined once in the Lean file under these names.
KEYS = {
    'ksNil': [],
    'ksA': [[3, ('sq',), []], [5, ('fr', True, 2, False, 1, False), [[13, 1]]],
            [7, ('sq',), [[3, 1], [5, 2]]]],
    'ksDup': [[7, ('sq',), []], [7, ('fr', False, 1, False, 4, False), [[3, 1]]]],
    'ksZero': [[0, ('sq',), []]],
}

# Each vector is (arguments, comment); an empty comment writes no comment line.
FIND_DIV = [  # (fuel, n, d)
    ((0, 91, 2), 'no fuel'),
    ((1, 0, 2), 'out of domain: n = 0'),
    ((1, 1, 2), 'out of domain: n = 1'),
    ((2, 7, 0), 'start d = 0: 7 % 0 = 7, then 7 % 1 = 0'),
    ((1, 0, 0), 'n = d = 0: 0 % 0 = 0'),
    ((6, 91, 2), 'the divisor 7 of 91 = 7 * 13: fuel exactly enough'),
    ((5, 91, 2), 'one step short'),
    ((9, 97, 2), 'the prime 97: fuel exactly enough to pass its square root'),
    ((8, 97, 2), 'one step short'),
    ((1, 25, 6), 'start above the square root'),
    ((2, 10, 3), 'start above the least divisor'),
    ((2, 4295098369, 65536), '65537 ^ 2 from 65536: fuel exactly enough'),
    ((1, 4295098369, 65536), 'one step short'),
    ((2, 4295098403, 65537), 'the prime 4295098403 from 65537: fuel exactly enough'),
    ((1, 4295098403, 65537), 'one step short'),
    ((32767, 1073741789, 2), 'the prime 1073741789 below 2 ^ 30: fuel exactly enough'),
    ((32766, 1073741789, 2), 'one step short'),
]
SMALL_PRIME = [  # n
    (0, ''), (1, ''), (2, ''), (4, ''), (91, ''), (97, ''), (4093, ''), (65537, ''),
    (1073741789, 'the largest prime below 2 ^ 30'),
    (1073741823, '2 ^ 30 - 1, divisible by 3'),
]
PRIME_B = [  # n: below 4096 the table PMASK, above trial division
    (0, ''), (1, ''), (2, ''), (4, ''), (4093, ''),
    (4095, 'the last entry of the table'), (4096, 'the first number above the table'),
    (4097, '17 * 241'), (4099, ''), (65537, ''),
]
PRIME_TABLE = [  # (Lean text, function of the list of the values of small_prime below 4096)
    ('(List.range 4096).countP primeB', lambda bs: sum(bs), 'the number of table primes'),
    ('((List.range 4096).filter primeB).sum', lambda bs: sum(i for i, b in enumerate(bs) if b),
     'the sum of the table primes'),
    ('((List.range 4096).filter primeB).foldl (fun a p => (a * 4099 + p) % 1000000007) 0',
     lambda bs: fold([i for i, b in enumerate(bs) if b]), 'a hash of the ordered table primes'),
]
POW_MOD = [  # (b, e, n)
    ((3, 0, 7), ''), ((3, 0, 1), 'modulus 1'), ((0, 0, 5), ''), ((2, 10, 1000), ''),
    ((100, 3, 7), 'base above the modulus'),
    ((5, 3, 0), 'out of domain: modulus 0, where a % 0 = a'),
    ((7, 1, 0), 'modulus 0'),
    ((2, 100, 1), 'modulus 1'),
    ((3, ('pow', 64, 13), 1000003), 'an exponent above 2 ^ 64'),
    ((10, 10 ** 18, 999999937), ''),
]
PFACS = [  # d
    (0, 'out of domain'), (1, 'out of domain'), (12, ''), (360, ''), (1001, ''),
    (9991, '97 * 103'),
]
ORD_OK = [  # (d, g, p)
    ((6, 3, 7), 'the order of 3 modulo 7'),
    ((3, 2, 7), 'the order of 2 modulo 7'),
    ((3, 3, 7), 'not a multiple of the order'),
    ((12, 3, 7), 'a multiple of the order'),
    ((6, 10, 7), 'a base above the modulus'),
    ((7, 8, 7), 'g = 1 modulo p: d must be p'),
    ((0, 3, 7), 'd = 0'),
    ((1, 0, 7), 'g = 0'),
    ((16, 5, 17), ''),
    ((1, 3, 2), 'modulus 2, g = 1 modulo 2, d = 1'),
    ((2, 3, 2), 'modulus 2, g = 1 modulo 2, d = 2'),
    ((1, 5, 1), 'out of domain: modulus 1, where 1 % 1 = 0'),
    ((2, 5, 1), 'modulus 1, d = 2'),
    ((0, 1, 0), 'out of domain: modulus 0, where 1 % 0 = 1'),
    ((5, 2, 0), 'modulus 0'),
]
FIND_KEY = [  # (p, name of a key list)
    ((3, 'ksA'), ''), ((5, 'ksA'), ''), ((7, 'ksA'), ''), ((11, 'ksA'), 'absent'),
    ((0, 'ksA'), 'absent, 0'), ((3, 'ksNil'), 'empty list'),
    ((7, 'ksDup'), 'the prime twice: the first key'), ((0, 'ksZero'), 'a key 0'),
]
LOOKUP_W = [  # (c, list of (component, weight))
    ((3, [(3, 1), (5, 2), (3, 4)]), 'the component twice: the first weight'),
    ((5, [(3, 1), (5, 2), (3, 4)]), ''),
    ((7, [(3, 1), (5, 2), (3, 4)]), 'absent'),
    ((0, [(0, 9)]), 'component 0'),
    ((3, []), 'empty list'),
]
LOOKUP_P = [  # (p, c, list of (prime, component, weight))
    ((13, 3, [(13, 3, 1), (13, 5, 2), (7, 3, 1), (13, 3, 5)]), 'the pair twice: the first weight'),
    ((7, 3, [(13, 3, 1), (13, 5, 2), (7, 3, 1), (13, 3, 5)]), ''),
    ((7, 5, [(13, 3, 1), (13, 5, 2), (7, 3, 1), (13, 3, 5)]), 'the prime without the component'),
    ((5, 3, [(13, 3, 1), (13, 5, 2), (7, 3, 1), (13, 3, 5)]), 'the component without the prime'),
    ((13, 3, []), 'empty list'),
]
# Trial division over the whole fuel of smallPrime (65536 candidates, numbers near 2 ^ 32) is
# left out: one such kernel evaluation takes minutes. The fuel boundary at the candidate 65537
# is fixed by starting findDiv at 65536 and 65537 instead.
# Values that fail exactly one test of the filter, in the order of the moduli, and the least
# value that passes every test without being a square.
FAIL_ONE = [15794, 126494, 50879, 108339, 758234, 524195, 182919]
PASS_NONSQUARE = 860574
QR_PASS = [  # z
    (0, ''), (1, ''), (10 ** 6, 'a square'),
    (PASS_NONSQUARE, 'the least nonsquare that passes'),
] + [(z, f'fails only modulo {m}') for z, m in zip(FAIL_ONE, engine.QR_MODS)] + [
    (('sq', 50, 3, Q), 'a nonsquare that passes'),
    (('sq', 500, 1, Q), 'a large nonsquare that passes'),
]
QR_BITS = [(z, '') for z in [PASS_NONSQUARE] + FAIL_ONE]
NEWTON = [  # (fuel, z, s)
    ((0, 7, 5), 'no fuel'),
    ((1, 7, 0), 'start 0: 7 / 0 = 0'),
    ((5, 100, 3), 'start below the root: no step'),
    ((5, 100, 10), 'start at the root'),
    ((52, 0, ('pow', 51, 0)), 'z = 0 from 2 ^ 51: fuel exactly enough'),
    ((51, 0, ('pow', 51, 0)), 'one step short'),
    ((34, 10 ** 12, ('pow', 51, 0)), 'a square from 2 ^ 51: fuel exactly enough'),
    ((33, 10 ** 12, ('pow', 51, 0)), 'one step short'),
    ((50, 99, ('pow', 51, 0)), 'a nonsquare from 2 ^ 51: fuel exactly enough'),
    ((49, 99, ('pow', 51, 0)), 'one step short'),
    ((56, ('pow', 102, 0), ('pow', 102, 0)), '2 ^ 102 from itself: fuel exactly enough'),
    ((55, ('pow', 102, 0), ('pow', 102, 0)), 'one step short'),
    ((400, ('pow', 784, 0), ('pow', 784, 0)),
     '2 ^ 784 from itself: the fuel of sqrtIfSq is enough'),
    ((399, ('pow', 784, 0), ('pow', 784, 0)), 'one step short'),
]
SQRT = [  # z
    (0, ''), (1, ''), (99, ''), (100, ''),
    (PASS_NONSQUARE, 'passes the filter, rejected by Newton'),
    (FAIL_ONE[0], 'rejected by the filter'),
    (10 ** 12, ''),
    (('sq', 51, -1, -1), 'below 2 ^ 102: Newton starts at 2 ^ 51'),
    (('sq', 51, -1, 0), ''),
    (('sq', 51, -1, 1), ''),
    (('sq', 51, -1, Q), 'passes the filter'),
    (('pow', 102, -1), ''),
    (('pow', 102, 0), 'from 2 ^ 102 on Newton starts at z'),
    (('pow', 102, 1), ''),
    (('sq', 51, 1, -1), ''),
    (('sq', 51, 1, 0), ''),
    (('sq', 51, 1, 1), ''),
    (('sq', 51, 1, Q), 'passes the filter'),
    (('sq', 50, 3, 0), ''),
    (('sq', 50, 3, Q), 'passes the filter'),
    (('pow', 784, 0), 'Newton settles in exactly 400 steps'),
    (('pow', 786, 0), 'Newton needs 401 steps: the outer none'),
    (('sq', 500, 1, 0), 'a large square: the outer none'),
    (('sq', 500, 1, Q), 'a large nonsquare that passes the filter: the outer none'),
]

# ---------------------------------------------------------------- the mirror side

def fold(ps):
    a = 0
    for p in ps:
        a = (a * 4099 + p) % 1000000007
    return a


def ord_ok(d, g, p):
    """ord_ok of the mirror; its rejection (a factor list that fails) is `ordOK = false`."""
    try:
        return engine.ord_ok(d, g, p)
    except engine.Reject:
        return False


def sqrt_text(z):
    """square_root_if_square of the mirror as the value of `sqrtIfSq`: a root s is
    `some (some s)`, None is `some none`, a rejection is the outer `none`."""
    try:
        s = engine.square_root_if_square(z)
    except engine.Reject:
        return 'none'
    if s is None:
        return 'some none'
    t = nat(s)
    return f'some (some {t if t.isdigit() else f"({t})"})'


def pairs(l):
    return '[' + ', '.join('(' + ', '.join(map(str, e)) + ')' for e in l) + ']'


def qr_bits(z):
    return [1 if z % m in engine.QR_SETS[m] else 0 for m in engine.QR_MODS]


def examples():
    """The groups: (heading, [(comment, Lean expression, Lean value)])."""
    g = []
    v = []
    for (f, n, d), c in FIND_DIV:
        v.append((c, f'findDiv {f} {n} {d}', nat(engine.find_div(n, d, f))))
    for n, c in SMALL_PRIME:
        v.append((c, f'smallPrime {n}', boolean(engine.small_prime(n))))
    g.append(('Trial division (`TwoExcEngine.findDiv`, `smallPrime`)', v))
    v = []
    for n, c in PRIME_B:
        v.append((c, f'primeB {n}', boolean(engine.small_prime(n))))
    bs = [engine.small_prime(n) for n in range(4096)]
    for t, fn, c in PRIME_TABLE:
        v.append((c, t, nat(fn(bs))))
    g.append(('The prime table (`TwoExcEngine.primeB`, `PMASK`)', v))
    v = []
    for (b, e, n), c in POW_MOD:
        bv, bt = arg(b)
        ev, et = arg(e)
        nv, nt = arg(n)
        v.append((c, f'powModE {bt} {et} {nt}', nat(engine.pow_mod_e(bv, ev, nv))))
    for d, c in PFACS:
        v.append((c, f'pfacs {d}', nats(engine.pfacs(d))))
    for (d, gg, p), c in ORD_OK:
        v.append((c, f'ordOK {d} {gg} {p}', boolean(ord_ok(d, gg, p))))
    g.append(('Orders (`TwoExcEngine.powModE`, `pfacs`, `ordOK`)', v))
    v = []
    for (p, name), c in FIND_KEY:
        k = engine.key_find({'keys': KEYS[name]}, p)
        v.append((c, f'findKey {p} {name}', 'none' if k is None else f'some {key_text(k)}'))
    for (cc, l), c in LOOKUP_W:
        v.append((c, f'lookupW {cc} {pairs(l)}', nat(engine.lookup_w(cc, l))))
    for (p, cc, l), c in LOOKUP_P:
        v.append((c, f'lookupP {p} {cc} {pairs(l)}', nat(engine.lookup_p(p, cc, l))))
    g.append(('Lookups (`TwoExcEngine.findKey`, `lookupW`, `lookupP`)', v))
    v = [('the moduli of the filter', 'qrTable.map Prod.fst', nats(engine.QR_MODS))]
    for z, c in QR_PASS:
        zv, zt = arg(z)
        v.append((c, f'qrPass {zt}', boolean(engine.qr_pass(zv))))
    for z, c in QR_BITS:
        v.append((c, f'qrBits {z}', nats(qr_bits(z))))
    g.append(('The square filter (`TwoExcEngine.qrPass`, `qrTable`)', v))
    v = []
    for (f, z, s), c in NEWTON:
        zv, zt = arg(z)
        sv, st = arg(s)
        v.append((c, f'newton {f} {zt} {st}', nat(engine.newton(f, zv, sv))))
    for z, c in SQRT:
        zv, zt = arg(z)
        v.append((c, f'sqrtIfSq {zt}', sqrt_text(zv)))
    g.append(('Square roots (`TwoExcEngine.newton`, `sqrtIfSq`)', v))
    return g

# ---------------------------------------------------------------- the Lean file

HEAD = '''import OddPerfect.TwoExcEngineCode

/-!
# Paired controls of the two exception engine helpers

Regression controls, not part of the library: nothing imports this file and the library build
never compiles it. It is checked by `sh CheckerControls/run.sh`.

This whole file is the output of `python3 -I scripts/TwoExceptionTwo/paired.py emit`, unchanged
(`paired.py check FILE` compares a file with it). Each `example` fixes the value of one low level
helper of `OddPerfect/TwoExcEngineCode.lean` on one input vector; the value on the right is the
value that the Python mirror `scripts/TwoExceptionTwo/engine.py` computes on the same input. So
the kernel checks that the two sides agree on every vector. The pairs (Lean, then Python):
`findDiv` and `find_div`; `smallPrime` and `primeB` (table `PMASK` below 4096) and
`small_prime`; `powModE` and `pow_mod_e`; `pfacs` and `pfacs`; `ordOK` and `ord_ok`; `findKey`
and `key_find`; `lookupW` and `lookup_w`; `lookupP` and `lookup_p`; `qrTable` and `qrPass` and
`QR_MODS`, `QR_SETS` and `qr_pass`; `newton` and `newton`; `sqrtIfSq` and
`square_root_if_square`.

Where the mirror rejects (raises `Reject`) instead of returning a value, the Lean value is the
one that the rejection mirrors: for `square_root_if_square` a root `s` is `some (some s)`, the
result `None` (not a square) is `some none`, and a rejection (Newton did not settle) is the outer
`none`; for `ord_ok` a rejection (a factor list that fails its check) is `false`. A key of the
mirror `[p, role, cs]` is the key `⟨p, role, cs⟩`, and its `None` is `none`. The values of
`qrBits` are the bits of the masks of `qrTable` at `z`, on the Python side membership of `z` in
`QR_SETS`. Long numbers are written as `2 ^ a + b` or `(2 ^ a + b) ^ 2 + c`.
-/

namespace CheckerControls.Paired

open OddPerfect.TwoExcEngine

/-- The test bits of the square filter at `z`, one per modulus of `qrTable`. -/
def qrBits (z : ℕ) : List ℕ :=
  qrTable.map fun mm => Nat.land (Nat.shiftRight mm.2 (z % mm.1)) 1
'''


def example_lines(lhs, rhs):
    for form in (f'example : {lhs} = {rhs} := by decide +kernel',
                 f'example : {lhs} = {rhs} :=\n  by decide +kernel',
                 f'example : {lhs} =\n    {rhs} := by decide +kernel'):
        if all(len(line) <= 100 for line in form.split('\n')):
            return form
    raise SystemExit(f'paired.py: a line of the example for {lhs} exceeds 100 characters')


def emit():
    out = [HEAD]
    for name, ks in KEYS.items():
        doc = 'The empty key list.' if not ks else 'A key list of the lookup vectors.'
        body = ',\n    '.join(key_text(k) for k in ks)
        out.append(f'/-- {doc} -/\ndef {name} : List Key :=\n  [{body}]\n')
    for heading, vs in examples():
        out.append(f'/-! ## Paired with engine.py: {heading} -/\n\n' + ''.join(
            (f'-- {c}\n' if c else '') + example_lines(lhs, rhs) + '\n' for c, lhs, rhs in vs))
    out.append('end CheckerControls.Paired\n')
    text = '\n'.join(out)
    for i, line in enumerate(text.split('\n'), 1):
        if len(line) > 100:
            raise SystemExit(f'paired.py: line {i} of the Lean file exceeds 100 characters')
    return text


def main(argv):
    if argv[1:2] == ['emit'] and len(argv) == 2:
        sys.stdout.buffer.write(emit().encode('utf-8'))
        return 0
    if argv[1:2] == ['check'] and len(argv) == 3:
        try:
            with open(argv[2], 'rb') as f:
                have = f.read()
        except OSError as e:
            print(f'paired.py: cannot read {argv[2]}: {e.strerror}', file=sys.stderr)
            return 2
        want = emit().encode('utf-8')
        n = want.count(b'\nexample ')
        if have == want:
            print(f'paired controls equal ({n} examples)')
            return 0
        hl, wl = have.split(b'\n'), want.split(b'\n')
        i = next((i for i, (a, b) in enumerate(zip(hl, wl)) if a != b), min(len(hl), len(wl)))
        print(f'paired controls differ from line {i + 1} on')
        return 1
    print('usage: python3 -I paired.py emit | python3 -I paired.py check FILE', file=sys.stderr)
    return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv))
