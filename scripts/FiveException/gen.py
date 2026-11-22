"""Generator of the data modules for the five exception theorem with special prime 13.

Deterministic: python3 -I gen.py OUTDIR writes FiveExceptionData0.lean, FiveExceptionData79.lean,
FiveExceptionDataT.lean and FiveExceptionScan.lean into OUTDIR, after recomputing every check in
exact arithmetic (a Python mirror of the Lean checks smoothOK, sqOK, scan and ivOK). It also
checks and prints the constants written by hand in FiveExceptionThirteen.lean (the sender bounds
cfun t, the uniform bound 6756757 and the final inequalities).
"""
import sys
import textwrap
from fractions import Fraction as Fr
from math import gcd, isqrt
from itertools import product

sys.set_int_max_str_digits(0)

T0 = [7, 13, 19, 31]
D4 = 10 ** 4
K0 = 10 ** 7
PIN = {67: 10 ** 5, 79: 10 ** 6, 307: 10 ** 5}


def wr(r, j):
    lo, hi = 1, D4
    while lo < hi:
        m = (lo + hi) // 2
        if m ** j * r >= D4 ** j:
            hi = m
        else:
            lo = m + 1
    return lo


def isprime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def H(p):
    return Fr(p, p - 1)


def h(p, e):
    return Fr(p ** (e + 1) - 1, p ** e * (p - 1))


# mirror of nsq and sqOK
def nsq(f, m, x):
    for _ in range(f):
        y = (x + m // x) // 2
        if y < x:
            x = y
        else:
            break
    return x


def sq_ok(hits, n):
    m = 4 * n - 3
    r = nsq(120, m, 2 ** 48)
    if r * r == m:
        if not (r % 2 == 1 and (r // 2) % 6 == 5 and 5 <= r // 2):
            return True
        return (r // 2) in hits
    return r * r < m < (r + 1) * (r + 1)


def smooth_ok(P, B, ps, x):
    if not ps:
        return P(x)
    p, rest = ps[0], ps[1:]
    for _ in range(100):
        if x > B:
            return True
        if not smooth_ok(P, B, rest, x):
            return False
        x *= p
    return B < x


def smooth_hits(B, ps, x):
    out, cnt = set(), [0]

    def P(n):
        cnt[0] += 1
        m = 4 * n - 3
        r = isqrt(m)
        if r * r == m and r % 2 == 1 and (r // 2) % 6 == 5 and r // 2 >= 5:
            out.add(r // 2)
        return True
    smooth_ok(P, B, ps, x)
    return sorted(out), cnt[0]


u4 = [wr(p, 4) for p in T0]
P4 = Fr(1)
for u in u4:
    P4 /= 1 - Fr(u, D4)
X0 = Fr(2, K0) * P4
hits0, n0 = smooth_hits(K0 ** 4, T0, 1)
assert hits0 == [5, 11, 191, 653], hits0
assert smooth_ok(lambda n: sq_ok(hits0, n), K0 ** 4, T0, 1)
print('G0 products', n0, 'hits', hits0, 'X0', float(X0), 'weights', u4)

Hq = H(13) * H(7) * H(19) * H(31)
Hh0 = Fr(1)
for s in hits0:
    Hh0 *= H(s)


def pair(x):
    return (x.numerator, x.denominator)


def lpair(x):
    return '(%d, %d)' % pair(x)


def hpair(p, e):
    return '(%d, %d)' % (p ** (e + 1) - 1, p ** e * (p - 1))


def rpair(p):
    return '(%d, %d)' % (p, p - 1)


# pinned tables
tables = {}
pin_hits = {}
for t in (17, 67, 79, 307):
    if t in PIN:
        Kt = PIN[t]
        ut = wr(t, 4)
        X1 = Fr(2, Kt) * Fr(ut, D4) / (1 - Fr(ut, D4)) * P4
        h1, n1 = smooth_hits(Kt ** 4, [t] + T0, t)
        assert smooth_ok(lambda n: sq_ok(h1, n), Kt ** 4, [t] + T0, t)
        pin_hits[t] = (h1, Kt, ut, n1)
    else:
        X1, h1 = Fr(0), []
    hits = sorted(set(hits0) | set(h1))
    hits = [s for s in hits if s != t]
    R = 1 / ((1 - X0) * (1 - X1))
    opts = [
        [(hpair(13, 1), hpair(13, 1)), (hpair(13, 5), rpair(13))],
        [(hpair(7, 4), hpair(7, 4)), (hpair(7, 6), rpair(7))],
        [(hpair(19, 4), rpair(19))],
        [(hpair(31, 4), rpair(31))],
        [(hpair(t, 4), rpair(t))],
    ]
    vals = [
        [(h(13, 1), h(13, 1)), (h(13, 5), H(13))],
        [(h(7, 4), h(7, 4)), (h(7, 6), H(7))],
        [(h(19, 4), H(19))], [(h(31, 4), H(31))], [(h(t, 4), H(t))],
    ]
    for s in hits:
        opts.append([('(1, 1)', '(1, 1)'), (hpair(s, 2), hpair(s, 2)), (hpair(s, 8), rpair(s))])
        vals.append([(Fr(1), Fr(1)), (h(s, 2), h(s, 2)), (h(s, 8), H(s))])
    opts.append([('(1, 1)', lpair(R))])
    vals.append([(Fr(1), R)])
    n = 0
    for combo in product(*vals):
        lo = hi = Fr(1)
        for a, b in combo:
            lo *= a
            hi *= b
        assert hi < 2 or lo > 2
        n += 1
    tables[t] = (hits, opts, n, X1, R)
    print('pinned', t, 'hits', hits, 'intervals', n, 'X1', float(X1),
          'products', pin_hits.get(t, (0, 0, 0, 0))[3])

# scan
lo_t, hi_t = 37, 24500
primes = [x for x in range(lo_t, hi_t) if x % 6 == 1 and isprime(x)]
assert len(primes) == 1345
bigP = 1
for x in primes:
    bigP *= x


def rem0(s):
    r = 1 + s + s * s
    for p in T0:
        for _ in range(40):
            if r % p == 0:
                r //= p
            else:
                break
    return r


def sender(s):
    r = rem0(s)
    if r == 1:
        return None
    g = gcd(r, bigP)
    if g == 1 or g >= 24500:
        return None
    x = r
    ok = False
    for _ in range(45):
        if x == 1:
            ok = True
            break
        if x % g == 0:
            x //= g
        else:
            break
    if ok and isprime(g):
        return g
    return None


CH = 10000
NS = 166666
chunks = []
for c in range((NS + CH - 1) // CH):
    k = min(CH, NS - c * CH)
    st = 5 + 6 * CH * c
    L = []
    for j in range(k):
        s = st + 6 * j
        g = sender(s)
        if g is not None:
            L.append((s, g))
    chunks.append((st, k, L))
allsend = [e for st, k, L in chunks for e in L]
send = []
for s, g in allsend:
    d = 0
    if not isprime(s):
        d = next(x for x in range(2, s) if s % x == 0)
    send.append((s, g, d))
print('senders', len(send), 'composite', sum(1 for e in send if e[2]))
uU = wr(37, 4)
tailU = Fr(1001, 1000) / 1000 * Fr(uU, D4) / (1 - Fr(uU, D4)) * P4
budget = 1 - tailU - Hq * Hh0 * H(37) / (2 * (1 - X0))
# condition: Hq Hh0 H(37) / ((1 - X0)(1 - S - tailU)) <= 2  <=>  S <= budget
bases = sorted({g for s, g, d in send})
special = []
for g in bases:
    S = sum((Fr(1, s - 1) for s, gg, d in send if gg == g and d == 0), Fr(0))
    if S > budget:
        special.append((g, S))
budget_r = Fr(int(budget * 10 ** 7), 10 ** 7)
assert budget_r <= budget
print('uniform tail', float(tailU), 'budget', float(budget), 'special', [g for g, S in special])
for g, S in special:
    if g in PIN:
        continue
    b = Hq * Hh0 * H(g) / ((1 - X0) * (1 - S - tailU))
    assert b <= 2, (g, float(b))
for g in bases:
    if g in [x for x, _ in special]:
        continue
    S = sum((Fr(1, s - 1) for s, gg, d in send if gg == g and d == 0), Fr(0))
    assert S <= budget_r
w2 = [wr(p, 2) for p in T0]
P2 = Fr(1)
for u in w2:
    P2 /= 1 - Fr(u, D4)
wL = wr(24500, 2)
XL = 2 * Fr(wL, D4) / (1 - Fr(wL, D4)) * P2
bL = Hq * Hh0 * H(24500) / ((1 - X0) * (1 - XL))
assert bL <= 2
print('large t bound', float(bL), 'w2', w2, wL)
b23 = Hq * Hh0 * H(23) / (1 - X0)
assert b23 <= 2
for t in (5, 11):
    hh = Fr(1)
    for s in hits0:
        if s != t:
            hh *= H(s)
    assert Hq * H(t) * hh / (1 - X0) <= 2
print('t = 23 bound', float(b23))


def lst(xs, per=8):
    items = [str(x) for x in xs]
    lines = []
    for i in range(0, len(items), per):
        lines.append(', '.join(items[i:i + per]))
    return '[' + (',\n    ').join(lines) + ']'


def tup(e):
    return '(' + ', '.join(str(x) for x in e) + ')'


HDR = """import OddPerfect.FiveExceptionCore

/-!
# Five exceptional primes with special prime 13: {what}

Kernel checks (`decide +kernel`) used by `OddPerfect.FiveExceptionThirteen`, written by
`scripts/FiveException/gen.py`.
-/

namespace OddPerfect

namespace FiveException
"""
FTR = """
end FiveException

end OddPerfect
"""


TARGET = 3000


def count_prod(B, ps, x):
    if not ps:
        return 1
    n = 0
    while x <= B:
        n += count_prod(B, ps[1:], x)
        x *= ps[0]
    return n


def least_k(B, x, p):
    k = 0
    while x * p ** k <= B:
        k += 1
    return k


def split_block(name, hits, Bexpr, B, x, p, q, ps, doc):
    """Emit the check of every product x p^j q^i (...) <= B over p :: q :: ps as chunks."""
    P = lambda n: sq_ok(hits_val[hits], n)
    k1, k2 = least_k(B, x, p), least_k(B, x, q)
    assert k1 <= 100 and k2 <= 100
    xs = [x * p ** j * q ** i for j in range(k1) for i in range(k2) if x * p ** j * q ** i <= B]
    for y in xs:
        assert smooth_ok(P, B, ps, y)
    chunks, cur, cnt, total = [], [], 0, 0
    for y in xs:
        c = count_prod(B, ps, y)
        if cur and cnt + c > TARGET:
            chunks.append(cur)
            cur, cnt = [], 0
        cur.append(y)
        cnt += c
        total += c
    chunks.append(cur)
    pl = '[' + ', '.join(str(r) for r in ps) + ']'
    out = ''
    for m, ch in enumerate(chunks):
        out += """
/-- Starting values, chunk {m}. -/
def {nm}L{m} : List ℕ := {L}

theorem {nm}_c{m} : {nm}L{m}.all (smoothOK (sqOK {h}) ({B}) {pl}) = true := by
  decide +kernel
""".format(nm=name, m=m, L=lst(ch, 3), h=hits, B=Bexpr, pl=pl)
    out += """
/-- All starting values `{x} * {p}^j * {q}^i ≤ {B}`. -/
def {nm}L : List ℕ :=
  {cat}

{doc}
theorem {nm}_ok : smoothOK (sqOK {h}) ({B}) ({p} :: {q} :: {pl}) {x} = true :=
  smoothOK_two_of (k₁ := {k1}) (k₂ := {k2}) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) {nm}L
    (by simp only [{nm}L, List.all_append,
      {thms}, Bool.and_self])
    (by decide +kernel)
""".format(nm=name, x=x, p=p, q=q, B=Bexpr, cat=textwrap.fill(' ++ '.join('%sL%d' % (name, m) for m in range(len(chunks))), 96, subsequent_indent='    '),
           doc=textwrap.fill('/-- %s (%d products, %d chunks). -/' % (doc, total, len(chunks)), 100,
                             subsequent_indent=''), n=total, c=len(chunks), h=hits, pl=pl, k1=k1, k2=k2,
           thms=textwrap.fill(', '.join('%s_c%d' % (name, m) for m in range(len(chunks))), 90,
                              subsequent_indent='      '))
    return out


hits_val = {'hits0': hits0}
for t in pin_hits:
    hits_val['hits%d' % t] = pin_hits[t][0]


def gtheorem(t):
    h1, Kt, ut, n1 = pin_hits[t]
    return """
/-- The hits with a positive exponent of {t}. -/
def hits{t} : List ℕ := {h}
""".format(t=t, h=lst(h1)) + split_block('g%d' % t, 'hits%d' % t, '%d ^ 4' % Kt, Kt ** 4, t, t, 7,
                                         [13, 19, 31],
                                         'Every product `%d^(e+1) 7^a 13^b 19^c 31^d ≤ %d^4` passes the '
                                         'square test with the hits `hits%d`' % (t, Kt, t))


d0 = HDR.format(what='the enumeration for the receivers 7, 13, 19, 31') + """
/-- The hits of the receivers `7, 13, 19, 31`. -/
def hits0 : List ℕ := [5, 11, 191, 653]
""" + split_block('g0', 'hits0', '10 ^ 28', 10 ** 28, 1, 7, 13, [19, 31],
                  'Every product `7^a 13^b 19^c 31^d ≤ 10^28` passes the square test with the hits '
                  '`5, 11, 191, 653`') + FTR + "\n#print axioms OddPerfect.FiveException.g0_ok\n"
d79 = HDR.format(what='the enumeration for the fourth prime 79') + gtheorem(79) + FTR + \
    "\n#print axioms OddPerfect.FiveException.g79_ok\n"
dt = HDR.format(what='the enumerations for 67 and 307 and the interval tables')
dt += gtheorem(67) + gtheorem(307)
for t in sorted(tables):
    hits, opts, n, X1, R = tables[t]
    dt += """
/-- The hits of the interval table for the fourth prime {t}. -/
def hitsT{t} : List ℕ := {h}

/-- The interval table for the fourth prime {t} passes ({n} combinations). -/
theorem tab{t}_ok :
    ivOK (tabOf {t} hitsT{t}
      {R}) (1, 1) (1, 1) = true := by
  decide +kernel
""".format(t=t, h=lst(hits), n=n, R=lpair(R))
dt += FTR + "\n#print axioms OddPerfect.FiveException.g67_ok\n#print axioms OddPerfect.FiveException.g307_ok\n"
for t in sorted(tables):
    dt += '#print axioms OddPerfect.FiveException.tab%d_ok\n' % t

scn = []
scn.append('''import OddPerfect.FiveExceptionCore

/-!
# Five exceptional primes with special prime 13: the sender scan

Kernel checks (`decide +kernel`) used by `OddPerfect.FiveExceptionThirteen`, written by
`scripts/FiveException/gen.py`: the product `bigP` of the primes `x ≡ 1 (mod 6)` with
`37 ≤ x < 24500`, and the senders `(s, g)` for `s ≡ 5 (mod 6)`, `5 ≤ s < 10^6`, in chunks of
10000 values of `s`. Each sender carries `0` or a proper divisor of `s`.
-/

namespace OddPerfect

namespace FiveException

/-- The product of the primes `x ≡ 1 (mod 6)` with `37 ≤ x < 24500`. -/
def bigP : ℕ := {P}

/-- The primes `x ≡ 1 (mod 6)` with `37 ≤ x < 24500`, as a list. -/
def primesL : List ℕ :=
  {L}

theorem primesP_eq : primesP = primesL := by decide +kernel

theorem primesP_prod : primesP.prod = bigP := by rw [primesP_eq]; decide +kernel
'''.format(P=bigP, L=lst(primes, 12)))
for c, (st, k, L) in enumerate(chunks):
    scn.append('''
theorem scan{c} : scan bigP {k} {st} = {L} := by decide +kernel
'''.format(c=c, k=k, st=st, L=lst([tup(e) for e in L], 6)))
scn.append('''
/-- The senders with a divisor certificate (0 when none is claimed). -/
def sendList : List (ℕ × ℕ × ℕ) :=
  {L}

theorem sendList_eq : sendList.map (fun e => (e.1, e.2.1)) =
    {cat} := by decide +kernel

theorem sendList_cert : sendList.all (fun e => decide (e.2.2 = 0) ||
    (decide (1 < e.2.2) && decide (e.2.2 < e.1) && decide (e.1 % e.2.2 = 0))) = true := by
  decide +kernel

theorem sendList_nodup : (sendList.map (fun e => e.1)).Nodup := by decide +kernel

end FiveException

end OddPerfect

#print axioms OddPerfect.FiveException.primesP_eq
#print axioms OddPerfect.FiveException.primesP_prod
'''.format(L=lst([tup(e) for e in send], 5),
           cat=' ++\n      '.join('[' + ', '.join(tup(e) for e in L) + ']' for st, k, L in chunks)))
for c in range(len(chunks)):
    scn.append('#print axioms OddPerfect.FiveException.scan%d\n' % c)
scn.append('#print axioms OddPerfect.FiveException.sendList_eq\n')
scn.append('#print axioms OddPerfect.FiveException.sendList_cert\n')
scn.append('#print axioms OddPerfect.FiveException.sendList_nodup\n')

DG = 10 ** 9


def cfun(t):
    return sum((DG + s - 2) // (s - 1) for s, g, d in send if g == t and d == 0)


SPECIAL = [67, 79, 127, 307, 367, 409, 991, 1723, 3541, 5113, 8011, 10303, 17293]
assert SPECIAL == [g for g, S in special]
CU = 6756757
for t in primes:
    assert bigP % (t * t) != 0
    assert t in SPECIAL or cfun(t) <= CU
tailU = Fr(1001, 1000) / 1000 * P4 * Fr(4055, D4) / (1 - Fr(4055, D4))
assert (Fr(4055, D4)) ** 4 * 37 >= 1


def mid_bound(rt, C):
    return Hq * rt * Hh0 / (1 - X0) / (1 - (Fr(C, DG) + tailU))


assert mid_bound(H(37), CU) < 2
CSPEC = {}
for t in SPECIAL:
    if t in PIN:
        continue
    CSPEC[t] = cfun(t)
    assert mid_bound(H(t), CSPEC[t]) < 2
print('uniform bound', float(mid_bound(H(37), CU)), 'special C', CSPEC)

consts = dict(ut={t: pin_hits[t][2] for t in pin_hits}, R={t: pair(tables[t][4]) for t in tables}, u4=u4, w2=w2, wL=wL, uU=uU, budget_r=budget_r, special=[g for g, S in special],
              X0=X0, nchunks=len(chunks), bases=bases)
if __name__ == '__main__':
    out = sys.argv[1]
    open(out + '/FiveExceptionData0.lean', 'w').write(d0)
    open(out + '/FiveExceptionData79.lean', 'w').write(d79)
    open(out + '/FiveExceptionDataT.lean', 'w').write(dt)
    open(out + '/FiveExceptionScan.lean', 'w').write(''.join(scn))
    print('constants', consts)
