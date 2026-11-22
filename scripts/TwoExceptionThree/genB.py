"""Writes OddPerfect/TwoExceptionThreeBData.lean: the walk over s = 11, 21, ..., 19871 and the walk
over t = 19, 22, ..., 29998, checked by TwoExceptionThreeB.scover and TwoExceptionThreeB.tcover,
with one Pratt certificate per chunk for the primes at least 10^4. Every entry is first checked by
an exact Python mirror of the Lean checker. Deterministic.
Usage: python3 -I genB.py OUT.lean"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from math import gcd
from sympy import factorint, isprime
import pratt

SHI = 19881           # the cutoff of the abundancy bound; s walk covers 11 <= s < SHI
THI = 30001           # t walk covers 19 <= t < THI
TH = 10 ** 4          # primes below TH pass trial division, the others carry a Pratt certificate
SCHUNK = 200
TCHUNK = 1000

def phi3(t): return t * t + t + 1
def phi5(x): return x ** 4 + x ** 3 + x ** 2 + x + 1
def sqrt_prime(w):
    if w < 2: return False
    d = 2
    while d * d <= w:
        if w % d == 0: return False
        d += 1
    return True
def prime_ok(P, w): return w in P or sqrt_prime(w)

# exact mirrors of the Lean checker
def fchk(P, s, known, steps, a, b):
    known = list(known)
    for w, v in steps:
        if not (w != 2 and prime_ok(P, w) and
                ((v == 0 and phi5(s) % w == 0) or
                 (v in known and v not in (5, 13, s) and phi3(v) % w == 0))):
            return False
        known.insert(0, w)
    return a in known and (a == 7 or (b in known and a != b and a % 3 == 1 and b % 3 == 1 and
                                      a != 13 and b != 13 and a != s and b != s))
def s_entry(P, n, d, steps, a, b):
    return (1 < d < n and n % d == 0) or n == 61 or fchk(P, n, [], steps, a, b)
def t_entry(P, lo, t, d, a, m, p, k, steps, u, v):
    if 1 < d < t and t % d == 0: return True
    return (phi3(t) == 3 * 13 ** a * m and m % 13 != 0 and
            ((m != 1 and m < lo) or (1 < d < m and m % d == 0 and gcd(d, m // d) == 1) or
             (1 <= k and p ** k == m and prime_ok(P, p) and
              (p < lo or p % 5 != 1 or fchk(P, p, [t], steps, u, v)))))

_fc = {}
def pfactors(z):
    if z not in _fc: _fc[z] = sorted(factorint(z))
    return _fc[z]
def strip(z, gs):
    for g in gs:
        while z % g == 0: z //= g
    return z

def closure(s, init):
    """Breadth first forcing from Phi5(s) (and the primes init). Returns (steps, a, b)."""
    par = {}
    order = []
    for w in pfactors(phi5(s)):
        if w not in (5, 13, s) and w not in par:
            par[w] = 0; order.append(w)
    level = list(order)
    known0 = list(init)
    def done():
        F = known0 + order
        if 7 in F: return (7, 0)
        one = [w for w in F if w % 3 == 1 and w not in (13, s)]
        one = sorted(set(one))
        if len(one) >= 2: return (one[0], one[1])
        return None
    frontier = list(init) + level
    for depth in range(8):
        r = done()
        if r: break
        new = []
        for v in frontier:
            if v in (3, 5, 13, s): continue
            c = strip(phi3(v), [3, 13, s])
            if c == 1: continue
            for w in pfactors(c):
                if w not in par and w not in init and w not in (3, 5, 13, s):
                    par[w] = v; order.append(w); new.append(w)
            if done(): break
        frontier = new
    r = done()
    assert r, s
    a, b = r
    need = []
    def add(w):
        if w in init or w in need: return
        v = par[w]
        if v: add(v)
        need.append(w)
    add(a)
    if a != 7: add(b)
    return [(w, par[w]) for w in need], a, b

def certs_for(primes):
    cert, seen = [], set()
    for w in sorted(set(primes)):
        if w >= TH:
            for e in pratt.cert(w):
                if e[0] not in seen:
                    seen.add(e[0]); cert.append(e)
    assert pratt.check(cert)
    return cert

def main():
    out = sys.argv[1]
    # the walk over s
    sent = []
    for n in range(11, SHI, 10):
        f = factorint(n)
        if n == 61: sent.append((n, 0, [], 0, 0)); continue
        if len(f) > 1 or max(f.values()) > 1:
            sent.append((n, min(f), [], 0, 0)); continue
        steps, a, b = closure(n, [])
        sent.append((n, 0, steps, a, b))
    # the walk over t
    tent = []
    for t in range(19, THI, 3):
        f = factorint(t)
        if len(f) > 1 or max(f.values()) > 1:
            tent.append((t, min(f), 0, 0, 0, 0, [], 0, 0)); continue
        z = phi3(t)
        assert z % 3 == 0
        z //= 3
        a = 0
        while z % 13 == 0: z //= 13; a += 1
        m = z
        assert m != 1, t
        if m < SHI:
            tent.append((t, 0, a, m, 0, 0, [], 0, 0)); continue
        fm = factorint(m)
        if len(fm) > 1:
            q = min(fm); d = q ** fm[q]
            tent.append((t, d, a, m, 0, 0, [], 0, 0)); continue
        p, k = list(fm.items())[0]
        if p < SHI or p % 5 != 1:
            tent.append((t, 0, a, m, p, k, [], 0, 0)); continue
        steps, u, v = closure(p, [t])
        tent.append((t, 0, a, m, p, k, steps, u, v))
    def sprimes(e): return [w for w, _ in e[2]]
    def tprimes(e): return ([e[4]] if e[4] else []) + [w for w, _ in e[6]]
    schunks = [sent[i:i + SCHUNK] for i in range(0, len(sent), SCHUNK)]
    tchunks = [tent[i:i + TCHUNK] for i in range(0, len(tent), TCHUNK)]
    scerts = [certs_for([w for e in ch for w in sprimes(e)]) for ch in schunks]
    tcerts = [certs_for([w for e in ch for w in tprimes(e)]) for ch in tchunks]
    for ch, c in zip(schunks, scerts):
        P = set(e[0] for e in c)
        assert all(s_entry(P, *e) for e in ch)
    for ch, c in zip(tchunks, tcerts):
        P = set(e[0] for e in c)
        assert all(t_entry(P, SHI, *e) for e in ch)
    L = []
    L.append('import OddPerfect.TwoExceptionThreeBCheck')
    L.append('')
    L.append('/-!')
    L.append('# Data for branch B')
    L.append('')
    L.append('Generated by `scripts/TwoExceptionThree/genB.py`. The walk over `s = 11, 21, …, %d` gives' % (SHI - 10))
    L.append('a divisor of a composite `s` or a forcing walk that closes a prime `s`; the walk over')
    L.append('`t = 19, 22, …, %d` gives a divisor of a composite `t` or the decomposition' % (THI - 3))
    L.append('`t^2 + t + 1 = 3 · 13^a · m` with the reason why `m` is no power of a prime `s ≥ %d` left' % SHI)
    L.append('open. Each chunk carries a Pratt certificate of its primes at least `%d`.' % TH)
    L.append('-/')
    L.append('')
    L.append('set_option Elab.async false')
    L.append('')
    L.append('namespace OddPerfect.TwoExceptionThreeB')
    def certdef(name, c):
        L.append('')
        L.append('/-- Pratt certificate `%s`. -/' % name)
        L.append('def %s : List (ℕ × ℕ × List ℕ) :=' % name)
        L.append('  [' + ',\n   '.join('(%d, %d, [%s])' % (p, a, ', '.join(map(str, fs)))
                                     for p, a, fs in c) + ']')
        L.append('')
        L.append('theorem %s_ok : Pratt.check %s = true := by decide +kernel' % (name, name))
    def st(steps): return '[' + ', '.join('(%d, %d)' % x for x in steps) + ']'
    sb = []
    for i, ch in enumerate(schunks):
        lo = ch[0][0]; hi = ch[-1][0] + 10; sb.append((lo, hi))
        certdef('scert%d' % i, scerts[i])
        L.append('')
        L.append('/-- Walk over `s`, chunk %d. -/' % i)
        L.append('def swalk%d : List (ℕ × ℕ × List (ℕ × ℕ) × ℕ × ℕ) :=' % i)
        L.append('  [' + ',\n   '.join('(%d, %d, %s, %d, %d)' % (n, d, st(s_), a, b)
                                     for n, d, s_, a, b in ch) + ']')
        L.append('')
        L.append('theorem swalk%d_ok : scover (scert%d.map Prod.fst) %d swalk%d %d = true := by' % (i, i, lo, i, hi))
        L.append('  decide +kernel')
        L.append('')
        L.append('theorem sgood%d {x : ℕ} (hx : x.Prime) (h10 : x %% 10 = 1) (h61 : x ≠ 61)' % i)
        L.append('    (hlo : %d ≤ x) (hhi : x < %d) (N : ℕ) (hc : Ctx N x) : False :=' % (lo, hi))
        L.append('  scover_sound (fun p hp => by')
        L.append('    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp')
        L.append('    exact Pratt.check_sound scert%d_ok e he) swalk%d %d swalk%d_ok x hlo hhi (by omega) hx' % (i, i, lo, i))
        L.append('    h61 N hc')
    tb = []
    for i, ch in enumerate(tchunks):
        lo = ch[0][0]; hi = ch[-1][0] + 3; tb.append((lo, hi))
        certdef('tcert%d' % i, tcerts[i])
        L.append('')
        L.append('/-- Walk over `t`, chunk %d. -/' % i)
        L.append('def twalk%d : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ) × ℕ × ℕ) :=' % i)
        L.append('  [' + ',\n   '.join('(%d, %d, %d, %d, %d, %d, %s, %d, %d)' % (t, d, a, m, p, k, st(s_), u, v)
                                     for t, d, a, m, p, k, s_, u, v in ch) + ']')
        L.append('')
        L.append('theorem twalk%d_ok : tcover (tcert%d.map Prod.fst) %d %d twalk%d %d = true := by' % (i, i, SHI, lo, i, hi))
        L.append('  decide +kernel')
        L.append('')
        L.append('theorem tgood%d {x : ℕ} (h3 : x %% 3 = 1) (hlo : %d ≤ x) (hhi : x < %d) :' % (i, lo, hi))
        L.append('    TGood %d x :=' % SHI)
        L.append('  tcover_sound (fun p hp => by')
        L.append('    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp')
        L.append('    exact Pratt.check_sound tcert%d_ok e he) twalk%d %d twalk%d_ok x hlo hhi (by omega)' % (i, i, lo, i))
    L.append('')
    L.append('/-- Every prime `11 ≤ x < %d` with `x %% 10 = 1` and `x ≠ 61` is closed. -/' % SHI)
    L.append('theorem s_closed {x : ℕ} (hx : x.Prime) (h10 : x % 10 = 1) (h61 : x ≠ 61)')
    L.append('    (h11 : 11 ≤ x) (hlt : x < %d) (N : ℕ) (hc : Ctx N x) : False := by' % SHI)
    for i, (lo, hi) in enumerate(sb):
        if i < len(sb) - 1:
            L.append('  by_cases c%d : x < %d' % (i, hi))
            L.append('  · exact sgood%d hx h10 h61 (by omega) c%d N hc' % (i, i))
        else:
            L.append('  exact sgood%d hx h10 h61 (by omega) hlt N hc' % i)
    L.append('')
    L.append('/-- Every `19 ≤ x < %d` with `x %% 3 = 1` is excluded as the square of branch B. -/' % THI)
    L.append('theorem t_closed {x : ℕ} (h3 : x %% 3 = 1) (h19 : 19 ≤ x) (hlt : x < %d) :' % THI)
    L.append('    TGood %d x := by' % SHI)
    for i, (lo, hi) in enumerate(tb):
        if i < len(tb) - 1:
            L.append('  by_cases c%d : x < %d' % (i, hi))
            L.append('  · exact tgood%d h3 (by omega) c%d' % (i, i))
        else:
            L.append('  exact tgood%d h3 (by omega) hlt' % i)
    L.append('')
    L.append('end OddPerfect.TwoExceptionThreeB')
    L.append('')
    for i in range(len(schunks)):
        for nm in ('scert%d_ok', 'swalk%d_ok', 'sgood%d'):
            L.append('#print axioms OddPerfect.TwoExceptionThreeB.' + nm % i)
    for i in range(len(tchunks)):
        for nm in ('tcert%d_ok', 'twalk%d_ok', 'tgood%d'):
            L.append('#print axioms OddPerfect.TwoExceptionThreeB.' + nm % i)
    L.append('#print axioms OddPerfect.TwoExceptionThreeB.s_closed')
    L.append('#print axioms OddPerfect.TwoExceptionThreeB.t_closed')
    open(out, 'w').write('\n'.join(L) + '\n')
    nst = sum(len(e[2]) for e in sent) + sum(len(e[6]) for e in tent)
    print('s entries', len(sent), 't entries', len(tent),
          'forcing walks', sum(1 for e in sent if e[2]) + sum(1 for e in tent if e[6]),
          'steps', nst, 'pratt entries', sum(map(len, scerts)) + sum(map(len, tcerts)),
          'largest step prime', max([w for e in sent for w, _ in e[2]] + [w for e in tent for w, _ in e[6]]))

if __name__ == '__main__':
    main()
