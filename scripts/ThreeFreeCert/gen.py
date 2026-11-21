# Untrusted helper script for the OddPerfect Lean library.
# Generates a Cert term (force / split / abundant / parity steps) for the seeds given on
# the command line with exponent 2 and 3 not dividing N, rechecks it with an independent
# mirror of Certificate.check, and prints the Lean term.
# Used by: OddPerfect/ThreeFreeCert.lean (certThreeFree17, 23, 41, 47, 53).
# Run: python3 gen.py 5 11 29 17   (likewise with 23, 41, 47, 53 as the last seed)
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

"""Generate and independently check Cert terms for three free OPN seed exclusions."""
import sys
from fractions import Fraction

def isprime(n):
    return n >= 2 and all(n % d for d in range(2, int(n**0.5) + 1))

def geom(p, e):
    return sum(p**i for i in range(e + 1))

def oddprimes(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: out.append(n)
    return [q for q in out if q != 2]

PMAX = 5000  # kernel trial division is linear; refuse forced primes above this

# Generator
# state: dict prime -> ('exact', e) | ('pow', e) ; plus notDvd 3
def divisor(st):
    return [(p, v[1]) for p, v in sorted(st.items()) if v[1] >= 1]

def abundant(ps):
    return Fraction(1) * prodg(ps) > 2 * prodp(ps)

def prodg(ps):
    r = 1
    for p, e in ps: r *= geom(p, e)
    return r

def prodp(ps):
    r = 1
    for p, e in ps: r *= p**e
    return r

class Fail(Exception): pass

def search(st, todo, done):
    """st: facts; todo: primes known to divide N but not yet split (state has pow p 1)."""
    ps = divisor(st)
    if abundant(ps):
        return ('abundant', ps)
    if not todo:
        raise Fail(str(st))
    # choose: 3 mod 4 primes first (no branching), then smallest
    t = sorted(todo, key=lambda q: (q % 4 == 1, q))[0]
    rest = [q for q in todo if q != t]
    return split_chain(st, t, rest, done)

def add_forced(st, p, e, todo):
    """Return list of force steps (p,e,e,q) for new primes from geom(p,e), and updated st/todo."""
    steps = []
    st = dict(st); todo = list(todo)
    for q in oddprimes(geom(p, e)):
        if q == 3:
            steps.append(('force', p, e, e, 3))
            return steps, st, todo, ('notDvd', 3, 1)
        if q in st or q > PMAX:
            continue
        steps.append(('force', p, e, e, q))
        st[q] = ('pow', 1); todo.append(q)
    return steps, st, todo, None

def wrap(steps, body):
    for s in reversed(steps):
        body = s + (body,)
    return body

def split_chain(st, t, rest, done):
    # exponent 1
    st1 = dict(st); st1[t] = ('exact', 1)
    if t % 4 != 1:
        c1 = ('paritySpecial', t, 1)
    else:
        other = [p for p, v in st.items() if v[0] == 'exact' and v[1] % 2 == 1]
        if other:
            c1 = ('parityTwo', t, 1, other[0], st[other[0]][1])
        else:
            steps, st1b, todo1, close = add_forced(st1, t, 1, rest)
            c1 = wrap(steps, close if close else search(st1b, todo1, done))
    # exponent 2
    st2 = dict(st); st2[t] = ('exact', 2)
    steps, st2b, todo2, close = add_forced(st2, t, 2, rest)
    c2 = wrap(steps, close if close else search(st2b, todo2, done))
    # exponent 3: always closed by parity (3 % 4 = 3)
    c3 = ('paritySpecial', t, 3)
    st4 = dict(st); st4[t] = ('pow', 4)
    c4 = search(st4, rest, done)
    return ('split', t, 1, c1, ('split', t, 2, c2, ('split', t, 3, c3, c4)))

def gen(seeds):
    st = {p: ('exact', 2) for p in seeds}
    steps, todo = [], []
    for p in seeds:
        s, st, todo, close = add_forced(st, p, 2, todo)
        assert close is None, p
        steps += s
    return wrap(steps, search(st, todo, set()))

# Independent checker (mirrors Certificate.check)
def lean_isprime(n):
    return 2 <= n and all(d < 2 or n % d != 0 for d in range(n))

def has_pow(s, p, e):
    return ('powDvd', p, e) in s or ('exact', p, e) in s

def check(s, c):
    k = c[0]
    if k == 'force':
        _, p, e, a, q, nx = c
        return (('exact', p, e) in s and lean_isprime(p) and lean_isprime(q) and q != 2
                and (e + 1) % (a + 1) == 0 and geom(p, a) % q == 0
                and check([('powDvd', q, 1)] + s, nx))
    if k == 'split':
        _, p, e, c1, c2 = c
        return (has_pow(s, p, e) and lean_isprime(p) and check([('exact', p, e)] + s, c1)
                and check([('powDvd', p, e + 1)] + s, c2))
    if k == 'abundant':
        ps = c[1]
        ok = all(has_pow(s, p, e) and lean_isprime(p) for p, e in ps)
        ok = ok and len({p for p, _ in ps}) == len(ps)
        return ok and 2 * prodp(ps) < prodg(ps)
    if k == 'notDvd':
        _, p, e = c
        return has_pow(s, p, e) and 1 <= e and ('notDvd', p) in s
    if k == 'parityTwo':
        _, p, e, q, f = c
        return (('exact', p, e) in s and ('exact', q, f) in s and lean_isprime(p)
                and lean_isprime(q) and p != q and e % 2 == 1 and f % 2 == 1)
    if k == 'paritySpecial':
        _, p, e = c
        return ('exact', p, e) in s and lean_isprime(p) and e % 2 == 1 and (p % 4 != 1 or e % 4 != 1)
    return False

def size(c):
    if c[0] == 'force': return 1 + size(c[5])
    if c[0] == 'split': return 1 + size(c[3]) + size(c[4])
    return 1

def leaves(c):
    if c[0] == 'force': return leaves(c[5])
    if c[0] == 'split': return leaves(c[3]) + leaves(c[4])
    return [c]

def lean(c, ind=2):
    pad = ' ' * ind
    k = c[0]
    if k == 'force':
        return f".force {c[1]} {c[2]} {c[3]} {c[4]} <|\n{pad}" + lean(c[5], ind)
    if k == 'split':
        return (f".split {c[1]} {c[2]}\n{pad}  ({lean(c[3], ind + 4)})\n{pad}  ({lean(c[4], ind + 4)})")
    if k == 'abundant':
        return ".abundant [" + ", ".join(f"({p}, {e})" for p, e in c[1]) + "]"
    return "." + k + " " + " ".join(map(str, c[1:]))

if __name__ == '__main__':
    seeds = list(map(int, sys.argv[1:]))
    c = gen(seeds)
    s0 = [('notDvd', 3)] + [('exact', p, 2) for p in seeds]
    ok = check(s0, c)
    worst = min((Fraction(prodg(l[1]), prodp(l[1])) for l in leaves(c) if l[0] == 'abundant'))
    print(f"-- seeds {seeds}: check={ok} nodes={size(c)} leaves={len(leaves(c))} min abundancy={float(worst):.4f}", file=sys.stderr)
    assert ok
    print(lean(c))
