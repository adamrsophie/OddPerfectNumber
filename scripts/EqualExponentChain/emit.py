# Untrusted helper script for the OddPerfect Lean library.
# Turns one certificate JSON file written by gen2.py into the Lean declarations pcL,
# ordL, specL, checkL and the theorem not_all_exponents_eq_*.
# Used by: OddPerfect/EqualExponentChain.lean (instances section).
# Run: python3 emit.py cert_L.json > out.lean
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

"""Emit Lean declarations for a certificate JSON file."""
import sys
import json

NAMES = {4: 'four', 6: 'six', 10: 'ten', 12: 'twelve', 16: 'sixteen', 18: 'eighteen',
         22: 'twenty_two', 28: 'twenty_eight', 30: 'thirty', 36: 'thirty_six', 40: 'forty',
         42: 'forty_two', 46: 'forty_six', 52: 'fifty_two'}


def node(t, ind):
    pad = ' ' * ind
    k = t[0]
    if k == 'ord':
        return f'{pad}.ord {t[1]} {t[2]} <|\n' + node(t[3], ind)
    if k == 'spec':
        return f'{pad}.spec {t[1]} {t[2]} <|\n' + node(t[3], ind)
    if k == 'expo':
        return f'{pad}.expo {t[1]} {t[2]} {t[3]} <|\n' + node(t[4], ind)
    if k == 'branch':
        return (f'{pad}.branch {t[1]}\n{pad}  (\n' + node(t[2], ind + 2) + f'{pad}  )\n'
                f'{pad}  (\n' + node(t[3], ind + 2) + f'{pad}  )\n')
    if k == 'over':
        ps = ', '.join(f'({p}, {j})' for p, j in t[2])
        return f'{pad}.overflow {t[1]} [{ps}] {t[3]} {t[4]}\n'
    if k == 'mod4':
        return f'{pad}.mod4\n'
    raise ValueError(k)


def pratt_list(pc):
    if not pc:
        return '[]'
    rows = [f'({p}, {a}, [{", ".join(map(str, fs))}])' for p, a, fs in pc]
    return '[' + ',\n    '.join(rows) + ']'


def emit(d):
    l = d['l']
    e = l - 1
    name = NAMES[e]
    out = []
    out.append(f'/-- Pratt certificates for `l = {l}`. -/\n'
               f'def pc{l} : List (ℕ × ℕ × List ℕ) :=\n  {pratt_list(d["pratt"])}\n')
    out.append(f'/-- The tree for `l = {l}` when `{l}` is ordinary. -/\n'
               f'def ord{l} : Node :=\n' + node(d['ord'], 2))
    out.append(f'/-- The tree for `l = {l}` when `{l}` is the special prime. -/\n'
               f'def spec{l} : Node :=\n' + node(d['spec'], 2))
    out.append(f'/-- The certificate for `l = {l}` is accepted. -/\n'
               f'theorem check{l} : checkAll {l} pc{l} ord{l} spec{l} = true := by\n'
               f'  decide +kernel\n')
    return '\n'.join(out), (l, name)


def theorem(l, name):
    return (f'/-- In an odd perfect number the exponents of the primes other than the special\n'
            f'prime cannot all equal `{l - 1}`. -/\n'
            f'theorem not_all_exponents_eq_{name} {{N q : ℕ}} (h : OddPerfect N) (hq : q.Prime)\n'
            f'    (hodd : Odd (N.factorization q))\n'
            f'    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = {l - 1}) : False :=\n'
            f'  EqChain.checkAll_sound EqChain.check{l} h hq hodd hexp\n')


if __name__ == '__main__':
    d = json.load(open(sys.argv[1]))
    body, (l, name) = emit(d)
    print(body)
    print(theorem(l, name))
