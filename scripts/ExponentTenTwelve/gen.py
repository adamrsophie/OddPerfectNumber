# Untrusted helper script for the OddPerfect Lean library.
# Checks the six forcing cases of the exponent ten and twelve theorems (every edge divides,
# l + 1 children congruent to 1 mod l), then emits the Lean text: primality lemmas (norm_num
# below 10^6, Pratt certificates above) and the bodies of the six case lemmas.
# Used by: OddPerfect/ExponentTenTwelve.lean (the pr_* lemmas and the lemmas ten_gen,
# ten_1806113, ten_15797, twelve_gen, twelve_53, twelve_8346157).
# Run: python3 gen.py
# Writes primes.lean, bodies.lean and cases.lean to the current folder.
# Requires: sympy (version 1.14.0 was used). Running time: a few seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from sympy import factorint, isprime, primitive_root, n_order

def sig(p, e): return (p**(e+1)-1)//(p-1)

# (l, special, edges: list of (parent, child)), S
cases = {
 "ten_gen": (11, None, [(11,15797),(11,1806113),(15797,463),(1806113,199),(463,23),(463,5479),
   (5479,1277),(5479,18701),(15797,116880853),(463,1546150189),(199,75449464927),(463,211677855071)]),
 "ten_1806113": (11, 1806113, [(11,15797),(15797,463),(463,23),(463,5479),(5479,1277),(5479,18701),
   (18701,34607),(1277,36751837),(36751837,67),(67,89),(15797,116880853),(463,1546150189)]),
 "ten_15797": (11, 15797, [(11,1806113),(1806113,199),(3,23),(3,3851),(2633,2113),(2113,683),(2113,7459),
   (3851,603510799),(2633,947684519),(2633,9620773471),(199,75449464927),(199,117942356533)]),
 "twelve_gen": (13, None, [(13,53),(13,264031),(13,1803647),(1803647,131),(1803647,55816123897),(131,79),
   (79,8346157),(79,551604349222681),(53,3297113),(53,11681692691969),(8346157,2128503313),
   (8346157,2497868257),(8346157,2767761413),(131,25061845458479893445539)]),
 "twelve_53": (13, 53, [(13,264031),(13,1803647),(1803647,131),(1803647,55816123897),(131,79),
   (79,8346157),(79,551604349222681),(8346157,2128503313),(8346157,2497868257),(8346157,2767761413),
   (2767761413,2939),(2767761413,1334737),(55816123897,1093),(1093,937)]),
 "twelve_8346157": (13, 8346157, [(13,53),(13,264031),(13,1803647),(1803647,131),(1803647,55816123897),
   (131,79),(79,551604349222681),(53,3297113),(53,11681692691969),(55816123897,1093),(1093,937),
   (937,599),(1093,58782569),(1093,8209505981)]),
}
allp = set()
for name, (l, sp, edges) in cases.items():
    S = [c for _, c in edges]
    assert len(set(S)) == len(S) == l + 1, name
    for par, c in edges:
        assert isprime(par) and isprime(c)
        assert sig(par, l - 1) % c == 0, (name, par, c)
        allp |= {par, c}
    for c in S:
        assert c % l == 1 and c != sp, (name, c)
    # internal nodes must be ordinary: either 3 mod 4, or fixed special differs, or excluded in gen case
    for par, _ in edges:
        assert par != sp
    print(name, "ok; internal 1mod4:", sorted({p for p, _ in edges if p % 4 == 1}))
# special-derived facts
assert 15798 == 2 * 3 * 2633 and isprime(2633)

def pratt(p, out, done):
    if p in done or p < 10**4: return
    f = factorint(p - 1)
    for q in f: pratt(q, out, done)
    # find witness a with order p-1
    a = 2
    while not (pow(a, p-1, p) == 1 and all(pow(a, (p-1)//q, p) != 1 for q in f)): a += 1
    fs = [q for q, m in sorted(f.items()) for _ in range(m)]
    out.append((p, a, fs)); done.add(p)

big = sorted(p for p in allp if p >= 10**6)
small = sorted(p for p in allp if p < 10**6)
print("small (norm_num):", small)
for p in big:
    out = []; pratt(p, out, set())
    print(f"{p}: [" + ", ".join(f"({a}, {b}, [{', '.join(map(str, c))}])" for a, b, c in out) + "]")

# Lean emission
def pratt2(p, out, done):
    if p in done or p < 1000: return
    f = factorint(p - 1)
    for q in f: pratt2(q, out, done)
    a = 2
    while not (pow(a, p-1, p) == 1 and all(pow(a, (p-1)//q, p) != 1 for q in f)): a += 1
    out.append((p, a, [q for q, m in sorted(f.items()) for _ in range(m)])); done.add(p)

allp |= {3, 2633}
L = []
for p in sorted(allp):
    if p < 10**6:
        L.append(f"private theorem pr_{p} : Nat.Prime {p} := by norm_num")
    else:
        out = []; pratt2(p, out, set())
        cert = ",\n    ".join(f"({a}, {b}, [{', '.join(map(str, c))}])" for a, b, c in out)
        L.append(f"private theorem pr_{p} : Nat.Prime {p} :=\n  Pratt.prime_of_checkPrime (c := [{cert}])\n    (by decide +kernel)")
open("primes.lean", "w").write("\n\n".join(L) + "\n")

def body(name, root_hyp):
    l, sp, edges = cases[name]
    lines = []
    for par, c in edges:
        dpar = root_hyp if par == l else f"d{par}"
        if sp is not None: ne = "(by norm_num)"
        elif par % 4 == 3: ne = "(ne_of_mod_four hq4 (by norm_num))"
        else: ne = {15797: "(Ne.symm ha)", 1806113: "(Ne.symm hb)", 53: "(Ne.symm ha)", 8346157: "(Ne.symm hb)", 13: "(Ne.symm hc)"}[par]
        lines.append(f"  have d{c} := force h hexp pr_{par} {dpar}\n    {ne} pr_{c} (by norm_num) (by decide +kernel)")
    S = [c for _, c in edges]
    lines.append(f"  refine close h (l := {l}) (by norm_num) (by norm_num) e{l} hexp")
    lines.append(f"    {{{', '.join(map(str, S))}}} ?_ (by decide)")
    lines.append("  intro p hp")
    lines.append("  simp only [Finset.mem_insert, Finset.mem_singleton] at hp")
    lines.append("  rcases hp with " + " | ".join(["rfl"] * len(S)))
    lines.append("  exacts [" + ", ".join(f"⟨pr_{c}, d{c}, by norm_num⟩" for c in S) + "]")
    return "\n".join(lines)
with open("bodies.lean", "w") as f:
    for name in cases:
        f.write(f"-- {name}\n" + body(name, "h" + str(cases[name][0])) + "\n\n")

hdr = {
 "ten_gen": ("Exponent ten, `q ∉ {15797, 1806113}`.",
   "{N q : ℕ} (h : OddPerfect N) (hq4 : q % 4 = 1)\n    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 10) (h11 : 11 ∣ N)\n    (e11 : N.factorization 11 = 10) (ha : q ≠ 15797) (hb : q ≠ 1806113)"),
 "ten_1806113": ("Exponent ten, `q = 1806113`.",
   "{N : ℕ} (h : OddPerfect N)\n    (hexp : ∀ p ∈ N.primeFactors, p ≠ 1806113 → N.factorization p = 10) (h11 : 11 ∣ N)\n    (e11 : N.factorization 11 = 10)"),
 "ten_15797": ("Exponent ten, `q = 15797`; the primes `3` and `2633` divide `15797 + 1`.",
   "{N : ℕ} (h : OddPerfect N)\n    (hexp : ∀ p ∈ N.primeFactors, p ≠ 15797 → N.factorization p = 10) (h11 : 11 ∣ N)\n    (e11 : N.factorization 11 = 10) (d3 : 3 ∣ N) (d2633 : 2633 ∣ N)"),
 "twelve_gen": ("Exponent twelve, `13` ordinary, `q ∉ {53, 8346157}`.",
   "{N q : ℕ} (h : OddPerfect N) (hq4 : q % 4 = 1)\n    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 12) (h13 : 13 ∣ N)\n    (e13 : N.factorization 13 = 12) (hc : q ≠ 13) (ha : q ≠ 53) (hb : q ≠ 8346157)"),
 "twelve_53": ("Exponent twelve, `13` ordinary, `q = 53`.",
   "{N : ℕ} (h : OddPerfect N)\n    (hexp : ∀ p ∈ N.primeFactors, p ≠ 53 → N.factorization p = 12) (h13 : 13 ∣ N)\n    (e13 : N.factorization 13 = 12)"),
 "twelve_8346157": ("Exponent twelve, `13` ordinary, `q = 8346157`.",
   "{N : ℕ} (h : OddPerfect N)\n    (hexp : ∀ p ∈ N.primeFactors, p ≠ 8346157 → N.factorization p = 12) (h13 : 13 ∣ N)\n    (e13 : N.factorization 13 = 12)"),
}
with open("cases.lean", "w") as f:
    for name in cases:
        doc, args = hdr[name]
        f.write(f"/-- {doc} -/\nprivate lemma {name} {args} : False := by\n" + body(name, "h" + str(cases[name][0])) + "\n\n")
