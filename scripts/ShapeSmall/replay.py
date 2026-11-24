"""Independent replay of the kernel and norm_num checks of OddPerfect/ShapeSmall.lean.

Usage:
    python3 -I replay.py PATH          replay every check on the literals of the Lean file PATH
    python3 -I replay.py PATH bad      the two negative controls (each must be rejected)

Standard library only, exact integer arithmetic, does not import gen.py. It mirrors the Lean
definitions geo, isq, sqOK, nsq, maskOK, filt, good and chk literally (nested loops, Lean's
truncated division with x / 0 = 0) and checks the certificate hypotheses of
prime_le_of_two_sq_eq_succ_sigma. Prints ACCEPT or REJECT per check; exit 1 on any REJECT
(or, with `bad`, on any control that is accepted). Every family of the module must be present
(c1, c2, c3, c5, c6 with prime_le_h; L2, L3, L5, L6 with Lh_ok, chkh_j and no_sol_h), and each
declaration must name its own exponent, list and chunks; a missing or misnamed declaration is
a REJECT. Exit 2 for a usage error, an unreadable file or a file without the expected text.
"""
import re
import sys

HS = [1, 2, 3, 5, 6]          # the exponents e = 2 h of the module
MASK_HS = [2, 3, 5, 6]        # the exponents with masks and kernel ranges


def geo(r, n):
    s = 0
    for _ in range(n):
        s = 1 + r * s
    return s


def isq(v, k, x):
    for _ in range(k):
        x = min(x, (x + (v // x if x != 0 else 0)) // 2)
    return x


def sqOK(v, r):
    return r * r < v and v < (r + 1) * (r + 1)


def nsq(h, p, steps):
    v = (1 + geo(p, 2 * h + 1)) // 2
    return sqOK(v, isq(v, steps, p ** h))


def maskOK(h, m, mask):
    if not 0 < m:
        return False
    for r in range(m):
        if (mask >> r) % 2 == 0:
            continue
        target = (1 + geo(r, 2 * h + 1)) % m
        for x in range(m):
            if (2 * x * x) % m == target:
                return False
    return True


def filt(L, p):
    return any((mask >> (p % m)) % 2 == 1 for m, mask in L)


def chk(h, L, p, n, steps):
    for i in range(n):
        q = p + 2 * i
        if not (filt(L, q) or nsq(h, q, steps)):
            return False, q
    return True, None


def cert_ok(h, D, c):
    """Hypotheses of prime_le_of_two_sq_eq_succ_sigma, with c i = c.getD i 0."""
    cc = lambda i: c[i] if i < len(c) else 0
    if not (0 < D and cc(0) == D and 1 <= h):
        return False
    for k in range(1, h + 1):
        if 2 * sum(cc(i) * cc(k - i) for i in range(k + 1)) != D ** 2:
            return False
    return all(2 * cc(i) <= D for i in range(1, h + 1))


def read(text):
    d = {"steps": int(re.search(r"isq \(\(1 \+ geo p \(2 \* h \+ 1\)\) / 2\) (\d+)", text).group(1))}
    blk = text[text.index("theorem no_sol_1"):text.index("theorem prime_le_1")]
    d["key"] = tuple(map(int, re.search(r"key : ∀ p < (\d+), ∀ u < (\d+)", blk).groups()))
    d["hu"] = int(re.search(r"hu : u < (\d+)", blk).group(1))
    d["hB1"] = int(re.search(r"hB : p ≤ (\d+)", blk).group(1))
    d["c"] = {int(h): [int(x) for x in l.split(",")]
              for h, l in re.findall(r"def c(\d) \(i : ℕ\) : ℕ := \[([\d, ]+)\]", text)}
    d["prime_le"] = {int(h): (int(b), int(hh), int(D), int(ch)) for h, b, hh, D, ch in re.findall(
        r"theorem prime_le_(\d) .*?: p ≤ (\d+) := by\s*have hb := "
        r"prime_le_of_two_sq_eq_succ_sigma \(h := (\d+)\) \(D := (\d+)\) c(\d)", text, re.S)}
    d["L"] = {int(h): [(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)", body)]
              for h, body in re.findall(r"def L(\d) : List \(ℕ × ℕ\) :=\s*\[(.*?)\]\n", text, re.S)}
    # Names: every declaration must refer to its own exponent, list and chunks.
    d["names"] = []
    d["L_ok"] = {}
    for h, hl, hm in re.findall(
            r"theorem L(\d)_ok : L(\d)\.all \(fun mm => maskOK (\d) mm\.1 mm\.2\) = true", text):
        d["L_ok"][int(h)] = True
        if not h == hl == hm:
            d["names"].append(f"L{h}_ok checks L{hl} with maskOK {hm}")
    d["chk"] = {}
    for h, j, hh, hl, s, n in re.findall(
            r"theorem chk(\d)_(\d) : chk (\d) L(\d) (\d+) (\d+) = true", text):
        if not (h == hh == hl and int(j) == len(d["chk"].get(int(h), []))):
            d["names"].append(f"chk{h}_{j} states chk {hh} L{hl}")
        d["chk"].setdefault(int(h), []).append((int(s), int(n)))
    d["no_sol"] = {}
    for h, body in re.findall(r"theorem no_sol_(\d) (.*?)\n\n", text, re.S):
        if h != "1":
            d["no_sol"][int(h)] = (int(re.search(r"hB : p ≤ (\d+)", body).group(1)),
                                   [int(x) for x in re.findall(r"by_cases c\d : i < (\d+)", body)],
                                   [(int(a), int(b)) for a, b in re.findall(
                                       r"show (\d+) \+ 2 \* \(i - (\d+)\) = 3 \+ 2 \* i", body)])
            refs = re.findall(r"good_sound L(\d)_ok", body)
            uses = re.findall(r"chk_sound _ _ chk(\d)_(\d)", body)
            want = [(h, str(j)) for j in range(len(d["chk"].get(int(h), [])))]
            if refs != [h] or uses != want:
                d["names"].append(f"no_sol_{h} uses good_sound {refs} and chunks {uses}")
    return d


def replay(d, log):
    ok = True

    def say(good, what):
        nonlocal ok
        ok &= good
        log(("ACCEPT " if good else "REJECT ") + what)

    for what in d["names"]:
        say(False, "declaration names: " + what)
    for fam, hs in (("c", HS), ("prime_le", HS), ("L", MASK_HS), ("L_ok", MASK_HS),
                    ("chk", MASK_HS), ("no_sol", MASK_HS)):
        if sorted(d[fam]) != hs:
            say(False, f"families: {fam} declared for h in {sorted(d[fam])}, expected {hs}")

    # no_sol_1: `key` by decide +kernel, and `hu` (u < U from p <= hB1 and the equation).
    P, U = d["key"]
    say(all(2 * (2 * u + 1) ** 2 != 1 + geo(p, 3)
            for p in range(P) for u in range(U) if p % 2 == 1),
        f"no_sol_1 key: p < {P}, u < {U}, p odd: 2 (2u+1)^2 != 1 + geo p 3")
    say(d["hu"] == U and P == d["hB1"] + 1 and
        2 * (2 * U + 1) ** 2 > 1 + geo(d["hB1"], 3),
        f"no_sol_1 hu: p <= {d['hB1']} and the equation force u < {d['hu']}; key covers p <= {d['hB1']}")
    # prime_le_h: certificate hypotheses (interval_cases; decide +kernel) and norm_num facts.
    for h, (b, hh, D, ch) in sorted(d["prime_le"].items()):
        if ch not in d["c"]:
            say(False, f"prime_le_{h}: no list c{ch}")
            continue
        c = d["c"][ch]
        say(h == hh == ch and len(c) == h + 1 and cert_ok(h, D, c) and max(7, 2 * D) <= b,
            f"prime_le_{h}: c{ch} = {c} is a certificate of degree {h} with D = {D}, "
            f"max 7 (2 D) = {max(7, 2 * D)} <= {b}")
    # L_h_ok and chk h L_h start n (decide +kernel), and coverage of no_sol_h.
    for h in sorted(d["L"]):
        if h not in d["chk"] or h not in d["no_sol"]:
            continue    # reported as a missing family above
        L = d["L"][h]
        say(all(maskOK(h, m, mask) for m, mask in L), f"L{h}_ok: {len(L)} masks")
        for s, n in d["chk"][h]:
            good, q = chk(h, L, s, n, d["steps"])
            say(good, f"chk {h} L{h} {s} {n}" + ("" if good else f": fails at {q}"))
        b, thr, shows = d["no_sol"][h]
        chunks = d["chk"][h]
        # case i lies in [lo_k, hi_k) with lo_k = offset of chunk k, hi_k = next threshold.
        his = thr + [None]
        cover = (len(shows) == len(chunks) == len(thr) + 1 and
                 all(s == st == 3 + 2 * off for (s, _), (st, off) in zip(chunks, shows)) and
                 shows[0][1] == 0 and
                 all(t == shows[k + 1][1] for k, t in enumerate(thr)))
        # the last chunk must reach the bound: i <= (b - 3) / 2
        imax = (b - 3) // 2
        for k, (s, n) in enumerate(chunks if cover else []):
            hi = his[k] if his[k] is not None else imax + 1
            cover &= hi - shows[k][1] <= n
        say(cover, f"no_sol_{h}: chunks {chunks} cover the odd p in [3, {b}]")
    return ok


def main():
    if len(sys.argv) not in (2, 3) or (len(sys.argv) == 3 and sys.argv[2] != "bad"):
        print(__doc__)
        return 2
    try:
        with open(sys.argv[1], encoding="utf-8") as f:
            d = read(f.read())
    except (OSError, UnicodeDecodeError) as e:
        print(f"cannot read {sys.argv[1]}: {e}", file=sys.stderr)
        return 2
    except (AttributeError, ValueError):
        print(f"{sys.argv[1]}: the text of ShapeSmall.lean (isq steps, no_sol_1, prime_le_1) "
              "was not found", file=sys.stderr)
        return 2
    if len(sys.argv) == 2:
        return 0 if replay(d, print) else 1
    if not replay(d, lambda line: None):
        print("the file itself is rejected; the controls need the accepted module", file=sys.stderr)
        return 2
    # Negative controls: each corrupted copy must be rejected.
    import copy
    controls = []
    d1 = copy.deepcopy(d)
    m, mask = d1["L"][5][1]
    r = next(r for r in range(m) if not (mask >> r) & 1)   # a residue that is twice a square
    d1["L"][5][1] = (m, mask | (1 << r))
    controls.append((f"L5 mask for modulus {m} with bit {r} added", d1))
    d2 = copy.deepcopy(d)
    d2["c"][6][-1] += 1
    controls.append((f"c6 with last coefficient {d['c'][6][-1]} -> {d2['c'][6][-1]}", d2))
    allrej = True
    for name, dd in controls:
        lines = []
        rejected = not replay(dd, lines.append)
        first = next((l for l in lines if l.startswith("REJECT")), "none")
        print(("REJECTED " if rejected else "ACCEPTED (control failed) ") + name)
        print("  first failure: " + first)
        allrej &= rejected
    return 0 if allrej else 1


if __name__ == "__main__":
    sys.exit(main())
