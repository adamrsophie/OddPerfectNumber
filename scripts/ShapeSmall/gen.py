"""Regenerate the numeric literals of OddPerfect/ShapeSmall.lean.

Usage:
    python3 -I gen.py                 print every literal in the order of the source
    python3 -I gen.py --check PATH    also compare with the literals of the Lean file PATH;
                                      exit 1 on any difference (also a declaration that
                                      names another exponent, list or chunk, or a missing
                                      Lh_ok), exit 2 for an unreadable file or a file
                                      without the expected text

Standard library only, deterministic. Each line is tagged:
    exact    the value is determined by the mathematics (or by a stated canonical rule)
    rule     reproduced exactly by a stated deterministic rule whose parameters were chosen
             (greedy moduli, candidate set and count); the needed property is verified too
    choice   the value was chosen; the script verifies the property the Lean proof needs
"""
import math
import re
import sys
from fractions import Fraction

HS = [1, 2, 3, 5, 6]          # e = 2 h with e + 1 prime and e < 16
MASK_HS = [2, 3, 5, 6]        # exponents handled by masks and the square root test
# Choices recorded from the Lean module (not forced by the mathematics):
ISQ_STEPS = 10                # averaging steps in nsq
MASK_COUNT = {2: 3, 3: 4, 5: 8, 6: 6}   # how many greedy moduli are kept
CHUNK = 16384                 # largest number of odd values per kernel check
# Candidate moduli of the greedy choice: odd primes below 100 and powers of 2 up to 64.
CANDIDATES = [q for q in range(3, 100) if all(q % d for d in range(2, q))] + [4, 8, 16, 32, 64]


def require(ok, what):
    """A property the Lean proof needs; stops with exit status 1 when it fails (no assert,
    so that python -O checks it too)."""
    if not ok:
        raise SystemExit("gen.py: property fails: " + what)


def geo(r, n, m=None):
    """1 + r + ... + r^(n-1), by the recurrence of the Lean `geo` (reduced mod m if given)."""
    s = 0
    for _ in range(n):
        s = 1 + r * s
        if m is not None:
            s %= m
    return s


def series(h):
    """First h + 1 coefficients of sqrt((1 - X/2) / (1 - X)) as fractions: f_0 = 1 and
    2 sum_{i+j=k} f_i f_j = 1 for k >= 1 (the coefficients of (2 - X)/(1 - X) are 2, 1, 1, ...)."""
    f = [Fraction(1)]
    for k in range(1, h + 1):
        rest = sum(f[i] * f[k - i] for i in range(1, k))
        f.append((Fraction(1, 2) - rest) / 2)
    return f


def certificate(h):
    """Smallest D > 0 with D f_i integral for i <= h, and c_i = D f_i (exact: every valid
    certificate is a multiple of this one, since c_0 = D fixes the recursion)."""
    f = series(h)
    D = 1
    for x in f:
        D = D * x.denominator // math.gcd(D, x.denominator)
    c = [int(x * D) for x in f]
    require(c[0] == D, f"c_0 = D for h = {h}")
    for k in range(1, h + 1):
        require(2 * sum(c[i] * c[k - i] for i in range(k + 1)) == D * D, f"convolution {h} {k}")
    require(all(2 * c[i] <= D for i in range(1, h + 1)), f"2 c_i <= D for h = {h}")
    return D, c


def fullmask(h, m):
    """Bit r is set iff 1 + geo(r, 2h+1) is not twice a square mod m (unique given m)."""
    tw = {(2 * x * x) % m for x in range(m)}
    return sum(1 << r for r in range(m) if (1 + geo(r, 2 * h + 1, m)) % m not in tw)


def isq(v, k, x):
    for _ in range(k):
        x = min(x, (x + (v // x if x else 0)) // 2)
    return x


def isq_steps_needed(v, x):
    """Fewest averaging steps after which the Lean test sqOK holds (None if never)."""
    for k in range(64):
        r = isq(v, k, x)
        if r * r < v < (r + 1) * (r + 1):
            return k
    return None


def masks(h, bound):
    """Greedy: repeatedly take the candidate modulus whose full mask removes the most odd
    numbers in [3, bound] that are still left (ties: smallest modulus)."""
    full = {m: fullmask(h, m) for m in CANDIDATES}
    left = list(range(3, bound + 1, 2))
    out = []
    for _ in range(MASK_COUNT[h]):
        gain = lambda m: sum((full[m] >> (p % m)) & 1 for p in left)
        best = max(full, key=lambda m: (gain(m), -m))
        require(gain(best) > 0, f"greedy modulus removes a number for h = {h}")
        out.append((best, full[best]))
        left = [p for p in left if not (full[best] >> (p % best)) & 1]
    return out, left


def generate():
    """Return [(name, value, tag, note)] in the order of the source."""
    out = []
    cert = {h: certificate(h) for h in HS}
    bound = {h: max(7, 2 * cert[h][0]) for h in HS}

    # nsq: the step count is a choice; verified below on every number left by the masks.
    out.append(("isq_steps", ISQ_STEPS, "choice", None))

    # no_sol_1: p <= bound_1, u < U with U the smallest value making 2 (2U+1)^2 exceed
    # 1 + sigma(p^2) for every p <= bound_1; key ranges p < bound_1 + 1, u < U.
    b1 = bound[1]
    U = 0
    while 2 * (2 * U + 1) ** 2 <= 1 + geo(b1, 3):
        U += 1
    out.append(("no_sol_1", (b1, U, b1 + 1, U), "exact",
                "hB : p <= 2 D_1, hu : u < U, key : p < 2 D_1 + 1, u < U"))

    for h in HS:
        D, c = cert[h]
        out.append((f"c{h}", c, "exact", "minimal D; any multiple also works"))
        out.append((f"prime_le_{h}", (bound[h], h, D), "exact", "(p <= max 7 (2 D), h, D)"))

    notes = []
    for h in MASK_HS:
        L, left = masks(h, bound[h])
        out.append((f"L{h}", L, "rule",
                    f"greedy moduli, count {MASK_COUNT[h]} chosen; each mask forced by its modulus"))
        # Every number left by the masks must pass the square root test with ISQ_STEPS.
        need = 0
        for p in left:
            v = (1 + geo(p, 2 * h + 1)) // 2
            k = isq_steps_needed(v, p ** h)
            require(k is not None and k <= ISQ_STEPS, f"square root test for h = {h}, p = {p}")
            need = max(need, k)
        notes.append(f"h={h}: {len(left)} odd numbers left after the masks, "
                     + (f"square root test needs at most {need} steps (Lean uses {ISQ_STEPS})"
                        if left else "the square root test is never reached"))
        # Chunks: odd numbers 3, 5, ..., 2 D + 1 (D of them) in chunks of at most CHUNK.
        D = cert[h][0]
        chunks = [(3 + 2 * s, min(CHUNK, D - s)) for s in range(0, D, CHUNK)]
        require(3 + 2 * (D - 1) >= bound[h], f"chunks reach the bound for h = {h}")
        out.append((f"chk{h}", chunks, "choice", f"chunk size {CHUNK}; covers [3, {bound[h]}]"))
        out.append((f"no_sol_{h}", bound[h], "exact", "hB : p <= 2 D"))
        if len(chunks) > 1:
            thr = [s for s in range(CHUNK, D, CHUNK)]
            split = [(3 + 2 * s, s) for s in range(0, D, CHUNK)]
            out.append((f"no_sol_{h}_split", (thr, split), "choice",
                        "case thresholds and (start, offset) of each chunk"))
    return out, notes


def parse_lean(text):
    """Extract the same literals from the Lean source. Declarations that name another
    exponent, list or chunk than their own are listed under the key "names", which the
    generated literals never have."""
    got = {}
    names = []
    m = re.search(r"isq \(\(1 \+ geo p \(2 \* h \+ 1\)\) / 2\) (\d+)", text)
    got["isq_steps"] = int(m.group(1))
    blk = text[text.index("theorem no_sol_1"):text.index("theorem prime_le_1")]
    got["no_sol_1"] = (int(re.search(r"hB : p ≤ (\d+)", blk).group(1)),
                       int(re.search(r"hu : u < (\d+)", blk).group(1)),
                       *map(int, re.search(r"key : ∀ p < (\d+), ∀ u < (\d+)", blk).groups()))
    for h, lst in re.findall(r"def c(\d) \(i : ℕ\) : ℕ := \[([\d, ]+)\]", text):
        got[f"c{h}"] = [int(x) for x in lst.split(",")]
    for d_h, d_D in re.findall(r"Certificate of degree `(\d)` \(from `cert.py`\): `D = (\d+)`", text):
        got[f"doc_D{d_h}"] = int(d_D)
    for h, b, hh, D, ch in re.findall(
            r"theorem prime_le_(\d) .*?: p ≤ (\d+) := by\s*have hb := "
            r"prime_le_of_two_sq_eq_succ_sigma \(h := (\d+)\) \(D := (\d+)\) c(\d)", text, re.S):
        if h != ch:
            names.append(f"prime_le_{h} uses c{ch}")
        got[f"prime_le_{h}"] = (int(b), int(hh), int(D))
    for h, body in re.findall(r"def L(\d) : List \(ℕ × ℕ\) :=\s*\[(.*?)\]\n", text, re.S):
        got[f"L{h}"] = [(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)", body)]
    for h, j, hh, hl, s, n in re.findall(
            r"theorem chk(\d)_(\d) : chk (\d) L(\d) (\d+) (\d+) = true", text):
        if not (h == hh == hl and int(j) == len(got.get(f"chk{h}", []))):
            names.append(f"chk{h}_{j} states chk {hh} L{hl}")
        got.setdefault(f"chk{h}", []).append((int(s), int(n)))
    oks = []
    for h, hl, hm in re.findall(
            r"theorem L(\d)_ok : L(\d)\.all \(fun mm => maskOK (\d) mm\.1 mm\.2\) = true", text):
        oks.append(int(h))
        if not h == hl == hm:
            names.append(f"L{h}_ok checks L{hl} with maskOK {hm}")
    if sorted(oks) != MASK_HS:
        names.append(f"Lh_ok declared for h in {sorted(oks)}")
    for h, body in re.findall(r"theorem no_sol_(\d) (.*?)\n\n", text, re.S):
        if h == "1":
            continue
        got[f"no_sol_{h}"] = int(re.search(r"hB : p ≤ (\d+)", body).group(1))
        refs = re.findall(r"good_sound L(\d)_ok", body)
        uses = re.findall(r"chk_sound _ _ chk(\d)_(\d)", body)
        if refs != [h] or uses != [(h, str(j)) for j in range(len(got.get(f"chk{h}", [])))]:
            names.append(f"no_sol_{h} uses good_sound {refs} and chunks {uses}")
        thr = [int(x) for x in re.findall(r"by_cases c\d : i < (\d+)", body)]
        if thr:
            # thresholds of the case split, then (start, offset) for each chunk use
            offs = [int(x) for x in re.findall(r"chk_sound _ _ chk\d_\d \(i - (\d+)\)", body)]
            shows = [(int(a), int(b)) for a, b in
                     re.findall(r"show (\d+) \+ 2 \* \(i - (\d+)\) = 3 \+ 2 \* i", body)]
            if [b for _, b in shows] != offs:
                names.append(f"no_sol_{h}: offsets {offs} of the chunks, {shows} in the shows")
            got[f"no_sol_{h}_split"] = (thr, shows)
    if names:
        got["names"] = names
    return got


def main():
    args = sys.argv[1:]
    out, notes = generate()
    for name, val, tag, note in out:
        print(f"{name} = {val}   [{tag}]" + (f"  {note}" if note else ""))
    for n in notes:
        print("verified:", n)
    if not args:
        return 0
    if len(args) != 2 or args[0] != "--check":
        print(__doc__)
        return 2
    try:
        with open(args[1], encoding="utf-8") as f:
            got = parse_lean(f.read())
    except (OSError, UnicodeDecodeError) as e:
        print(f"cannot read {args[1]}: {e}", file=sys.stderr)
        return 2
    except (AttributeError, ValueError):
        print(f"{args[1]}: the text of ShapeSmall.lean (isq steps, no_sol_1, prime_le_1) "
              "was not found", file=sys.stderr)
        return 2
    bad = 0
    gen = {name: val for name, val, _, _ in out}
    # the docstring D of each certificate must equal the certificate D
    for h in HS:
        gen[f"doc_D{h}"] = gen[f"prime_le_{h}"][2]
    for k in sorted(set(gen) | set(got)):
        if gen.get(k) != got.get(k):
            bad += 1
            print(f"DIFF {k}: generated {gen.get(k)} Lean {got.get(k)}")
    print(f"check: {len(gen)} literal groups, {bad} differences")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
