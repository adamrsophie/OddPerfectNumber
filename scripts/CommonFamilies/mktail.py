# Untrusted helper script for the OddPerfect Lean library.
# Emits the data lemmas for one table written by gen2.py: the row parts zp, the row, reach,
# primality and abundance checks, and the hcand lemma of every branch; writes <name>.tail.txt.
# Reads <name>.meta.json and <name>.lean.txt; the optional key "zc" of the meta file sets the
# number of rows per part (default 100). The optional key "fast" of the meta file (an object
# with the modulus "P") selects the cheaper checks of OddPerfect/CommonFastChecks.lean: rows
# through the node parts (rowChkP), primality by trial division over odd primes (fastPrime
# oddP), and reach checks with a few blocked sets (reachS) found greedily here, where the set
# number g blocks the candidates whose residue modulo P lies in a fixed set.
# Used by: OddPerfect/CommonFiveSeven.lean, CommonSixtyFive.lean, CommonFiftyFive.lean,
# CommonEightyFive.lean, and CommonOneFifteen.lean, CommonOneFifteenData.lean,
# CommonOneFifteenPrime.lean (the lemmas after the literals), and the 13 modules
# CommonNinetyFive*.lean (after ndflat.py, split.py and asm_split.py).
# Run: python3 mktail.py name d branch ... with branch = tag:ns:candLean, for example
# python3 mktail.py 65 65 'A:3:b == 13' 'B:2:b % 12 == 1 && b != 13'.
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, json, re
name, d = sys.argv[1], int(sys.argv[2])
meta = json.load(open(f'{name}.meta.json')); P = meta['passes']
FAST = meta.get('fast')
S, ND = meta['nsrcparts'], meta['nndparts']
pc = 'pc' + name if 'def pc' + name in open(f'{name}.lean.txt').read() else '[]'
n = name
o = []
def lst(pre, k):
    # a list of part names, wrapped at 100 columns with a 6 space continuation indent
    items = [f'{pre}{n}_{i}' for i in range(k)]; lines = []; cur = '['
    for i, it in enumerate(items):
        piece = it + (', ' if i < k - 1 else ']')
        if len(cur) + len(piece) > 84: lines.append(cur.rstrip()); cur = ''
        cur += piece
    lines.append(cur)
    return '\n      '.join(lines)
def wrap(head, items, sep, tail, ind):
    # join items after head, wrapped at 100 columns, continuation lines indented by ind
    lines = []; cur = head
    for i, it in enumerate(items):
        piece = it + (sep if i < len(items) - 1 else tail)
        if len(cur) + len(piece) > 99: lines.append(cur.rstrip()); cur = ' ' * ind
        cur += piece
    lines.append(cur)
    return '\n'.join(lines)
def pick(k, lem):
    # a term proof of `∀ c ∈ [p0, ..., p(k-1)], c.all f = true` from the part lemmas
    s = 'fun _ h => absurd h List.not_mem_nil'
    for i in reversed(range(k)):
        s = f'List.forall_mem_cons.mpr ⟨{lem(i)}, {s}⟩'
    return wrap('    exact ', s.split(' '), ' ', '', 6)
ZC = int(meta.get("zc", 100))
Z = (meta['nsrc'] + ZC - 1) // ZC
for k in range(Z):
    o.append(f'''/-- Rows with their sources, part {k}. -/
def zp{n}_{k} : List (ℕ × List ℕ) := ((nodes{n}.zip rows{n}).drop {ZC * k}).take {ZC}
''')
o.append(f'''/-- The rows with their sources in parts. -/
theorem zp{n}_eq : nodes{n}.zip rows{n} =\n    {lst('zp', Z)}.flatten := by\n  decide +kernel
''')
if FAST:
    txt = open(f'{name}.lean.txt').read()
    def grab(nm):
        m = re.search(r'def ' + nm + r' : [^\n]*:=\n  (\[.*?\])\n', txt, re.S); return eval(m.group(1))
    ndl = [len(grab(f'nd{n}_{k}')) for k in range(ND)]
    K = ndl[0]
    assert all(x == K for x in ndl[:-1]) and ndl[-1] <= K
    o.append(f'''/-- The node parts as one list. -/
def ndp{n} : List (List ℕ) :=\n  {lst('nd', ND)}

/-- The node parts have length `{K}`, the last one at most `{K}`. -/
theorem ndp{n}_lens : lensOK {K} ndp{n} = true := by decide +kernel
''')
    for k in range(Z):
        o.append(f'''/-- The divisibility checks of the rows, part {k}. -/
theorem rows{n}_{k} : zp{n}_{k}.all (rowChkP {K} ndp{n} {d}) = true := by decide +kernel
''')
    o.append(f'''/-- The divisibility checks of all rows. -/
theorem hrows{n} : ∀ e ∈ nodes{n}.zip rows{n}, rowChk {d} nodes{n} e = true := fun e he =>
  rowChk_of_rowChkP (K := {K}) (parts := ndp{n}) (by decide) nd{n}_eq ndp{n}_lens
    (all_of_parts _ zp{n}_eq (by
{pick(Z, lambda i: f'rows{n}_{i}')}) e he)
''')
else:
    for k in range(Z):
        o.append(f'''/-- The divisibility checks of the rows, part {k}. -/
theorem rows{n}_{k} : zp{n}_{k}.all (rowChk {d} nodes{n}) = true := by decide +kernel
''')
    o.append(f'''/-- The divisibility checks of all rows. -/
theorem hrows{n} : ∀ e ∈ nodes{n}.zip rows{n}, rowChk {d} nodes{n} e = true :=
  all_of_parts _ zp{n}_eq (by
{pick(Z, lambda i: f'rows{n}_{i}')})
''')
o.append(f'''/-- No node is `2`. -/
theorem nodes{n}_ne2 : ∀ t ∈ nodes{n}, t ≠ 2 := by
  have : nodes{n}.all (· != 2) = true := by decide +kernel
  intro t ht
  simpa using List.all_eq_true.mp this t ht

/-- The source nodes in parts. -/
theorem src{n}_eq : nodes{n}.take rows{n}.length =\n    {lst('src', S)}.flatten := by\n  decide +kernel

/-- The nodes in parts. -/
theorem nd{n}_eq : nodes{n} =\n    {lst('nd', ND)}.flatten := by\n  decide +kernel
''')
for br in sys.argv[3:]:
    tag, ns, cl = br.split(':', 2)
    cand = f'cand{n}{tag}'
    o.append(f'''/-- The blocked candidates{', branch ' + tag if tag else ''}. -/
def cand{n}{tag} (b : ℕ) : Bool := {cl}
''')
    if FAST:
        Pm = int(FAST['P'])
        nodes = grab(f'nodes{n}'); rows = grab(f'rows{n}')
        tm = int(re.search(r'def tm' + n + r' : ℕ :=\n  (\d+)', txt).group(1))
        masks = [sum(1 << j for j in set(r)) for r in rows]
        srcs = nodes[:len(rows)]
        # the candidate text is evaluated as Python, so only the form `b % m == r` is accepted
        assert re.fullmatch(r'b % \d+ == \d+', cl), cl
        cnd = [eval(cl, {'b': x}) for x in srcs]
        def ok(R):
            # the Python mirror of reachS with the blocked set: candidates with residue in R
            M = 2 ** int(ns) - 1
            for _ in range(P):
                if M & tm == tm: return True
                for i in range(len(rows)):
                    if (M >> i) & 1 and not (cnd[i] and srcs[i] % Pm in R): M |= masks[i]
            return M & tm == tm
        groups = []
        for x, c in zip(srcs, cnd):
            if not c or any(x % Pm in g for g in groups): continue
            for g in groups:
                if ok(g | {x % Pm}): g.add(x % Pm); break
            else:
                assert ok({x % Pm}), x
                groups.append({x % Pm})
        G = len(groups)
        bls = '[' + ', '.join(f'blk{n}{tag}_{g}' for g in range(G)) + ']'
        for g, R in enumerate(groups):
            o.append(f'''/-- Blocked set {g}{', branch ' + tag if tag else ''}: the candidates whose residue modulo `{Pm}` is a set bit of
the number below. -/
def blk{n}{tag}_{g} (x : ℕ) : Bool :=
  {cand} x && Nat.testBit {sum(1 << r for r in R)} (x % {Pm})
''')
        for g in range(G):
            o.append(f'''/-- Reach check with the blocked set {g}{', branch ' + tag if tag else ''}. -/
theorem reach{n}{tag}_{g} : reachS nodes{n} rows{n} {ns} tm{n} {P} blk{n}{tag}_{g} = true := by
  decide +kernel
''')
        o.append(f'''/-- Reach check with no source blocked{', branch ' + tag if tag else ''}. -/
theorem reach{n}{tag}_none : reach nodes{n} rows{n} {ns} tm{n} {P} 0 = true := by decide +kernel

/-- Every blocked candidate lies in one of the blocked sets{', branch ' + tag if tag else ''}. -/
theorem blk{n}{tag}_cover : (nodes{n}.take rows{n}.length).all
    (fun b => !{cand} b || {bls}.any fun f => f b) = true := by
  decide +kernel

/-- Every blocked source node passes the reach check{', branch ' + tag if tag else ''}. -/
theorem hcand{n}{tag} : ∀ b ∈ nodes{n}.take rows{n}.length, {cand} b = true →
    reach nodes{n} rows{n} {ns} tm{n} {P} b = true :=
  hcand_of_groups {bls} (by
{pick(G, lambda g: f'reach{n}{tag}_{g}')}) blk{n}{tag}_cover
''')
        continue
    for i in range(S):
        o.append(f'''/-- Reach checks for the blocked source nodes, part {i}{', branch ' + tag if tag else ''}. -/
theorem reach{n}{tag}_{i} :
    src{n}_{i}.all (fun b => !{cand} b || reach nodes{n} rows{n} {ns} tm{n} {P} b) = true := by
  decide +kernel
''')
    o.append(f'''/-- Reach check with no source blocked{', branch ' + tag if tag else ''}. -/
theorem reach{n}{tag}_none : reach nodes{n} rows{n} {ns} tm{n} {P} 0 = true := by decide +kernel

/-- Every blocked source node passes the reach check{', branch ' + tag if tag else ''}. -/
theorem hcand{n}{tag} : ∀ b ∈ nodes{n}.take rows{n}.length, {cand} b = true →
    reach nodes{n} rows{n} {ns} tm{n} {P} b = true := by
  intro b hb hcb
  have := all_of_parts (f := fun b => !{cand} b || reach nodes{n} rows{n} {ns} tm{n} {P} b)
    _ src{n}_eq (by
{pick(S, lambda i: f'reach{n}{tag}_{i}')}) b hb
  simpa [hcb] using this
''')
if pc != '[]':
    o.append(f'''/-- The Pratt certificates of the `d = {d}` table are accepted. -/
theorem pc{n}_check : Pratt.check pc{n} = true := by decide +kernel
''')
if FAST:
    for i in range(ND):
        o.append(f'''/-- The nodes of part {i} are prime by trial division. -/
theorem nd{n}_{i}_isPS : nd{n}_{i}.all (fastPrime oddP) = true := by decide +kernel
''')
    prime_txt = f'''/-- The nodes of the `d = {d}` table are prime. -/
theorem nodes{n}_prime : ∀ t ∈ nodes{n}, t.Prime := fun t ht =>
  prime_of_fastPrime (all_of_parts _ nd{n}_eq (by
{pick(ND, lambda i: f'nd{n}_{i}_isPS')}) t ht)
'''
else:
    for i in range(ND):
        o.append(f'''/-- The nodes of part {i} are certified. -/
theorem nd{n}_{i}_isPS : nd{n}_{i}.all (isPS {pc}) = true := by decide +kernel
''')
    pcc = f'pc{n}_check' if pc != '[]' else 'rfl'
    prime_txt = f'''/-- The nodes of the `d = {d}` table are prime. -/
theorem nodes{n}_prime : ∀ t ∈ nodes{n}, t.Prime := fun t ht =>
  isPS_sound {pcc} (all_of_parts _ nd{n}_eq (by
{pick(ND, lambda i: f'nd{n}_{i}_isPS')}) t ht)
'''
o.append(prime_txt + f'''
/-- The target primes are the nodes selected by the target mask. -/
theorem vals{n}_sel : CommonChain.sel 0 tm{n} 0 nodes{n} = vals{n} := by decide +kernel

/-- The target primes are distinct. -/
theorem vals{n}_nodup : vals{n}.Nodup :=
  (nodup_of_ndM (M := 0) (by decide +kernel)).1

/-- The two full products over the target primes. -/
theorem PG{n} : pPow (expL vals{n} 0) = P{n} ∧ pSig (expL vals{n} 0) = G{n} := by
  decide +kernel

/-- Abundance: the target primes with fourth powers, and with any one of them `≡ 1 (mod 12)` to
the first power. -/
theorem ab{n} : abOK2 vals{n} (fun b : ℕ => b % 12 == 1) P{n} G{n} = true := by decide +kernel
''')
open(f'{name}.tail.txt', 'w').write('\n'.join(o))
