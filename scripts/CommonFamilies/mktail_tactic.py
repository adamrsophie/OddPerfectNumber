# Untrusted helper script for the OddPerfect Lean library.
# The earlier form of mktail.py: the same lemmas, except that the gluing proofs inside
# hrows*, hcand* and nodes*_prime use intro, simp only, rcases and exacts, where mktail.py
# writes a List.forall_mem_cons term. This is the form of the landed files of the 57 and 65
# families; the other families use mktail.py.
# Reads <name>.meta.json and <name>.lean.txt; the optional key "zc" of the meta file sets the
# number of rows per part (default 100). Writes <name>.tail.txt.
# Used by: OddPerfect/CommonFiveSeven.lean, CommonSixtyFive.lean (the lemmas after the
# literals).
# Run: python3 mktail_tactic.py 57 5 ':2:b % 12 == 1'
#      python3 mktail_tactic.py 65 65 'A:3:b == 13' 'B:2:b % 12 == 1 && b != 13'
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, json
name, d = sys.argv[1], int(sys.argv[2])
meta = json.load(open(f'{name}.meta.json')); P = meta['passes']
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
    alts = ' | '.join(['rfl'] * k)
    return ('    intro c hc\n    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc\n'
            f'    rcases hc with {alts}\n    exacts [' + ', '.join(lem(i) for i in range(k)) + ']')
ZC = int(meta.get("zc", 100))
Z = (meta['nsrc'] + ZC - 1) // ZC
for k in range(Z):
    o.append(f'''/-- Rows with their sources, part {k}. -/
def zp{n}_{k} : List (ℕ × List ℕ) := ((nodes{n}.zip rows{n}).drop {ZC * k}).take {ZC}
''')
o.append(f'''/-- The rows with their sources in parts. -/
theorem zp{n}_eq : nodes{n}.zip rows{n} =\n    {lst('zp', Z)}.flatten := by\n  decide +kernel
''')
for k in range(Z):
    o.append(f'''/-- The divisibility checks of the rows, part {k}. -/
theorem rows{n}_{k} : zp{n}_{k}.all (rowChk {d} nodes{n}) = true := by decide +kernel
''')
o.append(f'''/-- The divisibility checks of all rows. -/
theorem hrows{n} : ∀ e ∈ nodes{n}.zip rows{n}, rowChk {d} nodes{n} e = true :=
  all_of_parts _ zp{n}_eq (by
{pick(Z, lambda i: f'rows{n}_{i}')})

/-- No node is `2`. -/
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
for i in range(ND):
    o.append(f'''/-- The nodes of part {i} are certified. -/
theorem nd{n}_{i}_isPS : nd{n}_{i}.all (isPS {pc}) = true := by decide +kernel
''')
pcc = f'pc{n}_check' if pc != '[]' else 'rfl'
o.append(f'''/-- The nodes of the `d = {d}` table are prime. -/
theorem nodes{n}_prime : ∀ t ∈ nodes{n}, t.Prime := fun t ht =>
  isPS_sound {pcc} (all_of_parts _ nd{n}_eq (by
{pick(ND, lambda i: f'nd{n}_{i}_isPS')}) t ht)

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
