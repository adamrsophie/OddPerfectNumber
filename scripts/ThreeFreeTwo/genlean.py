# Untrusted helper script for the OddPerfect Lean library.
# Step 3 of 3 for OddPerfect/ThreeFreeTwo.lean: emits Ctx.table, the box lemmas box_*
# and the leaf lemmas leaf_*. The closing tactic lines of the leaves in the Lean file were
# later edited by hand; the statements and the data passed to Ctx.close are as emitted.
# Run from the folder holding leaves.pkl: python3 genlean.py
# Writes table.lean, boxes.lean, leaves.lean and names.pkl to the current folder.
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import os
import pickle
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fac.py')).read())
res,Bv=pickle.load(open('leaves.pkl','rb'))
def isprime(n): return n>1 and all(n%d for d in range(2,int(n**.5)+1))
def pf(n):
    out=[];d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0: n//=d
        d+=1
    if n>1: out.append(n)
    return out
S=[s for s in range(5,300) if isprime(s) and s%3==2]
def tgt(d): return f"({d} = q ∨ {d} = r₁ ∨ {d} = r₂)"
disj=[]
for s in S:
    ds=pf(1+s+s*s)
    disj.append((s,ds))
L=[]
L.append("/-- The small ordinary primes: for each prime `s < 300` with `s ≡ 2 (mod 3)`, every prime")
L.append("factor of `1 + s + s^2` is `q`, `r₁` or `r₂`. -/")
L.append("theorem Ctx.table {N q r₁ r₂ s : ℕ} (c : Ctx N q r₁ r₂) (hs : s ∈ ord N q r₁ r₂)")
L.append("    (hlt : s < 300) :")
body=" ∨\n    ".join(f"(s = {s} ∧ " + " ∧ ".join(tgt(d) for d in ds) + ")" for s,ds in disj)
L.append("    "+body+" := by")
L.append("  obtain ⟨hsp, he, h5⟩ := c.ord_facts hs")
L.append("  have hm := OPNThreeFree.source_mod_three c.opn.perfect c.h3 hsp he")
L.append("  have hL : " + " ∨ ".join(f"s = {s}" for s in S) + " := by")
L.append("    interval_cases s <;> first | omega | (exfalso; norm_num at hsp)")
L.append("  rcases hL with " + " | ".join("rfl" for s in S))
n=len(disj)
for k,(s,ds) in enumerate(disj):
    inner="⟨rfl, " + ", ".join(f"(c.tgt hs (d := {d}) (by norm_num) (by norm_num)).1" for d in ds) + "⟩"
    term=inner
    if k<n-1: term=f"Or.inl {term}"
    for _ in range(k): term=f"Or.inr <| {term}"
    L.append(f"  · exact {term}")
table="\n".join(L)
# box lemmas
LS={'0':'0','7':'14 / 37','13':'5 / 18','31':'2 / 11'}
boxes=[]
for (a,b),(nu,de) in Bv.items():
    boxes.append(f"""theorem box_{a}_{b} : bsum (5 / 18) ({LS[a]}) ({LS[b]}) 300 5 ≤ {nu} / {de} := by
  simp only [bsum, wt, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num [Nat.even_iff, min_def]
""")
CLH={'5':('= 5',5),'n2':('% 3 = 2 ∧ 11 ≤ {r}',11),'7':('= 7',7),'13':('= 13',13),'19':('= 19',19),
 '31':('= 31',31),'37':('= 37',37),'43':('= 43',43),'big':('% 3 = 1 ∧ 61 ≤ {r}',61),
 'big307':('% 3 = 1 ∧ 61 ≤ {r} ∧ {r} ≠ 307',61),'307':('= 307',307)}
def hyp(cl,r):
    h,m=CLH[cl]
    return f"{r} "+h.format(r=r)
def mfact(cl):
    return CLH[cl][1]
leaves=[]
names={}
for (a,b,qh,C,la,lb,tot) in res:
    tag={None:'','q = 409':'_a','q = 3541':'_b','q ≠ 409 ∧ q ≠ 3541':'_c'}[qh]
    nm=f"leaf_{a}_{b}{tag}"
    names[(a,b,qh)]=nm
    ma,mb=mfact(a),mfact(b)
    def hb(lev,r,m,var):
        if lev=='0': return f"Or.inr (by omega)"
        return f"Or.inl (by nlinarith [show ({m} : ℚ) ≤ {r} by exact_mod_cast {var}])"
    Cs="{"+", ".join(map(str,C))+"}"
    extra=f" (hq : {qh})" if qh else ""
    nu,de=Bv[(la,lb)]
    leaves.append(f"""theorem {nm} {{N q r₁ r₂ : ℕ}} (c : Ctx N q r₁ r₂) (h1 : {hyp(a,'r₁')})
    (h2 : {hyp(b,'r₂')}){extra} : False := by
  have hq12 := c.q_mod
  have hm1 : {ma} ≤ r₁ := by omega
  have hm2 : {mb} ≤ r₂ := by omega
  refine c.close {Cs} (β := {LS[la]}) (γ := {LS[lb]}) (ρ₁ := {ma} / {ma-1}) (ρ₂ := {mb} / {mb-1})
    (B := {nu} / {de}) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ({hb(la,'r₁',ma,'hm1')})
    ({hb(lb,'r₂',mb,'hm2')})
    (le_trans (div_pred_le (by norm_num) hm1) (by norm_num))
    (le_trans (div_pred_le (by norm_num) hm2) (by norm_num))
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega)
    ?_ box_{la}_{lb} (by norm_num [kk, tl]) (by norm_num [fv, kk, tl])
  intro s hs hlt
  have ht := c.table hs hlt
  obtain ⟨-, hsq, hs1, hs2⟩ := mem_ord.mp hs
  have := c.h1q
  have := c.h2q
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega
""")
open('table.lean','w').write(table)
open('boxes.lean','w').write("\n".join(boxes))
open('leaves.lean','w').write("\n".join(leaves))
pickle.dump(names,open('names.pkl','wb'))
print(len(leaves))
