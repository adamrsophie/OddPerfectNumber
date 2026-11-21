# Untrusted helper script for the OddPerfect Lean library.
# Mirror of LPF.search in OddPerfect/LargestPrimeFactor.lean. Emits the prime list P,
# the number M = 2 * prod P and the row table T for a bound B, either as the final theorem
# (mode thm) or as a test file of four kernel checks (mode test).
# Used by: OddPerfect/LargestPrimeFactor.lean (the P, M and T arguments of
# exists_primeFactor_gt, B = 2000).
# Run: python3 gen2.py 2000 thm
# Requires: Python 3 standard library. Running time: about 2 seconds for B = 2000.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

# Mirror of the Lean search; emits P, M, row table T, and the final theorem or test file.
import sys
from math import gcd
sys.setrecursionlimit(100000)
B=int(sys.argv[1]); mode=sys.argv[2]
def isp(n): return n>=2 and all(n%d for d in range(2,int(n**.5)+1))
P=[p for p in range(3,B+1) if isp(p)]
M=2
for p in P: M*=p
def gs(p,e): return (p**(e+1)-1)//(p-1)
def big(m):
    r=m
    for _ in range(100):
        g=gcd(r,M)
        if g==1: break
        r//=g
    return r!=1 and gcd(r,M)==1
rowc={}
def row(p):
    if p not in rowc:
        rowc[p]=[e for e in range((B-3)//2+1) if e>=1 and (e%2==0 or (p%4==1 and e%4==1)) and not big(gs(p,e))]
    return rowc[p]
nodes=0
def upper(ex,nd):
    num=den=1
    d=dict(reversed(ex))
    for p in P:
        if p in nd: continue
        if p in d: num*=gs(p,d[p]); den*=p**d[p]
        else: num*=p; den*=p-1
    return num<2*den
def search(fuel,ex,dv,nd):
    global nodes; nodes+=1
    if fuel==0: return False
    if upper(ex,nd): return True
    if dv:
        p,rest=dv[0],dv[1:]
        if any(x==p for x,_ in ex): return search(fuel-1,ex,rest,nd)
        for e in row(p):
            if not all(gs(p,e)%q for q in nd): continue
            new=[q for q in P if gs(p,e)%q==0]
            if not search(fuel-1,[(p,e)]+ex,new+rest,nd): return False
        return True
    und=[q for q in P if not any(x==q for x,_ in ex) and q not in nd]
    if not und: return False
    q=und[0]
    return search(fuel-1,ex,[q],nd) and search(fuel-1,ex,[],[q]+nd)
ok=search(1000,[],[],[])
T=[(p,rowc[p]) for p in rowc]
sys.stderr.write(f"B={B} ok={ok} nodes={nodes} rows={len(T)} rowentries={sum(len(r) for _,r in T)}\n")
Ts="["+", ".join(f"({p}, {r})" for p,r in T)+"]"
if mode=='thm':
    print(f"""/-- The largest prime factor of an odd perfect number exceeds `{B}`. -/
theorem exists_primeFactor_gt {{N : ℕ}} (h : OddPerfect N) : ∃ p ∈ N.primeFactors, {B} < p :=
  LPF.exists_primeFactor_gt_of_search (P := {P})
    (M := {M})
    (T := {Ts})
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h""")
else:
    print(f"""set_option profiler true
set_option maxHeartbeats 0
example : LPF.primesUpTo {B} = {P} := by decide +kernel
example : 2 * ({P} : List ℕ).prod = {M} := by decide +kernel
example : ({Ts} : List (ℕ × List ℕ)).all (fun x => x.2 == LPF.row {B} {M} x.1) = true := by decide +kernel
example : LPF.search {B} {P} {M} {Ts} 1000 [] [] [] = true := by decide +kernel
end OddPerfect""")
