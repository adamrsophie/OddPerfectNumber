# Untrusted helper script for the OddPerfect Lean library.
# Primality proofs for the primes used by the McDaniel tree: norm_num below 10^7, Lucas
# witnesses (lucas_primality) above.
# Used by: OddPerfect/McDaniel.lean (the pr_* lemmas; the file marks them private).
# Run from any folder: python3 gen2.py
# Runs gen.py first, then writes certs.lean to the current folder.
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import os
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen.py')).read().replace("print('\\n'.join(tree_txt)); print(sorted(primes_needed))",""))
def fac(n):
    d={};
    for p in pf(n):
        while n%p==0: d[p]=d.get(p,0)+1; n//=p
    return d
done=set(); certs=[]
def cert(p):
    if p in done: return
    done.add(p)
    if p<10**7:
        certs.append(f"theorem pr_{p} : Nat.Prime {p} := by norm_num\n"); return
    f=fac(p-1)
    for r in f: cert(r)
    a=2
    while not (pow(a,p-1,p)==1 and all(pow(a,(p-1)//r,p)!=1 for r in f)): a+=1
    flat=[r for r in sorted(f) for _ in range(f[r])]
    L=[f"theorem pr_{p} : Nat.Prime {p} := by",
       f"  apply lucas_primality {p} ({a} : ZMod {p})",
       f"  · change ({a} : ZMod {p}) ^ {p-1} = 1",
       "    reduce_mod_char",
       "  · intro q hq hd",
       f"    change q ∣ {' * '.join(map(str,flat))} at hd",
       "    simp only [hq.dvd_mul,"]
    L.append(",\n".join(f"      Nat.prime_dvd_prime_iff_eq hq pr_{r}" for r in sorted(f))+"] at hd")
    n=len(flat)
    pat="rfl"
    for i in range(n-1): pat="("+pat+" | rfl)"
    if n==1: L.append("    subst hd")
    else: L.append(f"    rcases hd with {pat}")
    for r in flat:
        L+= [f"    · change ({a} : ZMod {p}) ^ {(p-1)//r} ≠ 1","      reduce_mod_char","      decide"]
    if n==1: L=L[:-3]+[f"    change ({a} : ZMod {p}) ^ {(p-1)//flat[0]} ≠ 1","    reduce_mod_char","    decide"]
    certs.append("\n".join(L)+"\n")
for p in sorted(primes_needed): cert(p)
open('certs.lean','w').write("\n".join(certs))
print(len(certs))
