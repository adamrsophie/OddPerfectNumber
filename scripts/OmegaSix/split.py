# Untrusted helper script for the OddPerfect Lean library.
# Cuts the kernel run of search_five in OddPerfect/OmegaSix.lean along the prime windows of the
# search (the theorem solve_of_window) into checks of at most CAP = 1200 search nodes of the
# mirror mirror.py, and prints the Lean lemmas five, five_5, five_5_17 and their window checks.
# Used by: OddPerfect/OmegaSix.lean (the private theorems five* between win_one and search_four).
# Run: python3 split.py > split.lean (in the folder that holds mirror.py)
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: mirror.py is read from the folder of this script; output goes to standard output.
# License: GPL 3, same as the repository.
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
sys.argv = ['mirror.py', '10', '4', '30']
src = open(os.path.join(here, 'mirror.py')).read()
exec(src[:src.rindex('print(solve(FUEL')])
CAP = 1200
def window(known,j,m):
    Ln=Ld=Un=Ud=1
    for (p,k,ex) in known:
        g=geom(p,k);Ln*=g;Ld*=p**k
        if ex: Un*=g;Ud*=p**k
        else: Un*=p;Ud*=p-1
    ps=[2]+[p for (p,_,_) in known]
    cs=[c for c in [strip(geom(p,k),ps) for (p,k,ex) in known if ex] if c!=1]
    allex=all(e[2] for e in known)
    bounds=[]
    if Un<2*Ud:
        bU=bsearch(Un,Ud,j,m,bhi(Un,Ud,j,m),200)
        if not cond(Un,Ud,j,bU+1): bounds.append(bU)
    bounds+=cs
    lo=m+1
    if j==1 and Ln<2*Ld:
        D=2*Ld-Ln; lo=max(lo,(Ln+D-1)//D)
    assert j!=0 and bounds and (minB(bounds)<=lo+W or allex or j>=2)
    return lo, minB(bounds)+1-lo
def cnt(known,j,m,fuel):
    st['nodes']=0; r=solve(fuel,known,j,m); assert r; return st['nodes']
def lit(l): return '[' + ', '.join('⟨%d, %d, %s⟩' % (p,k,'true' if ex else 'false') for p,k,ex in l) + ']'
out=[]; nchk=[0]
def P(f,l,j):  # the window predicate, written as in solve_of_window
    return 'isPrimeQ q = true → solve %d (%s ++ [⟨q, kmin q, false⟩]) (%d - 1) q = true' % (f,lit(l),j)
def emit_state(name,known,j,m,fuel):
    """Lemma `name : solve fuel known j m = true` through its window."""
    a,n=window(known,j,m)
    segs=[]  # (start,len,kind,child) kind 'chk' or 'sub'
    cur=None; cs=0
    for q in range(a,a+n):
        c=cnt(known+[(q,kmin(q),False)],j-1,q,fuel-1) if isPrimeQ(q) else 0
        if c>CAP:
            if cur: segs.append(cur); cur=None; cs=0
            segs.append([q,1,'sub',c])
            continue
        if cur and cs+c>CAP: segs.append(cur); cur=None; cs=0
        if not cur: cur=[q,0,'chk',0]
        cur[1]+=1; cur[3]+=c; cs+=c
    if cur: segs.append(cur)
    hyps=[]
    for s,k,kind,c in segs:
        if kind=='sub':
            sub='%s_%d' % (name,s)
            emit_state(sub,known+[(s,kmin(s),False)],j-1,s,fuel-1)
            hyps.append('(win_one (b := %d) %s)' % (s,sub))
        else:
            nchk[0]+=1; cn='%s_w%d' % (name,s)
            out.append('set_option maxRecDepth 100000 in')
            out.append('/-- Window `[%d, %d)` (mirror nodes: %d). -/' % (s,s+k,c))
            out.append('private theorem %s : ∀ q ∈ List.range\' %d %d,\n    %s := by' % (cn,s,k,P(fuel-1,known,j)))
            out.append('  decide +kernel')
            out.append('')
            hyps.append(cn)
    # combine right to left
    def comb(i):
        s,k=segs[i][0],segs[i][1]
        if i==len(segs)-1: return hyps[i], k
        rest,rk=comb(i+1)
        return '(win_split %s\n      %s rfl rfl)' % (hyps[i],rest), k+rk
    body,tot=comb(0); assert tot==n
    out.append('/-- The state `%s` with `%d` further primes above `%d`, through its window. -/' % (lit(known),j,m))
    out.append('private theorem %s : solve %d %s %d %d = true :=' % (name,fuel,lit(known),j,m))
    out.append('  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)')
    out.append('    %s' % body)
    out.append('')
emit_state('five',[(3,2,False)],4,3,30)
print('\n'.join(out))
print('-- checks', nchk[0], file=sys.stderr)
