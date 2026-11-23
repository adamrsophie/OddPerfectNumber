# Certificate format of the two exception search

This describes the certificate written by `search.py` (`python3 -I search.py 2 100000 cert`),
published as `cert.jsonl.xz`, and the rules it uses. The Lean checker `OddPerfect.TwoExcEngine`
reads a term translated from it (`engine.py`, `gen.py`) and checks it in the kernel; the text
below is the specification the search and `check.py` follow, not a proof. The Rankin part of
the tail bound is stated separately in `TAIL_BOUND.md`.

## 1. The statement the tree refutes

N is an odd perfect number with special prime q: q ≡ 1 (mod 4) and α = v_q(N) ≡ 1 (mod 4).
Moreover v_3(N) = 2, and there are at most EMAX prime factors p of N, other than q, with
v_p(N) ≠ 2 (EMAX = 2 in the published certificate). These primes are the *exceptions*.
By Euler's theorem their exponents are even, so they are at least 4. Every other prime factor
of N (3 included) is a *square prime*, with exponent exactly 2. The tree claims that no such N
exists.

Notation: σ is the divisor sum and Φ_d is the d-th cyclotomic polynomial. We write
w(p) = v_p(σ(N)). Since σ(N) = 2N, w(p) = v_p(N) for every odd p, and σ(N) = ∏ σ(p^{v_p(N)}).
nextprime(y) is the least prime > y.

## 2. State

A state (JSON object `state`) has these fields.

* `x`: every prime p < x that is not a key of `S` or `F` does not divide N. In every record
  of the certificate x is a prime.
* `S`: the square primes found so far (3 is always a key). `S[p]` is a list of contributions
  `[source, w]`. Each one says that the component named by `source` contributes at least w to
  w(p).
* `F`: the free primes (q and the exceptions). `F[p] = [D, no3, kmin, exact]` means that the
  exponent k = v_p(N) satisfies D | k + 1 and k ≥ kmin, and 3 ∤ k + 1 when `no3` is true.
  For p = q also k + 1 ≡ 2 (mod 4); for an exception k is even and k ≥ 4. `exact` means k = kmin.
* `R[p]`: contributions to w(p) for a free prime p (same form as `S[p]`).
* `q`: the special prime if it is decided, else null. When it is null, q ≥ x and q ∉ `exq`.
* `exq`: primes that cannot be q. `search.py` never fills it, so it is empty in every record;
  the field is kept because the checkers read it.

The number of exceptions is |F| minus 1 if q is decided, else |F|. The *budget* of a square
prime is 2 (w(p) = 2). The budget of an exact free prime is kmin. Other free primes have no
budget.

The *least ratio* of a component is a lower bound for σ(p^k)/p^k:

* square p ≠ 3: (p²+p+1)/p²; the prime 3: 13/9;
* free p: σ(p^m)/p^m with m = min(kmin, KCAP), KCAP = 64.

The *upper ratio* is an upper bound:

* square p: the same value as the least ratio;
* free exact p with kmin ≤ KCAP: σ(p^kmin)/p^kmin;
* every other free p: p/(p−1).

lo and hi are the products of these ratios over all components of the state.

Sources:

* `["row", p]`: σ(p²) = p²+p+1 of a square prime p. For p = 3 the value is 13.
* `["cyc", d, p]`: Φ_d(p) for a free prime p.
* `["receipt", p, d, g]`: p | Φ_d(g), because d is the order of g modulo p (or d = p when
  g ≡ 1 mod p). See rule 8.
* `["decided", x]`: marks a prime decided present by a `decide` node. Its weight is 0.

  A weight 0 source is never written into a state or an item list. A decided prime starts with
  an empty contribution list.

* `["multi", list]`: several sources (not stored in states; the state lists them one by one).

## 3. Records (JSON lines)

Every line has an `id` and a `kind`. Line 0 is the header: `root` (id of the root record),
`EMAX`, `flags` (the flags of the run of `search.py`: `["cert"]` for the published certificate,
`["cert", "pade"]` for a run with the flag `pade`, see rule 6), `MHIT` = 10^30, `DMAX` = 300,
`KCAP` = 64. These three constants are fixed in `search.py`; a checker must still read them
from the header and not assume them. Everywhere below, "KCAP", "DMAX" and "MHIT" mean the
header values. Lines are not ordered. Children are referenced by id. A record whose `outcome` is
`leaf` carries `reason` and `proof`.

### 3.1 `apply` (closure step)

Fields:

* `action`: how this record differs from its parent (role of a prime, sender, split child,
  root).
* `state`: the state after the action and before the items.
* `values`: a list of `{src, factors, complete, value?}`. `value` (a decimal string) is present
  when the value is below 10^40.
* `items`: a list of `[prime, weight, source]`.

**Items.** The items are, in this order:

1. for a child of a `force` record: the parent's pending items for primes other than the forced
   prime, in the parent's order;
2. the flattened factors of `values`: for each value, `[p, e, src]` for each `[p, e]` of its
   `factors`;
3. for a child of a `receipt` record: the item `[p, 1, ["receipt", p, d, g]]`, added only when
   no item of step 2 is on the receiver p.

**Factors.** Every listed `[p, e]` has p prime and p^e ∥ value. If `complete` is true, the
product of the listed prime powers equals the value with its factors 2 removed. If it is false,
the list is a subset of the prime factors. A partial list is always sound, because it only
weakens the forcing. (`search.py` factors a value below 2^64 completely; from a value of at
least 2^64 it removes the known primes and the odd primes below 20000, and factors the cofactor
only when it is below 2^64.)

**Applying the items.** The checker applies the items in order to the state:

* an item on a key of `S` is appended to `S[p]`;
* an item on a key of `F` is appended to `R[p]`;
* an item on a prime p < x that is not a key of `S` or `F` is a contradiction (leaf
  `absentforced`);
* every other item (prime ≥ x and not a key) is *pending*.

Items are applied one at a time, in item order. The first item that produces outcome 1, 2 or
3 ends the record with that outcome, and later items are not applied. Outcomes 1 to 3 are
therefore decided by item order, not by priority. Outcomes 4 to 8 are checked, in this order,
only after all items are applied.

1. `leaf`, reason `cap3` (p = 3) or `cap` (another square prime): the contributions of a square
   prime sum to more than 2. Proof: `{prime, budget: 2, contributions}`. The list includes the
   offending item.
2. `leaf`, reason `capexact`: an exact free prime gets contributions summing to more than kmin.
   Proof: `{prime, budget: kmin, contributions}`.
3. `leaf`, reason `absentforced`. Proof: `{prime, source, x}`.
4. `leaf`, reason `abundant`: lo > 2 after all items. Proof: `{divisor, ratio}`. `divisor` lists
   (prime, exponent): exponent 2 for every square prime (3 included) and m = min(kmin, KCAP) for
   every free prime. `ratio` is the exact fraction ∏ σ(p^e)/p^e over this list. It equals lo
   and must exceed 2. Each listed p^e divides N, because k ≥ kmin ≥ m.
5. `leaf`, reason `landedL`: rule 9 L fails. Proof: `{exceptions, x}`.
6. If items are pending: f is the least pending prime, and its contributions are the pending
   items on f (in order).
   * If f has no admissible role (section 4): `leaf` `noroles`, proof `{prime: f}`.
   * Otherwise `outcome` `force` with `forced` = f, `roles` (which role classes are admissible)
     and `children`: one `apply` per admissible role of f. In each child state f is a key with
     exactly these contributions (in `S[f]` or in `R[f]`). The child's x is the parent's x.
7. If no item is pending, q is decided and the number of exceptions equals EMAX: let p be the
   least prime ≡ 2 (mod 3) that is a key of `S` or `F` and has no contribution (sum 0). If p
   exists, the record is a receipt record (rule 8):
   * `receiver` = p;
   * `senders_infeasible`: a map from each infeasible free prime g ≠ p to `{d, infeasible}`;
   * `children`: one `apply` per feasible free prime g ≠ p, with action
     `{role: sender, receiver: p, sender: g, d}`.

   Every free prime g ≠ p is in exactly one of the two lists.

   **Sender child state**, with F[g] = [D, no3, kmin, exact] and Dn = lcm(D, d):
   * Non-exact g: F[g] becomes [Dn, no3, n−1, false], where n is the least allowed value of
     k+1 (section 3.4) with n ≥ kmin + 1 and Dn | n. The new values are Φ_{d'}(g) for
     d' | Dn, d' ∤ D, d' ≤ DMAX.
   * Feasible exact g (Dn | kmin+1): F[g] is unchanged, and there are no new values.

   The child's items are the new value items, followed by the receipt item when needed
   (step 3 of Items). The child keeps x and next_x. If there is no child, the record
   is a `leaf` with reason `receipt` and proof `{receiver: p, senders: senders_infeasible}`.
   Otherwise the `outcome` is `receipt`.
8. Otherwise `outcome` `closed`, with `next_x` and one child, a `decide`, `check` or `split`
   record. The child's state is this state after the items, with x replaced by `next_x`.

   **next_x rule.** Every prime p with state.x ≤ p < next_x must be a key of `S` or `F` after
   the items. In the certificate, next_x is one of two values. It is state.x for the root and
   for the children of a `split`. It is nextprime(x0) for the descendants of the child of a
   `decide` record with prime x0; their state.x is x0, which is a key. `force` and `receipt`
   children inherit both values from their parent.

### 3.2 `decide`

Fields: `x`, `state` (or null), `prev`, `roles`, `children`, `absent`.

**Effective state E of the record.**

* If `state` is not null, E = `state`.
* If `state` is null, E is the effective state of record `prev` with x replaced by
  nextprime(prev.x).

The state, its x included, is the effective state before the scan. A record is the absent
child of its `prev`; the first record of a chain is the child of a `closed`.

**The record's x.** The record's `x` is the least prime ≥ E.x that is not a key of `S` or `F`.
All primes in [E.x, x) are keys, so "every unlisted prime < x is absent" still holds.

**Children.** The `children` are the `apply` records, one per admissible role of x (section 4).
Each has weight 0, no contributions, x as the decided prime, and state.x equal to the record's
x. `absent` is the id of the record for "x does not divide N". Its effective state is E with
x := nextprime(x).

A checker must verify three things. The children are exactly the admissible roles of x. The
absent record exists and has `prev` equal to this id. Every prime is decided this way; there
are no ranges.

### 3.3 `check` (leaf at the end of a run of absent decisions)

`check` uses the same `state`/`prev`/`x` convention as `decide`. Its reason is `deficient`
(rule 6), `landedL` (rule 9 L at this x; proof `{exceptions, x}`) or `OPEN` (the scan passed
the LIMIT argument of `search.py`). The published certificate has no `OPEN` leaf.

The state used by the leaf is E with x replaced by the record's x. The tail bound uses this x;
H = hi is computed from this state.

### 3.4 `split`

Fields: `state`, `prime` p (a free, non-exact prime with kmin < KCAP), `kmin`, and two
`children`.

* `exact`: k = kmin. F[p] becomes [kmin+1, no3, kmin, true]. The new values are the Φ_d(p) for
  d | kmin+1, d ∤ D, d ≤ DMAX.
* `atleast`: F[p] becomes [D, no3, n−1, false], where n is the least allowed value of k+1 with
  n ≥ kmin + 2.

This is exhaustive by definition of the allowed set: n allowed means D | n, 3 ∤ n if no3, and
n ≡ 2 (mod 4) for q, or n odd and n ≥ 5 for an exception. The split is made only when hi > 2.
Its children are `apply` records with next_x = state.x.

## 4. Roles of a prime f that must divide N (exhaustive list)

* **square**, always. Its value is `["row", f]`.
* **q**, if q is not decided, f ≡ 1 (mod 4), f ∉ exq, f ≠ 5 and f ≢ 8 (mod 9) (rule 9).
  * For f ≡ 1 (mod 3) there are two classes: `q0` (D = 2, no3 true, kmin 1) and `q3` (D = 6,
    no3 false, kmin 5). Either 3 ∤ α+1, or 3 | α+1 and then 6 | α+1, because α+1 is even.
  * For f ≡ 2 (mod 3) there is one class, `q` (D = 2, no3 true, kmin 1); no3 holds by rule 9.
* **exception**, if there are fewer than EMAX exceptions.
  * For f ≡ 1 (mod 3) there are two classes: `e` (D = 1, no3 true, kmin 4) and `e3` (D = 3,
    no3 false, kmin 8).
  * For f ≡ 2 (mod 3) there is one class, `e` (D = 1, no3 false, kmin 4).

The values of a free class are Φ_d(f) for d | D, d > 1, d ≤ DMAX. The `roles` field records
`{square, q_allowed, exc_allowed}`; `square` is always true.

## 5. Rules and their justification

1. **Rows.** If p is a square prime, then σ(p²) = p²+p+1 divides σ(N) = 2N. So its odd prime
   factors divide N, with the stated multiplicity counted in w. Factor sizes depend on p mod 3:
   * p ≡ 1 (mod 3): 3 ∥ p²+p+1;
   * p ≡ 2 (mod 3): 3 ∤ p²+p+1.

   Every other prime factor of the row is ≡ 1 (mod 3).
2. **Budgets.** w(p) = v_p(2N). This is 2 for a square prime (3 included) and k for a free
   prime of exponent k. Contributions are lower bounds of v_p(σ(component)), and the components
   are distinct prime powers of N. So their sum is at most w(p).
3. **Free exponent data.** If D | k+1, then σ(p^{D−1}) | σ(p^k) and
   σ(p^{D−1}) = ∏_{d | D, d > 1} Φ_d(p). So each Φ_d(p) contributes.

   The 3-part of σ(p^k) depends on p mod 3:
   * p ≡ 1 (mod 3): v_3(σ(p^k)) = v_3(k+1);
   * p ≡ 2 (mod 3) and k even: 3 ∤ σ(p^k).

   Hence the classes q0 and e send nothing to 3, and q3 and e3 send at least 1 through Φ_3.
4. **q row.** Since α is odd, q + 1 = Φ_2(q) divides σ(q^α) (D = 2).
5. **Abundancy.** σ(N)/N = 2 is the product of the component ratios. Each ratio lies in
   [least ratio, upper ratio), because σ(p^k)/p^k increases with k and is below p/(p−1). A
   divisor d of N with σ(d)/d > 2 makes N abundant (leaf `abundant`).
6. **Tail bound (leaf `deficient`).** Fix the leaf's x. Every prime t ≥ x dividing N that is
   not a key of `S` or `F` is one of the following.
   * (a) q, if q is undecided: at most 1 such prime, ratio < x/(x−1).
   * (b) A new exception: at most b = EMAX − #exceptions, ratio < x/(x−1).
   * (c) A square t ≡ 1 (mod 3). Its row sends 1 to 3, so there are at most
     c = 2 − (sum of S[3]). Ratio ≤ (x²+x+1)/x².
   * (d) A square t ≡ 2 (mod 3) whose row contains a prime of A or an exact free prime
     ≡ 1 (mod 3). Here A is the set of square primes ≡ 1 (mod 3), known or new. Each such row
     uses budget, so there are at most
     d = Σ_{p ∈ A known} (2 − w_known(p)) + 2c + Σ_{exact free g ≡ 1 mod 3} max(0, kmin − w_known(g)).
     Ratio ≤ (x²+x+1)/x².
   * (e) A square t ≡ 2 (mod 3) whose row n_t = t²+t+1 is a product of powers of the non-exact
     free primes ≡ 1 (mod 3) (the set K, all known) and of the undecided free primes. The
     undecided free primes form a fixed set P of at most u = a + b primes, each ≥ x, where a is
     1 if q is undecided and 0 otherwise. This is exhaustive: rows of t ≡ 2 (mod 3) are prime
     to 3, and their prime factors are ≡ 1 (mod 3).

   **Hits.** The *generated values* are all n = ∏_{g ∈ K} g^{e_g} with n < MHIT; there are
   `generated` of them. For each generated n with 4n − 3 = (2t+1)², t is its *candidate*. It is
   a *hit* exactly when t is an odd prime, t ≡ 2 (mod 3), t ≥ x, and t is not a key of `S` or
   `F`. The proof lists the hits as `hits` = [[t, n], ...], sorted.

   Every other generated value has a reason in `nonhits` = [[n, t, reason, witness?], ...],
   sorted by n. A checker derives this list as follows; the first reason that applies is
   recorded.
   * 4n − 3 not a square: not listed; the checker recomputes these.
   * `even`: t is even. This includes t = 0 (n = 1) and t = 2 (n = 7).
   * `mod3`: t is odd and t ≢ 2 (mod 3).
   * `composite`: t is not prime; the witness is the least prime factor of t.
   * `below_x`: t < x.
   * `listed`: t is a key of `S` or `F`.

   Each listed entry satisfies 4n − 3 = (2t+1)². Every generated n with 4n − 3 a square is in
   exactly one of `hits` and `nonhits`.

   Size: 714,048 generated values over the 707 deficient leaves of the certificate, at most
   4,369 in one leaf, and 2,341 square cases in total (hits plus nonhits). In general a leaf has
   at most ∏_{g ∈ K} (⌊log_g MHIT⌋ + 1) generated values.

   Each hit is multiplied in exactly as n/t² (its ratio if t divides N, and n/t² > 1 anyway).
   No row of type (e) with only K factors and n < MHIT escapes the hits: its t would be an
   undecided odd prime ≡ 2 (mod 3) ≥ x.

   The remaining rows of type (e) form the set T of `TAIL_BOUND.md`. Each has a factor
   from P, or n_t ≥ MHIT. That statement bounds ∏_{t∈T} n_t/t² ≤ 1/(1 − S) when S < 1 and
   ∏_{t∈T} n_t/t² ≤ (S² + 4S + 6)/(6 − 2S) when S < 3, with S = ((x+1)/x)² · R and
   R = m_L·G·((1 − α_x)^{−u} − 1) + m_M·G, where G = ∏_{g∈K} 1/(1 − α_g). With

   U0 = H · (x/(x−1))^{a+b+extra_ab} · ((x²+x+1)/x²)^{c+d+extra_cd} · ∏_hits n/t²

   and H = hi of the leaf's state, the leaf requires U < 2 for one of two paths, tested in this
   order: the old path, S < 1 and U = U0/(1 − S); or else the Padé path, S < 3 and
   U = U0 · (S² + 4S + 6)/(6 − 2S). The second factor is at most the first for 0 ≤ S < 1, so the
   Padé path accepts every leaf the old path accepts and some more. The published certificate
   is written without the flag `pade`, and `search.py` then closes a leaf only by the old path;
   with the flag it also closes a leaf by the Padé path and writes that U. The checkers try
   both paths whatever the flags. `extra_ab` and `extra_cd` are nonnegative integers that
   only weaken the bound; `search.py` always writes 0 for both.

   If K is empty and u = 0, the proof has S = "0" and no `rankin`, `generated` or `nonhits`
   (no row of type (e) exists). The certificate has no such leaf.

   Rational witnesses (field `rankin`, `mode` = `theta`): k ∈
   {3,4,5,6,8,10,12,16,24}, chosen to minimize R.
   * α_g = 10^6/r with r = ⌊(g·10^{6k})^{1/k}⌋, so α_g^k·g ≥ 1. The proof stores [α_g, r, 10^6].
   * α_x is defined the same way.
   * m_L = (⌊L^{1/k}⌋ + 1)/⌊√L⌋ with L = x²+x+1, so m_L^{2k}·L^{k−2} ≥ 1.
   * m_M is defined the same way with M = max(L, MHIT).

   Proof fields: `x`, `H`, `a`, `b`, `c`, `d`, `d_items` (`A_capacity`, `future_A` = 2c,
   `exact_receivers`), `extra_ab`, `extra_cd`, `K`, `u`, `hits`, `generated`, `nonhits`,
   `rankin` = {mode, k, theta, alpha, alpha_x, G, mL, mM, L, M, R}, `S`, `U`. All fractions are
   "num/den" strings.
7. **Splitting.** The allowed exponents of a free prime form a set, so "k = kmin" or "k ≥ next
   allowed" is exhaustive. An exact exponent gives a budget (rule 2).
8. **Receipt.** A present prime p ≡ 2 (mod 3) divides N, so w(p) ≥ 1. Only w(p) > 0 is used.

   The other components cannot supply p. Rows of squares and σ(3²) = 13 contain only 3 and
   primes ≡ 1 (mod 3), and σ(p^{v_p}) is prime to p. So some free g ≠ p has p | σ(g^k). For a
   prime p ≠ g, p | σ(g^k) iff d | k+1, where d = ord_p(g) if g ≢ 1 (mod p) and d = p
   otherwise.

   The rule is applied only when all free primes are known: q decided and exceptions complete.
   The child for sender g raises D(g) to lcm(D, d) and adds the new Φ values.

   **When g is infeasible.**
   * g exact: (kmin + 1) is not divisible by lcm(D, d).
   * g = q: 4 | lcm(D, d).
   * g an exception: lcm(D, d) is even.
   * no3 and 3 | lcm(D, d).
   * No allowed exponent within 64 steps of D. This never occurs in the certificate.
9. **Landed facts.** The search uses three theorems of the library.
   * q ≠ 5 (`two_exceptions_five_three_ne_two`).
   * q ≢ 8 (mod 9), and for q ≡ 2 (mod 3), 3 ∤ (α+1)/2
     (`two_exceptions_three_ne_two_of_nine_dvd`, `_of_mod_nine`).
   * **Rule L** (`false_of_three_sq_of_index_three`): some exception lies in
     L = {7, 13, 19, 31, 61, 97, 127, 331}, is not q, and has 3 ∤ k+1.

   A state passes rule L if some listed exception in L has class e (no3 true; all primes of L
   are ≡ 1 mod 3). Leaf `landedL` holds exactly when no listed exception in L has class e and
   one of the following is true:
   * the number of exceptions equals EMAX; or
   * every prime of L is < x or a key of `S` or `F`.

## 6. What a checker verifies

* **Structure.** Every referenced id exists and the tree from `root` has no open leaf.
* **Values.** Recompute each value from `src`. Every listed [p, e] has p prime (primality to be
  certified separately) and p^e ∥ value. If `complete`, the product equals the value with its 2s
  removed. Every flattened factor is among the items.
* **Apply.** Applying the items to the state gives the recorded outcome (in the order of 3.1),
  and the force children carry the other pending items first.
* **Force and decide.** The children are exactly the admissible roles of section 4. Each child
  state is the parent state with the role added.
* **Closed.** The next_x rule of 3.1 holds.
* **Decide and check x.** The record's x is the least prime ≥ E.x that is not a key, as in 3.2.
* **Receipt.** The senders plus the infeasible ones are all the free primes ≠ p. d is the order
  (or p). The child's F[g] is as stated, and some child item is on p. Infeasibility follows from
  rule 8.
* **Deficient.** Recompute H, a, b, c, d, K and u from the state. Enumerate the generated
  values, check `generated`, the hits and each nonhit reason. Check the rational witnesses, R,
  and U < 2 exactly by the old path (S < 1) or the Padé path (S < 3) of rule 6.
* **Abundant.** Each divisor exponent is 2 for a square prime and between 1 and kmin for a free
  prime. The ratio of the divisor equals the stored ratio, which equals lo and exceeds 2.

## 7. Primality

Counts for the certificate:

* Primes in `factors`: 1,053 distinct, the largest 1680929146648258321 (about 1.68·10^18), all
  below 2^64. Their primality is needed.
* Decided x (`decide`/`check` records): 366 distinct, all ≤ 2,521. Their primality and the
  compositeness of the integers skipped between them are needed; both are trivial at this
  size. The search's own count of 1,195 "primes used" is the union of these two sets.
* Hit primes t: 7 distinct, the largest 14,387. Their primality is not needed for soundness,
  because a hit's factor n/t² > 1 is multiplied in whatever t is. Only the nonhit reasons need
  proof: parity, residue mod 3, a factor witness, t < x, or listed.

The Lean checker does not read the stored factor lists: it reads the items of each record and
asks a primality oracle (`prTwo`, a verified table below 4096 and a Pratt certificate above)
about the primes it needs; `engine.py` lists them (426 primes).

## 8. Checkers in this folder

* `check.py`: an independent recheck written from an earlier text of this format; see its
  header for what it checks and what it does not.
* `engine.py`: the translator to the Lean term and an exact Python mirror of the Lean checker.
  The translator sorts the composite witnesses of a leaf and both read the first pair for a
  candidate t, so of several witnesses for one t the smallest must be a divisor of t strictly between 1
  and t.
