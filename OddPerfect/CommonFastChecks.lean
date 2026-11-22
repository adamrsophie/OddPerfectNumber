import OddPerfect.CommonFiveSeven

/-!
# Common exponent families: cheaper kernel checks for the forcing tables

Three checks of the forcing table checkers of `OddPerfect.CommonFiveSeven`, each with its
soundness lemma, that the kernel evaluates with much less work:

* primality by trial division over a fixed list of odd primes (`FamInst.tdl`), with a one
  time check that the list contains every odd prime up to its last element
  (`FamInst.cover`); `FamInst.oddP` lists the odd primes up to `4201`, which is enough for
  every number below `4201 ^ 2`;
* the row divisibility check `FamInst.rowChk` read through a node list given in parts of
  equal length (`FamInst.rowChkP`), so that a node is found in two short list walks;
* a reach check with a whole set of source nodes blocked at once (`FamInst.reachS`), which
  implies the reach check `FamInst.reach` for every single blocked node of the set.
-/

namespace OddPerfect

namespace FamInst

open OddPerfect.EqChain (gm)
open OddPerfect.CommonChain (maskOf testBit_maskOf)

/-! ## Trial division by a list of odd primes -/

/-- `tdl q L` walks the list `L`: it returns `true` at the first element `p` with
`q < p * p` when no earlier element divides `q`, and `false` at the end of the list. -/
def tdl (q : ℕ) : List ℕ → Bool
  | [] => false
  | p :: ps => Nat.blt q (p * p) || (!(Nat.beq (q % p) 0) && tdl q ps)

/-- Soundness of `tdl` on an increasing list: the walk stops at some element `a` with
`q < a * a`, and no element `p` with `p * p ≤ q` divides `q`. -/
theorem tdl_sound {q : ℕ} : ∀ {L : List ℕ}, L.Pairwise (· < ·) → tdl q L = true →
    (∃ a ∈ L, q < a * a) ∧ ∀ p ∈ L, p * p ≤ q → q % p ≠ 0
  | [], _, h => by simp [tdl] at h
  | a :: L, hs, h => by
    rw [List.pairwise_cons] at hs
    simp only [tdl, Bool.or_eq_true, Nat.blt_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with h | ⟨h1, h2⟩
    · refine ⟨⟨a, List.mem_cons_self, h⟩, fun p hp hpq => absurd hpq ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · omega
      · have := hs.1 p hp
        have : a * a < p * p := Nat.mul_self_lt_mul_self this
        omega
    · obtain ⟨⟨b, hb, hqb⟩, ih⟩ := tdl_sound hs.2 h2
      refine ⟨⟨b, List.mem_cons_of_mem _ hb, hqb⟩, fun p hp hpq => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · intro h0
        rw [h0] at h1
        exact absurd h1 (by decide)
      · exact ih p hp hpq

/-- A list is strictly increasing: each element is below the next one. -/
def incr : List ℕ → Bool
  | a :: b :: l => Nat.blt a b && incr (b :: l)
  | _ => true

/-- Soundness of `incr`. -/
theorem pairwise_of_incr : ∀ {L : List ℕ}, incr L = true → L.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [incr, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := pairwise_of_incr h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons ih hx)

/-- `m` has a divisor `d` with `2 ≤ d < m`. -/
def hasDiv (m : ℕ) : Bool := (List.range' 2 (m - 2)).any fun d => Nat.beq (m % d) 0

/-- A number with a divisor `d` with `2 ≤ d < m` is not prime. -/
theorem not_prime_of_hasDiv {m : ℕ} (h : hasDiv m = true) : ¬ m.Prime := by
  simp only [hasDiv, List.any_eq_true, List.mem_range'_1, Nat.beq_eq] at h
  obtain ⟨d, ⟨hd2, hdm⟩, hmd⟩ := h
  intro hp
  rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmd) with h1 | h1 <;> omega

/-- `cover f m L` checks with fuel `f`, for every `x ≥ m` up to the last element of `L`, that
`x` is the next element of `L` or has a proper divisor below the next element. -/
def cover : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | f + 1, m, a :: L =>
    (Nat.beq m a && cover f (m + 1) L) || (Nat.blt m a && hasDiv m && cover f (m + 1) (a :: L))

/-- Soundness of `cover`: every prime `p ≥ m` that is at most some element of `L` is in
`L`. -/
theorem cover_sound : ∀ (f m : ℕ) (L : List ℕ), cover f m L = true →
    ∀ p, p.Prime → m ≤ p → (∃ a ∈ L, p ≤ a) → p ∈ L
  | 0, _, _, h => by simp [cover] at h
  | _ + 1, _, [], _ => fun _ _ _ ⟨_, ha, _⟩ => absurd ha List.not_mem_nil
  | f + 1, m, a :: L, h => by
    intro p hp hmp ⟨b, hb, hpb⟩
    simp only [cover, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
    rcases h with ⟨rfl, h⟩ | ⟨⟨hma, hd⟩, h⟩
    · rcases Nat.eq_or_lt_of_le hmp with rfl | hlt
      · exact List.mem_cons_self
      · rcases List.mem_cons.1 hb with rfl | hb
        · omega
        · exact List.mem_cons_of_mem _ (cover_sound f _ L h p hp hlt ⟨b, hb, hpb⟩)
    · rcases Nat.eq_or_lt_of_le hmp with rfl | hlt
      · exact absurd hp (not_prime_of_hasDiv hd)
      · exact cover_sound f _ (a :: L) h p hp hlt ⟨b, hb, hpb⟩

/-- Primality by trial division over the list `L`: `q` is odd, at least `3`, and `tdl q L`
holds. -/
def fastPrime (L : List ℕ) (q : ℕ) : Bool := Nat.beq (q % 2) 1 && Nat.blt 2 q && tdl q L

/-- Soundness of `fastPrime` for an increasing list that contains every odd prime up to its
elements. -/
theorem fastPrime_sound {L : List ℕ} {f : ℕ} (hi : incr L = true) (hc : cover f 3 L = true)
    {q : ℕ} (h : fastPrime L q = true) : q.Prime := by
  simp only [fastPrime, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨hodd, h2⟩, ht⟩ := h
  obtain ⟨⟨a, ha, hqa⟩, hnd⟩ := tdl_sound (pairwise_of_incr hi) ht
  by_contra hq
  have hm := Nat.minFac_prime (show q ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (by omega) hq
  have hdvd := Nat.minFac_dvd q
  rw [pow_two] at hsq
  have hm3 : 3 ≤ q.minFac := by
    rcases hm.eq_two_or_odd with h' | h'
    · rw [h'] at hdvd
      have := Nat.mod_eq_zero_of_dvd hdvd
      omega
    · have := hm.two_le
      omega
  have hlt : q.minFac < a := Nat.mul_self_lt_mul_self_iff.mp (by omega)
  have hmem := cover_sound f 3 L hc _ hm hm3 ⟨a, ha, hlt.le⟩
  exact hnd _ hmem hsq (Nat.mod_eq_zero_of_dvd hdvd)

/-- The odd primes up to `4201`. -/
def oddP : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
    431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
    557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797,
    809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
    937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039,
    1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151,
    1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259,
    1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373,
    1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483,
    1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583,
    1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697,
    1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811,
    1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933,
    1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053,
    2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153,
    2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287,
    2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389,
    2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531,
    2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659,
    2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741,
    2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857,
    2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999,
    3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121,
    3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257,
    3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371,
    3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511,
    3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613,
    3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727,
    3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853,
    3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989,
    4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099,
    4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201]

/-- `oddP` is increasing. -/
theorem oddP_incr : incr oddP = true := by decide +kernel

/-- `oddP` contains every odd prime up to `4201`. -/
theorem oddP_cover : cover 5000 3 oddP = true := by decide +kernel

/-- Primality by trial division over `oddP`, for odd numbers below `4201 ^ 2`. -/
theorem prime_of_fastPrime {q : ℕ} (h : fastPrime oddP q = true) : q.Prime :=
  fastPrime_sound oddP_incr oddP_cover h

/-! ## Row checks through a node list in parts -/

/-- Element `j` of the flattening of `parts`, read as element `j % K` of part `j / K`. -/
def ptD (K : ℕ) (parts : List (List ℕ)) (j : ℕ) : ℕ := (parts.getD (j / K) []).getD (j % K) 0

/-- Every part has length `K`, except the last one, which has length at most `K`. -/
def lensOK (K : ℕ) : List (List ℕ) → Bool
  | [] => true
  | [c] => Nat.ble c.length K
  | c :: d :: cs => Nat.beq c.length K && lensOK K (d :: cs)

/-- Reading the flattening of parts of length `K`. -/
theorem getD_flatten {K : ℕ} (hK : 0 < K) : ∀ (parts : List (List ℕ)), lensOK K parts = true →
    ∀ j, parts.flatten.getD j 0 = ptD K parts j
  | [], _, j => by simp [ptD]
  | [c], h, j => by
    simp only [lensOK, Nat.ble_eq] at h
    rcases Nat.lt_or_ge j K with hj | hj
    · simp [ptD, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
    · have h1 : 1 ≤ j / K := (Nat.one_le_div_iff hK).mpr hj
      obtain ⟨k, hk⟩ : ∃ k, j / K = k + 1 := ⟨j / K - 1, by omega⟩
      simp only [ptD, hk, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.getD_cons_succ, List.getD_nil]
      rw [List.getD_eq_default _ _ (by omega)]
  | c :: d :: cs, h, j => by
    simp only [lensOK, Bool.and_eq_true, Nat.beq_eq] at h
    have ih := getD_flatten hK (d :: cs) h.2
    rw [List.flatten_cons]
    rcases Nat.lt_or_ge j K with hj | hj
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
      simp [ptD, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
    · obtain ⟨x, rfl⟩ : ∃ x, j = x + K := ⟨j - K, by omega⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        ← List.getD_eq_getElem?_getD, h.1, Nat.add_sub_cancel, ih x]
      simp only [ptD, Nat.add_div_right x hK, Nat.add_mod_right, List.getD_cons_succ]

/-- The row check `rowChk` with nodes read from parts of length `K`. -/
def rowChkP (K : ℕ) (parts : List (List ℕ)) (d : ℕ) (e : ℕ × List ℕ) : Bool :=
  e.2.all fun j => gm e.1 (ptD K parts j) d == 0

/-- `rowChkP` agrees with `rowChk` on the flattened node list. -/
theorem rowChk_of_rowChkP {K d : ℕ} {nodes : List ℕ} {parts : List (List ℕ)} (hK : 0 < K)
    (hn : nodes = parts.flatten) (hl : lensOK K parts = true) {e : ℕ × List ℕ}
    (h : rowChkP K parts d e = true) : rowChk d nodes e = true := by
  subst hn
  simpa only [rowChk, rowChkP, getD_flatten hK parts hl] using h

/-! ## Reach checks with a set of source nodes blocked -/

/-- One in order pass over the rows, as `fpass`, where row `i` is skipped when its source
node `x` satisfies `bl x`. -/
def fpassS (bl : ℕ → Bool) : ℕ → List ℕ → List (List ℕ) → ℕ → ℕ
  | _, [], _, M => M
  | _, _ :: _, [], M => M
  | i, x :: xs, row :: rs, M =>
    if M.testBit i && !bl x then fpassS bl (i + 1) xs rs (M ||| maskOf row)
    else fpassS bl (i + 1) xs rs M

/-- At most `n` passes, as `fiter`, with the blocked set `bl`. -/
def fiterS (bl : ℕ → Bool) (nodes : List ℕ) (rows : List (List ℕ)) (tm : ℕ) : ℕ → ℕ → ℕ
  | 0, M => M
  | n + 1, M =>
    if M &&& tm == tm then M else fiterS bl nodes rows tm n (fpassS bl 0 nodes rows M)

/-- The reach check `reach` with every source node `x` with `bl x` blocked. -/
def reachS (nodes : List ℕ) (rows : List (List ℕ)) (ns tm passes : ℕ) (bl : ℕ → Bool) :
    Bool :=
  fiterS bl nodes rows tm passes (2 ^ ns - 1) &&& tm == tm

/-- `X &&& tm = tm` means that every bit of `tm` is set in `X`. -/
theorem land_eq_iff {X tm : ℕ} : X &&& tm = tm ↔ ∀ k, tm.testBit k = true → X.testBit k = true := by
  constructor
  · intro h k hk
    rw [← h, Nat.testBit_land, Bool.and_eq_true] at hk
    exact hk.1
  · intro h
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_land]
    cases hk : tm.testBit k
    · simp
    · simp [h k hk]

/-- A pass with a blocked set gives a submask of a pass with one blocked node of the set, from
a submask. -/
theorem fpassS_sub {bl : ℕ → Bool} {b : ℕ} (hb : bl b = true) :
    ∀ (i : ℕ) (xs : List ℕ) (rs : List (List ℕ)) (M M' : ℕ),
      (∀ k, M.testBit k = true → M'.testBit k = true) →
      ∀ k, (fpassS bl i xs rs M).testBit k = true → (fpass b i xs rs M').testBit k = true
  | _, [], _, _, _, h => by simpa [fpassS, fpass] using h
  | _, _ :: _, [], _, _, h => by simpa [fpassS, fpass] using h
  | i, x :: xs, row :: rs, M, M', h => by
    simp only [fpassS, fpass]
    have hor : ∀ A B : ℕ, (∀ k, A.testBit k = true → B.testBit k = true) →
        ∀ k, (A ||| maskOf row).testBit k = true → (B ||| maskOf row).testBit k = true := by
      intro A B hAB k hk
      rw [Nat.testBit_lor, Bool.or_eq_true] at hk ⊢
      exact hk.imp (hAB k) id
    split_ifs with h1 h2 h2
    · exact fpassS_sub hb (i + 1) xs rs _ _ (hor M M' h)
    · exfalso
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and] at h2
      exact h2 (h i h1.1) (by rintro rfl; rw [hb] at h1; exact absurd h1.2 (by decide))
    · refine fpassS_sub hb (i + 1) xs rs _ _ fun k hk => ?_
      rw [Nat.testBit_lor, h k hk, Bool.true_or]
    · exact fpassS_sub hb (i + 1) xs rs _ _ h

/-- The passes with a blocked set reach the target mask only if the passes with one blocked
node of the set do, from a submask. -/
theorem fiterS_sub {bl : ℕ → Bool} {b : ℕ} (hb : bl b = true) {nodes : List ℕ}
    {rows : List (List ℕ)} {tm : ℕ} : ∀ (n M M' : ℕ),
      (∀ k, M.testBit k = true → M'.testBit k = true) →
      fiterS bl nodes rows tm n M &&& tm = tm → fiter b nodes rows tm n M' &&& tm = tm
  | 0, M, M', h, hS => by
    simp only [fiterS, fiter] at hS ⊢
    exact land_eq_iff.mpr fun k hk => h k (land_eq_iff.mp hS k hk)
  | n + 1, M, M', h, hS => by
    rw [fiter]
    by_cases h2 : (M' &&& tm == tm) = true
    · rw [if_pos h2]
      simpa using h2
    · rw [if_neg h2]
      simp only [fiterS] at hS
      by_cases h1 : (M &&& tm == tm) = true
      · have : M' &&& tm = tm :=
          land_eq_iff.mpr fun k hk => h k (land_eq_iff.mp (by simpa using h1) k hk)
        exact absurd (by simpa using this) h2
      · rw [if_neg h1] at hS
        exact fiterS_sub hb n _ _ (fpassS_sub hb 0 nodes rows M M' h) hS

/-- A reach check with a blocked set implies the reach check for every blocked node of the
set. -/
theorem reach_of_reachS {nodes : List ℕ} {rows : List (List ℕ)} {ns tm passes : ℕ}
    {bl : ℕ → Bool} (h : reachS nodes rows ns tm passes bl = true) {b : ℕ} (hb : bl b = true) :
    reach nodes rows ns tm passes b = true := by
  simp only [reachS, reach, beq_iff_eq] at h ⊢
  exact fiterS_sub hb passes _ _ (fun _ hk => hk) h

/-- Reach checks for all blocked candidates from a few blocked sets: every source node `b`
with `cand b` lies in one of the sets of `bls`, and each set passes the reach check. -/
theorem hcand_of_groups {nodes : List ℕ} {rows : List (List ℕ)} {ns tm passes : ℕ}
    {cand : ℕ → Bool} (bls : List (ℕ → Bool))
    (hg : ∀ f ∈ bls, reachS nodes rows ns tm passes f = true)
    (hc : (nodes.take rows.length).all (fun b => !cand b || bls.any fun f => f b) = true) :
    ∀ b ∈ nodes.take rows.length, cand b = true → reach nodes rows ns tm passes b = true := by
  intro b hb hcb
  have h := List.all_eq_true.mp hc b hb
  simp only [hcb, Bool.not_true, Bool.false_or, List.any_eq_true] at h
  obtain ⟨f, hf, hfb⟩ := h
  exact reach_of_reachS (hg f hf) hfb

end FamInst

end OddPerfect

#print axioms OddPerfect.FamInst.tdl_sound
#print axioms OddPerfect.FamInst.pairwise_of_incr
#print axioms OddPerfect.FamInst.not_prime_of_hasDiv
#print axioms OddPerfect.FamInst.cover_sound
#print axioms OddPerfect.FamInst.fastPrime_sound
#print axioms OddPerfect.FamInst.oddP_incr
#print axioms OddPerfect.FamInst.oddP_cover
#print axioms OddPerfect.FamInst.prime_of_fastPrime
#print axioms OddPerfect.FamInst.getD_flatten
#print axioms OddPerfect.FamInst.rowChk_of_rowChkP
#print axioms OddPerfect.FamInst.land_eq_iff
#print axioms OddPerfect.FamInst.fpassS_sub
#print axioms OddPerfect.FamInst.fiterS_sub
#print axioms OddPerfect.FamInst.reach_of_reachS
#print axioms OddPerfect.FamInst.hcand_of_groups
