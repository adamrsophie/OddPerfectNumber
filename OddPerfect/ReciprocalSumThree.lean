import OddPerfect.ReciprocalSumTwo

/-!
# The reciprocal sum of the prime factors exceeds 59/100

For an odd perfect number `N` we prove `59/100 < ∑_{p ∣ N} 1/p`.

This is a classical kind of estimate and weaker than the published bound near `0.596` of
Cohen (1980); see also the sources cited in `OddPerfect.ReciprocalSumTwo`. No claim of novelty
is made.

As in `OddPerfect.ReciprocalSumTwo`, write `c(p) = log(p/(p-1)) - 1/p`, so that
`log 2 < ∑ 1/p + ∑ c(p)`, and split the prime factors into three parts:

* the head primes `H = {3, 5, ..., 43}` (the thirteen smallest odd primes). With `q` the special
  prime of Euler, the exponent of `q` in `N` is positive and every other exponent is positive
  and even, so the product over `T = H ∩ {p ∣ N}` of `1 + 1/q` (at `q`) and `1 + 1/p + 1/p^2`
  (at the other primes) is at most the abundancy `2` of `N`. A finite check over all subsets of
  `H` and all possible roles of the special prime shows that this forces the sum of the weights
  `W(p) ≥ 10^15 c(p)` over `T` to be at most `recipHeadBound`;
* the odd primes from `47` to `997`, which contribute at most the sum of their weights;
* the primes `p ≥ 1009`, which contribute at most `(1/4) * 1/(1009 - 2)` (telescoping).

The weight table and the bound `recipHeadBound` were computed outside Lean; the kernel checks
again every weight against `corrBound`, the subset check, and the final rational inequality.
-/

open Finset

namespace OddPerfect

/-- The weights: for each odd prime `p < 1009` (the head primes first), a natural number
`w` with `corrBound p ≤ w / 10 ^ 15`. -/
def recipWeightTable : List (ℕ × ℕ) :=
  [(3, 72132645667761), (5, 23143552260803), (7, 11293536981242), (11, 4401088895264),
   (13, 3119630750463), (17, 1801092404671), (19, 1435642322908), (23, 973501701269),
   (29, 608561190581), (31, 531758306862), (37, 371947161088), (41, 302368687933),
   (43, 274683456706), (47, 229609476283), (53, 180270442393), (59, 145280816928),
   (61, 135859328260), (67, 112504230213), (71, 100127949703), (73, 94691995350),
   (79, 80797929329), (83, 73167761261), (89, 63600197754), (97, 53508685032), (101, 49340754159),
   (103, 47437081288), (107, 43945957316), (109, 42343178319), (113, 39389895123),
   (127, 31163759082), (131, 29284959310), (137, 26770019081), (139, 26003369171),
   (149, 22622785371), (151, 22026162378), (157, 20371347179), (163, 18896249225),
   (167, 18000108117), (173, 16770863517), (179, 15663369899), (181, 15318497163),
   (191, 13753791903), (193, 13469726845), (197, 12927375492), (199, 12668401817),
   (211, 11266265707), (223, 10084655104), (227, 9731865505), (229, 9562372725), (233, 9236405829),
   (239, 8777841626), (241, 8632555303), (251, 7957524518), (257, 7589832000), (263, 7247047847),
   (269, 6926972024), (271, 6824980958), (277, 6532166940), (281, 6347303287), (283, 6257800531),
   (293, 5837465510), (307, 5316644589), (311, 5180616441), (313, 5114551758), (317, 4986157877),
   (331, 4572880284), (337, 4411338713), (347, 4160508732), (349, 4112915059), (353, 4020145398),
   (359, 3886767245), (367, 3719012878), (373, 3600223216), (379, 3487035399), (383, 3414516630),
   (389, 3309907770), (397, 3177745053), (401, 3114612553), (409, 2993863579), (419, 2852552513),
   (421, 2825492854), (431, 2695801291), (433, 2670936209), (439, 2598370707), (443, 2551624323),
   (449, 2483835065), (457, 2397572379), (461, 2356116545), (463, 2335790673), (467, 2295920126),
   (479, 2182247226), (487, 2111091747), (491, 2076812048), (499, 2010710834), (503, 1978837434),
   (509, 1932429802), (521, 1844381349), (523, 1830293183), (541, 1710452672), (547, 1673112177),
   (557, 1613540257), (563, 1579311719), (569, 1546160892), (571, 1535342301), (577, 1503559176),
   (587, 1452738308), (593, 1423472911), (599, 1395083015), (601, 1385808246), (607, 1358532194),
   (613, 1332053576), (617, 1314828919), (619, 1306341607), (631, 1257101753), (641, 1218164457),
   (643, 1210594315), (647, 1195664203), (653, 1173781632), (659, 1152494338), (661, 1145527131),
   (673, 1105020539), (677, 1091994865), (683, 1072883990), (691, 1048173471), (701, 1018467648),
   (709, 995602865), (719, 968088678), (727, 946890292), (733, 931445122), (739, 916374793),
   (743, 906530191), (751, 887311009), (757, 873294904), (761, 864134529), (769, 846240937),
   (773, 837501844), (787, 807957702), (797, 787801541), (809, 764594257), (811, 760826241),
   (821, 742397540), (823, 738792215), (827, 731659908), (829, 728132424), (839, 710871894),
   (853, 687719808), (857, 681312514), (859, 678142394), (863, 671868171), (877, 650580604),
   (881, 644684132), (883, 641765912), (887, 635988603), (907, 608239743), (911, 602908229),
   (919, 592453369), (929, 579762838), (937, 569901706), (941, 565065220), (947, 557925119),
   (953, 550919500), (967, 535077385), (971, 530676492), (977, 524176262), (983, 517794736),
   (991, 509465732), (997, 503350159)]

/-- The bound on the weight of an accepted head. -/
def recipHeadBound : ℕ := 100650788525097

/-- The odd primes below `1009`. -/
private def recipList : List ℕ := recipWeightTable.map Prod.fst

/-- The thirteen head primes. -/
private def recipHead : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

/-- The weight of `p` in the table, or `0`. -/
private def recipWeight (p : ℕ) : ℕ := (recipWeightTable.lookup p).getD 0

/-- The subset check. A branch fixes, for each prime of the list, whether it is outside the head
set, an ordinary member, or the special member (allowed once, only for `p ≡ 1 (mod 4)`); `num`
and `den` carry the product of the factors and `w` the sum of the weights. Each leaf must have
product above `2` or weight at most `K`. -/
private def headCheck (K : ℕ) : List ℕ → ℕ → ℕ → ℕ → Bool → Bool
  | [], num, den, w, _ => decide (2 * den < num) || decide (w ≤ K)
  | p :: l, num, den, w, sp =>
      headCheck K l num den w sp &&
      headCheck K l (num * (p * p + p + 1)) (den * (p * p)) (w + recipWeight p) sp &&
      (sp || decide (p % 4 ≠ 1) ||
        headCheck K l (num * (p + 1)) (den * p) (w + recipWeight p) true)

/-- The factor of `p` in the abundancy bound when `q` is the special prime. -/
private def roleFactor (q p : ℕ) : ℚ :=
  if p = q then ((p + 1 : ℕ) : ℚ) / (p : ℚ) else ((p * p + p + 1 : ℕ) : ℚ) / ((p * p : ℕ) : ℚ)

private theorem headCheck_sound (K q : ℕ) (S : Finset ℕ) :
    ∀ (l : List ℕ) (num den w : ℕ) (sp : Bool), headCheck K l num den w sp = true →
      l.Nodup → (∀ p ∈ l, 0 < p) → 0 < den →
      (sp = true → ∀ p ∈ l, p ∈ S → p ≠ q) → (q ∈ l → q ∈ S → q % 4 = 1) →
      (num : ℚ) / den * ((l.filter (· ∈ S)).map (roleFactor q)).prod ≤ 2 →
      w + ((l.filter (· ∈ S)).map recipWeight).sum ≤ K := by
  intro l
  induction l with
  | nil =>
    intro num den w sp hc _ _ hden _ _ hprod
    simp only [headCheck, Bool.or_eq_true, decide_eq_true_eq] at hc
    simp only [List.filter_nil, List.map_nil, List.prod_nil, mul_one, List.sum_nil,
      add_zero] at hprod ⊢
    rcases hc with hc | hc
    · exfalso
      have hd : (0 : ℚ) < den := by exact_mod_cast hden
      rw [div_le_iff₀ hd] at hprod
      have : ((2 * den : ℕ) : ℚ) < num := by exact_mod_cast hc
      push_cast at this
      linarith
    · exact hc
  | cons p l ih =>
    intro num den w sp hc hnd hpos hden hsp hq hprod
    simp only [headCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    have hp0 : 0 < p := hpos p List.mem_cons_self
    obtain ⟨hpl, hnd'⟩ := List.nodup_cons.mp hnd
    have hpos' : ∀ x ∈ l, 0 < x := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have hp0' : (0 : ℚ) < p := by exact_mod_cast hp0
    by_cases hpS : p ∈ S
    · rw [List.filter_cons_of_pos (by simpa using hpS)] at hprod ⊢
      rw [List.map_cons, List.prod_cons] at hprod
      rw [List.map_cons, List.sum_cons]
      by_cases hpq : p = q
      · subst hpq
        have hsp' : sp = false := by
          cases sp
          · rfl
          · exact absurd rfl (hsp rfl p List.mem_cons_self hpS)
        have h4 := hq List.mem_cons_self hpS
        subst hsp'
        have h3' : headCheck K l (num * (p + 1)) (den * p) (w + recipWeight p) true = true := by
          rcases h3 with (h | h) | h
          · exact absurd h (by simp)
          · exact absurd h4 h
          · exact h
        have := ih _ _ _ _ h3' hnd' hpos' (Nat.mul_pos hden hp0)
          (fun _ x hx _ hxq => hpl (hxq ▸ hx)) (fun hx _ => absurd hx hpl) ?_
        · omega
        · rw [roleFactor, if_pos rfl] at hprod
          refine le_of_eq_of_le ?_ hprod
          simp only [← mul_assoc, div_mul_div_comm, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      · have hrf : roleFactor q p = ((p * p + p + 1 : ℕ) : ℚ) / ((p * p : ℕ) : ℚ) := by
          rw [roleFactor, if_neg hpq]
        have := ih _ _ _ _ h2 hnd' hpos' (Nat.mul_pos hden (Nat.mul_pos hp0 hp0))
          (fun hs x hx hxS => hsp hs x (List.mem_cons_of_mem _ hx) hxS)
          (fun hx hxS => hq (List.mem_cons_of_mem _ hx) hxS) ?_
        · omega
        · rw [hrf] at hprod
          refine le_of_eq_of_le ?_ hprod
          simp only [← mul_assoc, div_mul_div_comm, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    · rw [List.filter_cons_of_neg (by simpa using hpS)] at hprod ⊢
      exact ih _ _ _ _ h1 hnd' hpos' hden
        (fun hs x hx hxS => hsp hs x (List.mem_cons_of_mem _ hx) hxS)
        (fun hx hxS => hq (List.mem_cons_of_mem _ hx) hxS) hprod

/-- The abundancy bound on the head: the product of the role factors over distinct prime
factors of `N` is at most `2`. -/
private theorem prod_roleFactor_le_two {N : ℕ} (h : OddPerfect N) {q : ℕ}
    (hev : ∀ p : ℕ, p.Prime → p ≠ q → Even (N.factorization p)) {l : List ℕ} (hnd : l.Nodup)
    (hl : ∀ p ∈ l, p ∈ N.primeFactors) : (l.map (roleFactor q)).prod ≤ 2 := by
  rw [← List.prod_toFinset _ hnd]
  have hab : abundancy N = 2 := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  have hfac : ∀ p ∈ N.primeFactors, p.Prime ∧ 0 < N.factorization p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    exact ⟨hp', hp'.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)⟩
  have hone : ∀ p ∈ N.primeFactors, 1 ≤ abundancy (p ^ N.factorization p) := by
    intro p hp
    obtain ⟨hp', ha⟩ := hfac p hp
    have := one_add_inv_le_abundancy_prime_pow hp' ha
    have : (0 : ℚ) ≤ (p : ℚ)⁻¹ := by positivity
    linarith
  calc ∏ p ∈ l.toFinset, roleFactor q p
      ≤ ∏ p ∈ l.toFinset, abundancy (p ^ N.factorization p) := by
        refine Finset.prod_le_prod₀ (fun p _ => ?_) (fun p hp => ?_)
        · unfold roleFactor
          split_ifs <;> positivity
        · have hpN := hl p (List.mem_toFinset.mp hp)
          obtain ⟨hp', ha⟩ := hfac p hpN
          have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp'.ne_zero
          unfold roleFactor
          split_ifs with hpq
          · refine le_of_eq_of_le ?_ (one_add_inv_le_abundancy_prime_pow hp' ha)
            push_cast
            field_simp
          · obtain ⟨k, hk⟩ := hev p hp' hpq
            refine le_trans (le_of_eq ?_) (abundancy_prime_pow_mono hp' (a := 2) (by omega))
            rw [abundancy_prime_pow hp']
            simp only [Finset.sum_range_succ, Finset.sum_range_zero]
            push_cast
            field_simp
            ring
    _ ≤ ∏ p ∈ N.primeFactors, abundancy (p ^ N.factorization p) := by
        refine Finset.prod_le_prod_of_subset_of_one_le₀ (fun p hp => hl p (List.mem_toFinset.mp hp))
          (fun p hp => le_trans zero_le_one (hone p (hl p (List.mem_toFinset.mp hp))))
          (fun p hp _ => hone p hp)
    _ = 2 := by rw [← abundancy_eq_prod_primeFactors h.ne_zero, hab]

private theorem headCheck_ok : headCheck recipHeadBound recipHead 1 1 0 false = true := by
  decide +kernel

private theorem recipHead_ok :
    recipHead.Nodup ∧ (∀ p ∈ recipHead, 0 < p) ∧ ∀ p ∈ recipHead, p < 1009 := by
  decide +kernel

private theorem weight_ok :
    recipList.all (fun p => decide (corrBound p ≤ (recipWeight p : ℚ) / 1000000000000000)) =
      true := by
  decide +kernel

private theorem recipList_ok : coverCheck 1009 32 recipList = true ∧ recipList.Nodup := by
  decide +kernel

private theorem final_ok :
    (59 / 100 : ℚ) + ((recipHeadBound : ℚ) / 1000000000000000 +
        ((((recipList.filter (· ∉ recipHead)).map recipWeight).sum : ℕ) : ℚ) /
          1000000000000000) + 1 / (4 * ((1009 : ℚ) - 2)) ≤ 6931471803 / 10000000000 := by
  decide +kernel

/-- For an odd perfect number, `59/100 < ∑_{p ∣ N} 1/p` (head primes `3` to `43`, cutoff
`1009`). -/
theorem sum_inv_gt_59_div_100 {N : ℕ} (h : OddPerfect N) :
    (59 / 100 : ℝ) < ∑ p ∈ N.primeFactors, 1 / (p : ℝ) := by
  set S := N.primeFactors with hS
  set f : ℕ → ℝ := fun p => Real.log ((p : ℝ) / (p - 1)) - 1 / p with hf
  have hodd : ∀ p ∈ S, 3 ≤ p ∧ Odd p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have ho : Odd p := h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    refine ⟨?_, ho⟩
    have := hp'.two_le
    obtain ⟨k, rfl⟩ := ho
    omega
  have hsplit : ∑ p ∈ S, Real.log ((p : ℝ) / (p - 1)) = ∑ p ∈ S, 1 / (p : ℝ) + ∑ p ∈ S, f p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by simp only [f]; ring
  obtain ⟨hcov, hndL⟩ := recipList_ok
  obtain ⟨hndH, hposH, hltH⟩ := recipHead_ok
  have hW : ∀ p ∈ recipList, corrBound p ≤ (recipWeight p : ℚ) / 1000000000000000 := by
    have := weight_ok
    rw [List.all_eq_true] at this
    exact fun p hp => of_decide_eq_true (this p hp)
  have hpos : ∀ p ∈ recipList, 0 ≤ corrBound p := fun p hp =>
    (corrBound_pos (by have := three_le_of_mem_coverCheck hcov hp; omega)).le
  -- the head primes
  obtain ⟨q, -, -, hq4, -, hev⟩ := exists_special_prime h
  set T := recipHead.filter (· ∈ S) with hT
  have hTnd : T.Nodup := hndH.filter _
  have hTS : ∀ p ∈ T, p ∈ S := fun p hp => by simpa using (List.mem_filter.mp hp).2
  have hTL : ∀ p ∈ T, p ∈ recipList := by
    intro p hp
    have hpH := (List.mem_filter.mp hp).1
    have := (hodd p (hTS p hp)).1
    exact mem_of_coverCheck hcov (hltH p hpH) (Nat.prime_of_mem_primeFactors (hTS p hp))
      (by omega)
  have hwT : (T.map recipWeight).sum ≤ recipHeadBound := by
    have := headCheck_sound recipHeadBound q S recipHead 1 1 0 false headCheck_ok hndH hposH
      one_pos (by simp) (fun _ _ => hq4) (by simpa using prod_roleFactor_le_two h hev hTnd hTS)
    simpa using this
  have hheadT : ∑ p ∈ T.toFinset, corrBound p ≤ (recipHeadBound : ℚ) / 1000000000000000 := by
    calc ∑ p ∈ T.toFinset, corrBound p
        ≤ ∑ p ∈ T.toFinset, (recipWeight p : ℚ) / 1000000000000000 :=
          Finset.sum_le_sum fun p hp => hW p (hTL p (List.mem_toFinset.mp hp))
      _ = (((T.map recipWeight).sum : ℕ) : ℚ) / 1000000000000000 := by
          rw [← Finset.sum_div, ← Nat.cast_sum, List.sum_toFinset _ hTnd]
      _ ≤ (recipHeadBound : ℚ) / 1000000000000000 := by
          gcongr
  -- the primes from 47 to 997
  set R := recipList.filter (· ∉ recipHead) with hR
  have hRnd : R.Nodup := hndL.filter _
  have hrest : ∑ p ∈ R.toFinset, corrBound p ≤
      (((R.map recipWeight).sum : ℕ) : ℚ) / 1000000000000000 := by
    calc ∑ p ∈ R.toFinset, corrBound p
        ≤ ∑ p ∈ R.toFinset, (recipWeight p : ℚ) / 1000000000000000 :=
          Finset.sum_le_sum fun p hp =>
            hW p (List.mem_filter.mp (List.mem_toFinset.mp hp)).1
      _ = (((R.map recipWeight).sum : ℕ) : ℚ) / 1000000000000000 := by
          rw [← Finset.sum_div, ← Nat.cast_sum, List.sum_toFinset _ hRnd]
  -- the prime factors below 1009
  set A := S.filter (· < 1009) with hA
  have hAQ : ∑ p ∈ A, corrBound p ≤ (recipHeadBound : ℚ) / 1000000000000000 +
      (((R.map recipWeight).sum : ℕ) : ℚ) / 1000000000000000 := by
    rw [← Finset.sum_filter_add_sum_filter_not A (· ∈ recipHead)]
    have hAL : ∀ p ∈ A, p ∈ recipList := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have := (hodd p hp.1).1
      exact mem_of_coverCheck hcov hp.2 (Nat.prime_of_mem_primeFactors hp.1) (by omega)
    gcongr
    · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hheadT
      · intro p hp
        rw [Finset.mem_filter] at hp
        rw [List.mem_toFinset, hT, List.mem_filter]
        exact ⟨hp.2, by simpa using (Finset.mem_filter.mp hp.1).1⟩
      · intro p hp _
        exact hpos p (hTL p (List.mem_toFinset.mp hp))
    · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hrest
      · intro p hp
        rw [Finset.mem_filter] at hp
        rw [List.mem_toFinset, hR, List.mem_filter]
        exact ⟨hAL p hp.1, by simpa using hp.2⟩
      · intro p hp _
        exact hpos p (List.mem_filter.mp (List.mem_toFinset.mp hp)).1
  have hhead : ∑ p ∈ A, f p ≤ ((((recipHeadBound : ℚ) / 1000000000000000 +
      (((R.map recipWeight).sum : ℕ) : ℚ) / 1000000000000000) : ℚ) : ℝ) := by
    refine (Finset.sum_le_sum fun p hp => ?_).trans
      (le_of_eq_of_le (Rat.cast_sum _ _).symm ((Rat.cast_le (K := ℝ)).mpr hAQ))
    have := (hodd p (Finset.mem_filter.mp hp).1).1
    exact log_div_sub_one_sub_inv_le_corrBound (by omega)
  -- the tail
  have htail : ∑ p ∈ S.filter (fun p => ¬ p < 1009), f p ≤
      1 / 4028 := by
    have hT' : ∀ p ∈ S.filter (fun p => ¬ p < 1009), Odd p ∧ 1009 ≤ p := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact ⟨(hodd p hp.1).2, by omega⟩
    calc ∑ p ∈ S.filter (fun p => ¬ p < 1009), f p
        ≤ ∑ p ∈ S.filter (fun p => ¬ p < 1009), (1 / 4) * (1 / ((p : ℝ) - 2) - 1 / p) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have : (3 : ℝ) ≤ p := by exact_mod_cast (by have := (hT' p hp).2; omega : 3 ≤ p)
          exact log_div_sub_one_sub_inv_le this
      _ = (1 / 4) * ∑ p ∈ S.filter (fun p => ¬ p < 1009), (1 / ((p : ℝ) - 2) - 1 / p) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / 4) * (1 / ((1009 : ℕ) - 2 : ℝ)) := by
          gcongr
          exact sum_telescope_le (by norm_num) (by decide) hT'
      _ = 1 / 4028 := by norm_num
  have hfin : (59 / 100 : ℚ) + ((recipHeadBound : ℚ) / 1000000000000000 +
      (((R.map recipWeight).sum : ℕ) : ℚ) / 1000000000000000) + 1 / (4 * ((1009 : ℚ) - 2)) ≤
      6931471803 / 10000000000 := final_ok
  generalize (recipHeadBound : ℚ) / 1000000000000000 +
    (((R.map recipWeight).sum : ℕ) : ℚ) / 1000000000000000 = X at hfin hhead
  have hfinR := (Rat.cast_le (K := ℝ)).mpr hfin
  have hsum := Finset.sum_filter_add_sum_filter_not S (· < 1009) f
  have hlog := log_two_lt_sum_log h
  have hl2 := Real.log_two_gt_d9
  rw [← hS, hsplit] at hlog
  push_cast at hfinR
  norm_num at hl2 hfinR
  linarith

end OddPerfect

#print axioms OddPerfect.sum_inv_gt_59_div_100
