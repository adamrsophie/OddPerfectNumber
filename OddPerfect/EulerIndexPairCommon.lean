import OddPerfect.EulerIndexPairAll
import OddPerfect.KanoldGeneral
import OddPerfect.OmegaSevenFinal

/-!
# Two prime Euler index with a common index prime

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and `q ∤ m`,
suppose the Euler index `J = σ(m ^ 2) / q` has exactly two prime factors, and suppose one prime
`l` divides `v_p(N) + 1` for every ordinary prime `p`. These hypotheses are contradictory.

Take the labeling `(t, u)` of `eulerIndex_pair_rows_all`. Then `v_u(N) + 1 = l`, so `t ≡ 1`
modulo `l`, so `l` divides the row `σ(t ^ v_t(N)) = q u ^ v`; as `l ≠ q` this gives `u = l`.
Every ordinary exponent is `l - 1` (an exponent `l ^ 2 - 1` would need two primes of the row that
are `1` modulo `l`), and `q ≡ 1 (mod l)`. The ledger of `l` counts the ordinary primes that are
`1` modulo `l`: there are `l - 1` of them. The ledger of `t` gives `l - 1 ≥ j + |P|` for the set
`P` of the remaining primes. Hence every `p ∈ P` is `1` modulo `l` and has row exactly `t l`.
As `ω(N) ≥ 7`, two distinct primes of `P` share the row `σ(p ^ (l - 1))`, which is impossible.

Restricted result (special exponent 1, an Euler index with exactly two prime factors, and one
prime dividing every ordinary index; it excludes only this intersection of two restricted
families; special exponent above 1 is not covered). No published source was checked; novelty not
verified. The odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace PairC

/-- If `l ∣ d`, `d ≥ 3`, `d ∣ e + 1` and the row `σ(p ^ e)` is `a ^ x l ^ y`, then the prime
factor of order `d` of the row is `a`. -/
theorem witness {p e a l x y d : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (ha : a.Prime)
    (hl : l.Prime) (hd3 : 3 ≤ d) (hld : l ∣ d) (hd : d ∣ e + 1)
    (hrow : σ 1 (p ^ e) = a ^ x * l ^ y) :
    a ∣ σ 1 (p ^ e) ∧ orderOf (p : ZMod a) = d ∧ a % d = 1 := by
  obtain ⟨w, hw, hwd, ho, hmod⟩ := exists_prime_dvd_sigma_orderOf_eq hp hp3 hd3 hd
  have hwl : w % l = 1 := by
    rw [← Nat.mod_mod_of_dvd w hld, hmod]
    exact Nat.mod_eq_of_lt hl.one_lt
  have hwa : w = a := by
    have h2 := hwd
    rw [hrow] at h2
    rcases (Nat.Prime.dvd_mul hw).mp h2 with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hw ha).mp (hw.dvd_of_dvd_pow h)
    · have hwl' := (Nat.prime_dvd_prime_iff_eq hw hl).mp (hw.dvd_of_dvd_pow h)
      rw [hwl', Nat.mod_self] at hwl
      exact absurd hwl (by norm_num)
  rw [← hwa]
  exact ⟨hwd, ho, hmod⟩

/-- A row `a ^ x l ^ y` with `l ∣ e + 1` and `e + 1` prime or the square of a prime has
`e + 1 = l`. -/
theorem succ_eq {p e a l x y : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (ha : a.Prime)
    (hl : l.Prime) (hl3 : 3 ≤ l) (hdiv : l ∣ e + 1)
    (hps : (e + 1).Prime ∨ ∃ P, P.Prime ∧ e + 1 = P ^ 2)
    (hrow : σ 1 (p ^ e) = a ^ x * l ^ y) : e + 1 = l := by
  rcases hps with hP | ⟨P, hP, hsq⟩
  · exact ((Nat.prime_dvd_prime_iff_eq hl hP).mp hdiv).symm
  · have hlP : l = P :=
      (Nat.prime_dvd_prime_iff_eq hl hP).mp (hl.dvd_of_dvd_pow (hsq ▸ hdiv))
    rw [← hlP] at hsq
    have h9 : 3 ≤ l ^ 2 := by nlinarith
    obtain ⟨-, ho1, -⟩ := witness hp hp3 ha hl hl3 (dvd_refl l) hdiv hrow
    obtain ⟨-, ho2, -⟩ := witness hp hp3 ha hl h9 (dvd_pow_self l two_ne_zero)
      ⟨1, by rw [hsq, mul_one]⟩ hrow
    rw [ho1] at ho2
    nlinarith

/-- `σ(p ^ k)` is strictly increasing in the prime `p` for `k ≠ 0`. -/
theorem sigma_pow_lt {p p' k : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hlt : p < p') (hk : k ≠ 0) :
    σ 1 (p ^ k) < σ 1 (p' ^ k) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp']
  exact Finset.sum_lt_sum (fun i _ => Nat.pow_le_pow_left hlt.le i)
    ⟨k, Finset.self_mem_range_succ k, Nat.pow_lt_pow_left hlt hk⟩

end PairC

open PairC

/-- **Two prime index with a common index prime.** Let `N = q m ^ 2` be an odd perfect number
with special prime `q` of exponent 1 and `q ∤ m`, suppose the Euler index `J = σ(m ^ 2) / q` has
exactly the two prime factors `r ≠ s`, and suppose the prime `l` divides `v_p(N) + 1` for every
ordinary prime `p`. This is impossible. Restricted result (special exponent 1 and an Euler index
with exactly two prime factors and one prime dividing every ordinary index; it excludes only this
intersection of two restricted families; special exponent above 1 is not covered). No published
source was checked; novelty not verified. The odd perfect number conjecture remains open. -/
theorem eulerIndex_pair_no_common_index {N q m r s l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) (hl : l.Prime)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) : False := by
  obtain ⟨t, u, htu, htu', ⟨v, hA⟩, ⟨j, hj, hB⟩, htq1, -, hf1, -, hmod, hEt, -, hrest⟩ :=
    eulerIndex_pair_rows_all h hq hN hqm hr hs hrs hJ
  have hN0 : N ≠ 0 := h.ne_zero
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hEq : N.factorization q = 1 := by
    rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero 2 hm), Finsupp.add_apply,
      hq.factorization, Finsupp.single_eq_same, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd hqm, smul_zero, add_zero]
  have hodd : Odd (N.factorization q) := by rw [hEq]; exact odd_one
  have hmemrs : ∀ w, w = t ∨ w = u → w.Prime := by
    intro w hw
    have hw' : w ∈ ({r, s} : Finset ℕ) := by
      rw [← htu]; rcases hw with hw | hw <;> simp [hw]
    rcases Finset.mem_insert.mp hw' with h' | h'
    · exact h' ▸ hr
    · exact (Finset.mem_singleton.mp h') ▸ hs
  have ht : t.Prime := hmemrs t (Or.inl rfl)
  have hu : u.Prime := hmemrs u (Or.inr rfl)
  have hmemF : ∀ p, p.Prime → N.factorization p ≠ 0 → p ∈ N.primeFactors := fun p hp h0 =>
    Nat.mem_primeFactors.mpr ⟨hp, Nat.dvd_of_factorization_pos h0, hN0⟩
  have huF : u ∈ N.primeFactors := hmemF u hu (by
    intro h0; rw [h0] at hf1; norm_num at hf1)
  have htF : t ∈ N.primeFactors := hmemF t ht (by
    intro h0
    rw [h0] at hEt
    rcases hEt with h1 | ⟨P, hP, h1⟩
    · norm_num at h1
    · have := hP.two_le; nlinarith)
  have hodd3 : ∀ p ∈ N.primeFactors, 3 ≤ p := by
    intro p hp
    have h2 := (Nat.prime_of_mem_primeFactors hp).two_le
    rcases (show p = 2 ∨ 3 ≤ p by omega) with h' | h'
    · rw [h'] at hp
      exact absurd (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
        (Nat.not_even_iff_odd.mpr h.1)
    · exact h'
  have hσq : σ 1 (q ^ N.factorization q) = q + 1 := by
    rw [hEq, sigma_one_apply_prime_pow hq, Finset.sum_range_succ, Finset.sum_range_one,
      pow_zero, pow_one, add_comm]
  have htq : t ≠ q := by
    intro heq
    rw [heq, hσq] at hA
    have h1 : q ∣ 1 := (Nat.dvd_add_right (dvd_refl q)).mp ⟨u ^ v, hA⟩
    exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
  have huq : u ≠ q := by
    intro heq
    rw [heq, hσq] at hB
    exact htq1 (by rw [hB]; exact dvd_pow_self t hj.ne')
  -- the exponent of `u` and the prime `l`
  have hle : N.factorization u + 1 = l :=
    ((Nat.prime_dvd_prime_iff_eq hl hf1).mp (hcomp u huF huq)).symm
  have hl2 : l ≠ 2 := by
    obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hu huq
    omega
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hlq : l ≠ q := by
    intro heq
    have h4 := pow_four_dvd_of_dvd_succ h hq hodd hcomp
    rw [heq, hq.pow_dvd_iff_le_factorization hN0, hEq] at h4
    omega
  have ht1 : t % l = 1 := by
    rw [← Nat.mod_mod_of_dvd t (dvd_mul_left l 2), ← hle, hmod]
    exact Nat.mod_eq_of_lt (by omega)
  -- `u = l`
  have hlA : l ∣ σ 1 (t ^ N.factorization t) := by
    have : Fact l.Prime := ⟨hl⟩
    have hv := padicValNat_sigma_of_mod_eq_one ht hl hl2 ht1 (a := N.factorization t)
    have hpos : 1 ≤ padicValNat l (N.factorization t + 1) := by
      rw [Nat.padicValNat_def]
      exact one_le_multiplicity_of_dvd (by omega) (hcomp t htF htq)
    rw [← hv, Nat.padicValNat_def] at hpos
    exact dvd_of_one_le_multiplicity hpos
  have hul : u = l := by
    rw [hA] at hlA
    rcases (Nat.Prime.dvd_mul hl).mp hlA with h' | h'
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hl hq).mp h') hlq
    · exact ((Nat.prime_dvd_prime_iff_eq hl hu).mp (hl.dvd_of_dvd_pow h')).symm
  rw [hul] at hA hB hrest huF htu' hle
  -- every ordinary exponent is `l - 1`
  have hA1 : σ 1 (t ^ N.factorization t) = q ^ 1 * l ^ v := by rw [pow_one]; exact hA
  have hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p + 1 = l := by
    intro p hp hpq
    by_cases hpl : p = l
    · rw [hpl]; exact hle
    by_cases hpt : p = t
    · rw [hpt]
      exact succ_eq ht (hodd3 t htF) hq hl hl3 (hcomp t htF htq) hEt hA1
    obtain ⟨⟨x, y, hrow⟩, -, hps⟩ := hrest p hp hpq hpt hpl
    exact succ_eq (Nat.prime_of_mem_primeFactors hp) (hodd3 p hp) ht hl hl3 (hcomp p hp hpq)
      hps hrow
  have het : N.factorization t + 1 = l := hexp t htF htq
  have hq1 : q % l = 1 :=
    (witness ht (hodd3 t htF) hq hl hl3 (dvd_refl l) ⟨1, by rw [het, mul_one]⟩ hA1).2.2
  -- the remaining primes
  obtain ⟨P, hP⟩ : ∃ P, P = ((N.primeFactors.erase q).erase t).erase l := ⟨_, rfl⟩
  have hmemP : ∀ p, p ∈ P ↔ p ≠ l ∧ p ≠ t ∧ p ≠ q ∧ p ∈ N.primeFactors := by
    intro p
    rw [hP, Finset.mem_erase, Finset.mem_erase, Finset.mem_erase]
  have hrowP : ∀ p ∈ P, ∃ x y, σ 1 (p ^ N.factorization p) = t ^ x * l ^ y := by
    intro p hp
    rw [hmemP] at hp
    exact (hrest p hp.2.2.2 hp.2.2.1 hp.2.1 hp.1).1
  have htP : ∀ p ∈ P, 1 ≤ padicValNat t (σ 1 (p ^ N.factorization p)) := by
    intro p hp
    obtain ⟨x, y, hrow⟩ := hrowP p hp
    have hp' := (hmemP p).mp hp
    have hpF := hp'.2.2.2
    have hpp := Nat.prime_of_mem_primeFactors hpF
    have hd := (witness hpp (hodd3 p hpF) ht hl hl3 (dvd_refl l)
      ⟨1, by rw [hexp p hpF hp'.2.2.1, mul_one]⟩ hrow).1
    have : Fact t.Prime := ⟨ht⟩
    rw [Nat.padicValNat_def]
    exact one_le_multiplicity_of_dvd (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne' hd
  -- the ledger of `l`
  have hel : N.factorization l = l - 1 := by have := hexp l huF hlq; omega
  have hcolL := factorization_eq_sum_erase h.2 hl hl2
  have hterm : ∀ p ∈ N.primeFactors.erase l,
      padicValNat l (σ 1 (p ^ N.factorization p)) = if p ≠ q ∧ p % l = 1 then 1 else 0 := by
    intro p hp
    obtain ⟨hpl, hpF⟩ := Finset.mem_erase.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpF
    have : Fact l.Prime := ⟨hl⟩
    by_cases hpq : p = q
    · rw [ite_eq_right (fun hc => hc.1 hpq), hpq, hσq, Nat.padicValNat_def]
      apply multiplicity_eq_zero_of_not_dvd
      intro hd
      have h2 : l ∣ 2 := by
        have hqk := Nat.div_add_mod q l
        rw [hq1] at hqk
        have h' : q + 1 = l * (q / l) + 2 := by omega
        rw [h'] at hd
        exact (Nat.dvd_add_right (dvd_mul_right l _)).mp hd
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    · have he := hexp p hpF hpq
      by_cases h1 : p % l = 1
      · rw [ite_eq_left ⟨hpq, h1⟩, padicValNat_sigma_of_mod_eq_one hpp hl hl2 h1, he,
          Nat.padicValNat_def, Nat.Prime.multiplicity_self]
      · rw [ite_eq_right (fun hc => h1 hc.2), show N.factorization p = l - 1 by omega]
        exact padicValNat_sigma_pred_of_mod_ne_one hpp hl hpl h1
  have hcardL : l - 1 = ((N.primeFactors.erase l).filter (fun p => p ≠ q ∧ p % l = 1)).card := by
    rw [← hel, hcolL, Finset.sum_congr rfl hterm]
    simp [Finset.sum_boole]
  have hsubL : (N.primeFactors.erase l).filter (fun p => p ≠ q ∧ p % l = 1) ⊆ insert t P := by
    intro p hp
    obtain ⟨hpe, hpq, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpl, hpF⟩ := Finset.mem_erase.mp hpe
    rw [Finset.mem_insert, hmemP]
    by_cases hpt : p = t
    · exact Or.inl hpt
    · exact Or.inr ⟨hpl, hpt, hpq, hpF⟩
  have htnP : t ∉ P := fun h' => ((hmemP t).mp h').2.1 rfl
  have hcardIns : (insert t P).card = P.card + 1 := Finset.card_insert_of_notMem htnP
  have hle1 := Finset.card_le_card hsubL
  -- the ledger of `t`
  have ht2 : t ≠ 2 := by have := hodd3 t htF; omega
  have hcolT := factorization_eq_sum_erase h.2 ht ht2
  have hsubT : insert l P ⊆ N.primeFactors.erase t := by
    intro p hp
    rcases Finset.mem_insert.mp hp with hp | hp
    · rw [hp]; exact Finset.mem_erase.mpr ⟨htu'.symm, huF⟩
    · obtain ⟨-, hpt, -, hpF⟩ := (hmemP p).mp hp
      exact Finset.mem_erase.mpr ⟨hpt, hpF⟩
  have hlP : l ∉ P := fun h' => ((hmemP l).mp h').1 rfl
  have hvB : padicValNat t (σ 1 (l ^ N.factorization l)) = j := by
    have : Fact t.Prime := ⟨ht⟩
    rw [hB, Nat.padicValNat_def, Nat.multiplicity_prime_pow]
  have het' : N.factorization t = l - 1 := by omega
  have hT : j + ∑ p ∈ P, padicValNat t (σ 1 (p ^ N.factorization p)) ≤ l - 1 := by
    have h1 : ∑ p ∈ insert l P, padicValNat t (σ 1 (p ^ N.factorization p)) ≤
        ∑ p ∈ N.primeFactors.erase t, padicValNat t (σ 1 (p ^ N.factorization p)) :=
      Finset.sum_le_sum_of_subset hsubT
    rw [Finset.sum_insert hlP, hvB, ← hcolT, het'] at h1
    exact h1
  have hXP : P.card ≤ ∑ p ∈ P, padicValNat t (σ 1 (p ^ N.factorization p)) := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum htP
  -- equality throughout
  have hfeq : (N.primeFactors.erase l).filter (fun p => p ≠ q ∧ p % l = 1) = insert t P :=
    Finset.eq_of_subset_of_card_le hsubL (by omega)
  have hP1 : ∀ p ∈ P, p % l = 1 := by
    intro p hp
    have hp' : p ∈ (N.primeFactors.erase l).filter (fun p => p ≠ q ∧ p % l = 1) := by
      rw [hfeq]; exact Finset.mem_insert_of_mem hp
    exact (Finset.mem_filter.mp hp').2.2
  have hx1 : ∀ p ∈ P, padicValNat t (σ 1 (p ^ N.factorization p)) = 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨p0, hp0, hne0⟩ := hne
    have hlt : ∑ p ∈ P, (1 : ℕ) < ∑ p ∈ P, padicValNat t (σ 1 (p ^ N.factorization p)) :=
      Finset.sum_lt_sum htP ⟨p0, hp0, by have := htP p0 hp0; omega⟩
    rw [← Finset.card_eq_sum_ones] at hlt
    omega
  -- every remaining row is `t l`
  have hrowTL : ∀ p ∈ P, σ 1 (p ^ N.factorization p) = t * l := by
    intro p hp
    obtain ⟨x, y, hrow⟩ := hrowP p hp
    have hpF := ((hmemP p).mp hp).2.2.2
    have hpq := ((hmemP p).mp hp).2.2.1
    have hpp := Nat.prime_of_mem_primeFactors hpF
    have : Fact t.Prime := ⟨ht⟩
    have : Fact l.Prime := ⟨hl⟩
    have hx : x = 1 := by
      have h' := hx1 p hp
      rwa [hrow, Nat.padicValNat_def, multiplicity_mul_pow_left x y htu'] at h'
    have hy : y = 1 := by
      have h' := padicValNat_sigma_of_mod_eq_one hpp hl hl2 (hP1 p hp) (a := N.factorization p)
      rwa [hrow, hexp p hpF hpq, Nat.padicValNat_def, Nat.padicValNat_def,
        multiplicity_mul_pow_right x y htu'.symm, Nat.Prime.multiplicity_self] at h'
    rw [hrow, hx, hy, pow_one, pow_one]
  -- two remaining primes share their row
  have hcard7 := seven_le_card_primeFactors h
  have hPcard : 1 < P.card := by
    have h1 := Finset.pred_card_le_card_erase (s := N.primeFactors) (a := q)
    have h2 := Finset.pred_card_le_card_erase (s := N.primeFactors.erase q) (a := t)
    have h3 := Finset.pred_card_le_card_erase (s := (N.primeFactors.erase q).erase t) (a := l)
    rw [hP]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hPcard
  have haF := ((hmemP a).mp ha).2.2.2
  have hbF := ((hmemP b).mp hb).2.2.2
  have hea := hexp a haF ((hmemP a).mp ha).2.2.1
  have heb := hexp b hbF ((hmemP b).mp hb).2.2.1
  have hra := hrowTL a ha
  have hrb := hrowTL b hb
  rw [show N.factorization a = l - 1 by omega] at hra
  rw [show N.factorization b = l - 1 by omega] at hrb
  have hk : l - 1 ≠ 0 := by omega
  have hpa := Nat.prime_of_mem_primeFactors haF
  have hpb := Nat.prime_of_mem_primeFactors hbF
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have := sigma_pow_lt hpa hpb hlt hk; omega
  · have := sigma_pow_lt hpb hpa hlt hk; omega

end OddPerfect

#print axioms OddPerfect.PairC.witness
#print axioms OddPerfect.PairC.succ_eq
#print axioms OddPerfect.PairC.sigma_pow_lt
#print axioms OddPerfect.eulerIndex_pair_no_common_index
