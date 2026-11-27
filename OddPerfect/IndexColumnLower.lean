import OddPerfect.KanoldFive
import OddPerfect.SpecialIndexWitness
import OddPerfect.PrimePowerIndexBound

/-!
# Lower bounds for a common index prime from its own column

Let `N` be an odd perfect number with special prime `q`, and let `l ≠ q` be an odd prime that
divides `e_p + 1` for every ordinary prime factor `p` (exponent `e_p = v_p(N)`). Write `B` for
the number of ordinary prime factors of `N` that are `1` modulo `l`. The column of `l`,
`e_l = Σ_{p ≠ l} v_l(σ(p ^ e_p))`, is paid only by primes `1` modulo `l` when no other prime
factor feeds `l`. Each ordinary such prime pays `v_l(e_p + 1) ≤ B`, and the special prime pays
`v_l(e_q + 1)` with `2 v_l(e_q + 1) ≤ B`. Since `l - 1 ≤ e_l`, this gives
`2 (l - 1) ≤ 2 B ^ 2 + B` (`two_mul_index_pred_le_of_no_outside_feeder`).

The hypothesis that no prime outside the class `1` modulo `l` feeds `l` holds when every
ordinary index is a power of `l` (`two_mul_index_pred_le_of_prime_pow_index`) and when `l` is a
Fermat prime with `l ∤ q + 1` (`two_mul_index_pred_le_of_fermat`). For equal exponents
`e_p = l - 1` every ordinary prime `1` modulo `l` pays exactly `1`, so `2 (l - 1) ≤ 3 B`
(`two_mul_index_pred_le_three_mul_card_of_equal_exponents`) and `2 l + 4 ≤ 3 ω(N)`
(`two_mul_index_add_four_le_of_equal_exponents`).

These are restricted results: lower bounds for the number of ordinary prime factors that are
`1` modulo `l`; they exclude no family. Restricted result; no published source was checked;
novelty not verified. The odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace LCol

/-- The special prime is a prime factor. -/
lemma mem_primeFactors_of_odd {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : q ∈ N.primeFactors :=
  Nat.mem_primeFactors.mpr ⟨hq,
    Nat.dvd_of_factorization_pos (by obtain ⟨k, hk⟩ := hodd; omega), h.ne_zero⟩

/-- A prime `l` never divides `σ(l ^ a)`. -/
lemma not_dvd_sigma_self {l : ℕ} (hl : l.Prime) (a : ℕ) : ¬ l ∣ σ 1 (l ^ a) := fun hd =>
  (prime_dvd_sigma_prime_pow hl hl hd).1 rfl

/-- The column of `l` when no prime factor outside the class `1` modulo `l` feeds `l`:
`e_l ≤ v_l(e_q + 1) + Σ_{p ∈ B} v_l(e_p + 1)`. -/
lemma column_le {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hfeed : ∀ p ∈ N.primeFactors, p % l ≠ 1 → ¬ l ∣ σ 1 (p ^ N.factorization p)) :
    N.factorization l ≤ padicValNat l (N.factorization q + 1) +
      ∑ p ∈ N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1),
        padicValNat l (N.factorization p + 1) := by
  have hqN := mem_primeFactors_of_odd h hq hodd
  set B := N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1) with hB
  set f : ℕ → ℕ := fun p => padicValNat l (σ 1 (p ^ N.factorization p)) with hf
  rw [factorization_eq_sum_erase h.perfect hl hl2]
  have hzero : ∀ p ∈ N.primeFactors, p % l ≠ 1 → f p = 0 := fun p hp h1 => by
    show padicValNat l (σ 1 (p ^ N.factorization p)) = 0
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_zero_of_not_dvd (hfeed p hp h1)
  have h1 : ∑ p ∈ N.primeFactors.erase l, f p =
      ∑ p ∈ (N.primeFactors.erase l).filter (fun p => p % l = 1), f p := by
    refine (Finset.sum_filter_of_ne fun p hp hne => ?_).symm
    by_contra h1
    exact hne (hzero p (Finset.mem_of_mem_erase hp) h1)
  have hsub : (N.primeFactors.erase l).filter (fun p => p % l = 1) ⊆ insert q B := by
    intro p hp
    obtain ⟨hpe, hp1⟩ := Finset.mem_filter.mp hp
    by_cases hpq : p = q
    · exact hpq ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hpe, hpq, hp1⟩)
  have hqB : q ∉ B := fun hm => (Finset.mem_filter.mp hm).2.1 rfl
  have hfq : f q ≤ padicValNat l (N.factorization q + 1) := by
    by_cases hq1 : q % l = 1
    · exact (padicValNat_sigma_of_mod_eq_one hq hl hl2 hq1).le
    · rw [hzero q hqN hq1]; exact Nat.zero_le _
  have hfB : ∑ p ∈ B, f p = ∑ p ∈ B, padicValNat l (N.factorization p + 1) :=
    Finset.sum_congr rfl fun p hp => by
      obtain ⟨hpN, -, hp1⟩ := Finset.mem_filter.mp hp
      exact padicValNat_sigma_of_mod_eq_one (Nat.prime_of_mem_primeFactors hpN) hl hl2 hp1
  calc ∑ p ∈ N.primeFactors.erase l, padicValNat l (σ 1 (p ^ N.factorization p))
        = ∑ p ∈ (N.primeFactors.erase l).filter (fun p => p % l = 1), f p := h1
    _ ≤ ∑ p ∈ insert q B, f p := Finset.sum_le_sum_of_subset hsub
    _ = f q + ∑ p ∈ B, f p := Finset.sum_insert hqB
    _ ≤ _ := by rw [hfB]; omega

/-- If every ordinary index is a power of the prime `l`, then `l` is not the special prime. -/
lemma ne_of_prime_pow_index {N q l : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hodd : Odd (N.factorization q))
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ) : l ≠ q := by
  rintro rfl
  exact false_of_special_of_prime_pow_index h hl hodd hidx

/-- If every ordinary index is a power of the odd prime `l ≠ q`, then no prime factor outside
the class `1` modulo `l` feeds `l`. -/
lemma no_feeder_of_prime_pow_index {N q l : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hlq : l ≠ q)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ) :
    ∀ p ∈ N.primeFactors, p % l ≠ 1 → ¬ l ∣ σ 1 (p ^ N.factorization p) := by
  intro p hp hp1 hd
  have hpp := Nat.prime_of_mem_primeFactors hp
  by_cases hpl : p = l
  · subst hpl
    exact not_dvd_sigma_self hpp _ hd
  by_cases hpq : p = q
  · subst hpq
    have hp2 : p ≠ 2 := by have := (special_mod_four h hpp hodd).1; omega
    have hne : N.factorization p ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
    rw [factorization_eq_sum_erase h.perfect hpp hp2] at hne
    obtain ⟨r, hr, hr0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨hrp, hrN⟩ := Finset.mem_erase.mp hr
    have hdr : p ∣ σ 1 (r ^ N.factorization r) := by
      by_contra hnd
      rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hnd] at hr0
      exact hr0 rfl
    obtain ⟨γ, hγ⟩ := hidx r hrN hrp
    rcases prime_dvd_sigma_of_succ_eq_pow (Nat.prime_of_mem_primeFactors hrN) hpp hl hγ hdr with
      h1 | h1
    · exact hlq h1.symm
    · exact hp1 h1
  · obtain ⟨γ, hγ⟩ := hidx p hp hpq
    rcases (prime_dvd_sigma_prime_pow hpp hl hd).2 with ⟨h1, -⟩ | ⟨ho1, hod, hot⟩
    · exact hp1 h1
    · rw [hγ] at hod
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).mp hod
      have hj0 : j ≠ 0 := by rintro rfl; rw [hj, pow_zero] at ho1; omega
      rw [hj] at hot
      have hl2 := hl.two_le
      have := Nat.le_of_dvd (by omega) ((dvd_pow_self l hj0).trans hot)
      omega

end LCol

/-- The column of a common index prime with no outside feeder. Let `q` be the special prime of
the odd perfect number `N` and `l ≠ q` an odd prime with `l ∣ e_p + 1` for every ordinary prime
factor `p`. If no prime factor that is not `1` modulo `l` feeds `l` (that is, `l ∤ σ(p ^ e_p)`
for every prime factor `p` with `p ≢ 1 (mod l)`), then the number `B` of ordinary prime factors
that are `1` modulo `l` satisfies `2 (l - 1) ≤ 2 B ^ 2 + B`. Restricted result (a lower bound
for `B`; it excludes no family); no published source was checked; novelty not verified. The
conjecture remains open. -/
theorem two_mul_index_pred_le_of_no_outside_feeder {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hlq : l ≠ q)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (hfeed : ∀ p ∈ N.primeFactors, p % l ≠ 1 → ¬ l ∣ σ 1 (p ^ N.factorization p)) :
    2 * (l - 1) ≤ 2 * (N.primeFactors.filter fun p => p ≠ q ∧ p % l = 1).card ^ 2 +
      (N.primeFactors.filter fun p => p ≠ q ∧ p % l = 1).card := by
  have hN0 := h.ne_zero
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hlN : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hl,
    (dvd_pow_self l (by norm_num : (4 : ℕ) ≠ 0)).trans (pow_four_dvd_of_dvd_succ h hq hodd hcomp),
    hN0⟩
  have hel : l - 1 ≤ N.factorization l := by
    have := Nat.le_of_dvd (Nat.succ_pos _) (hcomp l hlN hlq); omega
  have hcol := LCol.column_le h hq hodd hl hl2 hfeed
  have hz := two_mul_special_index_le_card h hq hodd hl hl2
  set B := N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1) with hB
  have hR : (N.primeFactors.filter (fun p => p % l = 1)).card ≤ B.card + 1 := by
    calc _ ≤ (insert q B).card := Finset.card_le_card (fun p hp => by
          obtain ⟨hpN, hp1⟩ := Finset.mem_filter.mp hp
          by_cases hpq : p = q
          · exact hpq ▸ Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hpN, hpq, hp1⟩))
      _ ≤ B.card + 1 := Finset.card_insert_le _ _
  have hterm : ∀ p ∈ B, padicValNat l (N.factorization p + 1) ≤ B.card := fun p hp => by
    obtain ⟨hpN, -, hp1⟩ := Finset.mem_filter.mp hp
    have hdv : l ^ padicValNat l (N.factorization p + 1) ∣ N.factorization p + 1 := by
      rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _
    have := succ_le_card_filter_mod_eq_one h hl3 hpN hp1 hdv
    omega
  have hsum : ∑ p ∈ B, padicValNat l (N.factorization p + 1) ≤ B.card * B.card := by
    calc _ ≤ ∑ p ∈ B, B.card := Finset.sum_le_sum hterm
      _ = B.card * B.card := by rw [Finset.sum_const, smul_eq_mul]
  rw [sq]
  generalize B.card * B.card = M at *
  omega

/-- The column of a prime power index. If every ordinary exponent `e_p` of the odd perfect
number `N` has `e_p + 1 = l ^ γ_p` with `γ_p ≥ 1` for an odd prime `l`, then the number `B` of
ordinary prime factors that are `1` modulo `l` satisfies `2 (l - 1) ≤ 2 B ^ 2 + B`. Restricted
result (a lower bound for `B`; it excludes no family); no published source was checked; novelty
not verified. The conjecture remains open. -/
theorem two_mul_index_pred_le_of_prime_pow_index {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, 1 ≤ γ ∧ N.factorization p + 1 = l ^ γ) :
    2 * (l - 1) ≤ 2 * (N.primeFactors.filter fun p => p ≠ q ∧ p % l = 1).card ^ 2 +
      (N.primeFactors.filter fun p => p ≠ q ∧ p % l = 1).card := by
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => by obtain ⟨γ, -, hγ⟩ := hidx p hp hpq; exact ⟨γ, hγ⟩
  have hlq := LCol.ne_of_prime_pow_index h hl hodd hidx'
  refine two_mul_index_pred_le_of_no_outside_feeder h hq hodd hl hl2 hlq (fun p hp hpq => ?_)
    (LCol.no_feeder_of_prime_pow_index h hodd hl hlq hidx')
  obtain ⟨γ, hγ1, hγ⟩ := hidx p hp hpq
  rw [hγ]
  exact dvd_pow_self l (by omega)

/-- The column of a Fermat prime index. Let `l = 2 ^ k + 1` be an odd prime, not the special
prime `q` of the odd perfect number `N`, with `l ∤ q + 1` and `l ∣ e_p + 1` for every ordinary
prime factor `p`. Then the number `B` of ordinary prime factors that are `1` modulo `l`
satisfies `2 (l - 1) ≤ 2 B ^ 2 + B`. Restricted result (a lower bound for `B`; it excludes no
family); no published source was checked; novelty not verified. The conjecture remains open. -/
theorem two_mul_index_pred_le_of_fermat {N q l k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) (hk : l = 2 ^ k + 1)
    (hlq : l ≠ q) (hq1 : ¬ l ∣ q + 1)
    (hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) :
    2 * (l - 1) ≤ 2 * (N.primeFactors.filter fun p => p ≠ q ∧ p % l = 1).card ^ 2 +
      (N.primeFactors.filter fun p => p ≠ q ∧ p % l = 1).card := by
  refine two_mul_index_pred_le_of_no_outside_feeder h hq hodd hl hl2 hlq hcomp ?_
  intro p hp hp1 hd
  have hpp := Nat.prime_of_mem_primeFactors hp
  by_cases hpl : p = l
  · subst hpl
    exact LCol.not_dvd_sigma_self hpp _ hd
  rcases (prime_dvd_sigma_prime_pow hpp hl hd).2 with ⟨h1, -⟩ | ⟨ho1, hod, hot⟩
  · exact hp1 h1
  have hl1 : l - 1 = 2 ^ k := by rw [hk, Nat.add_sub_cancel]
  rw [hl1] at hot
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hot
  have hj0 : j ≠ 0 := by rintro rfl; rw [hj, pow_zero] at ho1; omega
  rw [hj] at hod
  have h2 : 2 ∣ N.factorization p + 1 := (dvd_pow_self 2 hj0).trans hod
  have hpq : p = q := by
    by_contra hpq
    obtain ⟨q', hq', -, -, -, hev⟩ := exists_special_prime h
    have hqq : q = q' := by
      by_contra hne
      exact Nat.not_even_iff_odd.mpr hodd (hev q hq hne)
    obtain ⟨m, hm⟩ := hev p hpp (by rw [← hqq]; exact hpq)
    omega
  subst hpq
  have h4 := (special_mod_four h hpp hodd).2
  have hj1 : j = 1 := by
    by_contra hj1
    have : 4 ∣ N.factorization p + 1 :=
      (pow_dvd_pow 2 (by omega : 2 ≤ j)).trans hod
    omega
  rw [hj1, pow_one] at hj
  have : Fact l.Prime := ⟨hl⟩
  have hsq : (p : ZMod l) * (p : ZMod l) = 1 := by rw [← sq, ← hj, pow_orderOf_eq_one]
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · rw [h1, orderOf_one] at hj
    omega
  · apply hq1
    refine (ZMod.natCast_eq_zero_iff (p + 1) l).mp ?_
    push_cast
    rw [h1]
    ring

/-- Equal exponents, counting form. If every ordinary exponent of the odd perfect number `N`
equals `l - 1` for an odd prime `l`, then the number `B` of ordinary prime factors that are
`1` modulo `l` satisfies `2 (l - 1) ≤ 3 B`. Restricted result (a lower bound for `B`; it
excludes no family); no published source was checked; novelty not verified. The conjecture
remains open. -/
theorem two_mul_index_pred_le_three_mul_card_of_equal_exponents {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    2 * (l - 1) ≤ 3 * (N.primeFactors.filter fun p => p ≠ q ∧ p % l = 1).card := by
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => ⟨1, by rw [hexp p hp hpq, hl1, pow_one]⟩
  have hlq := LCol.ne_of_prime_pow_index h hl hodd hidx'
  have hfeed := LCol.no_feeder_of_prime_pow_index h hodd hl hlq hidx'
  have hcol := LCol.column_le h hq hodd hl hl2 hfeed
  have hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1 :=
    fun p hp hpq => by rw [hexp p hp hpq, hl1]
  have hlN : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hl,
    (dvd_pow_self l (by norm_num : (4 : ℕ) ≠ 0)).trans (pow_four_dvd_of_dvd_succ h hq hodd hcomp),
    h.ne_zero⟩
  have hel := hexp l hlN hlq
  have hz := two_mul_special_index_le_card h hq hodd hl hl2
  set B := N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1) with hB
  have hsum : ∑ p ∈ B, padicValNat l (N.factorization p + 1) = B.card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpN, hpq, -⟩ := Finset.mem_filter.mp hp
    rw [hexp p hpN hpq, hl1, Nat.padicValNat_def, Nat.multiplicity_self hl.one_lt]
  rw [hsum, hel] at hcol
  omega

/-- Equal exponents, prime factor count. If every ordinary exponent of the odd perfect number
`N` equals `l - 1` for an odd prime `l`, then `2 l + 4 ≤ 3 ω(N)`. Restricted result; no
published source was checked; novelty not verified. The conjecture remains open. -/
theorem two_mul_index_add_four_le_of_equal_exponents {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    2 * l + 4 ≤ 3 * N.primeFactors.card := by
  have hmain := two_mul_index_pred_le_three_mul_card_of_equal_exponents h hq hodd hl hl2 hexp
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  have hidx' : ∀ p ∈ N.primeFactors, p ≠ q → ∃ γ, N.factorization p + 1 = l ^ γ :=
    fun p hp hpq => ⟨1, by rw [hexp p hp hpq, hl1, pow_one]⟩
  have hlq := LCol.ne_of_prime_pow_index h hl hodd hidx'
  have hcomp : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1 :=
    fun p hp hpq => by rw [hexp p hp hpq, hl1]
  have hlN : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hl,
    (dvd_pow_self l (by norm_num : (4 : ℕ) ≠ 0)).trans (pow_four_dvd_of_dvd_succ h hq hodd hcomp),
    h.ne_zero⟩
  have hqN := LCol.mem_primeFactors_of_odd h hq hodd
  set B := N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1) with hB
  have hlB : l ∉ B := fun hm => by
    have := (Finset.mem_filter.mp hm).2.2
    rw [Nat.mod_self] at this
    omega
  have hqB : q ∉ insert l B := by
    rw [Finset.mem_insert]
    rintro (hql | hm)
    · exact hlq hql.symm
    · exact (Finset.mem_filter.mp hm).2.1 rfl
  have hsub : insert q (insert l B) ⊆ N.primeFactors := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hqN
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hlN
    · exact (Finset.mem_filter.mp hp).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hqB, Finset.card_insert_of_notMem hlB] at hcard
  have := hl.two_le
  omega

end OddPerfect

#print axioms OddPerfect.LCol.mem_primeFactors_of_odd
#print axioms OddPerfect.LCol.not_dvd_sigma_self
#print axioms OddPerfect.LCol.column_le
#print axioms OddPerfect.LCol.ne_of_prime_pow_index
#print axioms OddPerfect.LCol.no_feeder_of_prime_pow_index
#print axioms OddPerfect.two_mul_index_pred_le_of_no_outside_feeder
#print axioms OddPerfect.two_mul_index_pred_le_of_prime_pow_index
#print axioms OddPerfect.two_mul_index_pred_le_of_fermat
#print axioms OddPerfect.two_mul_index_pred_le_three_mul_card_of_equal_exponents
#print axioms OddPerfect.two_mul_index_add_four_le_of_equal_exponents
