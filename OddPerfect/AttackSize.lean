import OddPerfect.Abundancy
import OddPerfect.Euler
import OddPerfect.Network
import OddPerfect.ExponentCap
import OddPerfect.Steuerwald
import OddPerfect.Seed.ThreeFree

/-!
# Size and positivity: pure squares and large prime factors

Two families of results that mix exact arithmetic with inequalities.

## Pure squares when `3 ∤ N`

Let `N` be an odd perfect number with special prime `q` and `3 ∤ N`. Call a prime factor `p`
a *pure square* when `p ^ 2 ∥ N` and `σ(p ^ 2) = 1 + p + p ^ 2` is a power of `q`.

* `q ≡ 1 (mod 12)`, so `q ≥ 13` and `q/(q-1) ≤ 13/12`.
* A pure square `p` has `p ≡ 2 (mod 3)` (else `3 ∣ σ(p^2)`) and `p ≡ 3 (mod 4)` (because
  `q ^ a ≡ 1 (mod 4)`), so `p ≡ 11 (mod 12)`; the values `11, 23, 47` are excluded by
  `133 = 7 * 19`, `553 = 7 * 79`, `2257 = 37 * 61`, so `p ≥ 59`.
* The exponent `a` is odd since `1 + p + p ^ 2` lies strictly between two squares, so two
  pure squares `p < p'` have exponents differing by at least two and `13 p ≤ p'`.
* Hence the pure squares contribute at most `1 + 2/59 = 61/59` to the abundancy, and the
  remaining prime factors `Y` (neither `q` nor a pure square) satisfy
  `∏_{p ∈ Y} p/(p-1) > 2 * 12 * 59 / (13 * 61) = 1416/793`
  (`prod_nonpure_gt_of_not_three_dvd`).

Consequences (`three_dvd_of_exceptions_mod_three`, `three_dvd_of_exceptions_not_target`):
an odd perfect number in which every prime other than `q` has exponent exactly 2, except for
at most twelve primes that are all `≡ 2 (mod 3)`, or except for at most four primes none of
which divides any `σ(p ^ 2)` of an exponent-two prime, is divisible by 3. The second form
contains the first case of `three_dvd_of_one_exception` (one exceptional prime that is not a
target). The proofs use only elementary size bounds.

## Large prime factors (every odd perfect number)

If `S` is a set of prime factors, all at least `p`, then the components over `S` have product
at least `p ^ (2 |S| - 1)` (at most one exponent is odd). If `S` is not all of the prime
factors, the network has an edge from a component `l ^ b` outside `S` into `S`, so
`σ(l ^ b) ≥ p` and `3 l ^ b > 2 σ(l ^ b)`. Hence `2 p ^ (2 |S|) < 3 N`
(`two_mul_pow_lt_three_mul`). This is the method of Bibby, Vyncke and Zelinsky
(arXiv 1908.09420, Theorem 1) with the constant `3/2` in place of `2`. If `S` is everything,
Steuerwald's theorem gives an exponent at least four and `p ^ (2 ω(N) + 1) ≤ N`
(`pow_two_mul_card_add_one_le`).
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Elementary facts about `1 + p + p ^ 2` -/

private theorem sigma_sq_eq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]

/-- A value `1 + p + p ^ 2` with `p > 0` that is a power `q ^ a` has `a` odd. -/
private theorem odd_exp_of_eq_pow {p q a : ℕ} (hp : 0 < p) (h : 1 + p + p ^ 2 = q ^ a) :
    Odd a := by
  rcases Nat.even_or_odd a with ⟨b, rfl⟩ | ho
  · exfalso
    rw [← two_mul, pow_mul'] at h
    have h1 : p ^ 2 < (q ^ b) ^ 2 := by rw [← h]; omega
    have h2 : (q ^ b) ^ 2 < (p + 1) ^ 2 := by rw [← h]; nlinarith
    have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h1
    have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
    omega
  · exact ho

/-- Two values of `1 + x + x ^ 2` that are odd powers of `q ≥ 13` have inputs separated by
a factor 13. -/
private theorem sep_thirteen {p p' q a a' : ℕ} (hq : 13 ≤ q) (ha : Odd a) (ha' : Odd a')
    (h : 1 + p + p ^ 2 = q ^ a) (h' : 1 + p' + p' ^ 2 = q ^ a') (hlt : p < p') :
    13 * p ≤ p' := by
  have hlt' : q ^ a < q ^ a' := by rw [← h, ← h']; nlinarith
  have haa : a < a' := (pow_lt_pow_iff_right₀ (by omega)).mp hlt'
  have ha2 : a + 2 ≤ a' := by
    obtain ⟨i, rfl⟩ := ha; obtain ⟨j, rfl⟩ := ha'; omega
  have hle : q ^ a * q ^ 2 ≤ q ^ a' := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) ha2
  rw [← h, ← h'] at hle
  have hq2 : 169 ≤ q ^ 2 := by nlinarith
  have : (1 + p + p ^ 2) * 169 ≤ 1 + p' + p' ^ 2 := le_trans (Nat.mul_le_mul_left _ hq2) hle
  by_contra hc
  rw [not_le] at hc
  nlinarith

/-- The abundancy `σ(s^2)/s^2` of an exact square, as a rational function of `s`. -/
private def sqAb (s : ℕ) : ℚ := ((s : ℚ) ^ 2 + s + 1) / s ^ 2

private theorem step_le {a : ℕ} (ha : 5 ≤ a) :
    sqAb a * (1 + 2 / ((13 * a : ℕ) : ℚ)) ≤ 1 + 2 / (a : ℚ) := by
  have ha' : (5 : ℚ) ≤ a := by exact_mod_cast ha
  unfold sqAb
  push_cast
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h0 : (0 : ℚ) < a := by linarith
  field_simp
  nlinarith [mul_pos h0 h0]

/-- A finite set of integers `≥ m ≥ 5`, pairwise separated by a factor 13, has
`∏ σ(s^2)/s^2 ≤ 1 + 2/m`. -/
private theorem prod_sqAb_le (S : Finset ℕ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x < y → 13 * x ≤ y) :
    ∀ m : ℕ, 5 ≤ m → (∀ x ∈ S, m ≤ x) → ∏ x ∈ S, sqAb x ≤ 1 + 2 / (m : ℚ) := by
  induction S using Finset.induction_on_min with
  | empty => intro m hm _; simp; positivity
  | insert a s ha ih =>
    intro m hm hle
    have hsep' : ∀ x ∈ s, ∀ y ∈ s, x < y → 13 * x ≤ y := fun x hx y hy hxy =>
      hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have ham : m ≤ a := hle a (Finset.mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.prod_insert has]
    have hs := ih hsep' (13 * a) (by omega) fun x hx =>
      hsep a (Finset.mem_insert_self a s) x (Finset.mem_insert_of_mem hx) (ha x hx)
    have ham' : (m : ℚ) ≤ a := by exact_mod_cast ham
    have hm' : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
    have hpos : 0 ≤ sqAb a := by unfold sqAb; positivity
    calc _ ≤ sqAb a * (1 + 2 / ((13 * a : ℕ) : ℚ)) := mul_le_mul_of_nonneg_left hs hpos
      _ ≤ 1 + 2 / (a : ℚ) := step_le (by omega)
      _ ≤ 1 + 2 / (m : ℚ) := by gcongr

private theorem abundancy_sq {p : ℕ} (hp : p.Prime) : abundancy (p ^ 2) = sqAb p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [abundancy_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sqAb]
  field_simp
  ring

private theorem abundancy_nonneg' (n : ℕ) : 0 ≤ abundancy n := by
  unfold abundancy; positivity

/-! ## Pure squares -/

/-- A pure square in an odd perfect number with `3 ∤ N` is at least 59. -/
private theorem fiftynine_le {N p q a : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) (hq12 : q % 12 = 1)
    (hq : q.Prime) (hp : p.Prime) (he : N.factorization p = 2)
    (hpa : 1 + p + p ^ 2 = q ^ a) : 59 ≤ p := by
  have hp3 := OPNThreeFree.source_mod_three h.perfect h3 hp he
  have hpN : p ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp (h.odd.of_dvd_nat hpN)
  have hq4 : q ^ a % 4 = 1 := by
    simp [Nat.pow_mod, show q % 4 = 1 by omega]
  have hp4 : p % 4 = 3 := by
    rw [← hpa] at hq4
    have : (1 + p + p ^ 2) % 4 = (1 + p % 4 + (p % 4) ^ 2) % 4 := by
      simp [Nat.add_mod, Nat.pow_mod]
    rw [this] at hq4
    have : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : p % 4 <;> omega
  by_contra hlt
  push Not at hlt
  -- a prime divisor of `1 + p + p ^ 2 = q ^ a` is `q`
  have key : ∀ d, d.Prime → d ∣ 1 + p + p ^ 2 → d = q := fun d hd hdd =>
    (Nat.prime_dvd_prime_iff_eq hd hq).mp (hd.dvd_of_dvd_pow (hpa ▸ hdd))
  interval_cases p <;> try omega
  · have := key 7 (by norm_num) (by norm_num); omega
  · have := key 7 (by norm_num) (by norm_num); omega
  · norm_num at hp
  · have := key 37 (by norm_num) (by norm_num)
    have := key 61 (by norm_num) (by norm_num)
    omega

private theorem div_pred_le_of_le {p m : ℕ} (hm : 2 ≤ m) (hp : m ≤ p) :
    (p : ℚ) / (p - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hp' : (m : ℚ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Pure squares carry little abundancy.** Let `N` be an odd perfect number with special
prime `q` and `3 ∤ N`, and let `Y` be any set containing every prime factor `p ≠ q` that is
not a pure square (a pure square has `p ^ 2 ∥ N` and `σ(p ^ 2)` a power of `q`). Then the
prime factors of `N` in `Y` other than `q` satisfy `∏ p/(p-1) > 1416/793 ≈ 1.7856`. -/
theorem prod_nonpure_gt_of_not_three_dvd {N q : ℕ} {Y : Finset ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (h3 : ¬ 3 ∣ N)
    (hY : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ Y →
      N.factorization p = 2 ∧ ∃ a, σ 1 (p ^ 2) = q ^ a) :
    (1416 / 793 : ℚ) < ∏ p ∈ (N.primeFactors.erase q).filter (· ∈ Y), (p : ℚ) / (p - 1) := by
  have hN0 := h.ne_zero
  have hqT : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos hodd.pos.ne', hN0⟩
  have hq12 := special_mod_twelve h h3 hq hodd
  have hq13 : 13 ≤ q := by have := hq.two_le; omega
  have hab := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  rw [abundancy_eq_prod_primeFactors hN0, ← Finset.mul_prod_erase _ _ hqT,
    ← Finset.prod_filter_mul_prod_filter_not (N.primeFactors.erase q) (· ∈ Y)] at hab
  set X := (N.primeFactors.erase q).filter (fun p => ¬ p ∈ Y) with hXdef
  set Z := (N.primeFactors.erase q).filter (· ∈ Y) with hZdef
  have hmemX : ∀ {x}, x ∈ X → x.Prime ∧ N.factorization x = 2 ∧ ∃ a, σ 1 (x ^ 2) = q ^ a := by
    intro x hx
    rw [hXdef, Finset.mem_filter, Finset.mem_erase] at hx
    exact ⟨Nat.prime_of_mem_primeFactors hx.1.2, hY x hx.1.2 hx.1.1 hx.2⟩
  have hshape : ∀ x ∈ X, ∃ a, Odd a ∧ 1 + x + x ^ 2 = q ^ a := by
    intro x hx
    obtain ⟨hx', -, a, ha⟩ := hmemX hx
    rw [sigma_sq_eq hx'] at ha
    exact ⟨a, odd_exp_of_eq_pow hx'.pos ha, ha⟩
  have hX : ∏ x ∈ X, abundancy (x ^ N.factorization x) ≤ 61 / 59 := by
    have heq : ∏ x ∈ X, abundancy (x ^ N.factorization x) = ∏ x ∈ X, sqAb x := by
      refine Finset.prod_congr rfl fun x hx => ?_
      obtain ⟨hx', he, -⟩ := hmemX hx
      rw [he, abundancy_sq hx']
    rw [heq]
    have hsep : ∀ x ∈ X, ∀ y ∈ X, x < y → 13 * x ≤ y := by
      intro x hx y hy hxy
      obtain ⟨a, ha, hxa⟩ := hshape x hx
      obtain ⟨b, hb, hyb⟩ := hshape y hy
      exact sep_thirteen hq13 ha hb hxa hyb hxy
    have := prod_sqAb_le X hsep 59 (by norm_num) fun x hx => by
      obtain ⟨hx', he, -⟩ := hmemX hx
      obtain ⟨a, -, ha⟩ := hshape x hx
      exact fiftynine_le h h3 hq12 hq hx' he ha
    norm_num at this ⊢
    linarith
  have hZ : ∏ x ∈ Z, abundancy (x ^ N.factorization x) ≤ ∏ x ∈ Z, (x : ℚ) / (x - 1) :=
    Finset.prod_le_prod₀ (fun _ _ => abundancy_nonneg' _) fun x hx =>
      (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_filter x hx))) _).le
  have hX0 : 0 ≤ ∏ x ∈ X, abundancy (x ^ N.factorization x) :=
    Finset.prod_nonneg fun _ _ => abundancy_nonneg' _
  have hZ0 : 0 ≤ ∏ x ∈ Z, abundancy (x ^ N.factorization x) :=
    Finset.prod_nonneg fun _ _ => abundancy_nonneg' _
  have hqlt := abundancy_prime_pow_lt hq (N.factorization q)
  have hqle := div_pred_le_of_le (by norm_num) hq13
  have hA0 := abundancy_nonneg' (q ^ N.factorization q)
  norm_num at hqle
  set A := abundancy (q ^ N.factorization q)
  set x := ∏ x ∈ X, abundancy (x ^ N.factorization x)
  set z := ∏ x ∈ Z, abundancy (x ^ N.factorization x)
  have hxz : 0 < x * z := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hA0 hX0]
  have h1 : 2 < 13 / 12 * (x * z) := by nlinarith
  have h2 : x * z ≤ 61 / 59 * ∏ x ∈ Z, (x : ℚ) / (x - 1) := mul_le_mul hX hZ hZ0 (by norm_num)
  linarith

/-! ## Choosing the largest products -/

/-- Exchange bound: if `|T| ≤ |L|`, every factor of `T` outside `L` is at most `c ≥ 1`, and
every factor of `L` is at least `c`, then `∏_T f ≤ ∏_L f`. -/
private theorem prod_le_of_card_le {T L : Finset ℕ} (f : ℕ → ℚ) (c : ℚ) (hc : 1 ≤ c)
    (hT0 : ∀ t ∈ T, 0 ≤ f t) (hTc : ∀ t ∈ T, t ∉ L → f t ≤ c) (hLc : ∀ l ∈ L, c ≤ f l)
    (hcard : T.card ≤ L.card) : ∏ t ∈ T, f t ≤ ∏ l ∈ L, f l := by
  rw [← Finset.prod_inter_mul_prod_sdiff T L f, ← Finset.prod_inter_mul_prod_sdiff L T f,
    Finset.inter_comm L T]
  have hI0 : 0 ≤ ∏ t ∈ T ∩ L, f t :=
    Finset.prod_nonneg fun t ht => hT0 t (Finset.mem_inter.mp ht).1
  apply mul_le_mul_of_nonneg_left _ hI0
  have hc1 : (T \ L).card ≤ (L \ T).card := by
    have h1 := Finset.card_sdiff_add_card_inter T L
    have h2 := Finset.card_sdiff_add_card_inter L T
    rw [Finset.inter_comm] at h2
    omega
  calc ∏ t ∈ T \ L, f t ≤ ∏ _t ∈ T \ L, c :=
        Finset.prod_le_prod₀ (fun t ht => hT0 t (Finset.mem_sdiff.mp ht).1)
          fun t ht => hTc t (Finset.mem_sdiff.mp ht).1 (Finset.mem_sdiff.mp ht).2
    _ = c ^ (T \ L).card := Finset.prod_const c
    _ ≤ c ^ (L \ T).card := pow_le_pow_right₀ hc hc1
    _ = ∏ _l ∈ L \ T, c := (Finset.prod_const c).symm
    _ ≤ ∏ l ∈ L \ T, f l :=
        Finset.prod_le_prod₀ (fun _ _ => by linarith) fun l hl => hLc l (Finset.mem_sdiff.mp hl).1

/-- In an odd perfect number with `3 ∤ N`, every prime factor is at least 5. -/
private theorem five_le_of_mem {N p : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hp : p ∈ N.primeFactors) : 5 ≤ p := by
  obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp hp
  by_contra hc
  interval_cases p
  · exact absurd hpp (by norm_num)
  · exact absurd hpp (by norm_num)
  · exact h.not_two_dvd hpN
  · exact h3 hpN
  · exact absurd hpp (by norm_num)

/-- Ordinary primes outside `E` are pure squares when no prime of `E` divides their divisor
sums. -/
private theorem pure_of_ordinary {N q : ℕ} {E : Finset ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → N.factorization p = 2)
    (hE : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → ∀ d ∈ E, d.Prime → ¬ d ∣ σ 1 (p ^ 2)) :
    ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E →
      N.factorization p = 2 ∧ ∃ a, σ 1 (p ^ 2) = q ^ a := by
  intro p hp hpq hpE
  have he := hsq p hp hpq hpE
  have hp' := Nat.prime_of_mem_primeFactors hp
  refine ⟨he, ?_⟩
  have key : ∀ {d}, Nat.Prime d → d ∣ σ 1 (p ^ 2) → d = q := by
    intro d hd hdd
    obtain ⟨-, hdN, -, -, hd2⟩ := OPNThreeFree.exact_square_transfer h.perfect h3 hp' he hd hdd
    by_contra hdq
    have hdE : d ∉ E := fun hm => hE p hp hpq hpE d hm hd hdd
    exact hd2 (hsq d (Nat.mem_primeFactors.mpr ⟨hd, hdN, h.ne_zero⟩) hdq hdE)
  have hne : σ 1 (p ^ 2) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hp'.ne_zero)).ne'
  exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hne key⟩

/-- **Twelve exceptions `≡ 2 (mod 3)`.** Let `N` be an odd perfect number with special prime
`q`. If every prime factor other than `q` has exponent exactly 2, except for the primes of a
set `E` of at most twelve numbers that are all `≡ 2 (mod 3)`, then `3 ∣ N`. -/
theorem three_dvd_of_exceptions_mod_three {N q : ℕ} {E : Finset ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : E.card ≤ 12)
    (hE3 : ∀ r ∈ E, r % 3 = 2)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → N.factorization p = 2) : 3 ∣ N := by
  by_contra h3
  have hpure := pure_of_ordinary h h3 hsq fun p hp hpq hpE d hd hdp hdd => by
    have := (OPNThreeFree.exact_square_transfer h.perfect h3 (Nat.prime_of_mem_primeFactors hp)
      (hsq p hp hpq hpE) hdp hdd).2.2.2.1
    have := hE3 d hd
    omega
  have hgt := prod_nonpure_gt_of_not_three_dvd h hq hodd h3 hpure
  set Z := (N.primeFactors.erase q).filter (· ∈ E)
  have hZmem : ∀ t ∈ Z, t.Prime ∧ 5 ≤ t ∧ t % 3 = 2 := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_erase] at ht
    exact ⟨Nat.prime_of_mem_primeFactors ht.1.2, five_le_of_mem h h3 ht.1.2, hE3 t ht.2⟩
  have hZcard : Z.card ≤ 12 :=
    (Finset.card_le_card fun t ht => (Finset.mem_filter.mp ht).2).trans hE
  have hle := prod_le_of_card_le (T := Z) (L := {5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89})
    (fun t => (t : ℚ) / (t - 1)) (101 / 100) (by norm_num)
    (fun t ht => by
      have := (hZmem t ht).2.1
      have : (5 : ℚ) ≤ t := by exact_mod_cast this
      exact div_nonneg (by linarith) (by linarith))
    (fun t ht htL => by
      obtain ⟨htp, ht5, ht3⟩ := hZmem t ht
      have h101 : 101 ≤ t := by
        by_contra hc
        push Not at hc
        interval_cases t <;> first | omega | (norm_num at htp; done) | simp at htL
      have := div_pred_le_of_le (by norm_num) h101
      norm_num at this ⊢
      exact this)
    (fun l hl => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
    (by simpa using hZcard)
  have hval : ∏ l ∈ ({5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89} : Finset ℕ),
      (l : ℚ) / (l - 1) < 1416 / 793 := by
    norm_num [Finset.prod_insert, Finset.prod_singleton]
  linarith

/-- **Four exceptions that are not targets.** Let `N` be an odd perfect number with special
prime `q`. If every prime factor other than `q` has exponent exactly 2, except for the primes
of a set `E` with at most four elements, and no prime of `E` divides `σ(p ^ 2)` for any of
the exponent two primes `p ∉ E`, `p ≠ q`, then `3 ∣ N`. With `E = {r}` this is the first
case of `three_dvd_of_one_exception`. -/
theorem three_dvd_of_exceptions_not_target {N q : ℕ} {E : Finset ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : E.card ≤ 4)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → N.factorization p = 2)
    (hT : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → ∀ r ∈ E, r.Prime → ¬ r ∣ σ 1 (p ^ 2)) : 3 ∣ N := by
  by_contra h3
  have hpure := pure_of_ordinary h h3 hsq fun p hp hpq hpE d hd hdp => hT p hp hpq hpE d hd hdp
  have hgt := prod_nonpure_gt_of_not_three_dvd h hq hodd h3 hpure
  set Z := (N.primeFactors.erase q).filter (· ∈ E)
  have hZmem : ∀ t ∈ Z, t.Prime ∧ 5 ≤ t := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_erase] at ht
    exact ⟨Nat.prime_of_mem_primeFactors ht.1.2, five_le_of_mem h h3 ht.1.2⟩
  have hZcard : Z.card ≤ 4 :=
    (Finset.card_le_card fun t ht => (Finset.mem_filter.mp ht).2).trans hE
  have hle := prod_le_of_card_le (T := Z) (L := {5, 7, 11, 13})
    (fun t => (t : ℚ) / (t - 1)) (17 / 16) (by norm_num)
    (fun t ht => by
      have := (hZmem t ht).2
      have : (5 : ℚ) ≤ t := by exact_mod_cast this
      exact div_nonneg (by linarith) (by linarith))
    (fun t ht htL => by
      obtain ⟨htp, ht5⟩ := hZmem t ht
      have h17 : 17 ≤ t := by
        by_contra hc
        push Not at hc
        interval_cases t <;> first | omega | (norm_num at htp; done) | simp at htL
      have := div_pred_le_of_le (by norm_num) h17
      norm_num at this ⊢
      exact this)
    (fun l hl => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl | rfl <;> norm_num)
    (by simpa using hZcard)
  have hval : ∏ l ∈ ({5, 7, 11, 13} : Finset ℕ), (l : ℚ) / (l - 1) < 1416 / 793 := by
    norm_num [Finset.prod_insert, Finset.prod_singleton]
  linarith

/-! ## Large prime factors -/

/-- Exponent count: over any set `S` of prime factors, `2 |S| ≤ ∑ e_p + 1`, since at most
one exponent is odd and every exponent is positive. -/
private theorem two_mul_card_le_sum {N : ℕ} {S : Finset ℕ} (h : OddPerfect N)
    (hS : S ⊆ N.primeFactors) : 2 * S.card ≤ ∑ x ∈ S, N.factorization x + 1 := by
  obtain ⟨q, -, -, -, -, hev⟩ := exists_special_prime h
  have hpt : ∀ x ∈ S, 2 ≤ N.factorization x + if x = q then 1 else 0 := by
    intro x hx
    have hx' := Nat.prime_of_mem_primeFactors (hS hx)
    have h1 : 1 ≤ N.factorization x :=
      (hx'.dvd_iff_one_le_factorization h.ne_zero).mp (Nat.dvd_of_mem_primeFactors (hS hx))
    split_ifs with hxq
    · omega
    · obtain ⟨j, hj⟩ := hev x hx' hxq
      omega
  have := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at this
  simp only [Finset.sum_const, smul_eq_mul] at this
  split_ifs at this <;> omega

/-- With a prime factor of exponent at least four: `2 |S| + 2 ≤ ∑ e_p + 1` over all prime
factors. -/
private theorem two_mul_card_add_two_le_sum {N : ℕ} (h : OddPerfect N) :
    2 * N.primeFactors.card + 2 ≤ ∑ x ∈ N.primeFactors, N.factorization x + 1 := by
  obtain ⟨q, hq, -, -, hk, hev⟩ := exists_special_prime h
  obtain ⟨r, hr, hre, hr4⟩ := exists_even_exponent_ge_four h
  have hrq : r ≠ q := by
    rintro rfl
    obtain ⟨j, hj⟩ := hre
    omega
  have hpt : ∀ x ∈ N.primeFactors, 2 + (if x = r then 2 else 0) ≤
      N.factorization x + if x = q then 1 else 0 := by
    intro x hx
    have hx' := Nat.prime_of_mem_primeFactors hx
    have h1 : 1 ≤ N.factorization x :=
      (hx'.dvd_iff_one_le_factorization h.ne_zero).mp (Nat.dvd_of_mem_primeFactors hx)
    by_cases hxr : x = r
    · subst hxr
      simp [hrq]
      omega
    · rw [if_neg hxr]
      split_ifs with hxq
      · omega
      · obtain ⟨j, hj⟩ := hev x hx' hxq
        omega
  have := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq'] at this
  simp only [Finset.sum_const, smul_eq_mul, if_pos hr] at this
  split_ifs at this <;> omega

/-- The components over `S` have product at least `p ^ (∑ e)` when all of `S` is `≥ p`. -/
private theorem pow_sum_le_prod {N p : ℕ} {S : Finset ℕ} (hp : ∀ r ∈ S, p ≤ r) :
    p ^ (∑ x ∈ S, N.factorization x) ≤ ∏ x ∈ S, x ^ N.factorization x := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' fun x hx => Nat.pow_le_pow_left (hp x hx) _

/-- **Large prime factors.** Let `N` be an odd perfect number and `S` a set of prime factors,
all at least `p`, that is not the whole set of prime factors. Then `2 p ^ (2 |S|) < 3 N`. -/
theorem two_mul_pow_lt_three_mul {N p : ℕ} {S : Finset ℕ} (h : OddPerfect N)
    (hS : S ⊆ N.primeFactors) (hp : ∀ r ∈ S, p ≤ r) (hne : (N.primeFactors \ S).Nonempty) :
    2 * p ^ (2 * S.card) < 3 * N := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · have := h.pos
    simp
    omega
  obtain ⟨l, hl, r, hr, hedge⟩ := exists_sigmaEdge_crossing h.perfect hS hSne hne
  obtain ⟨hlN, -, hrd⟩ := hedge
  have hlS : l ∉ S := (Finset.mem_sdiff.mp hl).2
  have hl' := Nat.prime_of_mem_primeFactors hlN
  set b := N.factorization l
  set M := ∏ x ∈ S, x ^ N.factorization x with hMdef
  have hl3 : 3 ≤ l := by
    have := hl'.two_le
    have hl2 : l ≠ 2 := by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hlN)
    omega
  -- the component outside `S`
  have hσpos : 0 < σ 1 (l ^ b) := sigma_pos 1 _ (pow_ne_zero _ hl'.ne_zero)
  have hrσ : r ≤ σ 1 (l ^ b) := Nat.le_of_dvd hσpos hrd
  have hσ3 : 2 * σ 1 (l ^ b) < 3 * l ^ b := by
    have h1 := abundancy_prime_pow_lt hl' b
    have hl3' : (3 : ℚ) ≤ l := by exact_mod_cast hl3
    have h2 : (l : ℚ) / (l - 1) ≤ 3 / 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    unfold abundancy at h1
    have hpos : (0 : ℚ) < ((l ^ b : ℕ) : ℚ) := by
      have : 0 < l ^ b := pow_pos hl'.pos _
      exact_mod_cast this
    rw [div_lt_iff₀ hpos] at h1
    have : ((2 * σ 1 (l ^ b) : ℕ) : ℚ) < ((3 * l ^ b : ℕ) : ℚ) := by
      push_cast at h1 ⊢
      have h3 : (l : ℚ) / (l - 1) * (l : ℚ) ^ b ≤ 3 / 2 * (l : ℚ) ^ b :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      linarith
    exact_mod_cast this
  -- the components inside `S`
  have hsum := two_mul_card_le_sum h hS
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hM : p ^ (2 * S.card - 1) ≤ M := by
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [zero_pow (by omega)]
      exact Nat.zero_le _
    · exact (Nat.pow_le_pow_right hp0 (by omega)).trans (pow_sum_le_prod hp)
  have hM0 : 0 < M :=
    Finset.prod_pos fun x hx => pow_pos (Nat.prime_of_mem_primeFactors (hS hx)).pos _
  -- `M * l ^ b` divides `N`
  have hMd : M ∣ N := by
    have := Finset.prod_dvd_prod_of_subset S N.primeFactors (fun x => x ^ N.factorization x) hS
    exact this.trans (dvd_of_eq (Nat.prod_primeFactors_pow_factorization h.ne_zero).symm)
  have hcop : Nat.Coprime M (l ^ b) :=
    Nat.Coprime.prod_left fun x hx => Nat.coprime_pow_primes _ _
      (Nat.prime_of_mem_primeFactors (hS hx)) hl' fun hxl => hlS (hxl ▸ hx)
  have hle := Nat.le_of_dvd h.pos (hcop.mul_dvd_of_dvd_of_dvd hMd (Nat.ordProj_dvd N l))
  have hpr : p ≤ σ 1 (l ^ b) := (hp r hr).trans hrσ
  calc 2 * p ^ (2 * S.card) = 2 * (p ^ (2 * S.card - 1) * p) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    _ ≤ 2 * (M * σ 1 (l ^ b)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hM hpr)
    _ = M * (2 * σ 1 (l ^ b)) := by ring
    _ < M * (3 * l ^ b) := Nat.mul_lt_mul_of_pos_left hσ3 hM0
    _ = 3 * (M * l ^ b) := by ring
    _ ≤ 3 * N := Nat.mul_le_mul_left _ hle

/-- **Bibby, Vyncke and Zelinsky with constant `3/2`.** If an odd perfect number has a prime
factor smaller than `p`, and `j` prime factors are at least `p`, then `2 p ^ (2 j) < 3 N`. -/
theorem two_mul_pow_card_ge_lt_three_mul {N p p₀ : ℕ} (h : OddPerfect N)
    (hp₀ : p₀ ∈ N.primeFactors) (hlt : p₀ < p) :
    2 * p ^ (2 * (N.primeFactors.filter (p ≤ ·)).card) < 3 * N :=
  two_mul_pow_lt_three_mul h (Finset.filter_subset _ _) (fun r hr => (Finset.mem_filter.mp hr).2)
    ⟨p₀, Finset.mem_sdiff.mpr ⟨hp₀, fun hm => by
      have := (Finset.mem_filter.mp hm).2
      omega⟩⟩

/-- **The smallest prime factor.** If every prime factor of an odd perfect number `N` is at
least `p`, then `p ^ (2 ω(N) + 1) ≤ N`. -/
theorem pow_two_mul_card_add_one_le {N p : ℕ} (h : OddPerfect N)
    (hp : ∀ r ∈ N.primeFactors, p ≤ r) : p ^ (2 * N.primeFactors.card + 1) ≤ N := by
  have hsum := two_mul_card_add_two_le_sum h
  have hprod := pow_sum_le_prod (N := N) hp
  have hN := Nat.prod_primeFactors_pow_factorization h.ne_zero
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [zero_pow (by omega)]
    exact Nat.zero_le _
  · exact ((Nat.pow_le_pow_right hp0 (by omega)).trans hprod).trans_eq hN.symm

end OddPerfect

#print axioms OddPerfect.prod_nonpure_gt_of_not_three_dvd
#print axioms OddPerfect.three_dvd_of_exceptions_mod_three
#print axioms OddPerfect.three_dvd_of_exceptions_not_target
#print axioms OddPerfect.two_mul_pow_lt_three_mul
#print axioms OddPerfect.two_mul_pow_card_ge_lt_three_mul
#print axioms OddPerfect.pow_two_mul_card_add_one_le
