import OddPerfect.Abundancy
import OddPerfect.SpecialPrime
import OddPerfect.ExponentCap
import OddPerfect.Phi3
import OddPerfect.Valuation
import OddPerfect.Seed.Example
import Mathlib.Tactic.NormNum.Prime

/-!
# Thirty one exceptions that are `2 (mod 3)` force `3 ∣ N`

Let `N` be an odd perfect number with special prime `q`, and call a prime factor `p ≠ q`
exceptional when `3 ∤ e_p + 1`. If at most 31 primes are exceptional (more generally: every
prime factor `p ≠ q` outside a set `E` with at most 31 elements has `3 ∣ e_p + 1`) and every
member of `E` is `≡ 2 (mod 3)`, then `3 ∣ N`. This extends
`three_dvd_of_thirtyone_exceptions_mod_three_of_ne` in `ExceptionCount.lean` in two ways: the
other exponents need only satisfy `3 ∣ e_p + 1` instead of `e_p = 2`, and the case `q = 109`
is included. The small helpers of `ExceptionCount.lean` are private there, so the ones needed
are proved again here.

Assume `3 ∤ N`. Every prime factor other than `q` is `≡ 2 (mod 3)`. A prime `p ∉ E ∪ {q}` has
`F(p) = p ^ 2 + p + 1 ∣ σ(p ^ e_p)`, and every prime factor of `F(p)` is `≡ 1 (mod 3)` and
divides `N`, hence equals `q`: `F(p) = q ^ a` with `a` odd. Two such primes are separated by a
factor 13, so their factors `p/(p-1)` multiply to at most `12 b/(12 b - 13)` when all are at
least `b`. For `q ≠ 109` the comparison of `ExceptionCount.lean` then goes through with this
weaker tail bound (`b = 3000` for `229 ≤ q < 3541`, `b = 251` for `q ≥ 3541`).

For `q = 109`: `F(p) mod 5 ∈ {1, 2, 3}` while `109 ^ a ≡ 4 (mod 5)` for odd `a`, so every prime
factor other than `q` lies in `E`. The abundancy then allows at most one of them above 660.
The prime `5` divides `N` (as `5 ∣ 110`) with exponent at least 4, the special component
supplies exactly one factor 5 (a factor `5 ∣ e_q + 1` would bring `31 ∣ Φ_5(109)`), and every
other sender into `5` is `≡ 1 (mod 5)` and supplies `v_5(e_p + 1)`. A finite check of the 15
primes `p ≤ 660` with `p ≡ 2 (mod 3)`, `p ≡ 1 (mod 5)` shows that at most one of them supplies a
factor 5, at most one each, and only together with a specific large prime that then supplies
none; a large prime `x` supplies at most two, because `125 ∣ e_x + 1` would give
`Φ_125(x) = 5 · 251 ^ a`, impossible modulo 3 (forcing `a` odd) and modulo 8.

Whether these results are new was not verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Elementary facts -/

private theorem tf_sigma_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]

private theorem tf_sep {p p' q a a' : ℕ} (hq : 13 ≤ q) (ha : Odd a) (ha' : Odd a')
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

/-- The tail bound `T(m) = 12 m/(12 m - 13)`. -/
private def tfT (m : ℕ) : ℚ := 12 * m / (12 * m - 13)

private theorem tfT_one_le {m : ℕ} (hm : 2 ≤ m) : 1 ≤ tfT m := by
  have : (2 : ℚ) ≤ m := by exact_mod_cast hm
  unfold tfT
  rw [le_div_iff₀ (by linarith)]
  linarith

private theorem tfT_anti {m a : ℕ} (hm : 2 ≤ m) (ha : m ≤ a) : tfT a ≤ tfT m := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have ha' : (m : ℚ) ≤ a := by exact_mod_cast ha
  unfold tfT
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private theorem tf_step {a : ℕ} (ha : 2 ≤ a) :
    (a : ℚ) / (a - 1) * tfT (13 * a) ≤ tfT a := by
  have ha' : (2 : ℚ) ≤ a := by exact_mod_cast ha
  unfold tfT
  push_cast
  rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith

private theorem tf_prod_le (S : Finset ℕ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x < y → 13 * x ≤ y) :
    ∀ m : ℕ, 2 ≤ m → (∀ x ∈ S, m ≤ x) → ∏ x ∈ S, (x : ℚ) / (x - 1) ≤ tfT m := by
  induction S using Finset.induction_on_min with
  | empty => intro m hm _; simpa using tfT_one_le hm
  | insert a s ha ih =>
    intro m hm hle
    have hsep' : ∀ x ∈ s, ∀ y ∈ s, x < y → 13 * x ≤ y := fun x hx y hy hxy =>
      hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have ham : m ≤ a := hle a (Finset.mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.prod_insert has]
    have hs := ih hsep' (13 * a) (by omega) fun x hx =>
      hsep a (Finset.mem_insert_self a s) x (Finset.mem_insert_of_mem hx) (ha x hx)
    have ha' : (2 : ℚ) ≤ a := by exact_mod_cast (le_trans hm ham)
    have hpos : 0 ≤ (a : ℚ) / (a - 1) := div_nonneg (by linarith) (by linarith)
    calc _ ≤ (a : ℚ) / (a - 1) * tfT (13 * a) := mul_le_mul_of_nonneg_left hs hpos
      _ ≤ tfT a := tf_step (by omega)
      _ ≤ tfT m := tfT_anti hm ham

private theorem tf_div_pred_le {p m : ℕ} (hm : 2 ≤ m) (hp : m ≤ p) :
    (p : ℚ) / (p - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hp' : (m : ℚ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Exchange bound for products over sets of bounded size. -/
private theorem tf_prod_le_of_card_le {T L : Finset ℕ} (f : ℕ → ℚ) (c : ℚ) (hc : 1 ≤ c)
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

private theorem tf_five_le {N p : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hp : p ∈ N.primeFactors) : 5 ≤ p := by
  obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp hp
  by_contra hc
  interval_cases p
  · exact absurd hpp (by norm_num)
  · exact absurd hpp (by norm_num)
  · exact h.not_two_dvd hpN
  · exact h3 hpN
  · exact absurd hpp (by norm_num)

private theorem tf_abund_pos {n : ℕ} (hn : n ≠ 0) : 0 < abundancy n := by
  unfold abundancy
  have := sigma_pos 1 n hn
  exact div_pos (by exact_mod_cast this) (by exact_mod_cast Nat.pos_of_ne_zero hn)

/-! ## Envelopes -/

/-- The 29 smallest primes at least 5 that are `≡ 2 (mod 3)`. -/
private def tfL29 : Finset ℕ :=
  {5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89, 101, 107, 113, 131, 137, 149, 167, 173, 179,
    191, 197, 227, 233, 239, 251, 257, 263}

/-- The 31 smallest primes at least 5 that are `≡ 2 (mod 3)`. -/
private def tfL31 : Finset ℕ := insert 269 (insert 281 tfL29)

private theorem tfL29_card : tfL29.card = 29 := by decide

private theorem tfL31_card : tfL31.card = 31 := by decide

private theorem tfL29_val :
    ∏ l ∈ tfL29, (l : ℚ) / (l - 1) =
      1812498586146619514269851608750058738331 / 917440951333825631705850970112000000000 := by
  simp only [tfL29]
  norm_num [Finset.prod_insert, Finset.prod_singleton]

private theorem tfL31_lt : ∏ l ∈ tfL31, (l : ℚ) / (l - 1) < 19901 / 10000 := by
  simp only [tfL31, tfL29]
  norm_num [Finset.prod_insert, Finset.prod_singleton]

set_option maxHeartbeats 4000000 in
/-- A prime `5 ≤ t < 293` with `t ≡ 2 (mod 3)` lies in the 31 element envelope. -/
private theorem mem_tfL31 {t : ℕ} (htp : t.Prime) (ht5 : 5 ≤ t) (ht3 : t % 3 = 2)
    (ht : t < 293) : t ∈ tfL31 := by
  interval_cases t <;> first | omega | decide | (norm_num at htp; done)

private theorem mem_tfL29 {t : ℕ} (htp : t.Prime) (ht5 : 5 ≤ t) (ht3 : t % 3 = 2)
    (ht : t < 269) : t ∈ tfL29 := by
  have := mem_tfL31 htp ht5 ht3 (by omega)
  simp only [tfL31, Finset.mem_insert] at this
  rcases this with h | h | h
  · omega
  · omega
  · exact h

private theorem tfL_ge {L : Finset ℕ} {c : ℕ} (hL : ∀ l ∈ L, 2 ≤ l ∧ l ≤ c) :
    ∀ l ∈ L, (c : ℚ) / (c - 1) ≤ (l : ℚ) / (l - 1) := fun l hl =>
  tf_div_pred_le (hL l hl).1 (hL l hl).2

private theorem tfL31_bd : ∀ l ∈ tfL31, 2 ≤ l ∧ l ≤ 293 := by decide

private theorem tfL29_bd : ∀ l ∈ tfL29, 2 ≤ l ∧ l ≤ 269 := by decide

/-! ## Consequences of `3 ∤ N` -/

/-- Under the hypotheses, every prime factor other than `q` is `≡ 2 (mod 3)`. -/
private theorem tf_res {N q : ℕ} {E : Finset ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hE3 : ∀ r ∈ E, r % 3 = 2)
    (h3m : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → 3 ∣ N.factorization p + 1) :
    ∀ r, r.Prime → r ∣ N → r ≠ q → r % 3 = 2 := by
  intro r hr hrN hrq
  by_cases hrE : r ∈ E
  · exact hE3 r hrE
  have hrP : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩
  have hm := h3m r hrP hrq hrE
  have hr3 : r ≠ 3 := by rintro rfl; exact h3 hrN
  have h0 : r % 3 ≠ 0 := fun h0 =>
    hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp (Nat.dvd_of_mod_eq_zero h0)).symm
  have h1 : r % 3 ≠ 1 := by
    intro h1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hv := padicValNat_three_sigma_prime_pow_of_mod_one hr h1 (N.factorization r)
    have hpos : 1 ≤ padicValNat 3 (N.factorization r + 1) := by
      rw [Nat.padicValNat_def]; exact one_le_padicValNat_of_dvd (by omega) hm
    rw [← hv] at hpos
    exact h3 (OPNStarter.force_prime h.perfect hr rfl Nat.prime_three (by norm_num)
      (dvd_of_one_le_multiplicity (by rw [← Nat.padicValNat_def]; exact hpos)))
  omega

/-- Under `3 ∤ N` with all other prime factors `≡ 2 (mod 3)`, a prime factor `p ≠ q` with
`3 ∣ e_p + 1` has `p ^ 2 + p + 1 = q ^ a` with `a` odd. -/
private theorem tf_pure {N q : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hres : ∀ r, r.Prime → r ∣ N → r ≠ q → r % 3 = 2) :
    ∀ p ∈ N.primeFactors, p ≠ q → 3 ∣ N.factorization p + 1 →
      ∃ a, Odd a ∧ 1 + p + p ^ 2 = q ^ a := by
  intro p hp hpq hm
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hdvd : σ 1 (p ^ 2) ∣ σ 1 (p ^ N.factorization p) :=
    OPNExample.sigma_prime_pow_dvd hp' (show 2 + 1 ∣ _ from hm)
  rw [tf_sigma_sq hp'] at hdvd
  have hphi : phi3 p = 1 + p + p ^ 2 := by unfold phi3; ring
  have key : ∀ d, d.Prime → d ∣ 1 + p + p ^ 2 → d = q := by
    intro d hd hdd
    have hd2 : d ≠ 2 := by
      rintro rfl
      have := phi3_odd p
      rw [hphi] at this
      exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr hdd)
    have hdN := OPNStarter.force_prime h.perfect hp' rfl hd hd2 (hdd.trans hdvd)
    have hd3 : d ≠ 3 := by rintro rfl; exact h3 hdN
    have h1 := prime_dvd_phi3_mod_three hd hd3 (hphi ▸ hdd)
    by_contra hdq
    have := hres d hd hdN hdq
    omega
  have hne : 1 + p + p ^ 2 ≠ 0 := by omega
  have heq := Nat.eq_prime_pow_of_unique_prime_dvd hne (fun hd hdd => key _ hd hdd)
  refine ⟨_, ?_, heq⟩
  rcases Nat.even_or_odd (1 + p + p ^ 2).primeFactorsList.length with ⟨b, hb⟩ | ho
  · exfalso
    apply not_isSquare_phi3 hp'.one_lt.le
    refine ⟨q ^ b, ?_⟩
    rw [hphi, heq, hb, pow_add]
  · exact ho

/-- A prime `p ≡ 2 (mod 3)` with `p ^ 2 + p + 1 = q ^ a`, `q ≡ 1 (mod 12)` prime, is
`≡ 11 (mod 12)` and at least 59. -/
private theorem tf_shape {p q a : ℕ} (hq12 : q % 12 = 1) (hq : q.Prime) (hp : p.Prime)
    (hp3 : p % 3 = 2) (hp2 : p % 2 = 1) (hpa : 1 + p + p ^ 2 = q ^ a) :
    p % 12 = 11 ∧ 59 ≤ p := by
  have hq4 : q ^ a % 4 = 1 := by
    simp [Nat.pow_mod, show q % 4 = 1 by omega]
  have hp4 : p % 4 = 3 := by
    rw [← hpa] at hq4
    have : (1 + p + p ^ 2) % 4 = (1 + p % 4 + (p % 4) ^ 2) % 4 := by
      simp [Nat.add_mod, Nat.pow_mod]
    rw [this] at hq4
    have : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : p % 4 <;> omega
  refine ⟨by omega, ?_⟩
  by_contra hlt
  push Not at hlt
  have key : ∀ d, d.Prime → d ∣ 1 + p + p ^ 2 → d = q := fun d hd hdd =>
    (Nat.prime_dvd_prime_iff_eq hd hq).mp (hd.dvd_of_dvd_pow (hpa ▸ hdd))
  interval_cases p <;> try omega
  · have := key 7 (by norm_num) (by norm_num); omega
  · have := key 7 (by norm_num) (by norm_num); omega
  · norm_num at hp
  · have := key 37 (by norm_num) (by norm_num)
    have := key 61 (by norm_num) (by norm_num)
    omega

/-! ## The core inequality -/

/-- **Core inequality.** If every prime factor `p ≠ q` outside `E` has `p ^ 2 + p + 1 = q ^ a`
with `a` odd and is at least `m ≥ 2`, then `2 < q/(q-1) · T(m) · ∏_Z r/(r-1)` with `Z` the
prime factors in `E` other than `q`. -/
private theorem tf_core {N q m : ℕ} {E : Finset ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hqN : q ∈ N.primeFactors) (hq13 : 13 ≤ q) (hm : 2 ≤ m)
    (hpure : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → ∃ a, Odd a ∧ 1 + p + p ^ 2 = q ^ a)
    (hmin : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → m ≤ p) :
    2 < (q : ℚ) / (q - 1) *
      (tfT m * ∏ p ∈ (N.primeFactors.erase q).filter (· ∈ E), (p : ℚ) / (p - 1)) := by
  have hN0 := h.ne_zero
  have hab := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  rw [abundancy_eq_prod_primeFactors hN0, ← Finset.mul_prod_erase _ _ hqN,
    ← Finset.prod_filter_mul_prod_filter_not (N.primeFactors.erase q) (· ∈ E)] at hab
  set X := (N.primeFactors.erase q).filter (fun p => ¬ p ∈ E) with hXdef
  set Z := (N.primeFactors.erase q).filter (· ∈ E) with hZdef
  have hmemX : ∀ {x}, x ∈ X → x.Prime ∧ m ≤ x ∧ ∃ a, Odd a ∧ 1 + x + x ^ 2 = q ^ a := by
    intro x hx
    rw [hXdef, Finset.mem_filter, Finset.mem_erase] at hx
    exact ⟨Nat.prime_of_mem_primeFactors hx.1.2, hmin x hx.1.2 hx.1.1 hx.2,
      hpure x hx.1.2 hx.1.1 hx.2⟩
  have hPrime : ∀ {x}, x ∈ N.primeFactors.erase q → x.Prime := fun hx =>
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hx)
  have hX : ∏ x ∈ X, abundancy (x ^ N.factorization x) ≤ tfT m := by
    refine le_trans (Finset.prod_le_prod₀ (fun x _ => (tf_abund_pos
      (pow_ne_zero _ (hmemX ‹_›).1.ne_zero)).le) fun x hx =>
      (abundancy_prime_pow_lt (hmemX hx).1 _).le) ?_
    refine tf_prod_le X (fun x hx y hy hxy => ?_) m hm fun x hx => (hmemX hx).2.1
    obtain ⟨-, -, a, ha, hxa⟩ := hmemX hx
    obtain ⟨-, -, b, hb, hyb⟩ := hmemX hy
    exact tf_sep hq13 ha hb hxa hyb hxy
  have hZ : ∏ x ∈ Z, abundancy (x ^ N.factorization x) ≤ ∏ x ∈ Z, (x : ℚ) / (x - 1) :=
    Finset.prod_le_prod₀ (fun x hx => (tf_abund_pos (pow_ne_zero _
      (hPrime (Finset.mem_of_mem_filter x hx)).ne_zero)).le) fun x hx =>
      (abundancy_prime_pow_lt (hPrime (Finset.mem_of_mem_filter x hx)) _).le
  have hX0 : 0 < ∏ x ∈ X, abundancy (x ^ N.factorization x) :=
    Finset.prod_pos fun x hx => tf_abund_pos (pow_ne_zero _ (hmemX hx).1.ne_zero)
  have hZ0 : 0 < ∏ x ∈ Z, abundancy (x ^ N.factorization x) :=
    Finset.prod_pos fun x hx => tf_abund_pos (pow_ne_zero _
      (hPrime (Finset.mem_of_mem_filter x hx)).ne_zero)
  have hqlt := abundancy_prime_pow_lt hq (N.factorization q)
  set A := abundancy (q ^ N.factorization q)
  set x := ∏ x ∈ X, abundancy (x ^ N.factorization x)
  set z := ∏ x ∈ Z, abundancy (x ^ N.factorization x)
  set P := ∏ x ∈ Z, (x : ℚ) / (x - 1)
  have hq' : (13 : ℚ) ≤ q := by exact_mod_cast hq13
  have hzx : z * x ≤ P * tfT m := mul_le_mul hZ hX hX0.le (le_trans hZ0.le hZ)
  have h1 : 2 < (q : ℚ) / (q - 1) * (z * x) := by
    rw [← hab]
    exact mul_lt_mul_of_pos_right hqlt (mul_pos hZ0 hX0)
  have h2 : (q : ℚ) / (q - 1) * (z * x) ≤ (q : ℚ) / (q - 1) * (P * tfT m) :=
    mul_le_mul_of_nonneg_left hzx (div_nonneg (by linarith) (by linarith))
  calc 2 < (q : ℚ) / (q - 1) * (P * tfT m) := lt_of_lt_of_le h1 h2
    _ = (q : ℚ) / (q - 1) * (tfT m * P) := by ring

/-- Turning the core inequality into a contradiction. -/
private theorem tf_finish {A A0 T P P0 : ℚ} (hA : A ≤ A0) (hA0 : 0 ≤ A) (hT : 0 ≤ T)
    (hP0 : 0 ≤ P) (hP : P ≤ P0) (hkey : 2 < A * (T * P)) (hnum : A0 * (T * P0) ≤ 2) :
    False := by
  have := mul_le_mul hA (mul_le_mul_of_nonneg_left hP hT) (mul_nonneg hT hP0) (le_trans hA0 hA)
  linarith

/-- The envelope bound for at most 31 prime factors `≥ 5` that are `≡ 2 (mod 3)`. -/
private theorem tf_env31 {Z : Finset ℕ} (hZ : ∀ t ∈ Z, t.Prime ∧ 5 ≤ t ∧ t % 3 = 2)
    (hcard : Z.card ≤ 31) : ∏ t ∈ Z, (t : ℚ) / (t - 1) ≤ 19901 / 10000 := by
  refine le_trans (tf_prod_le_of_card_le (L := tfL31) (fun t => (t : ℚ) / (t - 1)) (293 / 292)
    (by norm_num) (fun t ht => ?_) (fun t ht htL => ?_) ?_ (by rw [tfL31_card]; exact hcard))
    tfL31_lt.le
  · have : (5 : ℚ) ≤ t := by exact_mod_cast (hZ t ht).2.1
    exact div_nonneg (by linarith) (by linarith)
  · obtain ⟨htp, ht5, ht3⟩ := hZ t ht
    have h293 : 293 ≤ t := by
      by_contra hc
      exact htL (mem_tfL31 htp ht5 ht3 (by omega))
    have := tf_div_pred_le (by norm_num) h293
    norm_num at this ⊢
    exact this
  · have := tfL_ge tfL31_bd
    intro l hl
    have := this l hl
    norm_num at this ⊢
    exact this

/-- The envelope bound for at most 29 prime factors `≥ 5` that are `≡ 2 (mod 3)`. -/
private theorem tf_env29 {Z : Finset ℕ} (hZ : ∀ t ∈ Z, t.Prime ∧ 5 ≤ t ∧ t % 3 = 2)
    (hcard : Z.card ≤ 29) : ∏ t ∈ Z, (t : ℚ) / (t - 1) ≤
      1812498586146619514269851608750058738331 / 917440951333825631705850970112000000000 := by
  rw [← tfL29_val]
  refine tf_prod_le_of_card_le (L := tfL29) (fun t => (t : ℚ) / (t - 1)) (269 / 268)
    (by norm_num) (fun t ht => ?_) (fun t ht htL => ?_) ?_ (by rw [tfL29_card]; exact hcard)
  · have : (5 : ℚ) ≤ t := by exact_mod_cast (hZ t ht).2.1
    exact div_nonneg (by linarith) (by linarith)
  · obtain ⟨htp, ht5, ht3⟩ := hZ t ht
    have h269 : 269 ≤ t := by
      by_contra hc
      exact htL (mem_tfL29 htp ht5 ht3 (by omega))
    have := tf_div_pred_le (by norm_num) h269
    norm_num at this ⊢
    exact this
  · have := tfL_ge tfL29_bd
    intro l hl
    have := this l hl
    norm_num at this ⊢
    exact this

/-! ## The case `q ≠ 109` -/

set_option maxHeartbeats 4000000 in
private theorem tf_ne109 {N q : ℕ} {E : Finset ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : ¬ 3 ∣ N) (hq109 : q ≠ 109) (hE : E.card ≤ 31)
    (hE3 : ∀ r ∈ E, r % 3 = 2)
    (h3m : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → 3 ∣ N.factorization p + 1) : False := by
  have hres := tf_res h h3 hE3 h3m
  have hpure : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → ∃ a, Odd a ∧ 1 + p + p ^ 2 = q ^ a :=
    fun p hp hpq hpE => tf_pure h h3 hres p hp hpq (h3m p hp hpq hpE)
  have hq12 := special_mod_twelve h h3 hq hodd
  have hqN : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos hodd.pos.ne', h.ne_zero⟩
  have hforce : ∀ r, r.Prime → r % 3 = 1 → r ∣ q + 1 → False := by
    intro r hr hr1 hrq
    have hr2 : r ≠ 2 := by rintro rfl; omega
    obtain ⟨hrN, hrq'⟩ := prime_dvd_of_dvd_succ_special h hq hodd hr hr2 hrq
    have := hres r hr hrN hrq'
    omega
  set Z := (N.primeFactors.erase q).filter (· ∈ E)
  have hZmem : ∀ t ∈ Z, t.Prime ∧ 5 ≤ t ∧ t % 3 = 2 := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_erase] at ht
    exact ⟨Nat.prime_of_mem_primeFactors ht.1.2, tf_five_le h h3 ht.1.2, hE3 t ht.2⟩
  have hZcard : Z.card ≤ 31 :=
    (Finset.card_le_card fun t ht => (Finset.mem_filter.mp ht).2).trans hE
  have hle := tf_env31 hZmem hZcard
  have hZ0 : 0 ≤ ∏ t ∈ Z, (t : ℚ) / (t - 1) := Finset.prod_nonneg fun t ht => by
    have : (5 : ℚ) ≤ t := by exact_mod_cast (hZmem t ht).2.1
    exact div_nonneg (by linarith) (by linarith)
  have hpureX : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E →
      p.Prime ∧ p % 12 = 11 ∧ 59 ≤ p ∧ ∃ a, Odd a ∧ 1 + p + p ^ 2 = q ^ a := by
    intro p hp hpq hpE
    have hp' := Nat.prime_of_mem_primeFactors hp
    obtain ⟨a, ha, hpa⟩ := hpure p hp hpq hpE
    have hp2 : p % 2 = 1 := Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
    obtain ⟨h12, h59⟩ := tf_shape hq12 hq hp' (hres p hp' (Nat.dvd_of_mem_primeFactors hp) hpq)
      hp2 hpa
    exact ⟨hp', h12, h59, a, ha, hpa⟩
  have hT0 : ∀ m : ℕ, 2 ≤ m → 0 ≤ tfT m := fun m hm => le_trans zero_le_one (tfT_one_le hm)
  by_cases hq229 : q < 229
  · have := hq.two_le
    interval_cases q <;> try omega
    all_goals first
      | (norm_num at hq; done)
      | (refine hforce 7 ?_ ?_ ?_ <;> norm_num; done)
      | (refine hforce 19 ?_ ?_ ?_ <;> norm_num; done)
      | (refine hforce 31 ?_ ?_ ?_ <;> norm_num; done)
      | (refine hforce 37 ?_ ?_ ?_ <;> norm_num; done)
      | (refine hforce 79 ?_ ?_ ?_ <;> norm_num; done)
      | (refine hforce 97 ?_ ?_ ?_ <;> norm_num; done)
  push Not at hq229
  have hq13 : 13 ≤ q := by omega
  by_cases hqmid : q < 3541
  · have hmin : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → 3000 ≤ p := by
      intro p hp hpq hpE
      obtain ⟨-, -, h59, a, ha, hpa⟩ := hpureX p hp hpq hpE
      have hbig : 3541 ≤ 1 + p + p ^ 2 := by nlinarith
      have ha3 : 3 ≤ a := by
        obtain ⟨j, rfl⟩ := ha
        rcases j with _ | j
        · simp at hpa; omega
        · omega
      have hq3 : 229 ^ 3 ≤ q ^ a :=
        (Nat.pow_le_pow_left hq229 3).trans (Nat.pow_le_pow_right (by omega) ha3)
      by_contra hc
      push Not at hc
      nlinarith
    have hkey := tf_core (m := 3000) h hq hqN hq13 (by norm_num) hpure hmin
    have hq' : (229 : ℚ) ≤ q := by exact_mod_cast hq229
    exact tf_finish (tf_div_pred_le (by norm_num) hq229)
      (div_nonneg (by linarith) (by linarith)) (hT0 _ (by norm_num)) hZ0 hle hkey
      (by norm_num [tfT])
  · push Not at hqmid
    have hmin : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → 251 ≤ p := by
      intro p hp hpq hpE
      obtain ⟨hp', h12, h59, a, ha, hpa⟩ := hpureX p hp hpq hpE
      have key : ∀ d, d.Prime → d ∣ 1 + p + p ^ 2 → d = q := fun d hd hdd =>
        (Nat.prime_dvd_prime_iff_eq hd hq).mp (hd.dvd_of_dvd_pow (hpa ▸ hdd))
      have hone : 1 + p + p ^ 2 < 3541 ^ 2 → q = 1 + p + p ^ 2 := by
        intro hlt
        obtain ⟨j, rfl⟩ := ha
        rcases j with _ | j
        · simp [hpa]
        · exfalso
          have : q ^ 2 ≤ q ^ (2 * (j + 1) + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          have : 3541 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hqmid 2
          omega
      by_contra hc
      push Not at hc
      interval_cases p <;> try omega
      · have := hone (by norm_num)
        subst this
        exact hforce 7 (by norm_num) (by norm_num) (by norm_num)
      · have := hone (by norm_num)
        subst this
        exact hforce 2557 (by norm_num) (by norm_num) (by norm_num)
      · have := key 19 (by norm_num) (by norm_num); omega
      · norm_num at hp'
      · have := key 7 (by norm_num) (by norm_num); omega
      · norm_num at hp'
      · have := hone (by norm_num)
        subst this
        exact hforce 8647 (by norm_num) (by norm_num) (by norm_num)
      · norm_num at hp'
      · norm_num at hp'
      · have := hone (by norm_num)
        subst this
        exact hforce 14029 (by norm_num) (by norm_num) (by norm_num)
      · have := key 7 (by norm_num) (by norm_num); omega
      · have := key 7 (by norm_num) (by norm_num); omega
      · norm_num at hp'
      · norm_num at hp'
      · have := key 73 (by norm_num) (by norm_num); omega
      · have := key 19 (by norm_num) (by norm_num); omega
    have hkey := tf_core (m := 251) h hq hqN hq13 (by norm_num) hpure hmin
    have hq' : (3541 : ℚ) ≤ q := by exact_mod_cast hqmid
    exact tf_finish (tf_div_pred_le (by norm_num) hqmid)
      (div_nonneg (by linarith) (by linarith)) (hT0 _ (by norm_num)) hZ0 hle hkey
      (by norm_num [tfT])

/-! ## The case `q = 109` -/

/-- `Φ_5(y) = 1 + y + y ^ 2 + y ^ 3 + y ^ 4`. -/
private def tfPhi5 (y : ℕ) : ℕ := 1 + y + y ^ 2 + y ^ 3 + y ^ 4

private theorem tfPhi5_mod (y m : ℕ) : tfPhi5 y % m = tfPhi5 (y % m) % m := by
  have h : y % m ≡ y [MOD m] := Nat.mod_modEq y m
  have := ((((Nat.ModEq.refl 1).add h).add (h.pow 2)).add (h.pow 3)).add (h.pow 4)
  exact this.symm

private theorem tf_geom_mul (x a : ℕ) : ∀ b, ∑ k ∈ Finset.range (a * b), x ^ k =
    (∑ j ∈ Finset.range a, x ^ j) * ∑ i ∈ Finset.range b, (x ^ a) ^ i
  | 0 => by simp
  | b + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, tf_geom_mul x a b,
      Finset.sum_range_succ (fun i => (x ^ a) ^ i) b, mul_add]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add, ← pow_mul]
    ring

/-- `Φ_125(x) = Φ_5(x ^ 25)` divides `σ(x ^ 124)`. -/
private theorem tf_phi_dvd {x : ℕ} (hx : x.Prime) : tfPhi5 (x ^ 25) ∣ σ 1 (x ^ 124) := by
  rw [sigma_one_apply_prime_pow hx, show 124 + 1 = 25 * 5 by norm_num, tf_geom_mul]
  have : ∑ i ∈ Finset.range 5, (x ^ 25) ^ i = tfPhi5 (x ^ 25) := by
    simp only [tfPhi5, Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [this]
  exact dvd_mul_left _ _

/-- A prime factor `r` of `Φ_5(x ^ 25)` does not divide `x`, and is `5` or `≡ 1 (mod 125)`. -/
private theorem tf_phi125_prime {x r : ℕ} (hr : r.Prime) (hd : r ∣ tfPhi5 (x ^ 25)) :
    ¬ r ∣ x ∧ (r = 5 ∨ r % 125 = 1) := by
  have : Fact r.Prime := ⟨hr⟩
  have hz : ((tfPhi5 (x ^ 25) : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hzY : 1 + (x : ZMod r) ^ 25 + ((x : ZMod r) ^ 25) ^ 2 + ((x : ZMod r) ^ 25) ^ 3 +
      ((x : ZMod r) ^ 25) ^ 4 = 0 := by
    simpa [tfPhi5] using hz
  have hx0 : (x : ZMod r) ≠ 0 := by
    intro h0
    rw [h0] at hzY
    norm_num at hzY
  refine ⟨fun h => hx0 ((ZMod.natCast_eq_zero_iff _ _).mpr h), ?_⟩
  have hY5 : ((x : ZMod r) ^ 25) ^ 5 = 1 := by
    linear_combination ((x : ZMod r) ^ 25 - 1) * hzY
  have h125 : (x : ZMod r) ^ (5 ^ 3) = 1 := by
    rw [show (5 : ℕ) ^ 3 = 25 * 5 by norm_num, pow_mul]
    exact hY5
  obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp
    (orderOf_dvd_of_pow_eq_one h125)
  by_cases hi3 : i = 3
  · right
    have := ZMod.orderOf_dvd_card_sub_one hx0
    rw [hio, hi3] at this
    have := (Nat.modEq_iff_dvd' hr.one_lt.le).mpr this
    rw [Nat.ModEq] at this
    norm_num at this
    exact this.symm
  · left
    have h25 : orderOf (x : ZMod r) ∣ 25 := by
      rw [hio, show (25 : ℕ) = 5 ^ 2 by norm_num]
      exact pow_dvd_pow 5 (by omega)
    have hY : (x : ZMod r) ^ 25 = 1 := orderOf_dvd_iff_pow_eq_one.mp h25
    rw [hY] at hzY
    norm_num at hzY
    have h5 : r ∣ 5 := (ZMod.natCast_eq_zero_iff 5 r).mp (by exact_mod_cast hzY)
    exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h5

private theorem tf_phi_mod25 {x : ℕ} (hx : x % 5 = 1) : tfPhi5 (x ^ 25) % 25 = 5 := by
  have hy : x ^ 25 % 25 = 1 := by
    rw [Nat.pow_mod]
    have : x % 25 = 1 ∨ x % 25 = 6 ∨ x % 25 = 11 ∨ x % 25 = 16 ∨ x % 25 = 21 := by omega
    rcases this with h | h | h | h | h <;> rw [h]
  rw [tfPhi5_mod, hy]
  decide

private theorem tf_phi_mod3 {x : ℕ} (hx : x % 3 = 2) : tfPhi5 (x ^ 25) % 3 = 1 := by
  have hy : x ^ 25 % 3 = 2 := by rw [Nat.pow_mod, hx]
  rw [tfPhi5_mod, hy]
  decide

private theorem tf_phi_mod8 {x : ℕ} (hx : x % 2 = 1) :
    tfPhi5 (x ^ 25) % 8 = 1 ∨ tfPhi5 (x ^ 25) % 8 = 5 := by
  have hy : x ^ 25 % 8 = 1 ∨ x ^ 25 % 8 = 3 ∨ x ^ 25 % 8 = 5 ∨ x ^ 25 % 8 = 7 := by
    rw [Nat.pow_mod]
    have : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
    rcases this with h | h | h | h <;> rw [h] <;> norm_num
  rw [tfPhi5_mod]
  rcases hy with h | h | h | h <;> rw [h] <;> decide

private theorem tf_251_even (k : ℕ) : 251 ^ (k + k) % 3 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + (k + 1) = (k + k) + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

private theorem tf_251_odd (k : ℕ) : 251 ^ (2 * k + 1) % 8 = 3 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

/-- `5 · 251 ^ a` is never `≡ 1 (mod 3)` and `≡ 1, 5 (mod 8)` at once. -/
private theorem tf_251 (a : ℕ) (h3 : 5 * 251 ^ a % 3 = 1)
    (h8 : 5 * 251 ^ a % 8 = 1 ∨ 5 * 251 ^ a % 8 = 5) : False := by
  rcases Nat.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hy := tf_251_even k
    rw [Nat.mul_mod, hy] at h3
    norm_num at h3
  · have hy := tf_251_odd k
    rw [Nat.mul_mod, hy] at h8
    norm_num at h8

private theorem tf_sig4 {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 4) = 1 + p + p ^ 2 + p ^ 3 + p ^ 4 := by
  rw [sigma_one_apply_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The primes `p ≤ 660` with `p ≡ 2 (mod 3)` and `p ≡ 1 (mod 5)`. -/
private theorem tf_list15 {p : ℕ} (hp : p.Prime) (h660 : p ≤ 660) (h3 : p % 3 = 2)
    (h5 : p % 5 = 1) :
    p = 11 ∨ p = 41 ∨ p = 71 ∨ p = 101 ∨ p = 131 ∨ p = 191 ∨ p = 251 ∨ p = 281 ∨ p = 311 ∨
      p = 401 ∨ p = 431 ∨ p = 461 ∨ p = 491 ∨ p = 521 ∨ p = 641 := by
  have he : p = 15 * (p / 15) + 11 := by omega
  have ht : p / 15 ≤ 43 := by omega
  generalize p / 15 = t at he ht
  subst he
  interval_cases t <;> first | (norm_num at hp; done) | simp

/-- The large prime attached to each of the five primes that can supply a factor 5. -/
private def tfX (p : ℕ) : ℕ :=
  if p = 11 then 3221 else if p = 41 then 579281 else if p = 251 then 6586781
  else if p = 431 then 510101 else 603791

private theorem tfX_inj {p p' : ℕ}
    (hp : p = 11 ∨ p = 41 ∨ p = 251 ∨ p = 431 ∨ p = 491)
    (hp' : p' = 11 ∨ p' = 41 ∨ p' = 251 ∨ p' = 431 ∨ p' = 491) (h : tfX p = tfX p') :
    p = p' := by
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> rcases hp' with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (simp [tfX] at h)

private theorem tf_ord31 : orderOf ((109 : ℕ) : ZMod 31) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

private theorem tf_ord5 : orderOf ((109 : ℕ) : ZMod 5) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- The weight sent to `5` by the component of `p`. -/
private def tfW (N p : ℕ) : ℕ := padicValNat 5 (σ 1 (p ^ N.factorization p))

set_option maxHeartbeats 4000000 in
private theorem tf_109 {N : ℕ} {E : Finset ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 109)) (h3 : ¬ 3 ∣ N) (hE : E.card ≤ 31)
    (hE3 : ∀ r ∈ E, r % 3 = 2)
    (h3m : ∀ p ∈ N.primeFactors, p ≠ 109 → p ∉ E → 3 ∣ N.factorization p + 1) : False := by
  have hq : Nat.Prime 109 := by norm_num
  have h5p : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨h5p⟩
  have hres := tf_res h h3 hE3 h3m
  have hqN : 109 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos hodd.pos.ne', h.ne_zero⟩
  -- no prime factor other than `109` has `3 ∣ e + 1`
  have hno3 : ∀ p ∈ N.primeFactors, p ≠ 109 → ¬ 3 ∣ N.factorization p + 1 := by
    intro p hp hpq hm
    obtain ⟨a, ⟨k, rfl⟩, hpa⟩ := tf_pure h h3 hres p hp hpq hm
    have h1 : 109 ^ (2 * k + 1) % 5 = 4 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h2 : (1 + p + p ^ 2) % 5 = (1 + p % 5 + (p % 5) ^ 2) % 5 := by
      simp [Nat.add_mod, Nat.pow_mod]
    rw [hpa, h1] at h2
    have : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : p % 5 <;> omega
  have hOE : ∀ p ∈ N.primeFactors, p ≠ 109 → p ∈ E := fun p hp hpq => by
    by_contra hpE
    exact hno3 p hp hpq (h3m p hp hpq hpE)
  set O := N.primeFactors.erase 109 with hOdef
  have hOmem : ∀ p ∈ O, p.Prime ∧ p ∣ N ∧ p ≠ 109 ∧ 5 ≤ p ∧ p % 3 = 2 ∧ p % 2 = 1 ∧
      Even (N.factorization p) ∧ N.factorization p ≠ 0 ∧ ¬ 3 ∣ N.factorization p + 1 := by
    intro p hp
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    have hp' := Nat.prime_of_mem_primeFactors hpN
    have hpd := Nat.dvd_of_mem_primeFactors hpN
    exact ⟨hp', hpd, hpq, tf_five_le h h3 hpN, hres p hp' hpd hpq,
      Nat.odd_iff.mp (h.odd.of_dvd_nat hpd), even_factorization_of_ne h hq hodd hp' hpq,
      Finsupp.mem_support_iff.mp (Nat.support_factorization N ▸ hpN), hno3 p hpN hpq⟩
  have hOcard : O.card ≤ 31 :=
    (Finset.card_le_card fun p hp => hOE p (Finset.mem_erase.mp hp).2
      (Finset.mem_erase.mp hp).1).trans hE
  set B := O.filter (660 < ·) with hBdef
  have hBO : ∀ x ∈ B, x ∈ O ∧ 660 < x := fun x hx => Finset.mem_filter.mp hx
  -- at most one prime factor above 660
  have hB : B.card ≤ 1 := by
    by_contra hc
    push Not at hc
    obtain ⟨y1, hy1, y2, hy2, hne⟩ := Finset.one_lt_card.mp hc
    have hkey := tf_core (m := 1000000) (E := E) h hq hqN (by norm_num) (by norm_num)
      (fun p hp hpq hpE => absurd (hOE p hp hpq) hpE)
      (fun p hp hpq hpE => absurd (hOE p hp hpq) hpE)
    set Z := (N.primeFactors.erase 109).filter (· ∈ E) with hZdef
    have hZO : ∀ t, t ∈ Z ↔ t ∈ O := fun t => by
      rw [hZdef, Finset.mem_filter]
      exact ⟨fun h => h.1, fun ht => ⟨ht, hOE t (Finset.mem_erase.mp ht).2
        (Finset.mem_erase.mp ht).1⟩⟩
    have hy1Z : y1 ∈ Z := (hZO y1).mpr (hBO y1 hy1).1
    have hy2Z : y2 ∈ Z := (hZO y2).mpr (hBO y2 hy2).1
    set f : ℕ → ℚ := fun t => (t : ℚ) / (t - 1)
    have hsplit : ∏ t ∈ Z, f t = f y1 * (f y2 * ∏ t ∈ (Z.erase y1).erase y2, f t) := by
      rw [← Finset.mul_prod_erase Z f hy1Z,
        ← Finset.mul_prod_erase (Z.erase y1) f (Finset.mem_erase.mpr ⟨hne.symm, hy2Z⟩)]
    have hrest_mem : ∀ t ∈ (Z.erase y1).erase y2, t.Prime ∧ 5 ≤ t ∧ t % 3 = 2 := by
      intro t ht
      obtain ⟨hp', -, -, h5, h3', -⟩ :=
        hOmem t ((hZO t).mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)))
      exact ⟨hp', h5, h3'⟩
    have hZcard : Z.card ≤ 31 :=
      (Finset.card_le_card fun t ht => (hZO t).mp ht).trans hOcard
    have hrest_card : ((Z.erase y1).erase y2).card ≤ 29 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm, hy2Z⟩),
        Finset.card_erase_of_mem hy1Z]
      omega
    have hrest := tf_env29 hrest_mem hrest_card
    have hf : ∀ y ∈ B, f y ≤ 661 / 660 := fun y hy => by
      have := tf_div_pred_le (by norm_num) (show 661 ≤ y by have := (hBO y hy).2; omega)
      norm_num at this ⊢
      exact this
    have hf0 : ∀ y ∈ B, 0 ≤ f y := fun y hy => by
      have : (661 : ℚ) ≤ y := by exact_mod_cast (show 661 ≤ y by have := (hBO y hy).2; omega)
      exact div_nonneg (by linarith) (by linarith)
    have hrest0 : 0 ≤ ∏ t ∈ (Z.erase y1).erase y2, f t := Finset.prod_nonneg fun t ht => by
      have : (5 : ℚ) ≤ t := by exact_mod_cast (hrest_mem t ht).2.1
      exact div_nonneg (by linarith) (by linarith)
    have hZb : ∏ t ∈ Z, f t ≤ 661 / 660 * (661 / 660 *
        (1812498586146619514269851608750058738331 / 917440951333825631705850970112000000000)) := by
      rw [hsplit]
      exact mul_le_mul (hf y1 hy1) (mul_le_mul (hf y2 hy2) hrest (hrest0) (by norm_num))
        (mul_nonneg (hf0 y2 hy2) hrest0) (by norm_num)
    exact tf_finish (A0 := 109 / 108) (by norm_num) (by norm_num)
      (le_trans zero_le_one (tfT_one_le (by norm_num)))
      (Finset.prod_nonneg fun t ht => by
        have : (5 : ℚ) ≤ t := by exact_mod_cast (hOmem t ((hZO t).mp ht)).2.2.2.1
        exact div_nonneg (by linarith) (by linarith)) hZb hkey (by norm_num [tfT])
  have hBeq : ∀ x ∈ B, ∀ y ∈ B, x = y := Finset.card_le_one.mp hB
  -- the prime `5`
  obtain ⟨h5N, h5q⟩ := prime_dvd_of_dvd_succ_special h hq hodd h5p (by norm_num)
    (by norm_num : 5 ∣ 109 + 1)
  have h5O : 5 ∈ O := Finset.mem_erase.mpr ⟨h5q, Nat.mem_primeFactors.mpr ⟨h5p, h5N, h.ne_zero⟩⟩
  have he5 : 4 ≤ N.factorization 5 := by
    obtain ⟨-, -, -, -, -, -, ⟨j, hj⟩, hne, hn3⟩ := hOmem 5 h5O
    by_contra hc
    have : j = 1 := by omega
    exact hn3 (by omega)
  -- the special component supplies exactly one factor `5`
  have ha5 : ¬ 5 ∣ N.factorization 109 + 1 := by
    intro h5
    have hord := tf_ord31
    have h31 := dvd_sigma_prime_pow_of_orderOf_dvd (a := N.factorization 109) hq
      (by norm_num : Nat.Prime 31) (by norm_num) (by rw [hord]; norm_num) (by rw [hord]; exact h5)
    have h31N := OPNStarter.force_prime h.perfect hq rfl (by norm_num) (by norm_num) h31
    have := hres 31 (by norm_num) h31N (by norm_num)
    norm_num at this
  have hw109 : padicValNat 5 (σ 1 (109 ^ N.factorization 109)) = 1 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord := tf_ord5
    have ha2 : 2 ∣ N.factorization 109 + 1 := by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k + 1, by omega⟩
    rw [padicValNat_sigma_prime_pow_of_orderOf_dvd hq h5p (by norm_num) (by norm_num)
      (by rw [hord]; norm_num) (by rw [hord]; exact ha2), hord]
    have h1 : padicValNat 5 (109 ^ 2 - 1) = 1 := by
      rw [show 109 ^ 2 - 1 = 5 * 2376 by norm_num, Nat.padicValNat_def,
        padicValNat.mul (by norm_num) (by norm_num), Nat.Prime.multiplicity_self,
        multiplicity_eq_zero_of_not_dvd (by norm_num)]
    have h2 : padicValNat 5 ((N.factorization 109 + 1) / 2) = 0 := by
      rw [Nat.padicValNat_def]
      exact padicValNat.eq_zero_of_not_dvd fun hd => ha5 (hd.trans (Nat.div_dvd_of_dvd ha2))
    rw [h1, h2]
  -- the ledger at `5`
  have hled : N.factorization 5 = 1 + ∑ p ∈ O, tfW N p := by
    rw [← sigmaWeight_sum_eq h.perfect h5p (by norm_num),
      ← Finset.add_sum_erase _ (fun p => sigmaWeight N p 5) hqN]
    rw [sigmaWeight_eq_padicValNat N 109 h5p, hw109]
    congr 1
    exact Finset.sum_congr rfl fun p _ => sigmaWeight_eq_padicValNat N p h5p
  have hsum3 : 3 ≤ ∑ p ∈ O, tfW N p := by omega
  -- the weight of one component
  have hwdvd : ∀ p ∈ O, ∀ k, k ≤ tfW N p →
      5 ^ k ∣ N.factorization p + 1 ∧ (1 ≤ k → p % 5 = 1) := by
    intro p hp k hk
    obtain ⟨hp', -, -, -, -, -, hev, -, -⟩ := hOmem p hp
    by_cases hp5 : p % 5 = 1
    · have hv : tfW N p = padicValNat 5 (N.factorization p + 1) :=
        padicValNat_sigma_prime_pow_of_dvd_pred hp' h5p (by norm_num)
          (Nat.dvd_of_mod_eq_zero (by omega))
      rw [hv] at hk
      exact ⟨(padicValNat_dvd_iff_le (by omega)).mpr (by rw [← Nat.padicValNat_def]; exact hk),
        fun _ => hp5⟩
    · have hv : tfW N p = 0 := by
        rw [tfW, Nat.padicValNat_def]
        refine multiplicity_eq_zero_of_not_dvd fun hd => ?_
        rcases (prime_dvd_sigma_prime_pow hp' h5p hd).2 with ⟨h1, -⟩ | ⟨h1, hd1, hd2⟩
        · exact hp5 h1
        · obtain ⟨j, hj⟩ := hev
          have hle := Nat.le_of_dvd (by norm_num) hd2
          set d := orderOf (p : ZMod 5)
          interval_cases d
          · omega
          · norm_num at hd2
          · omega
      rw [hv] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨by simp, fun h => absurd h (by norm_num)⟩
  -- transfer of prime divisors
  have hdivN : ∀ p ∈ O, ∀ k, k + 1 ∣ N.factorization p + 1 → ∀ r, r.Prime → r ≠ 2 →
      r ∣ σ 1 (p ^ k) → r ∣ N := fun p hp k hk r hr hr2 hrd =>
    OPNStarter.force_prime h.perfect (hOmem p hp).1 rfl hr hr2
      (hrd.trans (OPNExample.sigma_prime_pow_dvd (hOmem p hp).1 hk))
  have hK1 : ∀ p ∈ O, ∀ k, k + 1 ∣ N.factorization p + 1 → ∀ r, r.Prime → r % 3 = 1 →
      r ≠ 109 → r ∣ σ 1 (p ^ k) → False := by
    intro p hp k hk r hr hr3 hrq hrd
    have := hres r hr (hdivN p hp k hk r hr (by rintro rfl; norm_num at hr3) hrd) hrq
    omega
  have hBig : ∀ p ∈ O, ∀ k, k + 1 ∣ N.factorization p + 1 → ∀ r, r.Prime → 660 < r →
      r ∣ σ 1 (p ^ k) → r ∈ B := by
    intro p hp k hk r hr hr660 hrd
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by omega, Nat.mem_primeFactors.mpr
      ⟨hr, hdivN p hp k hk r hr (by omega) hrd, h.ne_zero⟩⟩, hr660⟩
  have hCof : ∀ p ∈ O, ∀ k, k + 1 ∣ N.factorization p + 1 → ∀ c, c ∣ σ 1 (p ^ k) → 1 < c →
      (∀ d < 661, 2 ≤ d → c % d ≠ 0) → ∃ r ∈ B, r ∣ c := by
    intro p hp k hk c hc hc1 hcd
    have hrp : c.minFac.Prime := Nat.minFac_prime (by omega)
    have hrc : c.minFac ∣ c := Nat.minFac_dvd c
    have hr660 : 660 < c.minFac := by
      by_contra hle
      push Not at hle
      exact hcd _ (by omega) hrp.two_le (Nat.mod_eq_zero_of_dvd hrc)
    exact ⟨_, hBig p hp k hk _ hrp hr660 (hrc.trans hc), hrc⟩
  -- a large prime supplies at most two factors `5`
  have hwB : ∀ x ∈ B, tfW N x ≤ 2 := by
    intro x hx
    by_contra hc
    push Not at hc
    obtain ⟨hxO, hx660⟩ := hBO x hx
    obtain ⟨hx', -, -, -, hx3, hx2, -⟩ := hOmem x hxO
    obtain ⟨h125, hx5'⟩ := hwdvd x hxO 3 hc
    have hx51 := hx5' (by norm_num)
    have hk : 124 + 1 ∣ N.factorization x + 1 := by norm_num at h125 ⊢; exact h125
    have hΦdvd := tf_phi_dvd hx'
    have hpf : ∀ r, r.Prime → r ∣ tfPhi5 (x ^ 25) → r = 5 ∨ r = 251 := by
      intro r hr hrd
      obtain ⟨hrx, hr5 | hr125⟩ := tf_phi125_prime hr hrd
      · exact Or.inl hr5
      · right
        have hr660 : r ≤ 660 := by
          by_contra hlt
          push Not at hlt
          have hrB := hBig x hxO 124 hk r hr hlt (hrd.trans hΦdvd)
          have := hBeq r hrB x hx
          exact hrx (this ▸ dvd_refl r)
        have : r = 1 ∨ r = 126 ∨ r = 251 ∨ r = 376 ∨ r = 501 ∨ r = 626 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | (norm_num at hr)
    have h25 := tf_phi_mod25 hx51
    have h3' := tf_phi_mod3 hx3
    have h8 := tf_phi_mod8 hx2
    obtain ⟨c, hc⟩ : 5 ∣ tfPhi5 (x ^ 25) := Nat.dvd_of_mod_eq_zero (by omega)
    have hc5 : ¬ 5 ∣ c := by
      rintro ⟨d, hd⟩
      rw [hd] at hc
      omega
    have hc0 : c ≠ 0 := by rintro rfl; omega
    have hcpow := Nat.eq_prime_pow_of_unique_prime_dvd hc0 (fun {d} hd hdd =>
      ((hpf d hd (hc ▸ Dvd.dvd.mul_left hdd 5)).resolve_left (by rintro rfl; exact hc5 hdd)))
    rw [hc, hcpow] at h3' h8
    exact tf_251 _ h3' h8
  -- the primes up to 660
  have hsmall : ∀ p ∈ O, p ≤ 660 → 1 ≤ tfW N p →
      tfW N p ≤ 1 ∧ tfX p ∈ B ∧ (p = 11 ∨ p = 41 ∨ p = 251 ∨ p = 431 ∨ p = 491) := by
    intro p hp h660 hw
    obtain ⟨hp', -, -, -, hp3, -⟩ := hOmem p hp
    obtain ⟨h5, hp5⟩ := hwdvd p hp 1 hw
    have hp51 := hp5 le_rfl
    have h4 : 4 + 1 ∣ N.factorization p + 1 := by simpa using h5
    have hcap : ∀ c, c ∣ σ 1 (p ^ 24) → 1 < c → (∀ d < 661, 2 ≤ d → c % d ≠ 0) →
        ¬ tfX p ∣ c → tfX p ∈ B → tfW N p ≤ 1 := by
      intro c hc hc1 hcd hxc hxB
      by_contra hlt
      push Not at hlt
      have h25 := (hwdvd p hp 2 hlt).1
      have h24 : 24 + 1 ∣ N.factorization p + 1 := by norm_num at h25 ⊢; exact h25
      obtain ⟨r, hrB, hrc⟩ := hCof p hp 24 h24 c hc hc1 hcd
      exact hxc (hBeq r hrB _ hxB ▸ hrc)
    rcases tf_list15 hp' h660 hp3 hp51 with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hxB : tfX 11 ∈ B := hBig _ hp 4 h4 3221 (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)
      refine ⟨hcap 134550834441333402101 ?_ (by norm_num) (by decide +kernel) (by norm_num [tfX])
        hxB, hxB, by norm_num⟩
      rw [sigma_one_apply_prime_pow (by norm_num)]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    · have hxB : tfX 41 ∈ B := hBig _ hp 4 h4 579281 (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)
      refine ⟨hcap 36033556902303851583445436592401 ?_ (by norm_num) (by decide +kernel)
        (by norm_num [tfX]) hxB, hxB, by norm_num⟩
      rw [sigma_one_apply_prime_pow (by norm_num)]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    · exact (hK1 _ hp 4 h4 211 (by norm_num) (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)).elim
    · exact (hK1 _ hp 4 h4 31 (by norm_num) (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)).elim
    · exact (hK1 _ hp 4 h4 61 (by norm_num) (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)).elim
    · have h1 := hBig _ hp 4 h4 1871 (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)
      have h2 := hBig _ hp 4 h4 13001 (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)
      exact absurd (hBeq _ h1 _ h2) (by norm_num)
    · have hxB : tfX 251 ∈ B := hBig _ hp 4 h4 6586781 (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)
      refine ⟨hcap 197017328238366196814957432669082038228051252501 ?_ (by norm_num)
        (by decide +kernel) (by norm_num [tfX]) hxB, hxB, by norm_num⟩
      rw [sigma_one_apply_prime_pow (by norm_num)]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    · exact (hK1 _ hp 4 h4 31 (by norm_num) (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)).elim
    · exact (hK1 _ hp 4 h4 170638711 (by norm_num) (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)).elim
    · exact (hK1 _ hp 4 h4 1231 (by norm_num) (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)).elim
    · have hxB : tfX 431 ∈ B := hBig _ hp 4 h4 510101 (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)
      refine ⟨hcap 9785328254060563287338516174078139711470798854312301 ?_ (by norm_num)
        (by decide +kernel) (by norm_num [tfX]) hxB, hxB, by norm_num⟩
      rw [sigma_one_apply_prime_pow (by norm_num)]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    · exact (hK1 _ hp 4 h4 61 (by norm_num) (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)).elim
    · have hxB : tfX 491 ∈ B := hBig _ hp 4 h4 603791 (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)
      refine ⟨hcap 132635518086962652147431928917197603478324547868366901 ?_ (by norm_num)
        (by decide +kernel) (by norm_num [tfX]) hxB, hxB, by norm_num⟩
      rw [sigma_one_apply_prime_pow (by norm_num)]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    · exact (hK1 _ hp 4 h4 17761 (by norm_num) (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)).elim
    · have h1 := hBig _ hp 4 h4 4091 (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)
      have h2 := hBig _ hp 4 h4 751481 (by norm_num) (by norm_num)
        (by rw [tf_sig4 (by norm_num)]; norm_num)
      exact absurd (hBeq _ h1 _ h2) (by norm_num)
  -- the attached large prime then supplies nothing
  have hpin : ∀ p, (p = 11 ∨ p = 41 ∨ p = 251 ∨ p = 431 ∨ p = 491) → tfX p ∈ B →
      tfW N (tfX p) = 0 := by
    intro p hp hxB
    by_contra hne
    have hxO := (hBO _ hxB).1
    have h5 := (hwdvd _ hxO 1 (by omega)).1
    have h4 : 4 + 1 ∣ N.factorization (tfX p) + 1 := by simpa using h5
    have key : ∀ c, c ∣ σ 1 (tfX p ^ 4) → 1 < c → (∀ d < 661, 2 ≤ d → c % d ≠ 0) →
        ¬ tfX p ∣ c → False := by
      intro c hc hc1 hcd hxc
      obtain ⟨r, hrB, hrc⟩ := hCof _ hxO 4 h4 c hc hc1 hcd
      exact hxc (hBeq r hrB _ hxB ▸ hrc)
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact key 1957650063931 (by simp only [tfX]; rw [tf_sig4 (by norm_num)]; norm_num)
        (by norm_num) (by decide +kernel) (by norm_num [tfX])
    · exact key 22521010969527450259361
        (by simp only [tfX]; rw [tf_sig4 (by norm_num)]; norm_num)
        (by norm_num) (by decide +kernel) (by norm_num [tfX])
    · exact key 34223961034250447684015851
        (by simp only [tfX]; rw [tf_sig4 (by norm_num)]; norm_num)
        (by norm_num) (by decide +kernel) (by norm_num [tfX])
    · exact key 4380831423867268211
        (by simp only [tfX]; rw [tf_sig4 (by norm_num)]; norm_num)
        (by norm_num) (by decide +kernel) (by norm_num [tfX])
    · exact key 857463341402423859251
        (by simp only [tfX]; rw [tf_sig4 (by norm_num)]; norm_num)
        (by norm_num) (by decide +kernel) (by norm_num [tfX])
  -- combine
  set Sm := O.filter (fun p => ¬ 660 < p) with hSm
  have hsplit : ∑ p ∈ B, tfW N p + ∑ p ∈ Sm, tfW N p = ∑ p ∈ O, tfW N p :=
    Finset.sum_filter_add_sum_filter_not O (fun p => 660 < p) (fun p => tfW N p)
  have hSmem : ∀ p ∈ Sm, p ∈ O ∧ p ≤ 660 := fun p hp => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    exact ⟨h1, by omega⟩
  have hBsum : ∑ p ∈ B, tfW N p ≤ 2 := by
    have := Finset.sum_le_card_nsmul B (fun p => tfW N p) 2 hwB
    rw [smul_eq_mul] at this
    omega
  by_cases hW : ∃ p ∈ Sm, 1 ≤ tfW N p
  · obtain ⟨p0, hp0, hw0⟩ := hW
    obtain ⟨hp0O, hp0s⟩ := hSmem p0 hp0
    obtain ⟨-, hx0B, hp0l⟩ := hsmall p0 hp0O hp0s hw0
    have hB0 : ∑ p ∈ B, tfW N p = 0 := Finset.sum_eq_zero fun y hy => by
      rw [hBeq y hy _ hx0B]
      exact hpin p0 hp0l hx0B
    have hSm1 : ∑ p ∈ Sm, tfW N p ≤ ∑ p ∈ Sm, if p = p0 then 1 else 0 := by
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨hpO, hps⟩ := hSmem p hp
      split_ifs with hpp
      · subst hpp
        by_contra hc
        push Not at hc
        exact absurd (hsmall p hpO hps (by omega)).1 (by omega)
      · by_contra hc
        push Not at hc
        obtain ⟨-, hxB, hpl⟩ := hsmall p hpO hps (by omega)
        exact hpp (tfX_inj hpl hp0l (hBeq _ hxB _ hx0B))
    rw [Finset.sum_ite_eq' Sm p0 (fun _ => 1), if_pos hp0] at hSm1
    omega
  · push Not at hW
    have hSm0 : ∑ p ∈ Sm, tfW N p = 0 := Finset.sum_eq_zero fun p hp => by
      have := hW p hp
      omega
    omega

/-- **Thirty one exceptions that are `2 (mod 3)` force `3`.** Let `N` be an odd perfect number
with special prime `q` (the prime of odd exponent). If every prime factor `p ≠ q` of `N`
outside a set `E` satisfies `3 ∣ e_p + 1`, where `E` has at most 31 elements, all
`≡ 2 (mod 3)`, then `3 ∣ N`. Taking `E` to be the set of prime factors `p ≠ q` with
`3 ∤ e_p + 1`: if at most 31 of them have `3 ∤ e_p + 1` and each of those is `≡ 2 (mod 3)`, then
`3 ∣ N`. There is no restriction on `q`.
Whether this result is new was not verified against the literature. -/
theorem three_dvd_of_thirtyone_exceptions_mod_three_of_three_dvd {N q : ℕ} {E : Finset ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : E.card ≤ 31)
    (hE3 : ∀ r ∈ E, r % 3 = 2)
    (h3m : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → 3 ∣ N.factorization p + 1) : 3 ∣ N := by
  by_contra h3
  by_cases hq109 : q = 109
  · subst hq109
    exact tf_109 h hodd h3 hE hE3 h3m
  · exact tf_ne109 h hq hodd h3 hq109 hE hE3 h3m

/-- **Filter form.** Let `N` be an odd perfect number with special prime `q`. If at most 31
prime factors `p ≠ q` have `3 ∤ e_p + 1` and each of them is `≡ 2 (mod 3)`, then `3 ∣ N`.
Whether this result is new was not verified against the literature. -/
theorem three_dvd_of_thirtyone_exceptional_mod_three {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hE : ((N.primeFactors.erase q).filter (fun p => ¬ 3 ∣ N.factorization p + 1)).card ≤ 31)
    (hE3 : ∀ p ∈ N.primeFactors, p ≠ q → ¬ 3 ∣ N.factorization p + 1 → p % 3 = 2) :
    3 ∣ N := by
  refine three_dvd_of_thirtyone_exceptions_mod_three_of_three_dvd h hq hodd hE
    (fun r hr => ?_) (fun p hp hpq hpE => ?_)
  · obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    exact hE3 r (Finset.mem_erase.mp hr1).2 (Finset.mem_erase.mp hr1).1 hr2
  · by_contra hc
    exact hpE (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpq, hp⟩, hc⟩)

end OddPerfect

#print axioms OddPerfect.three_dvd_of_thirtyone_exceptions_mod_three_of_three_dvd
#print axioms OddPerfect.three_dvd_of_thirtyone_exceptional_mod_three
