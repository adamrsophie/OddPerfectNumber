import OddPerfect.AttackSize

/-!
# Sharper counts of exceptional primes when `3 ∤ N`

Let `N` be an odd perfect number with special prime `q`, and `E` a finite set such that every
prime factor outside `E ∪ {q}` has exponent exactly 2. `OddPerfect/AttackSize.lean` shows
`3 ∣ N` when `E` has at most twelve elements all `≡ 2 (mod 3)`, or at most four elements none
of which is a prime divisor of some `σ(p ^ 2)`, `p ∉ E ∪ {q}`. Here the thresholds become 29
and 5.

Assume `3 ∤ N` and that no prime of `E` divides any `σ(p ^ 2)` with `p ∉ E ∪ {q}` (this
holds under either of the two conditions on `E` above; without it an exponent two prime
can feed a prime of `E`, as in `σ(5 ^ 2) = 31`). Then every exponent two prime
`p ∉ E ∪ {q}` is *pure*: `σ(p ^ 2) = q ^ a`
with `a` odd, `p ≡ 11 (mod 12)` and `p ≥ 59`; two pure primes `s < t` satisfy `13 s ≤ t`.

* **Sharper pure product.** If all pure primes are at least `m ≥ 5`, their abundancies have
  product at most `C(m) = (1 + 1/m + 1/m ^ 2) (1 + 2/(13 m))`: keep the smallest one exact
  and bound the rest by the factor `1 + 2/m'` at `m' ≥ 13 m`.
* **Core inequality.** With `Z` the prime factors in `E` other than `q`,
  `2 (q - 1) < q C(m) ∏_{r ∈ Z} r/(r-1)`.
* **29 exceptions `≡ 2 (mod 3)`.** Here every prime factor other than `q` is `≡ 2 (mod 3)`,
  while every odd prime dividing `q + 1` divides `N`. This excludes `q ∈ {13, 37, 61, 73, 97}`
  (the divisors `7, 19, 31, 37, 7` are `≡ 1 (mod 3)`). For `109 ≤ q < 3541` a pure prime has
  `σ(p ^ 2) ≥ σ(59 ^ 2) = 3541 > q`, so `a ≥ 3` and `p ≥ 1000`. For `q ≥ 3541` the bases
  `59, 71` force `q = 3541, 5113`, excluded by `7 ∣ 3542` and the prime `2557 ∣ 5114`; the
  bases `83, 107` give `19 ∣ σ` and `7 ∣ σ`; so pure primes are at least `131`. Each range
  contradicts the envelope given by the 29 smallest primes `≥ 5` that are `≡ 2 (mod 3)`.
* **Five non-target exceptions.** `q = 13` or `q ≥ 37`, and `C(59)` suffices against the
  envelopes `{5, 7, 11, 17, 19}` (for `q = 13`) and `{5, 7, 11, 13, 17}`.

For statements with no restriction on `q` these are the limits of the comparison. With
`q = 109` and no pure primes the lower bound is `2 * 108/109`, below the envelope of the 30
smallest primes `≥ 5` that are `≡ 2 (mod 3)`; with `q = 13` it is `24/13`, below the envelope
`{5, 7, 11, 17, 19, 23}`, and with `q = 37` it is `72/37`, below `{5, 7, 11, 13, 17, 19}`.

Setting these values of `q` aside as explicit case hypotheses, the same method gives 31
exceptions `≡ 2 (mod 3)` when `q ≠ 109` and six non-target exceptions when `q ≥ 61`. For the
first, `q < 229` is excluded by forcing (`79 ∣ 158`, `7 ∣ 182`, `97 ∣ 194` besides the values
above), `229 ≤ q < 3541` gives pure primes at least 3000, and for `q ≥ 3541` the further bases
`131, 167` force `q = 17293, 28057`, excluded by the primes `8647 ∣ 17294`, `14029 ∣ 28058`,
while `179, 191, 227, 239` give the prime divisors `7, 7, 73, 19`; so pure primes are at least
251.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Restated elementary facts -/

private theorem ec_sigma_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]

private theorem ec_odd_exp {p q a : ℕ} (hp : 0 < p) (h : 1 + p + p ^ 2 = q ^ a) : Odd a := by
  rcases Nat.even_or_odd a with ⟨b, rfl⟩ | ho
  · exfalso
    rw [← two_mul, pow_mul'] at h
    have h1 : p ^ 2 < (q ^ b) ^ 2 := by rw [← h]; omega
    have h2 : (q ^ b) ^ 2 < (p + 1) ^ 2 := by rw [← h]; nlinarith
    have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h1
    have := (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
    omega
  · exact ho

private theorem ec_sep {p p' q a a' : ℕ} (hq : 13 ≤ q) (ha : Odd a) (ha' : Odd a')
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

/-- `σ(s ^ 2)/s ^ 2` as a rational function. -/
private def ecAb (s : ℕ) : ℚ := ((s : ℚ) ^ 2 + s + 1) / s ^ 2

private theorem ec_step {a : ℕ} (ha : 5 ≤ a) :
    ecAb a * (1 + 2 / ((13 * a : ℕ) : ℚ)) ≤ 1 + 2 / (a : ℚ) := by
  have ha' : (5 : ℚ) ≤ a := by exact_mod_cast ha
  unfold ecAb
  push_cast
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h0 : (0 : ℚ) < a := by linarith
  field_simp
  nlinarith [mul_pos h0 h0]

private theorem ec_prod_le (S : Finset ℕ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x < y → 13 * x ≤ y) :
    ∀ m : ℕ, 5 ≤ m → (∀ x ∈ S, m ≤ x) → ∏ x ∈ S, ecAb x ≤ 1 + 2 / (m : ℚ) := by
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
    have hpos : 0 ≤ ecAb a := by unfold ecAb; positivity
    calc _ ≤ ecAb a * (1 + 2 / ((13 * a : ℕ) : ℚ)) := mul_le_mul_of_nonneg_left hs hpos
      _ ≤ 1 + 2 / (a : ℚ) := ec_step (by omega)
      _ ≤ 1 + 2 / (m : ℚ) := by gcongr

/-- The envelope `C(m) = σ(m ^ 2)/m ^ 2 * (1 + 2/(13 m))`. -/
private def ecC (m : ℕ) : ℚ := ecAb m * (1 + 2 / ((13 * m : ℕ) : ℚ))

private theorem ecAb_anti {m a : ℕ} (hm : 1 ≤ m) (ha : m ≤ a) : ecAb a ≤ ecAb m := by
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have ha' : (m : ℚ) ≤ a := by exact_mod_cast ha
  unfold ecAb
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_le_mul ha' ha' (by linarith) (by linarith), mul_nonneg (sub_nonneg.mpr ha')
    (show (0 : ℚ) ≤ (m : ℚ) * a by positivity)]

/-- **Sharper pure product.** A finite set of integers `≥ m ≥ 5`, pairwise separated by a factor
13, has `∏ σ(s ^ 2)/s ^ 2 ≤ C(m)`. -/
private theorem ec_prod_le_C (S : Finset ℕ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x < y → 13 * x ≤ y)
    {m : ℕ} (hm : 5 ≤ m) (hle : ∀ x ∈ S, m ≤ x) : ∏ x ∈ S, ecAb x ≤ ecC m := by
  have hm' : (5 : ℚ) ≤ m := by exact_mod_cast hm
  have hAm : 1 ≤ ecAb m := by
    unfold ecAb
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hD : (1 : ℚ) ≤ 1 + 2 / ((13 * m : ℕ) : ℚ) := by
    have : (0 : ℚ) ≤ 2 / ((13 * m : ℕ) : ℚ) := by positivity
    linarith
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.prod_empty, ecC]
    nlinarith
  set a := S.min' hne
  have haS : a ∈ S := S.min'_mem hne
  have ham : m ≤ a := hle a haS
  rw [← Finset.mul_prod_erase S _ haS]
  have hrest : ∏ x ∈ S.erase a, ecAb x ≤ 1 + 2 / ((13 * a : ℕ) : ℚ) := by
    refine ec_prod_le (S.erase a) (fun x hx y hy hxy =>
      hsep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy) (13 * a)
      (by omega) fun x hx => ?_
    have hxS := Finset.mem_of_mem_erase hx
    have hxa : a < x := lt_of_le_of_ne (S.min'_le x hxS) (Finset.ne_of_mem_erase hx).symm
    exact hsep a haS x hxS hxa
  have hpos : 0 ≤ ecAb a := by unfold ecAb; positivity
  have hDa : 1 + 2 / ((13 * a : ℕ) : ℚ) ≤ 1 + 2 / ((13 * m : ℕ) : ℚ) := by
    have : ((13 * m : ℕ) : ℚ) ≤ ((13 * a : ℕ) : ℚ) := by exact_mod_cast (by omega)
    gcongr
  calc ecAb a * ∏ x ∈ S.erase a, ecAb x ≤ ecAb a * (1 + 2 / ((13 * a : ℕ) : ℚ)) :=
        mul_le_mul_of_nonneg_left hrest hpos
    _ ≤ ecAb m * (1 + 2 / ((13 * m : ℕ) : ℚ)) :=
        mul_le_mul (ecAb_anti (by omega) ham) hDa (by positivity) (by linarith)

private theorem ec_abundancy_sq {p : ℕ} (hp : p.Prime) : abundancy (p ^ 2) = ecAb p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [abundancy_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ecAb]
  field_simp
  ring

private theorem ec_abundancy_nonneg (n : ℕ) : 0 ≤ abundancy n := by
  unfold abundancy; positivity

private theorem ec_div_pred_le {p m : ℕ} (hm : 2 ≤ m) (hp : m ≤ p) :
    (p : ℚ) / (p - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hp' : (m : ℚ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- A pure prime is `≡ 11 (mod 12)` and at least 59. -/
private theorem ec_pure_shape {N p q a : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hq12 : q % 12 = 1) (hq : q.Prime) (hp : p.Prime) (he : N.factorization p = 2)
    (hpa : 1 + p + p ^ 2 = q ^ a) : p % 12 = 11 ∧ 59 ≤ p := by
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

/-- Exchange bound for products over sets of bounded size. -/
private theorem ec_prod_le_of_card_le {T L : Finset ℕ} (f : ℕ → ℚ) (c : ℚ) (hc : 1 ≤ c)
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
        Finset.prod_le_prod (fun t ht => hT0 t (Finset.mem_sdiff.mp ht).1)
          fun t ht => hTc t (Finset.mem_sdiff.mp ht).1 (Finset.mem_sdiff.mp ht).2
    _ = c ^ (T \ L).card := Finset.prod_const c
    _ ≤ c ^ (L \ T).card := pow_le_pow_right₀ hc hc1
    _ = ∏ _l ∈ L \ T, c := (Finset.prod_const c).symm
    _ ≤ ∏ l ∈ L \ T, f l :=
        Finset.prod_le_prod (fun _ _ => by linarith) fun l hl => hLc l (Finset.mem_sdiff.mp hl).1

private theorem ec_five_le {N p : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
    (hp : p ∈ N.primeFactors) : 5 ≤ p := by
  obtain ⟨hpp, hpN, -⟩ := Nat.mem_primeFactors.mp hp
  by_contra hc
  interval_cases p
  · exact absurd hpp (by norm_num)
  · exact absurd hpp (by norm_num)
  · exact h.not_two_dvd hpN
  · exact h3 hpN
  · exact absurd hpp (by norm_num)

private theorem ec_pure_of_ordinary {N q : ℕ} {E : Finset ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N)
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
    exact hd2 (hsq d (Nat.mem_primeFactors.mpr ⟨hd, hdN, h.ne_zero⟩) hdq
      fun hm => hE p hp hpq hpE d hm hd hdd)
  have hne : σ 1 (p ^ 2) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hp'.ne_zero)).ne'
  exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hne key⟩

/-! ## The core inequality -/

/-- **Core inequality.** If `3 ∤ N`, every prime factor `p ≠ q` outside `Y` is a pure square,
and every such `p` is at least `m ≥ 5`, then `2 (q - 1) < q C(m) ∏_Z r/(r-1)`. -/
private theorem ec_core {N q m : ℕ} {Y : Finset ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (h3 : ¬ 3 ∣ N) (hm : 5 ≤ m)
    (hY : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ Y →
      N.factorization p = 2 ∧ ∃ a, σ 1 (p ^ 2) = q ^ a)
    (hmin : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ Y → m ≤ p) :
    2 * ((q : ℚ) - 1) <
      q * ecC m * ∏ p ∈ (N.primeFactors.erase q).filter (· ∈ Y), (p : ℚ) / (p - 1) := by
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
  have hmemX : ∀ {x}, x ∈ X → x.Prime ∧ N.factorization x = 2 ∧ m ≤ x ∧
      ∃ a, Odd a ∧ 1 + x + x ^ 2 = q ^ a := by
    intro x hx
    rw [hXdef, Finset.mem_filter, Finset.mem_erase] at hx
    have hx' := Nat.prime_of_mem_primeFactors hx.1.2
    obtain ⟨he, a, ha⟩ := hY x hx.1.2 hx.1.1 hx.2
    rw [ec_sigma_sq hx'] at ha
    exact ⟨hx', he, hmin x hx.1.2 hx.1.1 hx.2, a, ec_odd_exp hx'.pos ha, ha⟩
  have hX : ∏ x ∈ X, abundancy (x ^ N.factorization x) ≤ ecC m := by
    have heq : ∏ x ∈ X, abundancy (x ^ N.factorization x) = ∏ x ∈ X, ecAb x := by
      refine Finset.prod_congr rfl fun x hx => ?_
      obtain ⟨hx', he, -⟩ := hmemX hx
      rw [he, ec_abundancy_sq hx']
    rw [heq]
    refine ec_prod_le_C X (fun x hx y hy hxy => ?_) hm fun x hx => (hmemX hx).2.2.1
    obtain ⟨-, -, -, a, ha, hxa⟩ := hmemX hx
    obtain ⟨-, -, -, b, hb, hyb⟩ := hmemX hy
    exact ec_sep hq13 ha hb hxa hyb hxy
  have hZ : ∏ x ∈ Z, abundancy (x ^ N.factorization x) ≤ ∏ x ∈ Z, (x : ℚ) / (x - 1) :=
    Finset.prod_le_prod (fun _ _ => ec_abundancy_nonneg _) fun x hx =>
      (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_filter x hx))) _).le
  have hX0 : 0 ≤ ∏ x ∈ X, abundancy (x ^ N.factorization x) :=
    Finset.prod_nonneg fun _ _ => ec_abundancy_nonneg _
  have hZ0 : 0 ≤ ∏ x ∈ Z, abundancy (x ^ N.factorization x) :=
    Finset.prod_nonneg fun _ _ => ec_abundancy_nonneg _
  have hP0 : 0 < ∏ x ∈ Z, (x : ℚ) / (x - 1) := by
    refine Finset.prod_pos fun x hx => ?_
    have h5 := ec_five_le h h3 (Finset.mem_of_mem_erase (Finset.mem_of_mem_filter x hx))
    have : (5 : ℚ) ≤ x := by exact_mod_cast h5
    exact div_pos (by linarith) (by linarith)
  have hm' : (5 : ℚ) ≤ m := by exact_mod_cast hm
  have hC0 : 0 < ecC m := by unfold ecC ecAb; positivity
  have hqlt := abundancy_prime_pow_lt hq (N.factorization q)
  have hq' : (13 : ℚ) ≤ q := by exact_mod_cast hq13
  have hA0 := ec_abundancy_nonneg (q ^ N.factorization q)
  set A := abundancy (q ^ N.factorization q)
  set x := ∏ x ∈ X, abundancy (x ^ N.factorization x)
  set z := ∏ x ∈ Z, abundancy (x ^ N.factorization x)
  set P := ∏ x ∈ Z, (x : ℚ) / (x - 1)
  have hxz : x * z ≤ ecC m * P := mul_le_mul hX hZ hZ0 hC0.le
  have hCP : 0 < ecC m * P := mul_pos hC0 hP0
  have hA : A * (q - 1) < q := by
    rw [lt_div_iff₀ (by linarith)] at hqlt
    exact hqlt
  have h2 : 2 ≤ A * (ecC m * P) := by
    rw [← hab, mul_comm z x]
    exact mul_le_mul_of_nonneg_left hxz hA0
  have : 2 * ((q : ℚ) - 1) ≤ A * (q - 1) * (ecC m * P) := by
    nlinarith
  have h4 : A * (q - 1) * (ecC m * P) < q * (ecC m * P) := mul_lt_mul_of_pos_right hA hCP
  calc 2 * ((q : ℚ) - 1) < q * (ecC m * P) := by linarith
    _ = q * ecC m * P := by ring

/-- Turning the core inequality into a contradiction from a numerical comparison. -/
private theorem ec_finish {q q0 C P H : ℚ} (hq0 : 0 < q0) (hq : q0 ≤ q) (hC : 0 ≤ C)
    (hPH : P ≤ H) (hkey : 2 * (q - 1) < q * C * P) (hnum : q0 * (C * H) < 2 * (q0 - 1)) :
    False := by
  have h1 : q * C * P ≤ q * (C * H) := by
    have := mul_le_mul_of_nonneg_left hPH (mul_nonneg (by linarith : (0 : ℚ) ≤ q) hC)
    linarith [show q * C * H = q * (C * H) by ring]
  have hK : C * H < 2 := by nlinarith
  have h2 : 0 ≤ (q - q0) * (2 - C * H) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-! ## Twenty nine exceptions `≡ 2 (mod 3)` -/

/-- The 29 smallest primes at least 5 that are `≡ 2 (mod 3)`. -/
private def ecL29 : Finset ℕ :=
  {5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89, 101, 107, 113, 131, 137, 149, 167, 173, 179,
    191, 197, 227, 233, 239, 251, 257, 263}

private theorem ecL29_card : ecL29.card = 29 := by decide

private theorem ecL29_val :
    ∏ l ∈ ecL29, (l : ℚ) / (l - 1) =
      1812498586146619514269851608750058738331 / 917440951333825631705850970112000000000 := by
  simp only [ecL29]
  norm_num [Finset.prod_insert, Finset.prod_singleton]

set_option maxHeartbeats 4000000 in
/-- A prime `5 ≤ t < 269` with `t ≡ 2 (mod 3)` lies in the envelope. -/
private theorem mem_ecL29 {t : ℕ} (htp : t.Prime) (ht5 : 5 ≤ t) (ht3 : t % 3 = 2)
    (ht : t < 269) : t ∈ ecL29 := by
  interval_cases t <;> first | omega | decide | (norm_num at htp; done)

set_option maxHeartbeats 4000000 in
/-- **Twenty nine exceptions `≡ 2 (mod 3)`.** Let `N` be an odd perfect number with special
prime `q`. If every prime factor other than `q` has exponent exactly 2, except for the primes
of a set `E` of at most 29 numbers that are all `≡ 2 (mod 3)`, then `3 ∣ N`. -/
theorem three_dvd_of_twentynine_exceptions_mod_three {N q : ℕ} {E : Finset ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : E.card ≤ 29)
    (hE3 : ∀ r ∈ E, r % 3 = 2)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → N.factorization p = 2) : 3 ∣ N := by
  by_contra h3
  have hpure := ec_pure_of_ordinary h h3 hsq fun p hp hpq hpE d hd hdp hdd => by
    have := (OPNThreeFree.exact_square_transfer h.perfect h3 (Nat.prime_of_mem_primeFactors hp)
      (hsq p hp hpq hpE) hdp hdd).2.2.2.1
    have := hE3 d hd
    omega
  have hq12 := special_mod_twelve h h3 hq hodd
  -- every prime factor other than `q` is `≡ 2 (mod 3)`
  have hres : ∀ r, r.Prime → r ∣ N → r ≠ q → r % 3 = 2 := by
    intro r hr hrN hrq
    by_cases hrE : r ∈ E
    · exact hE3 r hrE
    · exact OPNThreeFree.source_mod_three h.perfect h3 hr
        (hsq r (Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩) hrq hrE)
  -- an odd prime `≡ 1 (mod 3)` dividing `q + 1` is impossible
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
    exact ⟨Nat.prime_of_mem_primeFactors ht.1.2, ec_five_le h h3 ht.1.2, hE3 t ht.2⟩
  have hZcard : Z.card ≤ 29 :=
    (Finset.card_le_card fun t ht => (Finset.mem_filter.mp ht).2).trans hE
  have hle : ∏ t ∈ Z, (t : ℚ) / (t - 1) ≤ ∏ l ∈ ecL29, (l : ℚ) / (l - 1) :=
    ec_prod_le_of_card_le (fun t => (t : ℚ) / (t - 1)) (269 / 268) (by norm_num)
    (fun t ht => by
      have := (hZmem t ht).2.1
      have : (5 : ℚ) ≤ t := by exact_mod_cast this
      exact div_nonneg (by linarith) (by linarith))
    (fun t ht htL => by
      obtain ⟨htp, ht5, ht3⟩ := hZmem t ht
      have h269 : 269 ≤ t := by
        by_contra hc
        exact htL (mem_ecL29 htp ht5 ht3 (by omega))
      have := ec_div_pred_le (by norm_num) h269
      norm_num at this ⊢
      exact this)
    (fun l hl => by
      simp only [ecL29, Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> norm_num)
    (by rw [ecL29_card]; exact hZcard)
  rw [ecL29_val] at hle
  -- a pure prime: shape facts
  have hpureX : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E →
      p.Prime ∧ p % 12 = 11 ∧ 59 ≤ p ∧ ∃ a, Odd a ∧ 1 + p + p ^ 2 = q ^ a := by
    intro p hp hpq hpE
    have hp' := Nat.prime_of_mem_primeFactors hp
    obtain ⟨he, a, ha⟩ := hpure p hp hpq hpE
    rw [ec_sigma_sq hp'] at ha
    obtain ⟨h12, h59⟩ := ec_pure_shape h h3 hq12 hq hp' he ha
    exact ⟨hp', h12, h59, a, ec_odd_exp hp'.pos ha, ha⟩
  have hC0 : ∀ m : ℕ, 0 ≤ ecC m := fun m => by unfold ecC ecAb; positivity
  -- small special primes
  by_cases hq109 : q < 109
  · have := hq.two_le
    interval_cases q <;> try omega
    all_goals first
      | (norm_num at hq; done)
      | (refine hforce 7 ?_ ?_ ?_ <;> norm_num; done)
      | (refine hforce 19 ?_ ?_ ?_ <;> norm_num; done)
      | (refine hforce 31 ?_ ?_ ?_ <;> norm_num; done)
      | (refine hforce 37 ?_ ?_ ?_ <;> norm_num; done)
  push Not at hq109
  by_cases hqmid : q < 3541
  · -- pure primes are at least 1000
    have hmin : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → 1000 ≤ p := by
      intro p hp hpq hpE
      obtain ⟨-, -, h59, a, ha, hpa⟩ := hpureX p hp hpq hpE
      have hbig : 3541 ≤ 1 + p + p ^ 2 := by nlinarith
      have ha3 : 3 ≤ a := by
        obtain ⟨j, rfl⟩ := ha
        rcases j with _ | j
        · simp at hpa; omega
        · omega
      have hq3 : 109 ^ 3 ≤ q ^ a :=
        (Nat.pow_le_pow_left hq109 3).trans (Nat.pow_le_pow_right (by omega) ha3)
      by_contra hc
      push Not at hc
      nlinarith
    have hkey := ec_core h hq hodd h3 (m := 1000) (by norm_num) hpure hmin
    have hq' : (109 : ℚ) ≤ q := by exact_mod_cast hq109
    exact ec_finish (q0 := 109) (by norm_num) hq' (hC0 _) hle hkey
      (by norm_num [ecC, ecAb])
  · push Not at hqmid
    -- pure primes are at least 131
    have hmin : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → 131 ≤ p := by
      intro p hp hpq hpE
      obtain ⟨hp', h12, h59, a, ha, hpa⟩ := hpureX p hp hpq hpE
      have key : ∀ d, d.Prime → d ∣ 1 + p + p ^ 2 → d = q := fun d hd hdd =>
        (Nat.prime_dvd_prime_iff_eq hd hq).mp (hd.dvd_of_dvd_pow (hpa ▸ hdd))
      -- a value below `3541 ^ 2` that is a power of `q ≥ 3541` equals `q`
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
    have hkey := ec_core h hq hodd h3 (m := 131) (by norm_num) hpure hmin
    have hq' : (3541 : ℚ) ≤ q := by exact_mod_cast hqmid
    exact ec_finish (q0 := 3541) (by norm_num) hq' (hC0 _) hle hkey
      (by norm_num [ecC, ecAb])

/-! ## Five non-target exceptions -/

set_option maxHeartbeats 4000000 in
/-- **Five exceptions that are not targets.** Let `N` be an odd perfect number with special
prime `q`. If every prime factor other than `q` has exponent exactly 2, except for the primes
of a set `E` with at most five elements, and no prime of `E` divides `σ(p ^ 2)` for any of the
exponent two primes `p ∉ E`, `p ≠ q`, then `3 ∣ N`. -/
theorem three_dvd_of_five_exceptions_not_target {N q : ℕ} {E : Finset ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : E.card ≤ 5)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → N.factorization p = 2)
    (hT : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → ∀ r ∈ E, r.Prime → ¬ r ∣ σ 1 (p ^ 2)) :
    3 ∣ N := by
  by_contra h3
  have hpure := ec_pure_of_ordinary h h3 hsq fun p hp hpq hpE d hd hdp => hT p hp hpq hpE d hd hdp
  have hq12 := special_mod_twelve h h3 hq hodd
  have hmin : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → 59 ≤ p := by
    intro p hp hpq hpE
    have hp' := Nat.prime_of_mem_primeFactors hp
    obtain ⟨he, a, ha⟩ := hpure p hp hpq hpE
    rw [ec_sigma_sq hp'] at ha
    exact (ec_pure_shape h h3 hq12 hq hp' he ha).2
  have hkey := ec_core h hq hodd h3 (m := 59) (by norm_num) hpure hmin
  have hC0 : 0 ≤ ecC 59 := by unfold ecC ecAb; positivity
  set Z := (N.primeFactors.erase q).filter (· ∈ E)
  have hZmem : ∀ t ∈ Z, t.Prime ∧ 5 ≤ t ∧ t ≠ q := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_erase] at ht
    exact ⟨Nat.prime_of_mem_primeFactors ht.1.2, ec_five_le h h3 ht.1.2, ht.1.1⟩
  have hZcard : Z.card ≤ 5 :=
    (Finset.card_le_card fun t ht => (Finset.mem_filter.mp ht).2).trans hE
  have hZ0 : ∀ t ∈ Z, (0 : ℚ) ≤ (t : ℚ) / (t - 1) := fun t ht => by
    have := (hZmem t ht).2.1
    have : (5 : ℚ) ≤ t := by exact_mod_cast this
    exact div_nonneg (by linarith) (by linarith)
  by_cases h13 : q = 13
  · have hle := ec_prod_le_of_card_le (T := Z) (L := {5, 7, 11, 17, 19})
      (fun t => (t : ℚ) / (t - 1)) (23 / 22) (by norm_num) hZ0
      (fun t ht htL => by
        obtain ⟨htp, ht5, ht13⟩ := hZmem t ht
        rw [h13] at ht13
        have h23 : 23 ≤ t := by
          by_contra hc
          push Not at hc
          interval_cases t <;> first | omega | (norm_num at htp; done) | simp at htL
        have := ec_div_pred_le (by norm_num) h23
        norm_num at this ⊢
        exact this)
      (fun l hl => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl | rfl | rfl | rfl <;> norm_num)
      (by simpa using hZcard)
    have hq' : (13 : ℚ) ≤ q := by rw [h13]; norm_num
    exact ec_finish (q0 := 13) (by norm_num) hq' hC0 hle hkey
      (by norm_num [ecC, ecAb, Finset.prod_insert, Finset.prod_singleton])
  · have hq37 : 37 ≤ q := by
      have := hq.two_le
      by_contra hc
      push Not at hc
      interval_cases q <;> first | omega | (norm_num at hq; done)
    have hle := ec_prod_le_of_card_le (T := Z) (L := {5, 7, 11, 13, 17})
      (fun t => (t : ℚ) / (t - 1)) (19 / 18) (by norm_num) hZ0
      (fun t ht htL => by
        obtain ⟨htp, ht5, -⟩ := hZmem t ht
        have h19 : 19 ≤ t := by
          by_contra hc
          push Not at hc
          interval_cases t <;> first | omega | (norm_num at htp; done) | simp at htL
        have := ec_div_pred_le (by norm_num) h19
        norm_num at this ⊢
        exact this)
      (fun l hl => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl | rfl | rfl | rfl <;> norm_num)
      (by simpa using hZcard)
    have hq' : (37 : ℚ) ≤ q := by exact_mod_cast hq37
    exact ec_finish (q0 := 37) (by norm_num) hq' hC0 hle hkey
      (by norm_num [ecC, ecAb, Finset.prod_insert, Finset.prod_singleton])

/-! ## Extensions under a restriction on the special prime -/

/-- The 31 smallest primes at least 5 that are `≡ 2 (mod 3)`. -/
private def ecL31 : Finset ℕ :=
  {5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89, 101, 107, 113, 131, 137, 149, 167, 173, 179,
    191, 197, 227, 233, 239, 251, 257, 263, 269, 281}

private theorem ecL31_card : ecL31.card = 31 := by decide

private theorem ecL31_lt :
    ∏ l ∈ ecL31, (l : ℚ) / (l - 1) < 19901 / 10000 := by
  simp only [ecL31]
  norm_num [Finset.prod_insert, Finset.prod_singleton]

set_option maxHeartbeats 4000000 in
/-- A prime `5 ≤ t < 293` with `t ≡ 2 (mod 3)` lies in the 31 element envelope. -/
private theorem mem_ecL31 {t : ℕ} (htp : t.Prime) (ht5 : 5 ≤ t) (ht3 : t % 3 = 2)
    (ht : t < 293) : t ∈ ecL31 := by
  interval_cases t <;> first | omega | decide | (norm_num at htp; done)

set_option maxHeartbeats 4000000 in
/-- **Thirty one exceptions `≡ 2 (mod 3)` when `q ≠ 109`.** Let `N` be an odd perfect number
with special prime `q ≠ 109`. If every prime factor other than `q` has exponent exactly 2,
except for the primes of a set `E` of at most 31 numbers that are all `≡ 2 (mod 3)`, then
`3 ∣ N`. The restriction `q ≠ 109` is an explicit case hypothesis: for `q = 109` the
comparison used here does not reach 30 exceptions. -/
theorem three_dvd_of_thirtyone_exceptions_mod_three_of_ne {N q : ℕ} {E : Finset ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hq109 : q ≠ 109)
    (hE : E.card ≤ 31) (hE3 : ∀ r ∈ E, r % 3 = 2)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → N.factorization p = 2) : 3 ∣ N := by
  by_contra h3
  have hpure := ec_pure_of_ordinary h h3 hsq fun p hp hpq hpE d hd hdp hdd => by
    have := (OPNThreeFree.exact_square_transfer h.perfect h3 (Nat.prime_of_mem_primeFactors hp)
      (hsq p hp hpq hpE) hdp hdd).2.2.2.1
    have := hE3 d hd
    omega
  have hq12 := special_mod_twelve h h3 hq hodd
  have hres : ∀ r, r.Prime → r ∣ N → r ≠ q → r % 3 = 2 := by
    intro r hr hrN hrq
    by_cases hrE : r ∈ E
    · exact hE3 r hrE
    · exact OPNThreeFree.source_mod_three h.perfect h3 hr
        (hsq r (Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩) hrq hrE)
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
    exact ⟨Nat.prime_of_mem_primeFactors ht.1.2, ec_five_le h h3 ht.1.2, hE3 t ht.2⟩
  have hZcard : Z.card ≤ 31 :=
    (Finset.card_le_card fun t ht => (Finset.mem_filter.mp ht).2).trans hE
  have hle0 : ∏ t ∈ Z, (t : ℚ) / (t - 1) ≤ ∏ l ∈ ecL31, (l : ℚ) / (l - 1) :=
    ec_prod_le_of_card_le (fun t => (t : ℚ) / (t - 1)) (293 / 292) (by norm_num)
    (fun t ht => by
      have := (hZmem t ht).2.1
      have : (5 : ℚ) ≤ t := by exact_mod_cast this
      exact div_nonneg (by linarith) (by linarith))
    (fun t ht htL => by
      obtain ⟨htp, ht5, ht3⟩ := hZmem t ht
      have h293 : 293 ≤ t := by
        by_contra hc
        exact htL (mem_ecL31 htp ht5 ht3 (by omega))
      have := ec_div_pred_le (by norm_num) h293
      norm_num at this ⊢
      exact this)
    (fun l hl => by
      simp only [ecL31, Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by rw [ecL31_card]; exact hZcard)
  have hle : ∏ t ∈ Z, (t : ℚ) / (t - 1) ≤ 19901 / 10000 := hle0.trans ecL31_lt.le
  have hpureX : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E →
      p.Prime ∧ p % 12 = 11 ∧ 59 ≤ p ∧ ∃ a, Odd a ∧ 1 + p + p ^ 2 = q ^ a := by
    intro p hp hpq hpE
    have hp' := Nat.prime_of_mem_primeFactors hp
    obtain ⟨he, a, ha⟩ := hpure p hp hpq hpE
    rw [ec_sigma_sq hp'] at ha
    obtain ⟨h12, h59⟩ := ec_pure_shape h h3 hq12 hq hp' he ha
    exact ⟨hp', h12, h59, a, ec_odd_exp hp'.pos ha, ha⟩
  have hC0 : ∀ m : ℕ, 0 ≤ ecC m := fun m => by unfold ecC ecAb; positivity
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
    have hkey := ec_core h hq hodd h3 (m := 3000) (by norm_num) hpure hmin
    have hq' : (229 : ℚ) ≤ q := by exact_mod_cast hq229
    exact ec_finish (q0 := 229) (by norm_num) hq' (hC0 _) hle hkey
      (by norm_num [ecC, ecAb])
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
      · -- 59
        have := hone (by norm_num)
        subst this
        exact hforce 7 (by norm_num) (by norm_num) (by norm_num)
      · -- 71
        have := hone (by norm_num)
        subst this
        exact hforce 2557 (by norm_num) (by norm_num) (by norm_num)
      · have := key 19 (by norm_num) (by norm_num); omega
      · norm_num at hp'
      · have := key 7 (by norm_num) (by norm_num); omega
      · norm_num at hp'
      · -- 131
        have := hone (by norm_num)
        subst this
        exact hforce 8647 (by norm_num) (by norm_num) (by norm_num)
      · norm_num at hp'
      · norm_num at hp'
      · -- 167
        have := hone (by norm_num)
        subst this
        exact hforce 14029 (by norm_num) (by norm_num) (by norm_num)
      · have := key 7 (by norm_num) (by norm_num); omega
      · have := key 7 (by norm_num) (by norm_num); omega
      · norm_num at hp'
      · norm_num at hp'
      · have := key 73 (by norm_num) (by norm_num); omega
      · have := key 19 (by norm_num) (by norm_num); omega
    have hkey := ec_core h hq hodd h3 (m := 251) (by norm_num) hpure hmin
    have hq' : (3541 : ℚ) ≤ q := by exact_mod_cast hqmid
    exact ec_finish (q0 := 3541) (by norm_num) hq' (hC0 _) hle hkey
      (by norm_num [ecC, ecAb])

set_option maxHeartbeats 4000000 in
/-- **Six non-target exceptions when `q ≥ 61`.** Let `N` be an odd perfect number with special
prime `q ≥ 61`. If every prime factor other than `q` has exponent exactly 2, except for the
primes of a set `E` with at most six elements, and no prime of `E` divides `σ(p ^ 2)` for any
of the exponent two primes `p ∉ E`, `p ≠ q`, then `3 ∣ N`. The restriction `61 ≤ q` is an
explicit case hypothesis: for `q = 13` and `q = 37` the comparison used here does not reach
six exceptions. -/
theorem three_dvd_of_six_exceptions_not_target_of_le {N q : ℕ} {E : Finset ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hq61 : 61 ≤ q)
    (hE : E.card ≤ 6)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → N.factorization p = 2)
    (hT : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → ∀ r ∈ E, r.Prime → ¬ r ∣ σ 1 (p ^ 2)) :
    3 ∣ N := by
  by_contra h3
  have hpure := ec_pure_of_ordinary h h3 hsq fun p hp hpq hpE d hd hdp => hT p hp hpq hpE d hd hdp
  have hq12 := special_mod_twelve h h3 hq hodd
  have hpureX : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E →
      59 ≤ p ∧ ∃ a, Odd a ∧ 1 + p + p ^ 2 = q ^ a := by
    intro p hp hpq hpE
    have hp' := Nat.prime_of_mem_primeFactors hp
    obtain ⟨he, a, ha⟩ := hpure p hp hpq hpE
    rw [ec_sigma_sq hp'] at ha
    exact ⟨(ec_pure_shape h h3 hq12 hq hp' he ha).2, a, ec_odd_exp hp'.pos ha, ha⟩
  have hC0 : ∀ m : ℕ, 0 ≤ ecC m := fun m => by unfold ecC ecAb; positivity
  set Z := (N.primeFactors.erase q).filter (· ∈ E)
  have hZmem : ∀ t ∈ Z, t.Prime ∧ 5 ≤ t := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_erase] at ht
    exact ⟨Nat.prime_of_mem_primeFactors ht.1.2, ec_five_le h h3 ht.1.2⟩
  have hZcard : Z.card ≤ 6 :=
    (Finset.card_le_card fun t ht => (Finset.mem_filter.mp ht).2).trans hE
  have hle0 := ec_prod_le_of_card_le (T := Z) (L := {5, 7, 11, 13, 17, 19})
    (fun t => (t : ℚ) / (t - 1)) (23 / 22) (by norm_num)
    (fun t ht => by
      have := (hZmem t ht).2
      have : (5 : ℚ) ≤ t := by exact_mod_cast this
      exact div_nonneg (by linarith) (by linarith))
    (fun t ht htL => by
      obtain ⟨htp, ht5⟩ := hZmem t ht
      have h23 : 23 ≤ t := by
        by_contra hc
        push Not at hc
        interval_cases t <;> first | omega | (norm_num at htp; done) | simp at htL
      have := ec_div_pred_le (by norm_num) h23
      norm_num at this ⊢
      exact this)
    (fun l hl => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by simpa using hZcard)
  have hval : ∏ l ∈ ({5, 7, 11, 13, 17, 19} : Finset ℕ), (l : ℚ) / (l - 1) = 323323 / 165888 := by
    norm_num [Finset.prod_insert, Finset.prod_singleton]
  rw [hval] at hle0
  by_cases hqmid : q < 3541
  · have hmin : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ E → 476 ≤ p := by
      intro p hp hpq hpE
      obtain ⟨h59, a, ha, hpa⟩ := hpureX p hp hpq hpE
      have hbig : 3541 ≤ 1 + p + p ^ 2 := by nlinarith
      have ha3 : 3 ≤ a := by
        obtain ⟨j, rfl⟩ := ha
        rcases j with _ | j
        · simp at hpa; omega
        · omega
      have hq3 : 61 ^ 3 ≤ q ^ a :=
        (Nat.pow_le_pow_left hq61 3).trans (Nat.pow_le_pow_right (by omega) ha3)
      by_contra hc
      push Not at hc
      nlinarith
    have hkey := ec_core h hq hodd h3 (m := 476) (by norm_num) hpure hmin
    have hq' : (61 : ℚ) ≤ q := by exact_mod_cast hq61
    exact ec_finish (q0 := 61) (by norm_num) hq' (hC0 _) hle0 hkey (by norm_num [ecC, ecAb])
  · push Not at hqmid
    have hkey := ec_core h hq hodd h3 (m := 59) (by norm_num) hpure fun p hp hpq hpE =>
      (hpureX p hp hpq hpE).1
    have hq' : (3541 : ℚ) ≤ q := by exact_mod_cast hqmid
    exact ec_finish (q0 := 3541) (by norm_num) hq' (hC0 _) hle0 hkey (by norm_num [ecC, ecAb])

end OddPerfect

#print axioms OddPerfect.three_dvd_of_twentynine_exceptions_mod_three
#print axioms OddPerfect.three_dvd_of_five_exceptions_not_target
#print axioms OddPerfect.three_dvd_of_thirtyone_exceptions_mod_three_of_ne
#print axioms OddPerfect.three_dvd_of_six_exceptions_not_target_of_le
