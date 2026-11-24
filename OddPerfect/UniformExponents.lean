import OddPerfect.EqualExponents
import OddPerfect.SmallestPrime

/-!
# Uniform ordinary exponents `l - 1` for a general prime `l`

Let `N` be an odd perfect number with special prime `q` and exponent `k = v_q(N)`, and let
`l` be an odd prime such that every ordinary prime factor (every prime factor other than `q`)
has exponent exactly `l - 1`. We write

* `S = congrPrimes N q l`: the ordinary prime factors `≡ 1 (mod l)`;
* `W = otherPrimes N q l`: the ordinary prime factors `w` with `w ≠ l` and `w ≢ 1 (mod l)`.

Results, valid for every odd prime `l` at once:

1. Every `w ∈ W` is fed only by the special component: `v_w(σ(q ^ k)) = l - 1`. Hence
   `2 (∏ W) ^ (l - 1) ∣ σ(q ^ k)` and `8 (∏ W) ^ (l - 1) < 5 q ^ k`. For `w = 3` this is
   the theorem of Starni, J. Number Theory 116 (2006), 483 to 486 (p. 484), who proves it
   for every common exponent `2 β`, with no primality condition on `2 β + 1`.
2. `(∏_{s ∈ S} s/(s-1)) ^ (2 l) ≤ 2 |S| + 1`, so `≤ 2 l - 1` when `l` is ordinary.
3. Abundancy: `2 < (q/(q-1)) (l/(l-1)) ∏_S ∏_W`. For `l` ordinary this gives
   `(8 (l-1)/(5 l)) ^ (2 l) < (2 l - 1) (∏_W w/(w-1)) ^ (2 l)`, so `W` is nonempty,
   `8 · 3 ^ (l - 1) < 5 q ^ k`, `|W| ≥ 2` for `l ≥ 53`, and `|W| ≥ 3` if `3 ∉ W` and `l ≥ 37`.
4. For `w ∈ W` with `d` the order of `q` modulo `w`: `d = 1` gives `v_w(k + 1) = l - 1`;
   `d > 1` gives `d ∣ k + 1` and `v_w(q ^ d - 1) + v_w((k + 1)/d) = l - 1`. In all cases
   `w ^ (l - 1) ∣ (q ^ d - 1)(k + 1)`. For `w ∣ q + 1`: `v_w(q + 1) + v_w(k + 1) = l - 1`.
   For `w = 3` the dichotomy `q ≡ 1 (mod 3)` with `v_3(k + 1) = l - 1`, or `q ≡ 2 (mod 3)`
   with `v_3(q + 1) + v_3(k + 1) = l - 1`.
5. The case `l = q` is excluded by another module (`not_all_exponents_pred_of_special`), so
   Steps 3 and 6 assume `l` is an ordinary prime factor (`l ∈ N.primeFactors`, `l ≠ q`; note
   `l ∣ N` always holds by `not_all_exponents_eq_pred_prime`).
6. For `l` ordinary: `q ≡ 1 (mod l)`, and the exact `l`-adic ledger
   `|S| + v_l(k + 1) = l - 1`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The ordinary prime factors of `N` that are `1` modulo `l` (the set `S`). -/
def congrPrimes (N q l : ℕ) : Finset ℕ := N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1)

/-- The ordinary prime factors `w` of `N` with `w ≠ l` and `w` not `1` modulo `l`
(the set `W`). -/
def otherPrimes (N q l : ℕ) : Finset ℕ :=
  N.primeFactors.filter (fun p => p ≠ q ∧ p ≠ l ∧ p % l ≠ 1)

private lemma odd_prime_of_mem {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) :
    p.Prime ∧ p ≠ 2 :=
  ⟨Nat.prime_of_mem_primeFactors hp, fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)⟩

private lemma special_mem {N q : ℕ} (hodd : Odd (N.factorization q)) :
    q ∈ N.primeFactors :=
  Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)

private lemma five_le_special {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : 5 ≤ q := by
  have := (mod_four_special h hq hodd).1
  have := hq.two_le
  omega

/-! ## Step 1: the primes of `W` are fed only by the special component -/

/-- Step 1. For `w ∈ W`, the whole `w`-adic ledger comes from the special component:
`v_w(σ(q ^ k)) = l - 1`. Valid for every odd prime `l` (including `l = q`). -/
theorem padicValNat_sigma_special_of_mem_otherPrimes {N q l w : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : w ∈ otherPrimes N q l) :
    padicValNat w (σ 1 (q ^ N.factorization q)) = l - 1 := by
  obtain ⟨hwN, hwq, hwl, hw1⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwp, hw2⟩ := odd_prime_of_mem h hwN
  have hled := factorization_eq_sum_erase h.perfect hwp hw2
  rw [hexp w hwN hwq] at hled
  rw [hled, Finset.sum_eq_single_of_mem q (Finset.mem_erase.mpr ⟨Ne.symm hwq, special_mem hodd⟩)]
  intro p hp hpq
  obtain ⟨hpw, hpN⟩ := Finset.mem_erase.mp hp
  have hpp := Nat.prime_of_mem_primeFactors hpN
  rw [hexp p hpN hpq]
  by_contra hne
  have : Fact w.Prime := ⟨hwp⟩
  have hd : w ∣ σ 1 (p ^ (l - 1)) := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr hne)
  rcases prime_dvd_sigma_prime_pow_of_prime_length hpp hwp hl hd with h' | h'
  · exact hwl h'
  · exact hw1 h'

/-- A product of distinct primes `t` with `t ^ a ∣ n` for each has its `a`th power dividing
`n`. -/
private lemma prod_pow_dvd {T : Finset ℕ} {n a : ℕ} (hT : ∀ t ∈ T, t.Prime)
    (hd : ∀ t ∈ T, t ^ a ∣ n) : (∏ t ∈ T, t) ^ a ∣ n := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert x T hx ih =>
    rw [Finset.prod_insert hx, mul_pow]
    have hxp := hT x (Finset.mem_insert_self x T)
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hd x (Finset.mem_insert_self x T))
      (ih (fun t ht => hT t (Finset.mem_insert_of_mem ht))
        (fun t ht => hd t (Finset.mem_insert_of_mem ht)))
    refine Nat.Coprime.pow _ _ (Nat.Coprime.prod_right fun t ht => ?_)
    exact (Nat.coprime_primes hxp (hT t (Finset.mem_insert_of_mem ht))).mpr
      (fun hxt => hx (hxt ▸ ht))

/-- Step 1, product form: `2 (∏_{w ∈ W} w) ^ (l - 1) ∣ σ(q ^ k)`. -/
theorem two_mul_prod_otherPrimes_pow_dvd {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    2 * (∏ w ∈ otherPrimes N q l, w) ^ (l - 1) ∣ σ 1 (q ^ N.factorization q) := by
  have hσ0 : σ 1 (q ^ N.factorization q) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
  have hmemW : ∀ w ∈ otherPrimes N q l, w ∈ N.primeFactors := fun w hw =>
    (Finset.mem_filter.mp hw).1
  have hW : (∏ w ∈ otherPrimes N q l, w) ^ (l - 1) ∣ σ 1 (q ^ N.factorization q) := by
    refine prod_pow_dvd (fun w hw => (odd_prime_of_mem h (hmemW w hw)).1) fun w hw => ?_
    have : Fact w.Prime := ⟨(odd_prime_of_mem h (hmemW w hw)).1⟩
    exact (padicValNat_dvd_iff_le hσ0).mpr
      (padicValNat_sigma_special_of_mem_otherPrimes h hodd hl hexp hw).ge
  have h2 : 2 ∣ σ 1 (q ^ N.factorization q) := by
    have := (mod_four_special h hq hodd).1
    exact (show 2 ∣ q + 1 by omega).trans (succ_dvd_sigma_special hq hodd)
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ h2 hW
  refine Nat.Coprime.pow_right _ (Nat.Coprime.prod_right fun w hw => ?_)
  obtain ⟨hwp, hw2⟩ := odd_prime_of_mem h (hmemW w hw)
  exact (Nat.coprime_primes Nat.prime_two hwp).mpr (Ne.symm hw2)

/-- Step 1, size form: `8 (∏_{w ∈ W} w) ^ (l - 1) < 5 q ^ k`. -/
theorem eight_mul_prod_otherPrimes_pow_lt {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    8 * (∏ w ∈ otherPrimes N q l, w) ^ (l - 1) < 5 * q ^ N.factorization q := by
  have hq5 := five_le_special h hq hodd
  have hσ0 : σ 1 (q ^ N.factorization q) ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne'
  have hle : 2 * (∏ w ∈ otherPrimes N q l, w) ^ (l - 1) ≤ σ 1 (q ^ N.factorization q) :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hσ0) (two_mul_prod_otherPrimes_pow_dvd h hq hodd hl hexp)
  have hcl := sigma_prime_pow_mul_pred hq (N.factorization q)
  rw [pow_succ] at hcl
  have hQ : 1 ≤ q ^ N.factorization q := Nat.one_le_pow _ _ hq.pos
  generalize (∏ w ∈ otherPrimes N q l, w) ^ (l - 1) = X at hle ⊢
  generalize σ 1 (q ^ N.factorization q) = s at hle hcl
  generalize q ^ N.factorization q = Q at hQ hcl ⊢
  have h1 : 2 * X * (q - 1) < Q * q := by
    have := Nat.mul_le_mul_right (q - 1) hle
    have : 1 ≤ Q * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have h2 : 8 * X * q ≤ 2 * X * (q - 1) * 5 := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 5 := ⟨q - 5, by omega⟩
    rw [show r + 5 - 1 = r + 4 by omega]
    nlinarith
  have h3 : 8 * X * q < 5 * Q * q := by nlinarith
  exact Nat.lt_of_mul_lt_mul_right h3

/-! ## Step 2: the congruent part is thin -/

/-- `((c + 1)/(c - 1)) ^ n ≤ (c + n)/(c - n)` for `n < c`. -/
private lemma ratio_pow_le (c : ℚ) : ∀ n : ℕ, (n : ℚ) < c →
    ((c + 1) / (c - 1)) ^ n ≤ (c + n) / (c - n)
  | 0, hc => by simp [div_self hc.ne']
  | n + 1, hc => by
    push_cast at hc ⊢
    have h0 : (0 : ℚ) ≤ n := n.cast_nonneg
    have hn : (n : ℚ) < c := by linarith
    have ih := ratio_pow_le c n hn
    have hc1 : 0 < c - 1 := by linarith
    have hcn : 0 < c - n := by linarith
    have hcn1 : 0 < c - (n + 1) := by linarith
    rw [pow_succ]
    calc ((c + 1) / (c - 1)) ^ n * ((c + 1) / (c - 1))
        ≤ (c + n) / (c - n) * ((c + 1) / (c - 1)) :=
          mul_le_mul_of_nonneg_right ih (div_nonneg (by linarith) hc1.le)
      _ ≤ (c + (n + 1)) / (c - (n + 1)) := by
          rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hcn hc1) hcn1]
          have : (0 : ℚ) ≤ n * (n + 1) := by positivity
          nlinarith

/-- If `a ≥ j m + 1` with `j, m ≥ 1`, then `(a/(a-1)) ^ m ≤ (2 j + 1)/(2 j - 1)`. -/
private lemma div_pow_le {j m a : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) (ha : j * m + 1 ≤ a) :
    ((a : ℚ) / (a - 1)) ^ m ≤ (2 * j + 1) / (2 * j - 1) := by
  have hj' : (1 : ℚ) ≤ j := by exact_mod_cast hj
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have ha' : (j : ℚ) * m + 1 ≤ a := by exact_mod_cast ha
  have hjm : (1 : ℚ) ≤ j * m := by nlinarith
  set c : ℚ := 2 * j * m with hc
  have h1 : (a : ℚ) / (a - 1) ≤ (c + 1) / (c - 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 := pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) h1 m
  have hmc : (m : ℚ) < c := by rw [hc]; nlinarith
  have h3 := ratio_pow_le c m hmc
  have h4 : (c + m) / (c - m) = (2 * j + 1) / (2 * j - 1) := by
    rw [div_eq_div_iff (by linarith) (by linarith), hc]
    ring
  rw [← h4]
  exact h2.trans h3

/-- Telescoping bound. Let `S` be a finite set of numbers `s ≥ j m + 1` with `m ∣ s - 1`
(`j, m ≥ 1`). Then `(∏_{s ∈ S} s/(s-1)) ^ m ≤ (2 (j + |S|) - 1)/(2 j - 1)`. -/
theorem prod_div_sub_one_pow_le {m : ℕ} (hm : 1 ≤ m) (S : Finset ℕ) {j : ℕ} (hj : 1 ≤ j)
    (hS : ∀ s ∈ S, j * m + 1 ≤ s ∧ m ∣ s - 1) :
    (∏ s ∈ S, (s : ℚ) / (s - 1)) ^ m ≤ (2 * ((j : ℚ) + S.card) - 1) / (2 * j - 1) := by
  induction S using Finset.induction_on_min generalizing j with
  | empty =>
    have hj' : (1 : ℚ) ≤ j := by exact_mod_cast hj
    simp [div_self (show (2 * (j : ℚ) - 1) ≠ 0 by linarith)]
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    obtain ⟨hja, hma⟩ := hS a (Finset.mem_insert_self a S)
    have hS' : ∀ s ∈ S, (j + 1) * m + 1 ≤ s ∧ m ∣ s - 1 := by
      intro s hs
      obtain ⟨-, hms⟩ := hS s (Finset.mem_insert_of_mem hs)
      have has := ha s hs
      have hd : m ∣ s - a := by
        have := Nat.dvd_sub hms hma
        rwa [show s - 1 - (a - 1) = s - a by omega] at this
      have := Nat.le_of_dvd (by omega) hd
      refine ⟨?_, hms⟩
      rw [add_mul, one_mul]
      omega
    have ih' := ih (j := j + 1) (by omega) hS'
    have hpos : ∀ s ∈ S, (0 : ℚ) ≤ (s : ℚ) / (s - 1) := by
      intro s hs
      have h1 := (hS' s hs).1
      have : (1 : ℚ) ≤ s := by exact_mod_cast (show 1 ≤ s by nlinarith)
      exact div_nonneg (by linarith) (by linarith)
    rw [Finset.prod_insert haS, Finset.card_insert_of_notMem haS, mul_pow]
    have key := div_pow_le hj hm hja
    have hj' : (1 : ℚ) ≤ j := by exact_mod_cast hj
    calc ((a : ℚ) / (a - 1)) ^ m * (∏ s ∈ S, (s : ℚ) / (s - 1)) ^ m
        ≤ (2 * j + 1) / (2 * j - 1) *
            ((2 * (((j + 1 : ℕ) : ℚ) + S.card) - 1) / (2 * ((j + 1 : ℕ) : ℚ) - 1)) :=
          mul_le_mul key ih' (pow_nonneg (Finset.prod_nonneg hpos) _)
            (div_nonneg (by linarith) (by linarith))
      _ = (2 * ((j : ℚ) + ((S.card + 1 : ℕ) : ℚ)) - 1) / (2 * j - 1) := by
          have e1 : (2 * (j : ℚ) - 1) ≠ 0 := by linarith
          have e2 : (2 * (j : ℚ) + 1) ≠ 0 := by linarith
          push_cast
          rw [show 2 * ((j : ℚ) + 1) - 1 = 2 * j + 1 by ring, div_mul_div_comm,
            div_eq_div_iff (mul_ne_zero e1 e2) e1]
          ring

/-- Members of `S` are `1` modulo `2 l`, hence at least `2 l + 1`. -/
private lemma mem_congrPrimes_bound {N q l s : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hl2 : l ≠ 2) (hs : s ∈ congrPrimes N q l) : 1 * (2 * l) + 1 ≤ s ∧ 2 * l ∣ s - 1 := by
  obtain ⟨hsN, -, hs1⟩ := Finset.mem_filter.mp hs
  obtain ⟨hsp, hs2⟩ := odd_prime_of_mem h hsN
  have hsodd : s % 2 = 1 := Nat.odd_iff.mp (hsp.odd_of_ne_two hs2)
  have h1 : 1 ≤ s := hsp.one_lt.le
  have hld : l ∣ s - 1 := (Nat.modEq_iff_dvd' h1).mp
    (by rw [Nat.ModEq, hs1, Nat.mod_eq_of_lt hl.one_lt])
  have h2d : 2 ∣ s - 1 := by omega
  have hd : 2 * l ∣ s - 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd
    ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2)) h2d hld
  refine ⟨?_, hd⟩
  have := Nat.le_of_dvd (by have := hsp.two_le; omega) hd
  omega

/-- Step 2. `(∏_{s ∈ S} s/(s-1)) ^ (2 l) ≤ 2 |S| + 1` (the `j`th smallest element of `S` is at
least `2 j l + 1`). No hypothesis on the exponents is needed. -/
theorem prod_congrPrimes_pow_le {N q l : ℕ} (h : OddPerfect N) (hl : l.Prime) (hl2 : l ≠ 2) :
    (∏ s ∈ congrPrimes N q l, (s : ℚ) / (s - 1)) ^ (2 * l) ≤
      2 * (congrPrimes N q l).card + 1 := by
  have := prod_div_sub_one_pow_le (m := 2 * l) (by have := hl.two_le; omega)
    (congrPrimes N q l) (j := 1) le_rfl (fun s hs => mem_congrPrimes_bound h hl hl2 hs)
  convert this using 1
  push_cast
  ring

/-- Step 2, `l` ordinary: `|S| ≤ l - 1`, so `(∏_{s ∈ S} s/(s-1)) ^ (2 l) ≤ 2 l - 1`. -/
theorem prod_congrPrimes_pow_le_of_ordinary {N q l : ℕ} (h : OddPerfect N) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) :
    (∏ s ∈ congrPrimes N q l, (s : ℚ) / (s - 1)) ^ (2 * l) ≤ 2 * l - 1 := by
  have hl2 := (odd_prime_of_mem h hlN).2
  have hlodd : l % 2 = 1 := Nat.odd_iff.mp (hl.odd_of_ne_two hl2)
  have hc := card_mod_one_le h.perfect hl hl2 (β := (l - 1) / 2) (by omega)
    (fun p hp hpq => by rw [hexp p hp hpq]; omega) hlN hlq
  have hc' : ((congrPrimes N q l).card : ℚ) ≤ l - 1 := by
    have : (congrPrimes N q l).card + 1 ≤ l := by
      have := hl.two_le
      unfold congrPrimes
      omega
    have : ((congrPrimes N q l).card : ℚ) + 1 ≤ l := by exact_mod_cast this
    linarith
  have := prod_congrPrimes_pow_le h hl hl2 (q := q)
  linarith

/-! ## Step 3: the abundancy split -/

private lemma one_le_ratio {x : ℕ} (hx : 2 ≤ x) : (1 : ℚ) ≤ (x : ℚ) / (x - 1) := by
  have hx' : (2 : ℚ) ≤ x := by exact_mod_cast hx
  rw [le_div_iff₀ (by linarith)]
  linarith

private lemma prod_insert_le_mul {s : Finset ℕ} {a : ℕ} {f : ℕ → ℚ}
    (hf : ∀ x ∈ insert a s, 1 ≤ f x) : ∏ x ∈ insert a s, f x ≤ f a * ∏ x ∈ s, f x := by
  by_cases ha : a ∈ s
  · rw [Finset.insert_eq_of_mem ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 : 0 ≤ ∏ x ∈ s, f x :=
      Finset.prod_nonneg fun x hx => zero_le_one.trans (hf x (Finset.mem_insert_of_mem hx))
    nlinarith
  · rw [Finset.prod_insert ha]

/-- The prime factors of `N` lie in `{q, l} ∪ S ∪ W`, and every ratio `p/(p-1)` is at least
one, so `∏_{p ∣ N} p/(p-1) ≤ (q/(q-1)) ∏_{p ∈ insert l (S ∪ W)} p/(p-1)`. -/
private lemma prod_primeFactors_le {N q l : ℕ} (hq : q.Prime)
    (hl : l.Prime) :
    ∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1) ≤
      (q : ℚ) / (q - 1) * ∏ p ∈ insert l (congrPrimes N q l ∪ otherPrimes N q l),
        (p : ℚ) / (p - 1) := by
  have hsub : N.primeFactors ⊆ insert q (insert l (congrPrimes N q l ∪ otherPrimes N q l)) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_union, congrPrimes, otherPrimes, Finset.mem_filter]
    by_cases hpq : p = q
    · exact Or.inl hpq
    by_cases hpl : p = l
    · exact Or.inr (Or.inl hpl)
    by_cases hp1 : p % l = 1
    · exact Or.inr (Or.inr (Or.inl ⟨hp, hpq, hp1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hp, hpq, hpl, hp1⟩))
  have hge : ∀ x ∈ insert q (insert l (congrPrimes N q l ∪ otherPrimes N q l)), 2 ≤ x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_union, congrPrimes, otherPrimes,
      Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨hx, -⟩ | ⟨hx, -⟩
    · exact hq.two_le
    · exact hl.two_le
    · exact (Nat.prime_of_mem_primeFactors hx).two_le
    · exact (Nat.prime_of_mem_primeFactors hx).two_le
  calc ∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1)
      ≤ ∏ p ∈ insert q (insert l (congrPrimes N q l ∪ otherPrimes N q l)), (p : ℚ) / (p - 1) :=
        Finset.prod_le_prod_of_subset_of_one_le hsub
          (fun x hx => zero_le_one.trans (one_le_ratio (Nat.prime_of_mem_primeFactors hx).two_le))
          (fun x hx _ => one_le_ratio (hge x hx))
    _ ≤ _ := prod_insert_le_mul fun x hx => one_le_ratio (hge x hx)

private lemma disjoint_congr_other (N q l : ℕ) :
    Disjoint (congrPrimes N q l) (otherPrimes N q l) := by
  unfold congrPrimes otherPrimes
  rw [Finset.disjoint_filter]
  intro x _ h1 h2
  exact h2.2.2 h1.2

/-- Step 3, abundancy split (any odd prime `l`):
`2 < (q/(q-1)) (l/(l-1)) ∏_{s ∈ S} s/(s-1) ∏_{w ∈ W} w/(w-1)`. -/
theorem two_lt_abundancy_split {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime) (hl : l.Prime) :
    2 < (q : ℚ) / (q - 1) * ((l : ℚ) / (l - 1)) *
      (∏ s ∈ congrPrimes N q l, (s : ℚ) / (s - 1)) *
      ∏ w ∈ otherPrimes N q l, (w : ℚ) / (w - 1) := by
  have h1 := prod_primeFactors_le (N := N) hq hl
  have hge : ∀ x ∈ insert l (congrPrimes N q l ∪ otherPrimes N q l), 2 ≤ x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_union, congrPrimes, otherPrimes,
      Finset.mem_filter] at hx
    rcases hx with rfl | ⟨hx, -⟩ | ⟨hx, -⟩
    · exact hl.two_le
    · exact (Nat.prime_of_mem_primeFactors hx).two_le
    · exact (Nat.prime_of_mem_primeFactors hx).two_le
  have h2 := prod_insert_le_mul (f := fun p : ℕ => (p : ℚ) / (p - 1))
    fun x hx => one_le_ratio (hge x hx)
  rw [Finset.prod_union (disjoint_congr_other N q l)] at h2
  have hq0 : (0 : ℚ) ≤ (q : ℚ) / (q - 1) := zero_le_one.trans (one_le_ratio hq.two_le)
  have := two_lt_prod_primeFactors h
  calc (2 : ℚ) < _ := this
    _ ≤ _ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hq0
    _ = _ := by ring

/-- If `b ≥ 1`, `2 L - 1 ≤ b ^ (2 L)` and `2 L + 1 ≤ b ^ 2 (2 L - 1)`, then
`2 l - 1 ≤ b ^ (2 l)` for every `l ≥ L`. -/
private lemma two_mul_sub_one_le_pow {b : ℚ} {L : ℕ} (hb : 1 ≤ b)
    (h0 : 2 * (L : ℚ) - 1 ≤ b ^ (2 * L)) (h1 : 2 * (L : ℚ) + 1 ≤ b ^ 2 * (2 * L - 1)) :
    ∀ l, L ≤ l → 2 * (l : ℚ) - 1 ≤ b ^ (2 * l) := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => exact h0
  | succ n hn ih =>
    have hn' : (L : ℚ) ≤ n := by exact_mod_cast hn
    have hb2 : 1 ≤ b ^ 2 := one_le_pow₀ hb
    have hstep : 2 * (n : ℚ) + 1 ≤ b ^ 2 * (2 * n - 1) := by nlinarith
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
    push_cast
    nlinarith

/-- `5 ≤ l` for an odd prime `l` that is the common ordinary exponent plus one (Steuerwald
excludes `l = 3`). -/
private lemma five_le_of_uniform {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) : 5 ≤ l := by
  have h3 : l ≠ 3 := by
    rintro rfl
    exact steuerwald h hq hodd fun p hp hpq => by rw [hexp p hp hpq]
  have h4 : l ≠ 4 := by rintro rfl; norm_num at hl
  have := hl.two_le
  omega

/-- Step 3, quantitative form for `l` ordinary:
`(8 (l - 1)/(5 l)) ^ (2 l) < (2 l - 1) (∏_{w ∈ W} w/(w-1)) ^ (2 l)`. -/
theorem pow_lt_mul_prod_otherPrimes_pow {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) :
    (8 * ((l : ℚ) - 1) / (5 * l)) ^ (2 * l) <
      (2 * l - 1) * (∏ w ∈ otherPrimes N q l, (w : ℚ) / (w - 1)) ^ (2 * l) := by
  have hl2 := (odd_prime_of_mem h hlN).2
  have hq5 : (5 : ℚ) ≤ q := by exact_mod_cast five_le_special h hq hodd
  have hl3 : (3 : ℚ) ≤ l := by exact_mod_cast (show 3 ≤ l by have := hl.two_le; omega)
  set P := ∏ s ∈ congrPrimes N q l, (s : ℚ) / (s - 1) with hP
  set Q := ∏ w ∈ otherPrimes N q l, (w : ℚ) / (w - 1) with hQ
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun s hs =>
    zero_le_one.trans (one_le_ratio (Nat.prime_of_mem_primeFactors
      (Finset.mem_filter.mp hs).1).two_le)
  have hQ0 : 0 ≤ Q := Finset.prod_nonneg fun s hs =>
    zero_le_one.trans (one_le_ratio (Nat.prime_of_mem_primeFactors
      (Finset.mem_filter.mp hs).1).two_le)
  have hsplit := two_lt_abundancy_split h hq hl (N := N)
  rw [← hP, ← hQ] at hsplit
  have hq54 : (q : ℚ) / (q - 1) ≤ 5 / 4 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hl1 : (l : ℚ) - 1 ≠ 0 := by linarith
  have hlr : (l : ℚ) / (l - 1) * (P * Q) * (l - 1) = l * (P * Q) := by
    field_simp
  have hPQ : 8 * ((l : ℚ) - 1) / (5 * l) < P * Q := by
    rw [div_lt_iff₀ (by linarith)]
    have h1 : 2 < 5 / 4 * ((l : ℚ) / (l - 1) * (P * Q)) := by
      have hlq0 : 0 ≤ (l : ℚ) / (l - 1) * (P * Q) :=
        mul_nonneg (div_nonneg (by linarith) (by linarith)) (mul_nonneg hP0 hQ0)
      calc (2 : ℚ) < _ := hsplit
        _ = (q : ℚ) / (q - 1) * ((l : ℚ) / (l - 1) * (P * Q)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hq54 hlq0
    have h2 := mul_lt_mul_of_pos_right h1 (show (0 : ℚ) < l - 1 by linarith)
    rw [mul_assoc (5 / 4 : ℚ), hlr] at h2
    linarith
  have hpow := pow_lt_pow_left₀ hPQ (div_nonneg (by linarith) (by linarith))
    (show 2 * l ≠ 0 by have := hl.two_le; omega)
  rw [mul_pow] at hpow
  have hPb := prod_congrPrimes_pow_le_of_ordinary h hl hexp hlN hlq
  rw [← hP] at hPb
  have : 0 ≤ Q ^ (2 * l) := pow_nonneg hQ0 _
  nlinarith

/-- Step 3: for `l` ordinary, `W` is nonempty. -/
theorem otherPrimes_nonempty {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) : (otherPrimes N q l).Nonempty := by
  have hl2 := (odd_prime_of_mem h hlN).2
  have hl5 := five_le_of_uniform h hq hodd hl hl2 hexp
  have hl5' : (5 : ℚ) ≤ l := by exact_mod_cast hl5
  by_contra hW
  rw [Finset.not_nonempty_iff_eq_empty] at hW
  have key := pow_lt_mul_prod_otherPrimes_pow h hq hodd hl hexp hlN hlq
  rw [hW, Finset.prod_empty, one_pow, mul_one] at key
  have hb := two_mul_sub_one_le_pow (b := 32 / 25) (L := 5) (by norm_num) (by norm_num)
    (by norm_num) l hl5
  have hc : (32 / 25 : ℚ) ≤ 8 * ((l : ℚ) - 1) / (5 * l) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have := pow_le_pow_left₀ (by norm_num) hc (2 * l)
  linarith

/-- Step 3: for `l` ordinary there is an ordinary prime `w ≠ l`, `w ≢ 1 (mod l)`, with
`v_w(σ(q ^ k)) = l - 1`, so `2 w ^ (l - 1) ∣ σ(q ^ k)`. -/
theorem exists_mem_otherPrimes {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) :
    ∃ w ∈ N.primeFactors, w ≠ q ∧ w ≠ l ∧ w % l ≠ 1 ∧
      padicValNat w (σ 1 (q ^ N.factorization q)) = l - 1 ∧
      2 * w ^ (l - 1) ∣ σ 1 (q ^ N.factorization q) := by
  obtain ⟨w, hw⟩ := otherPrimes_nonempty h hq hodd hl hexp hlN hlq
  obtain ⟨hwN, hwq, hwl, hw1⟩ := Finset.mem_filter.mp hw
  refine ⟨w, hwN, hwq, hwl, hw1, padicValNat_sigma_special_of_mem_otherPrimes h hodd hl hexp hw,
    ?_⟩
  refine dvd_trans ?_ (two_mul_prod_otherPrimes_pow_dvd h hq hodd hl hexp)
  exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ hw) _)

/-- `3 ^ a ≤ (∏ W) ^ a` when `W` is nonempty. -/
private lemma three_pow_le_prod_pow {N q l : ℕ} (h : OddPerfect N)
    (hne : (otherPrimes N q l).Nonempty) (a : ℕ) :
    3 ^ a ≤ (∏ w ∈ otherPrimes N q l, w) ^ a := by
  obtain ⟨w, hw⟩ := hne
  have hge : ∀ x ∈ otherPrimes N q l, 1 ≤ x := fun x hx =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hx).1).one_lt.le
  have h1 : w ≤ ∏ x ∈ otherPrimes N q l, x := Finset.single_le_prod' hge hw
  obtain ⟨hwp, hw2⟩ := odd_prime_of_mem h (Finset.mem_filter.mp hw).1
  have : 3 ≤ w := by have := hwp.two_le; omega
  exact Nat.pow_le_pow_left (by omega) a

/-- Step 3: for `l` ordinary, `8 · 3 ^ (l - 1) < 5 q ^ k`. -/
theorem eight_mul_three_pow_lt {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) :
    8 * 3 ^ (l - 1) < 5 * q ^ N.factorization q := by
  have := three_pow_le_prod_pow h (otherPrimes_nonempty h hq hodd hl hexp hlN hlq) (l - 1)
  have := eight_mul_prod_otherPrimes_pow_lt h hq hodd hl hexp
  omega

/-- Step 3, large `l`: if `l ≥ 53` is ordinary then `W` has at least two elements. -/
theorem two_le_card_otherPrimes {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) (h53 : 53 ≤ l) :
    2 ≤ (otherPrimes N q l).card := by
  by_contra hlt
  push Not at hlt
  have hl' : (53 : ℚ) ≤ l := by exact_mod_cast h53
  have key := pow_lt_mul_prod_otherPrimes_pow h hq hodd hl hexp hlN hlq
  have hQ := prod_div_sub_one_le (otherPrimes N q l) (m := 3) (by norm_num) fun w hw => by
    obtain ⟨hwp, hw2⟩ := odd_prime_of_mem h (Finset.mem_filter.mp hw).1
    have := hwp.two_le
    omega
  have hc : ((otherPrimes N q l).card : ℚ) ≤ 1 := by exact_mod_cast (show _ ≤ 1 by omega)
  have hQ' : ∏ w ∈ otherPrimes N q l, (w : ℚ) / (w - 1) ≤ 3 / 2 := by
    have : ((otherPrimes N q l).card : ℚ) / ((3 : ℕ) - 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      push_cast
      linarith
    linarith
  have hQ0 : 0 ≤ ∏ w ∈ otherPrimes N q l, (w : ℚ) / (w - 1) := Finset.prod_nonneg fun s hs =>
    zero_le_one.trans (one_le_ratio (Nat.prime_of_mem_primeFactors
      (Finset.mem_filter.mp hs).1).two_le)
  have hQp := pow_le_pow_left₀ hQ0 hQ' (2 * l)
  have hb := two_mul_sub_one_le_pow (b := 209 / 200) (L := 53) (by norm_num) (by norm_num)
    (by norm_num) l h53
  have hc' : (3 / 2 : ℚ) * (209 / 200) ≤ 8 * ((l : ℚ) - 1) / (5 * l) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hp := pow_le_pow_left₀ (by norm_num) hc' (2 * l)
  rw [mul_pow] at hp
  have h32 : (0 : ℚ) < (3 / 2) ^ (2 * l) := by positivity
  have hl1 : (0 : ℚ) ≤ 2 * l - 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hQp hl1, mul_le_mul_of_nonneg_left hb h32.le]

/-- Step 3, large `l` without `3`: if `l ≥ 37` is ordinary and `3 ∉ W`, then `W` has at least
three elements. -/
theorem three_le_card_otherPrimes_of_three_not_mem {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) (h37 : 37 ≤ l) (h3 : 3 ∉ otherPrimes N q l) :
    3 ≤ (otherPrimes N q l).card := by
  by_contra hlt
  push Not at hlt
  have hl' : (37 : ℚ) ≤ l := by exact_mod_cast h37
  have key := pow_lt_mul_prod_otherPrimes_pow h hq hodd hl hexp hlN hlq
  have hT := prod_div_sub_one_mul_le_of_card_lt (S := otherPrimes N q l)
    (T := {5, 7, 11}) (L := 11)
    (by intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht; omega)
    (fun s hs => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hs).1).two_le)
    (by
      intro s hs hsT
      obtain ⟨hsp, hs2⟩ := odd_prime_of_mem h (Finset.mem_filter.mp hs).1
      have hs3 : s ≠ 3 := fun e => h3 (e ▸ hs)
      have := hsp.two_le
      by_contra hle
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsT
      interval_cases s
      all_goals first | omega | norm_num at hsp)
    (by rw [show ({5, 7, 11} : Finset ℕ).card = 3 by rfl]; omega)
  have hval : ∏ t ∈ ({5, 7, 11} : Finset ℕ), (t : ℚ) / (t - 1) =
      35 / 24 * ((11 : ℕ) / ((11 : ℕ) - 1)) := by
    norm_num [Finset.prod_insert]
  rw [hval] at hT
  have hQ' : ∏ w ∈ otherPrimes N q l, (w : ℚ) / (w - 1) ≤ 35 / 24 := by
    have : (0 : ℚ) < (11 : ℕ) / ((11 : ℕ) - 1) := by norm_num
    nlinarith
  have hQ0 : 0 ≤ ∏ w ∈ otherPrimes N q l, (w : ℚ) / (w - 1) := Finset.prod_nonneg fun s hs =>
    zero_le_one.trans (one_le_ratio (Nat.prime_of_mem_primeFactors
      (Finset.mem_filter.mp hs).1).two_le)
  have hQp := pow_le_pow_left₀ hQ0 hQ' (2 * l)
  have hb := two_mul_sub_one_le_pow (b := 16 / 15) (L := 37) (by norm_num) (by norm_num)
    (by norm_num) l h37
  have hc' : (35 / 24 : ℚ) * (16 / 15) ≤ 8 * ((l : ℚ) - 1) / (5 * l) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hp := pow_le_pow_left₀ (by norm_num) hc' (2 * l)
  rw [mul_pow] at hp
  have h32 : (0 : ℚ) < (35 / 24) ^ (2 * l) := by positivity
  have hl1 : (0 : ℚ) ≤ 2 * l - 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hQp hl1, mul_le_mul_of_nonneg_left hb h32.le]

/-! ## Step 4: consequences of `w ^ (l - 1) ∥ σ(q ^ k)` -/

private lemma dvd_sigma_of_mem_otherPrimes {N q l w : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : w ∈ otherPrimes N q l) : w ∣ σ 1 (q ^ N.factorization q) := by
  have : Fact w.Prime := ⟨(odd_prime_of_mem h (Finset.mem_filter.mp hw).1).1⟩
  refine dvd_of_one_le_padicValNat ?_
  rw [padicValNat_sigma_special_of_mem_otherPrimes h hodd hl hexp hw]
  have := hl.two_le
  omega

/-- Step 4, order one: if `w ∈ W` and `q ≡ 1 (mod w)`, then `v_w(k + 1) = l - 1`. -/
theorem padicValNat_succ_of_mem_otherPrimes_of_mod_eq_one {N q l w : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : w ∈ otherPrimes N q l) (hqw : q % w = 1) :
    padicValNat w (N.factorization q + 1) = l - 1 := by
  obtain ⟨hwp, hw2⟩ := odd_prime_of_mem h (Finset.mem_filter.mp hw).1
  rw [← padicValNat_sigma_of_mod_eq_one hq hwp hw2 hqw]
  exact padicValNat_sigma_special_of_mem_otherPrimes h hodd hl hexp hw

/-- Step 4, order above one: if `w ∈ W` and the order `d` of `q` modulo `w` exceeds one, then
`d ∣ k + 1` and `v_w(q ^ d - 1) + v_w((k + 1)/d) = l - 1`. -/
theorem padicValNat_of_mem_otherPrimes_of_one_lt_orderOf {N q l w : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : w ∈ otherPrimes N q l) (h1 : 1 < orderOf (q : ZMod w)) :
    orderOf (q : ZMod w) ∣ N.factorization q + 1 ∧
      padicValNat w (q ^ orderOf (q : ZMod w) - 1) +
        padicValNat w ((N.factorization q + 1) / orderOf (q : ZMod w)) = l - 1 := by
  obtain ⟨hwN, hwq, -, -⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwp, hw2⟩ := odd_prime_of_mem h hwN
  have hd := (dvd_sigma_prime_pow_iff hq hwp (Ne.symm hwq)).mp
    (dvd_sigma_of_mem_otherPrimes h hodd hl hexp hw)
  rw [if_neg (by omega)] at hd
  refine ⟨hd, ?_⟩
  rw [← padicValNat_sigma_prime_pow_of_orderOf_dvd hq hwp hw2 (Ne.symm hwq) h1 hd]
  exact padicValNat_sigma_special_of_mem_otherPrimes h hodd hl hexp hw

/-- Step 4, unified corollary: for `w ∈ W` with `d` the order of `q` modulo `w`,
`w ^ (l - 1) ∣ (q ^ d - 1)(k + 1)`. -/
theorem pow_dvd_mul_of_mem_otherPrimes {N q l w : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : w ∈ otherPrimes N q l) :
    w ^ (l - 1) ∣ (q ^ orderOf (q : ZMod w) - 1) * (N.factorization q + 1) := by
  obtain ⟨hwN, -, -, -⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwp, -⟩ := odd_prime_of_mem h hwN
  have : Fact w.Prime := ⟨hwp⟩
  rcases Nat.lt_trichotomy (orderOf (q : ZMod w)) 1 with h0 | h1 | h1
  · rw [show orderOf (q : ZMod w) = 0 by omega, pow_zero, Nat.sub_self, zero_mul]
    exact dvd_zero _
  · have hc : (q : ZMod w) = 1 := orderOf_eq_one_iff.mp h1
    have hqw : q % w = 1 := by
      have := (ZMod.natCast_eq_natCast_iff' q 1 w).mp (by simpa using hc)
      rwa [Nat.mod_eq_of_lt hwp.one_lt] at this
    have hv := padicValNat_succ_of_mem_otherPrimes_of_mod_eq_one h hq hodd hl hexp hw hqw
    refine Dvd.dvd.mul_left ?_ _
    rw [← hv]
    exact pow_padicValNat_dvd
  · obtain ⟨hdvd, hv⟩ := padicValNat_of_mem_otherPrimes_of_one_lt_orderOf h hq hodd hl hexp hw h1
    have hq1 : 1 < q ^ orderOf (q : ZMod w) := Nat.one_lt_pow (by omega) hq.one_lt
    have hk0 : N.factorization q + 1 ≠ 0 := by omega
    have hmul : padicValNat w ((N.factorization q + 1) / orderOf (q : ZMod w)) ≤
        padicValNat w (N.factorization q + 1) := by
      obtain ⟨c, hc⟩ := hdvd
      have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; omega
      rw [hc, Nat.mul_div_cancel_left _ (by omega), padicValNat.mul (by omega) hc0]
      omega
    rw [padicValNat_dvd_iff_le (mul_ne_zero (by omega) hk0), padicValNat.mul (by omega) hk0]
    omega

/-- Step 4, the case `w ∣ q + 1` (order two): `v_w(q + 1) + v_w(k + 1) = l - 1`. -/
theorem padicValNat_add_of_mem_otherPrimes_of_dvd_succ {N q l w : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : w ∈ otherPrimes N q l) (hwq1 : w ∣ q + 1) :
    padicValNat w (q + 1) + padicValNat w (N.factorization q + 1) = l - 1 := by
  obtain ⟨hwN, -, -, -⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwp, hw2⟩ := odd_prime_of_mem h hwN
  have : Fact w.Prime := ⟨hwp⟩
  have : Fact (2 < w) := ⟨by have := hwp.two_le; omega⟩
  have hneg : (q : ZMod w) = -1 := by
    have : ((q + 1 : ℕ) : ZMod w) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hwq1
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hord : orderOf (q : ZMod w) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime
    · rw [hneg]; norm_num
    · rw [hneg]; exact ZMod.neg_one_ne_one
  obtain ⟨hdvd, hv⟩ := padicValNat_of_mem_otherPrimes_of_one_lt_orderOf h hq hodd hl hexp hw
    (by omega)
  rw [hord] at hdvd hv
  have hw2' : ¬ w ∣ 2 := fun h2 => hw2 ((Nat.prime_dvd_prime_iff_eq hwp Nat.prime_two).mp h2)
  have hq1 : ¬ w ∣ q - 1 := by
    intro hd
    have := Nat.dvd_sub hwq1 hd
    rw [show q + 1 - (q - 1) = 2 by have := hq.two_le; omega] at this
    exact hw2' this
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    have := hq.one_lt
    zify [Nat.one_le_pow 2 q hq.pos, this.le]
    ring
  rw [hsq, padicValNat.mul (by omega) (by have := hq.one_lt; omega),
    padicValNat.eq_zero_of_not_dvd hq1] at hv
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Nat.mul_div_cancel_left _ (by norm_num)] at hv
  have hc0 : c ≠ 0 := by rintro rfl; omega
  rw [hc, padicValNat.mul (by norm_num) hc0, padicValNat.eq_zero_of_not_dvd hw2']
  omega

/-- Step 4, the case `w ∣ q + 1`, divisibility form: `w ^ (l - 1) ∣ (q + 1)(k + 1)`. -/
theorem pow_dvd_succ_mul_succ_of_mem_otherPrimes {N q l w : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hw : w ∈ otherPrimes N q l) (hwq1 : w ∣ q + 1) :
    w ^ (l - 1) ∣ (q + 1) * (N.factorization q + 1) := by
  have : Fact w.Prime := ⟨(odd_prime_of_mem h (Finset.mem_filter.mp hw).1).1⟩
  have hv := padicValNat_add_of_mem_otherPrimes_of_dvd_succ h hq hodd hl hexp hw hwq1
  rw [padicValNat_dvd_iff_le (by positivity), padicValNat.mul (by omega) (by omega)]
  omega

/-- Step 4, the prime `3`: if `3 ∈ W` then either `q ≡ 1 (mod 3)` and `v_3(k + 1) = l - 1`,
or `q ≡ 2 (mod 3)` and `v_3(q + 1) + v_3(k + 1) = l - 1`. (Since `k + 1` is even,
`v_3(k + 1) = v_3((k + 1)/2)`.) -/
theorem three_mem_otherPrimes_dichotomy {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (h3 : 3 ∈ otherPrimes N q l) :
    (q % 3 = 1 ∧ padicValNat 3 (N.factorization q + 1) = l - 1) ∨
      (q % 3 = 2 ∧ padicValNat 3 (q + 1) + padicValNat 3 (N.factorization q + 1) = l - 1) := by
  have hv := padicValNat_sigma_special_of_mem_otherPrimes h hodd hl hexp h3
  rw [padicValNat_three_sigma_prime_pow hq] at hv
  unfold threeWeight at hv
  have hq4 := (mod_four_special h hq hodd).1
  have hq3 : q ≠ 3 := by omega
  have hq30 : q % 3 ≠ 0 := fun h0 =>
    hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp (Nat.dvd_of_mod_eq_zero h0)).symm
  rw [if_neg hq3] at hv
  by_cases h1 : q % 3 = 1
  · rw [if_pos h1] at hv
    exact Or.inl ⟨h1, hv⟩
  · rw [if_neg h1, if_neg (Nat.not_even_iff_odd.mpr hodd)] at hv
    exact Or.inr ⟨by omega, hv⟩

/-! ## Step 6: the `q`-adic and `l`-adic ledgers -/

/-- Step 6. If `l` is ordinary then `q ≡ 1 (mod l)`: the `q`-adic ledger `k ≥ 1` needs an
ordinary component `σ(p ^ (l - 1))` divisible by `q`, whose prime factors are `l` or `≡ 1`. -/
theorem special_mod_eq_one {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) (hlq : l ≠ q) :
    q % l = 1 := by
  have hq2 : q ≠ 2 := by have := five_le_special h hq hodd; omega
  have hled := factorization_eq_sum_erase h.perfect hq hq2
  have hk : N.factorization q ≠ 0 := by rintro h0; rw [h0] at hodd; simp at hodd
  rw [hled] at hk
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
  have : Fact q.Prime := ⟨hq⟩
  have hd : q ∣ σ 1 (p ^ (l - 1)) := by
    rw [← hexp p hpN hpq]
    exact dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr hne)
  rcases prime_dvd_sigma_prime_pow_of_prime_length (Nat.prime_of_mem_primeFactors hpN) hq hl hd
    with h' | h'
  · exact absurd h'.symm hlq
  · exact h'

/-- Step 6. The exact `l`-adic ledger for `l` ordinary: `|S| + v_l(k + 1) = l - 1`. Each
`s ∈ S` contributes `v_l(σ(s ^ (l - 1))) = 1`, the other ordinary components contribute `0`,
and the special component contributes `v_l(σ(q ^ k)) = v_l(k + 1)` since `q ≡ 1 (mod l)`. -/
theorem card_congrPrimes_add_padicValNat {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) :
    (congrPrimes N q l).card + padicValNat l (N.factorization q + 1) = l - 1 := by
  have : Fact l.Prime := ⟨hl⟩
  have hl2 := (odd_prime_of_mem h hlN).2
  have hled := factorization_eq_sum_erase h.perfect hl hl2
  rw [hexp l hlN hlq] at hled
  have hqmem : q ∈ N.primeFactors.erase l := Finset.mem_erase.mpr ⟨Ne.symm hlq, special_mem hodd⟩
  rw [← Finset.add_sum_erase _ _ hqmem,
    padicValNat_sigma_of_mod_eq_one hq hl hl2 (special_mod_eq_one h hq hodd hl hexp hlq)] at hled
  have hset : congrPrimes N q l = ((N.primeFactors.erase l).erase q).filter (fun p => p % l = 1) := by
    ext p
    simp only [congrPrimes, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hp, hpq, hp1⟩
      refine ⟨⟨hpq, ?_, hp⟩, hp1⟩
      rintro rfl
      rw [Nat.mod_self] at hp1
      omega
    · rintro ⟨⟨hpq, -, hp⟩, hp1⟩
      exact ⟨hp, hpq, hp1⟩
  have hsum : ∑ p ∈ (N.primeFactors.erase l).erase q, padicValNat l (σ 1 (p ^ N.factorization p))
      = (congrPrimes N q l).card := by
    rw [hset, Finset.card_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpq, hp'⟩ := Finset.mem_erase.mp hp
    obtain ⟨hpl, hpN⟩ := Finset.mem_erase.mp hp'
    have hpp := Nat.prime_of_mem_primeFactors hpN
    rw [hexp p hpN hpq]
    split_ifs with h1
    · rw [padicValNat_sigma_of_mod_eq_one hpp hl hl2 h1, Nat.sub_add_cancel hl.one_lt.le,
        padicValNat_self]
    · exact padicValNat_sigma_pred_of_mod_ne_one hpp hl hpl h1
  omega

end OddPerfect

#print axioms OddPerfect.padicValNat_sigma_special_of_mem_otherPrimes
#print axioms OddPerfect.two_mul_prod_otherPrimes_pow_dvd
#print axioms OddPerfect.eight_mul_prod_otherPrimes_pow_lt
#print axioms OddPerfect.prod_div_sub_one_pow_le
#print axioms OddPerfect.prod_congrPrimes_pow_le
#print axioms OddPerfect.prod_congrPrimes_pow_le_of_ordinary
#print axioms OddPerfect.two_lt_abundancy_split
#print axioms OddPerfect.pow_lt_mul_prod_otherPrimes_pow
#print axioms OddPerfect.otherPrimes_nonempty
#print axioms OddPerfect.exists_mem_otherPrimes
#print axioms OddPerfect.eight_mul_three_pow_lt
#print axioms OddPerfect.two_le_card_otherPrimes
#print axioms OddPerfect.three_le_card_otherPrimes_of_three_not_mem
#print axioms OddPerfect.padicValNat_succ_of_mem_otherPrimes_of_mod_eq_one
#print axioms OddPerfect.padicValNat_of_mem_otherPrimes_of_one_lt_orderOf
#print axioms OddPerfect.pow_dvd_mul_of_mem_otherPrimes
#print axioms OddPerfect.padicValNat_add_of_mem_otherPrimes_of_dvd_succ
#print axioms OddPerfect.pow_dvd_succ_mul_succ_of_mem_otherPrimes
#print axioms OddPerfect.three_mem_otherPrimes_dichotomy
#print axioms OddPerfect.special_mod_eq_one
#print axioms OddPerfect.card_congrPrimes_add_padicValNat
