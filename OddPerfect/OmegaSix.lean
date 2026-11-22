import OddPerfect.Certificate
import OddPerfect.OmegaFour
import OddPerfect.SmallestPrime

/-!
# Gradshtein and Kühnel: an odd perfect number has at least six prime factors

The proof is a verified branch and bound search over the prime factors of `N` in increasing
order, run by the kernel (`decide +kernel`) and justified once by `solve_sound`.

A search state is a list of entries `(p, k, ex)`: `p` is a prime factor of `N` whose exponent
is exactly `k` (when `ex`) or at least `k`; there are `j` further prime factors, all above `m`.
Writing `L` and `U` for the products of the lower and upper abundancy bounds of the entries
(`σ(p^k)/p^k`, and `p/(p-1)` for an inexact entry), and using `σ(N)/N = 2`:

* `L > 2`, or `L ≥ 2` with `j > 0`, is impossible (abundant divisor).
* Two exact odd exponents contradict Euler's theorem.
* For an exact entry, the part `c` of `σ(p^k)` coprime to `2` and to the listed primes is a
  product of unlisted prime factors of `N`. If `c > 1`, then `c` bounds the next prime from
  above, and `c` is impossible when `j = 0` or `c ≤ m`.
* With `j = 0`, all exact: `L = 2` is required; some inexact: `U > 2` is required.
* With `j > 0`, the smallest unlisted prime `q` satisfies `U (q/(q-1))^j > 2`, and when
  `j = 1` also `q (2 - L) ≥ L`. The search enumerates every prime `q` in that window.
* Otherwise an inexact entry is split into the exact case and the next admissible exponent.

Starting from `3` (which divides `N` when `ω(N) ≤ 6`), the search closes `ω(N) = 4` and
`ω(N) = 5`.
-/

set_option Elab.async false

namespace OddPerfect.OmegaSixSearch

open Cert (geom)

/-- An entry: a prime `p` with exponent `k`, exact when `ex`. -/
structure Ent where
  p : ℕ
  k : ℕ
  ex : Bool

/-- Remove all factors `y` from `g` (fuel `n`). -/
def remove (y : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | n + 1, g => if 2 ≤ y ∧ g ≠ 0 ∧ g % y = 0 then remove y n (g / y) else g

/-- Remove all factors from a list. -/
def strip (g : ℕ) : List ℕ → ℕ
  | [] => g
  | y :: ys => strip (remove y g g) ys

/-- Trial division up to the square root (fuel `n`). -/
def noDiv (q : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, d => q < d * d || (q % d != 0 && noDiv q n (d + 1))

/-- A primality test that is true on every prime. -/
def isPrimeQ (q : ℕ) : Bool := 2 ≤ q && noDiv q q 2

/-- An exponent admissible by Euler's theorem. -/
def valid (p e : ℕ) : Bool := e % 2 == 0 || (p % 4 == 1 && e % 4 == 1)

/-- The next admissible exponent above `k`. -/
def nextValid (p k : ℕ) : ℕ := if valid p (k + 1) then k + 1 else k + 2

/-- The least admissible positive exponent of `q`. -/
def kmin (q : ℕ) : ℕ := if q % 4 = 1 then 1 else 2

/-- Numerator of the lower abundancy bound. -/
def lnum (l : List Ent) : ℕ := (l.map fun e => geom e.p e.k).prod
/-- Denominator of the lower abundancy bound. -/
def lden (l : List Ent) : ℕ := (l.map fun e => e.p ^ e.k).prod
/-- Numerator of the upper abundancy bound. -/
def unum (l : List Ent) : ℕ := (l.map fun e => if e.ex then geom e.p e.k else e.p).prod
/-- Denominator of the upper abundancy bound. -/
def uden (l : List Ent) : ℕ := (l.map fun e => if e.ex then e.p ^ e.k else e.p - 1).prod

/-- All entries are exact. -/
def allEx (l : List Ent) : Bool := l.all (·.ex)

/-- The condition `U (q/(q-1))^j > 2` with `U = un/ud`. -/
def cond (un ud j q : ℕ) : Bool := 2 * ud * (q - 1) ^ j < un * q ^ j

/-- Bisection for the last `q` satisfying `cond`; its result is checked afterwards. -/
def bsearch (un ud j : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, a, _ => a
  | n + 1, a, b => if b ≤ a + 1 then a else
      if cond un ud j ((a + b) / 2) then bsearch un ud j n ((a + b) / 2) b
      else bsearch un ud j n a ((a + b) / 2)

/-- Minimum of a list. -/
def minB : List ℕ → ℕ
  | [] => 0
  | [a] => a
  | a :: l => min a (minB l)

/-- Index of the inexact entry with the largest abundancy gap. -/
def pickAux : List Ent → ℕ → ℕ → ℕ → ℕ → ℕ
  | [], _, bi, _, _ => bi
  | e :: l, i, bi, bn, bd =>
      if !e.ex && bn * ((e.p - 1) * geom e.p e.k) < e.p * e.p ^ e.k * bd then
        pickAux l (i + 1) i (e.p * e.p ^ e.k) ((e.p - 1) * geom e.p e.k)
      else pickAux l (i + 1) bi bn bd

/-- The entry to split. -/
def pick (l : List Ent) : ℕ := pickAux l 0 0 0 1

/-- The cofactors of the exact component divisor sums that are not one. -/
def chainList (l : List Ent) : List ℕ :=
  ((l.filter (·.ex)).map fun e => strip (geom e.p e.k) (2 :: l.map Ent.p)).filter (· != 1)

/-- The abundancy test. -/
def deadAbund (l : List Ent) (j : ℕ) : Bool :=
  2 * lden l < lnum l || (0 < j && 2 * lden l ≤ lnum l)

/-- The parity test. -/
def deadParity (l : List Ent) : Bool :=
  l.any fun a => l.any fun b => a.ex && b.ex && a.k % 2 == 1 && b.k % 2 == 1 && a.p != b.p

/-- The factor chain test. -/
def deadChain (l : List Ent) (j m : ℕ) : Bool :=
  (chainList l).any fun c => j == 0 || c ≤ m

/-- The candidate abundancy bound for the next prime. -/
def bU (l : List Ent) (j m : ℕ) : ℕ :=
  bsearch (unum l) (uden l) j 200 m (m + 2 * j * unum l / (2 * uden l - unum l) + 2)

/-- Upper bounds for the next prime. -/
def bounds (l : List Ent) (j m : ℕ) : List ℕ :=
  (if unum l < 2 * uden l ∧ 1 ≤ bU l j m ∧ cond (unum l) (uden l) j (bU l j m + 1) = false
    then [bU l j m] else []) ++ chainList l

/-- Lower bound for the next prime. -/
def lowB (l : List Ent) (j m : ℕ) : ℕ :=
  if j = 1 ∧ lnum l < 2 * lden l then
    max (m + 1) ((lnum l + (2 * lden l - lnum l) - 1) / (2 * lden l - lnum l))
  else m + 1

/-- Window width below which the search enumerates rather than splits. -/
def W : ℕ := 10

/-- The search. `true` means no odd perfect number satisfies the state. -/
def solve : ℕ → List Ent → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | f + 1, l, j, m =>
    deadAbund l j || deadParity l || deadChain l j m ||
    (if j = 0 then
      (if allEx l then lnum l != 2 * lden l
       else unum l ≤ 2 * uden l ||
        (solve f (l.set (pick l) ⟨(l.getD (pick l) ⟨0, 0, true⟩).p,
            (l.getD (pick l) ⟨0, 0, true⟩).k, true⟩) j m &&
         solve f (l.set (pick l) ⟨(l.getD (pick l) ⟨0, 0, true⟩).p,
            nextValid (l.getD (pick l) ⟨0, 0, true⟩).p (l.getD (pick l) ⟨0, 0, true⟩).k,
              false⟩) j m))
     else
      (if bounds l j m ≠ [] ∧ (minB (bounds l j m) ≤ lowB l j m + W ∨ allEx l = true ∨ 2 ≤ j) then
        (List.range' (lowB l j m) (minB (bounds l j m) + 1 - lowB l j m)).all fun q =>
          !isPrimeQ q || solve f (l ++ [⟨q, kmin q, false⟩]) (j - 1) q
       else
        !allEx l &&
        (solve f (l.set (pick l) ⟨(l.getD (pick l) ⟨0, 0, true⟩).p,
            (l.getD (pick l) ⟨0, 0, true⟩).k, true⟩) j m &&
         solve f (l.set (pick l) ⟨(l.getD (pick l) ⟨0, 0, true⟩).p,
            nextValid (l.getD (pick l) ⟨0, 0, true⟩).p (l.getD (pick l) ⟨0, 0, true⟩).k,
              false⟩) j m)))



open ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem remove_dvd (y : ℕ) : ∀ n g, remove y n g ∣ g
  | 0, g => by simp [remove]
  | n + 1, g => by
    unfold remove
    split_ifs with h
    · exact (remove_dvd y n (g / y)).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h.2.2))
    · exact dvd_rfl

private theorem remove_ne_zero (y : ℕ) : ∀ n g, g ≠ 0 → remove y n g ≠ 0
  | 0, g, hg => by simpa [remove] using hg
  | n + 1, g, hg => by
    unfold remove
    split_ifs with h
    · apply remove_ne_zero y n
      have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hg) (Nat.dvd_of_mod_eq_zero h.2.2))
        (by omega : 0 < y)
      omega
    · exact hg

private theorem not_dvd_remove {y : ℕ} (hy : 2 ≤ y) : ∀ n g, g ≠ 0 → g < 2 ^ n → ¬ y ∣ remove y n g
  | 0, g, hg, hlt => by simp at hlt; omega
  | n + 1, g, hg, hlt => by
    unfold remove
    split_ifs with h
    · apply not_dvd_remove hy n
      · have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hg) (Nat.dvd_of_mod_eq_zero h.2.2))
          (by omega : 0 < y)
        omega
      · have h1 : g / y ≤ g / 2 := Nat.div_le_div_left hy (by norm_num)
        have h2 : g / 2 < 2 ^ n := by rw [pow_succ] at hlt; omega
        omega
    · intro hd
      exact h ⟨hy, hg, Nat.mod_eq_zero_of_dvd hd⟩

private theorem strip_dvd : ∀ (ys : List ℕ) (g : ℕ), strip g ys ∣ g
  | [], g => by simp [strip]
  | y :: ys, g => (strip_dvd ys _).trans (remove_dvd y g g)

private theorem strip_ne_zero : ∀ (ys : List ℕ) (g : ℕ), g ≠ 0 → strip g ys ≠ 0
  | [], g, hg => hg
  | y :: ys, g, hg => strip_ne_zero ys _ (remove_ne_zero y g g hg)

private theorem not_dvd_strip : ∀ (ys : List ℕ) (g : ℕ) {y : ℕ}, y ∈ ys → 2 ≤ y → g ≠ 0 →
    ¬ y ∣ strip g ys
  | [], _, _, hy, _, _ => by simp at hy
  | z :: ys, g, y, hy, h2, hg => by
    intro hd
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact not_dvd_remove h2 g g hg Nat.lt_two_pow_self (hd.trans (strip_dvd ys _))
    · exact not_dvd_strip ys _ hy' h2 (remove_ne_zero z g g hg) hd

private theorem noDiv_of_prime {q : ℕ} (hq : q.Prime) : ∀ n d, 2 ≤ d → noDiv q n d = true
  | 0, _, _ => rfl
  | n + 1, d, hd => by
    simp only [noDiv, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq]
    by_cases hlt : q < d * d
    · exact Or.inl hlt
    · right
      refine ⟨fun h0 => ?_, noDiv_of_prime hq n (d + 1) (by omega)⟩
      rcases hq.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h0) with h | h
      · omega
      · subst h; nlinarith

private theorem isPrimeQ_of_prime {q : ℕ} (hq : q.Prime) : isPrimeQ q = true := by
  simp [isPrimeQ, hq.two_le, noDiv_of_prime hq q 2 le_rfl]

variable {N : ℕ}

/-- The exponent of a prime of an odd perfect number is even, or the prime and the exponent
are both `1 mod 4`. -/
private theorem valid_fact (h : OddPerfect N) {p : ℕ} (hp : p.Prime) :
    valid p (N.factorization p) = true := by
  obtain ⟨q, -, -, hq4, hqe, hev⟩ := exists_special_prime h
  simp only [valid, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
  by_cases hpq : p = q
  · subst hpq; exact Or.inr ⟨hq4, hqe⟩
  · exact Or.inl (Nat.even_iff.mp (hev p hp hpq))

private theorem nextValid_le {p k f : ℕ} (hk : k < f) (hf : valid p f = true) : nextValid p k ≤ f := by
  unfold nextValid
  split_ifs with h
  · omega
  · rcases Nat.lt_or_ge (k + 1) f with h1 | h1
    · omega
    · exact absurd (show f = k + 1 by omega ▸ hf) h

/-- The exponent of a prime factor `q` is at least `kmin q`: at least 1 when `q ≡ 1 (mod 4)`,
at least 2 otherwise. -/
theorem kmin_le (h : OddPerfect N) {q : ℕ} (hq : q ∈ N.primeFactors) :
    kmin q ≤ N.factorization q := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  have h1 : 1 ≤ N.factorization q :=
    (hqp.dvd_iff_one_le_factorization h.ne_zero).mp (Nat.dvd_of_mem_primeFactors hq)
  have hv := valid_fact h hqp
  simp only [valid, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hv
  unfold kmin
  split_ifs with h4
  · exact h1
  · rcases hv with hv | hv
    · omega
    · exact absurd hv.1 h4

/-- The meaning of an entry for `N`. -/
def Ent.Holds (N : ℕ) (e : Ent) : Prop :=
  e.p ∈ N.primeFactors ∧ e.k ≤ N.factorization e.p ∧ (e.ex = true → N.factorization e.p = e.k)

/-- The meaning of a search state: `N` is an odd perfect number, the entries are distinct
prime factors of `N` with the recorded exponents, there are `j` further prime factors, and
all of them exceed `m`. -/
def Holds (N : ℕ) (l : List Ent) (j m : ℕ) : Prop :=
  OddPerfect N ∧ (l.map Ent.p).Nodup ∧ (∀ e ∈ l, e.Holds N) ∧
    N.primeFactors.card = l.length + j ∧ ∀ q ∈ N.primeFactors, q ∉ l.map Ent.p → m < q

/-- Lower abundancy bound of an entry. -/
def lo (e : Ent) : ℚ := (geom e.p e.k : ℚ) / ((e.p ^ e.k : ℕ) : ℚ)

/-- Upper abundancy bound of an entry. -/
def hi (e : Ent) : ℚ := if e.ex then lo e else (e.p : ℚ) / (e.p - 1)

/-- The actual abundancy of the component of an entry. -/
def ab (N : ℕ) (e : Ent) : ℚ := abundancy (e.p ^ N.factorization e.p)

private theorem abundancy_eq_lo {p : ℕ} (hp : p.Prime) (k : ℕ) :
    abundancy (p ^ k) = (geom p k : ℚ) / ((p ^ k : ℕ) : ℚ) := by
  rw [abundancy, Cert.sigma_eq_geom hp]

private theorem ab_pos (N : ℕ) {e : Ent} (hp : e.p.Prime) : 0 < ab N e := by
  have := one_add_inv_le_abundancy_prime_pow hp (a := 0)
  rw [ab, abundancy_eq_lo hp, Cert.geom_eq]
  have : 0 < ∑ i ∈ Finset.range (N.factorization e.p + 1), e.p ^ i :=
    Finset.sum_pos (fun i _ => pow_pos hp.pos i) (by simp)
  have : 0 < e.p ^ N.factorization e.p := pow_pos hp.pos _
  positivity

private theorem lo_le_ab {e : Ent} (he : e.Holds N) : lo e ≤ ab N e := by
  have hp := Nat.prime_of_mem_primeFactors he.1
  rw [lo, ab, ← abundancy_eq_lo hp]
  exact abundancy_prime_pow_mono hp he.2.1

private theorem ab_le_hi {e : Ent} (he : e.Holds N) : ab N e ≤ hi e := by
  have hp := Nat.prime_of_mem_primeFactors he.1
  unfold hi
  split_ifs with hx
  · rw [lo, ab, he.2.2 hx, abundancy_eq_lo hp]
  · exact (abundancy_prime_pow_lt hp _).le

private theorem ab_lt_hi {e : Ent} (he : e.Holds N) (hx : e.ex = false) : ab N e < hi e := by
  have hp := Nat.prime_of_mem_primeFactors he.1
  simp only [hi, hx, Bool.false_eq_true, ↓reduceIte]
  exact abundancy_prime_pow_lt hp _

private theorem lo_pos {e : Ent} (hp : e.p.Prime) : 0 < lo e := by
  rw [lo, ← abundancy_eq_lo hp]
  have := one_add_inv_le_abundancy_prime_pow hp (a := 1) one_pos
  have : (0 : ℚ) < (e.p : ℚ)⁻¹ := by have : (0 : ℚ) < e.p := by exact_mod_cast hp.pos
                                     positivity
  have h0 := abundancy_prime_pow_mono hp (Nat.zero_le e.k)
  have : abundancy (e.p ^ 0) = 1 := by simp [abundancy]
  linarith

private theorem prod_le_of_le (l : List Ent) (x y : Ent → ℚ) (h : ∀ e ∈ l, 0 ≤ x e ∧ x e ≤ y e) :
    (l.map x).prod ≤ (l.map y).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha := h a (by simp)
    have ih' := ih (fun e he => h e (by simp [he]))
    have h0 : 0 ≤ (l.map x).prod := List.prod_nonneg (by
      intro z hz; obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz; exact (h e (by simp [he])).1)
    exact mul_le_mul ha.2 ih' h0 (ha.1.trans ha.2)

private theorem prod_lt_of_lt (l : List Ent) (x y : Ent → ℚ) (h : ∀ e ∈ l, 0 < x e ∧ x e ≤ y e)
    (hs : ∃ e ∈ l, x e < y e) : (l.map x).prod < (l.map y).prod := by
  induction l with
  | nil => simp at hs
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha := h a (by simp)
    have hle := prod_le_of_le l x y (fun e he => ⟨(h e (by simp [he])).1.le, (h e (by simp [he])).2⟩)
    have h0 : 0 < (l.map x).prod := List.prod_pos (by
      intro z hz; obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz; exact (h e (by simp [he])).1)
    obtain ⟨e, he, hlt⟩ := hs
    rcases List.mem_cons.mp he with rfl | he'
    · calc x e * (l.map x).prod < y e * (l.map x).prod := mul_lt_mul_of_pos_right hlt h0
        _ ≤ y e * (l.map y).prod := mul_le_mul_of_nonneg_left hle (ha.1.le.trans ha.2)
    · have := ih (fun e he => h e (by simp [he])) ⟨e, he', hlt⟩
      calc x a * (l.map x).prod < x a * (l.map y).prod := mul_lt_mul_of_pos_left this ha.1
        _ ≤ y a * (l.map y).prod := mul_le_mul_of_nonneg_right ha.2 (h0.le.trans this.le)

private theorem cast_prod_div (l : List Ent) (f g : Ent → ℕ) (r : Ent → ℚ)
    (h : ∀ e ∈ l, (f e : ℚ) / g e = r e) :
    (((l.map f).prod : ℕ) : ℚ) / (((l.map g).prod : ℕ) : ℚ) = (l.map r).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    rw [mul_div_mul_comm, h a (by simp), ih (fun e he => h e (by simp [he]))]

private theorem lnum_div (l : List Ent) : (lnum l : ℚ) / (lden l : ℚ) = (l.map lo).prod :=
  cast_prod_div l _ _ lo (fun e _ => rfl)

private theorem unum_div (l : List Ent) (hl : ∀ e ∈ l, 1 ≤ e.p) :
    (unum l : ℚ) / (uden l : ℚ) = (l.map hi).prod := by
  apply cast_prod_div
  intro e he
  unfold hi
  split_ifs with hx
  · rfl
  · rw [Nat.cast_sub (hl e he)]; simp

private theorem lden_pos (l : List Ent) (hl : ∀ e ∈ l, 1 ≤ e.p) : 0 < lden l := by
  unfold lden
  apply List.prod_pos
  intro z hz
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
  exact pow_pos (hl e he) _

private theorem uden_pos (l : List Ent) (hl : ∀ e ∈ l, 2 ≤ e.p) : 0 < uden l := by
  unfold uden
  apply List.prod_pos
  intro z hz
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
  have := hl e he
  by_cases hx : e.ex = true
  · simp only [hx, ↓reduceIte]; exact pow_pos (by omega) _
  · simp only [hx, Bool.false_eq_true, ↓reduceIte]; omega

/-- The basic decomposition of a state. -/
private theorem decomp {l : List Ent} {j m : ℕ} (H : Holds N l j m) :
    (∀ e ∈ l, e.p.Prime) ∧
    ∃ T : Finset ℕ, T.card = j ∧ (∀ q ∈ T, q ∈ N.primeFactors ∧ q ∉ l.map Ent.p ∧ m < q) ∧
      (∀ q ∈ N.primeFactors, q ∉ l.map Ent.p → q ∈ T) ∧
      (l.map (ab N)).prod * ∏ q ∈ T, abundancy (q ^ N.factorization q) = 2 := by
  obtain ⟨h, hnd, hent, hcard, hbig⟩ := H
  refine ⟨fun e he => Nat.prime_of_mem_primeFactors (hent e he).1, ?_⟩
  set K := (l.map Ent.p).toFinset
  have hK : K ⊆ N.primeFactors := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact (hent e he).1
  refine ⟨N.primeFactors \ K, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hK, hcard, List.toFinset_card_of_nodup hnd, List.length_map]
    omega
  · intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hq
    have : q ∉ l.map Ent.p := fun hh => h2 (List.mem_toFinset.mpr hh)
    exact ⟨h1, this, hbig q h1 this⟩
  · intro q hq hn
    exact Finset.mem_sdiff.mpr ⟨hq, fun hh => hn (List.mem_toFinset.mp hh)⟩
  · have h2 := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
    rw [abundancy_eq_prod_primeFactors h.ne_zero, ← Finset.prod_sdiff hK,
      List.prod_toFinset _ hnd, List.map_map] at h2
    rw [← h2, mul_comm]
    rfl

private theorem one_lt_abundancy_pow {q : ℕ} (hq : q ∈ N.primeFactors) (h : OddPerfect N) :
    1 + (q : ℚ)⁻¹ ≤ abundancy (q ^ N.factorization q) := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  exact one_add_inv_le_abundancy_prime_pow hqp
    ((hqp.dvd_iff_one_le_factorization h.ne_zero).mp (Nat.dvd_of_mem_primeFactors hq))

private theorem rest_ge {T : Finset ℕ} (h : OddPerfect N) (hT : ∀ q ∈ T, q ∈ N.primeFactors) :
    1 ≤ ∏ q ∈ T, abundancy (q ^ N.factorization q) ∧
      (T.Nonempty → 1 < ∏ q ∈ T, abundancy (q ^ N.factorization q)) := by
  have hgt : ∀ q ∈ T, 1 < abundancy (q ^ N.factorization q) := by
    intro q hq
    have := one_lt_abundancy_pow (hT q hq) h
    have : (0 : ℚ) < (q : ℚ)⁻¹ := by
      have : (0 : ℚ) < q := by exact_mod_cast (Nat.prime_of_mem_primeFactors (hT q hq)).pos
      positivity
    linarith
  constructor
  · calc (1 : ℚ) = ∏ q ∈ T, (1 : ℚ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun q hq => (hgt q hq).le)
  · intro hne
    calc (1 : ℚ) = ∏ q ∈ T, (1 : ℚ) := by simp
      _ < _ := Finset.prod_lt_prod_of_nonempty (fun _ _ => one_pos) hgt hne

private theorem ab_prod_nonneg {l : List Ent} (hpr : ∀ e ∈ l, e.p.Prime) : 0 ≤ (l.map (ab N)).prod :=
  List.prod_nonneg (by
    intro z hz; obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz; exact (ab_pos N (hpr e he)).le)

private theorem lo_le_prod {l : List Ent} {j m : ℕ} (H : Holds N l j m) (hpr : ∀ e ∈ l, e.p.Prime) :
    (lnum l : ℚ) / lden l ≤ (l.map (ab N)).prod := by
  rw [lnum_div]
  exact prod_le_of_le l _ _ (fun e he => ⟨(lo_pos (hpr e he)).le, lo_le_ab (H.2.2.1 e he)⟩)

private theorem prod_le_hi {l : List Ent} {j m : ℕ} (H : Holds N l j m) (hpr : ∀ e ∈ l, e.p.Prime) :
    (l.map (ab N)).prod ≤ (unum l : ℚ) / uden l := by
  rw [unum_div l (fun e he => (hpr e he).one_lt.le)]
  exact prod_le_of_le l _ _ (fun e he => ⟨(ab_pos N (hpr e he)).le, ab_le_hi (H.2.2.1 e he)⟩)

private theorem deadAbund_sound {l : List Ent} {j m : ℕ} (hd : deadAbund l j = true)
    (H : Holds N l j m) : False := by
  obtain ⟨hpr, T, hTc, hT, -, h2⟩ := decomp H
  have hLA := lo_le_prod H hpr
  obtain ⟨hR1, hR2⟩ := rest_ge H.1 (fun q hq => (hT q hq).1)
  have hA0 := ab_prod_nonneg (N := N) hpr
  have hd0 : (0 : ℚ) < lden l := by exact_mod_cast lden_pos l (fun e he => (hpr e he).one_lt.le)
  simp only [deadAbund, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hd
  rcases hd with hd | ⟨hj, hd⟩
  · have hq : (2 : ℚ) < (lnum l : ℚ) / lden l := by
      rw [lt_div_iff₀ hd0]; exact_mod_cast (by omega : 2 * lden l < lnum l)
    nlinarith
  · have hq : (2 : ℚ) ≤ (lnum l : ℚ) / lden l := by
      rw [le_div_iff₀ hd0]; exact_mod_cast (by omega : 2 * lden l ≤ lnum l)
    have := hR2 (Finset.card_pos.mp (by omega))
    nlinarith

private theorem deadParity_sound {l : List Ent} {j m : ℕ} (hd : deadParity l = true)
    (H : Holds N l j m) : False := by
  simp only [deadParity, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at hd
  obtain ⟨a, ha, b, hb, ⟨⟨⟨⟨hax, hbx⟩, hak⟩, hbk⟩, hab⟩⟩ := hd
  obtain ⟨q, -, hu⟩ := existsUnique_odd_exponent H.1
  have h1 := hu a.p ⟨Nat.prime_of_mem_primeFactors (H.2.2.1 a ha).1,
    by rw [(H.2.2.1 a ha).2.2 hax]; exact Nat.odd_iff.mpr hak⟩
  have h2 := hu b.p ⟨Nat.prime_of_mem_primeFactors (H.2.2.1 b hb).1,
    by rw [(H.2.2.1 b hb).2.2 hbx]; exact Nat.odd_iff.mpr hbk⟩
  exact hab (h1.trans h2.symm)

private theorem geom_pos (p k : ℕ) : 0 < geom p k := by
  rw [Cert.geom_eq]; exact Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨0, by simp, by simp⟩

private theorem chain_prime {l : List Ent} {j m : ℕ} (H : Holds N l j m) {c : ℕ}
    (hc : c ∈ chainList l) :
    ∃ r, r.Prime ∧ r ∣ c ∧ 0 < c ∧ r ∈ N.primeFactors ∧ r ∉ l.map Ent.p := by
  simp only [chainList, List.mem_filter, List.mem_map, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨e, ⟨he, hex⟩, rfl⟩, hc1⟩ := hc
  have hE := H.2.2.1 e he
  have hp := Nat.prime_of_mem_primeFactors hE.1
  have hg := (geom_pos e.p e.k).ne'
  have hc0 := strip_ne_zero (2 :: l.map Ent.p) _ hg
  obtain ⟨r, hr, hrc⟩ := Nat.exists_prime_and_dvd hc1
  have hr2 : r ≠ 2 := by
    rintro rfl; exact not_dvd_strip _ _ (by simp) le_rfl hg hrc
  have hrg : r ∣ σ 1 (e.p ^ N.factorization e.p) := by
    rw [hE.2.2 hex, Cert.sigma_eq_geom hp]; exact hrc.trans (strip_dvd _ _)
  have hrN := OPNStarter.force_prime H.1.perfect hp rfl hr hr2 hrg
  refine ⟨r, hr, hrc, Nat.pos_of_ne_zero hc0, Nat.mem_primeFactors.mpr ⟨hr, hrN, H.1.ne_zero⟩, ?_⟩
  intro hm
  exact not_dvd_strip _ _ (List.mem_cons_of_mem _ hm) hr.two_le hg hrc

private theorem deadChain_sound {l : List Ent} {j m : ℕ} (hd : deadChain l j m = true)
    (H : Holds N l j m) : False := by
  simp only [deadChain, List.any_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hd
  obtain ⟨c, hc, hj⟩ := hd
  obtain ⟨r, hr, hrc, hc0, hrN, hrl⟩ := chain_prime H hc
  have hmr := H.2.2.2.2 r hrN hrl
  have hrle := Nat.le_of_dvd hc0 hrc
  rcases hj with hj | hj
  · subst hj
    obtain ⟨-, T, hTc, -, hTall, -⟩ := decomp H
    have := hTall r hrN hrl
    rw [Finset.card_eq_zero] at hTc
    simp [hTc] at this
  · omega

private theorem ab_eq_lo {l : List Ent} {j m : ℕ} (H : Holds N l j m) (hall : allEx l = true) :
    (l.map (ab N)).prod = (l.map lo).prod := by
  congr 1
  apply List.map_congr_left
  intro e he
  have hE := H.2.2.1 e he
  have hx : e.ex = true := by
    simp only [allEx, List.all_eq_true] at hall; exact hall e he
  rw [ab, lo, hE.2.2 hx, abundancy_eq_lo (Nat.prime_of_mem_primeFactors hE.1)]

private theorem rest_eq_one {l : List Ent} {m : ℕ} (H : Holds N l 0 m) :
    (l.map (ab N)).prod = 2 := by
  obtain ⟨-, T, hTc, -, -, h2⟩ := decomp H
  rw [Finset.card_eq_zero] at hTc
  simpa [hTc] using h2

private theorem exactFull_sound {l : List Ent} {m : ℕ} (hall : allEx l = true)
    (hne : (lnum l != 2 * lden l) = true) (H : Holds N l 0 m) : False := by
  have h2 := rest_eq_one H
  rw [ab_eq_lo H hall, ← lnum_div] at h2
  have hpr := (decomp H).1
  have hd0 : (0 : ℚ) < lden l := by exact_mod_cast lden_pos l (fun e he => (hpr e he).one_lt.le)
  rw [div_eq_iff hd0.ne'] at h2
  have : lnum l = 2 * lden l := by exact_mod_cast h2
  simp [this] at hne

private theorem prod_lt_hi {l : List Ent} {j m : ℕ} (H : Holds N l j m) (hall : allEx l = false) :
    (l.map (ab N)).prod < (unum l : ℚ) / uden l := by
  have hpr := (decomp H).1
  rw [unum_div l (fun e he => (hpr e he).one_lt.le)]
  apply prod_lt_of_lt l _ _ (fun e he => ⟨ab_pos N (hpr e he), ab_le_hi (H.2.2.1 e he)⟩)
  simp only [allEx, List.all_eq_false] at hall
  obtain ⟨e, he, hx⟩ := hall
  exact ⟨e, he, ab_lt_hi (H.2.2.1 e he) (by simpa using hx)⟩

private theorem uFull_sound {l : List Ent} {m : ℕ} (hall : allEx l = false)
    (hu : unum l ≤ 2 * uden l) (H : Holds N l 0 m) : False := by
  have h2 := rest_eq_one H
  have hlt := prod_lt_hi H hall
  have hpr := (decomp H).1
  have hd0 : (0 : ℚ) < uden l := by exact_mod_cast uden_pos l (fun e he => (hpr e he).two_le)
  have : (unum l : ℚ) / uden l ≤ 2 := by
    rw [div_le_iff₀ hd0]; exact_mod_cast hu
  linarith

private theorem holds_set {l : List Ent} {j m i : ℕ} (H : Holds N l j m) (hi : i < l.length) {x : Ent}
    (hxp : x.p = l[i].p) (hx : x.Holds N) : Holds N (l.set i x) j m := by
  have hmap : (l.set i x).map Ent.p = l.map Ent.p := by
    rw [List.map_set]
    have : x.p = (l.map Ent.p)[i]'(by simpa using hi) := by simp [hxp]
    rw [this, List.set_getElem_self]
  obtain ⟨h, hnd, hent, hcard, hbig⟩ := H
  refine ⟨h, hmap ▸ hnd, ?_, by rw [List.length_set]; exact hcard, fun q hq hn => hbig q hq
    (hmap ▸ hn)⟩
  intro e he
  rcases List.mem_or_eq_of_mem_set he with he | rfl
  · exact hent e he
  · exact hx

private theorem split_holds {l : List Ent} {j m : ℕ} (H : Holds N l j m) (i : ℕ) (d : Ent) :
    Holds N (l.set i ⟨(l.getD i d).p, (l.getD i d).k, true⟩) j m ∨
    Holds N (l.set i ⟨(l.getD i d).p, nextValid (l.getD i d).p (l.getD i d).k, false⟩) j m := by
  by_cases hi : i < l.length
  · have hg : l.getD i d = l[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [hg]
    have hE := H.2.2.1 _ (List.getElem_mem hi)
    by_cases hf : N.factorization l[i].p = l[i].k
    · exact Or.inl (holds_set H hi rfl ⟨hE.1, hE.2.1, fun _ => hf⟩)
    · refine Or.inr (holds_set H hi rfl ⟨hE.1, ?_, fun h => by simp at h⟩)
      show nextValid _ _ ≤ N.factorization l[i].p
      exact nextValid_le (by have := hE.2.1; omega)
        (valid_fact H.1 (Nat.prime_of_mem_primeFactors hE.1))
  · rw [List.set_eq_of_length_le (by omega), List.set_eq_of_length_le (by omega)]
    exact Or.inl H

private theorem le_minB {q : ℕ} : ∀ {bs : List ℕ}, bs ≠ [] → (∀ b ∈ bs, q ≤ b) → q ≤ minB bs
  | [], h, _ => absurd rfl h
  | [a], _, hb => by simpa [minB] using hb a (by simp)
  | a :: b :: l, _, hb => by
    simp only [minB]
    exact le_min (hb a (by simp)) (le_minB (by simp) (fun x hx => hb x (by simp [hx])))

private theorem div_sub_one_le' {c x : ℕ} (hc : 2 ≤ c) (hx : c ≤ x) :
    (x : ℚ) / (x - 1) ≤ (c : ℚ) / (c - 1) := by
  have hc' : (2 : ℚ) ≤ c := by exact_mod_cast hc
  have hx' : (c : ℚ) ≤ x := by exact_mod_cast hx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Enumeration step: in a state with `j ≠ 0` further primes and a nonempty list of bounds,
the smallest unlisted prime factor `q` lies in the window from `lowB` to `minB`, and the state
extended by `q` with exponent at least `kmin q` holds. -/
theorem enum_sound {l : List Ent} {j m : ℕ} (H : Holds N l j m) (hj : j ≠ 0)
    (hb : bounds l j m ≠ []) :
    ∃ q, lowB l j m ≤ q ∧ q ≤ minB (bounds l j m) ∧ isPrimeQ q = true ∧
      Holds N (l ++ [⟨q, kmin q, false⟩]) (j - 1) q := by
  obtain ⟨hpr, T, hTc, hT, hTall, h2⟩ := decomp H
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  set q0 := T.min' hne with hq0
  have hq0T : q0 ∈ T := Finset.min'_mem T hne
  have hmin : ∀ q ∈ T, q0 ≤ q := fun q hq => Finset.min'_le T q hq
  obtain ⟨hq0N, hq0l, hmq0⟩ := hT q0 hq0T
  have hq0p := Nat.prime_of_mem_primeFactors hq0N
  obtain ⟨hR1, hR2⟩ := rest_ge H.1 (fun q hq => (hT q hq).1)
  have hA0 := ab_prod_nonneg (N := N) hpr
  have hLA := lo_le_prod H hpr
  have hAU := prod_le_hi H hpr
  have hd0 : (0 : ℚ) < lden l := by exact_mod_cast lden_pos l (fun e he => (hpr e he).one_lt.le)
  have hu0 : (0 : ℚ) < uden l := by exact_mod_cast uden_pos l (fun e he => (hpr e he).two_le)
  refine ⟨q0, ?_, ?_, isPrimeQ_of_prime hq0p, ?_⟩
  · -- the lower end of the window
    unfold lowB
    split_ifs with hc
    · refine max_le (by omega) ?_
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hc.1 ▸ hTc)
      have hqa : q0 = a := by rw [ha] at hq0T; simpa using hq0T
      rw [ha, Finset.prod_singleton, ← hqa] at h2
      have hR := one_lt_abundancy_pow hq0N H.1
      set L := (lnum l : ℚ) / lden l with hL
      have hq0pos : (0 : ℚ) < q0 := by exact_mod_cast hq0p.pos
      have key : L * (1 + (q0 : ℚ)⁻¹) ≤ 2 := by
        rw [← h2]
        exact mul_le_mul hLA hR (by positivity) hA0
      have key2 : L * (q0 + 1) ≤ 2 * q0 := by
        have : L * (1 + (q0 : ℚ)⁻¹) * q0 = L * (q0 + 1) := by field_simp
        nlinarith
      have key3 : (lnum l : ℚ) * (q0 + 1) ≤ 2 * q0 * lden l := by
        rw [hL, div_mul_eq_mul_div, div_le_iff₀ hd0] at key2; linarith
      have key4 : lnum l ≤ q0 * (2 * lden l - lnum l) := by
        have : (lnum l * (q0 + 1) : ℕ) ≤ 2 * q0 * lden l := by exact_mod_cast key3
        rw [Nat.mul_sub]
        have e1 : lnum l * (q0 + 1) = q0 * lnum l + lnum l := by ring
        have e2 : 2 * q0 * lden l = q0 * (2 * lden l) := by ring
        omega
      have hD : 0 < 2 * lden l - lnum l := by omega
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul hD]
      have : q0.succ * (2 * lden l - lnum l) = q0 * (2 * lden l - lnum l) +
        (2 * lden l - lnum l) := by rw [Nat.succ_eq_add_one]; ring
      omega
    · omega
  · -- the upper end of the window
    apply le_minB hb
    intro b hbm
    simp only [bounds, List.mem_append] at hbm
    rcases hbm with hbm | hbm
    · split_ifs at hbm with hc
      · simp only [List.mem_singleton] at hbm
        subst hbm
        obtain ⟨hlt, h1, hcnd⟩ := hc
        by_contra hgt
        replace hgt := not_le.mp hgt
        set B := bU l j m
        have hcnd' : unum l * (B + 1) ^ j ≤ 2 * uden l * B ^ j := by
          simp only [cond, decide_eq_false_iff_not, not_lt, Nat.add_sub_cancel] at hcnd
          exact hcnd
        have hB0 : (0 : ℚ) < B := by exact_mod_cast h1
        set c : ℚ := ((B + 1 : ℕ) : ℚ) / ((B + 1 : ℕ) - 1)
        have hc_eq : c = ((B : ℚ) + 1) / B := by simp [c]
        have hRlt : ∏ q ∈ T, abundancy (q ^ N.factorization q) < c ^ j := by
          rw [← hTc, ← Finset.prod_const]
          apply Finset.prod_lt_prod_of_nonempty _ _ hne
          · intro q hq
            have := one_lt_abundancy_pow (hT q hq).1 H.1
            have : (0 : ℚ) < (q : ℚ)⁻¹ := by
              have : (0 : ℚ) < q := by exact_mod_cast (Nat.prime_of_mem_primeFactors (hT q hq).1).pos
              positivity
            linarith
          · intro q hq
            exact (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors (hT q hq).1) _).trans_le
              (div_sub_one_le' (by omega) ((Nat.succ_le_of_lt hgt).trans (hmin q hq)))
        have hU2 : (unum l : ℚ) / uden l * c ^ j ≤ 2 := by
          rw [hc_eq, div_pow, div_mul_div_comm, div_le_iff₀ (by positivity)]
          exact_mod_cast (by simpa [mul_comm, mul_assoc, mul_left_comm] using hcnd')
        have hRpos : 0 < ∏ q ∈ T, abundancy (q ^ N.factorization q) := by linarith
        have hUpos : (0 : ℚ) < (unum l : ℚ) / uden l := by
          have : (0 : ℚ) < (l.map (ab N)).prod := by
            by_contra hh; replace hh := not_lt.mp hh
            have : (l.map (ab N)).prod = 0 := le_antisymm hh hA0
            rw [this] at h2; simp at h2
          linarith
        have : (2 : ℚ) < (unum l : ℚ) / uden l * c ^ j := by
          rw [← h2]
          calc (l.map (ab N)).prod * ∏ q ∈ T, abundancy (q ^ N.factorization q)
              ≤ (unum l : ℚ) / uden l * ∏ q ∈ T, abundancy (q ^ N.factorization q) :=
                mul_le_mul_of_nonneg_right hAU hRpos.le
            _ < _ := mul_lt_mul_of_pos_left hRlt hUpos
        linarith
      · simp at hbm
    · obtain ⟨r, -, hrc, hc0, hrN, hrl⟩ := chain_prime H hbm
      exact (hmin r (hTall r hrN hrl)).trans (Nat.le_of_dvd hc0 hrc)
  · -- the new state
    obtain ⟨h, hnd, hent, hcard, hbig⟩ := H
    refine ⟨h, ?_, ?_, ?_, ?_⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      rintro rfl
      exact hq0l (hb ▸ ha)
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hent e he
      · simp only [List.mem_singleton] at he
        subst he
        exact ⟨hq0N, kmin_le h hq0N, fun h => by simp at h⟩
    · rw [hcard, List.length_append]; simp; omega
    · intro q hq hn
      simp only [List.map_append, List.mem_append, not_or, List.map_cons, List.map_nil,
        List.mem_singleton] at hn
      have := hmin q (hTall q hq hn.1)
      omega

/-- Soundness of the search: an accepted state holds for no `N`. -/
theorem solve_sound : ∀ (f : ℕ) (l : List Ent) (j m : ℕ), solve f l j m = true →
    ¬ Holds N l j m := by
  intro f
  induction f with
  | zero => intro l j m hs; simp [solve] at hs
  | succ f ih =>
    intro l j m hs H
    simp only [solve, Bool.or_eq_true] at hs
    rcases hs with ((hs | hs) | hs) | hs
    · exact deadAbund_sound hs H
    · exact deadParity_sound hs H
    · exact deadChain_sound hs H
    · split_ifs at hs with hj hall hb
      · subst hj; exact exactFull_sound hall hs H
      · subst hj
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hs
        rcases hs with hs | ⟨h1, h2⟩
        · exact uFull_sound (by simpa using hall) hs H
        · rcases split_holds H (pick l) ⟨0, 0, true⟩ with H' | H'
          · exact ih _ _ _ h1 H'
          · exact ih _ _ _ h2 H'
      · obtain ⟨q, hlo, hhi, hpq, H'⟩ := enum_sound H hj hb.1
        rw [List.all_eq_true] at hs
        have hmem : q ∈ List.range' (lowB l j m) (minB (bounds l j m) + 1 - lowB l j m) := by
          rw [List.mem_range'_1]; omega
        have := hs q hmem
        simp only [hpq, Bool.not_true, Bool.false_or] at this
        exact ih _ _ _ this H'
      · simp only [Bool.and_eq_true] at hs
        obtain ⟨-, h1, h2⟩ := hs
        rcases split_holds H (pick l) ⟨0, 0, true⟩ with H' | H'
        · exact ih _ _ _ h1 H'
        · exact ih _ _ _ h2 H'

/-- The initial state: `3` is a prime factor with exponent at least two, and all other prime
factors exceed `3`. -/
private theorem holds_init (h : OddPerfect N) (h3 : 3 ∈ N.primeFactors) :
    Holds N [⟨3, 2, false⟩] (N.primeFactors.card - 1) 3 := by
  have hpos : 0 < N.primeFactors.card := Finset.card_pos.mpr ⟨3, h3⟩
  refine ⟨h, by simp, ?_, by simp; omega, ?_⟩
  · intro e he
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨h3, kmin_le h h3, fun h => by simp at h⟩
  · intro q hq hn
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hn
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := fun e => h.not_two_dvd (e ▸ Nat.dvd_of_mem_primeFactors hq)
    have := hqp.two_le
    by_contra hle
    interval_cases q <;> simp_all

set_option maxRecDepth 100000 in
/-- The search closes four prime factors. -/
theorem search_four : solve 30 [⟨3, 2, false⟩] 3 3 = true := by decide +kernel

/-- One step of the search through its prime window: when `j ≠ 0` and the window branch of
`solve` is taken, it suffices to close every prime `q` of the window. -/
private theorem solve_of_window {f : ℕ} {l : List Ent} {j m a n : ℕ} (hj : j ≠ 0)
    (hb : bounds l j m ≠ [] ∧ (minB (bounds l j m) ≤ lowB l j m + W ∨ allEx l = true ∨ 2 ≤ j))
    (ha : lowB l j m = a) (hn : minB (bounds l j m) + 1 - lowB l j m = n)
    (h : ∀ q ∈ List.range' a n, isPrimeQ q = true →
      solve f (l ++ [⟨q, kmin q, false⟩]) (j - 1) q = true) :
    solve (f + 1) l j m = true := by
  rw [solve.eq_2, if_neg hj, if_pos hb]
  simp only [Bool.or_eq_true, List.all_eq_true]
  right
  intro q hq
  rw [hn, ha] at hq
  cases hp : isPrimeQ q
  · simp
  · exact Or.inr (h q hq hp)

/-- A window split into two consecutive parts. -/
private theorem win_split {f : ℕ} {l : List Ent} {j a b k n2 n : ℕ}
    (h1 : ∀ q ∈ List.range' a k, isPrimeQ q = true →
      solve f (l ++ [⟨q, kmin q, false⟩]) (j - 1) q = true)
    (h2 : ∀ q ∈ List.range' b n2, isPrimeQ q = true →
      solve f (l ++ [⟨q, kmin q, false⟩]) (j - 1) q = true)
    (hk : a + k = b) (hn : k + n2 = n) :
    ∀ q ∈ List.range' a n, isPrimeQ q = true →
      solve f (l ++ [⟨q, kmin q, false⟩]) (j - 1) q = true := by
  intro q hq
  rw [List.mem_range'_1] at hq
  by_cases hqb : q < b
  · exact h1 q (List.mem_range'_1.mpr ⟨hq.1, by omega⟩)
  · exact h2 q (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

/-- A window of one prime `b`, closed by a separate check of its child state. -/
private theorem win_one {f : ℕ} {l : List Ent} {j b : ℕ}
    (hc : solve f (l ++ [⟨b, kmin b, false⟩]) (j - 1) b = true) :
    ∀ q ∈ List.range' b 1, isPrimeQ q = true →
      solve f (l ++ [⟨q, kmin q, false⟩]) (j - 1) q = true := by
  intro q hq _
  rw [List.mem_range'_1] at hq
  obtain rfl : q = b := by omega
  exact hc

set_option maxRecDepth 100000 in
/-- Window `[4, 5)` (mirror nodes: 0). -/
private theorem five_w4 : ∀ q ∈ List.range' 4 1,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩] ++ [⟨q, kmin q, false⟩]) (4 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[6, 17)` (mirror nodes: 907). -/
private theorem five_5_w6 : ∀ q ∈ List.range' 6 11,
    isPrimeQ q = true → solve 28 ([⟨3, 2, false⟩, ⟨5, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (3 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[18, 257)` (mirror nodes: 1166). -/
private theorem five_5_17_w18 : ∀ q ∈ List.range' 18 239,
    isPrimeQ q = true → solve 27 ([⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨17, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[257, 337)` (mirror nodes: 1178). -/
private theorem five_5_17_w257 : ∀ q ∈ List.range' 257 80,
    isPrimeQ q = true → solve 27 ([⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨17, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[337, 512)` (mirror nodes: 1124). -/
private theorem five_5_17_w337 : ∀ q ∈ List.range' 337 175,
    isPrimeQ q = true → solve 27 ([⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨17, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (2 - 1) q = true := by
  decide +kernel

/-- The state `[⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨17, 1, false⟩]` with `2` further primes above `17`, through its window. -/
private theorem five_5_17 : solve 28 [⟨3, 2, false⟩, ⟨5, 1, false⟩, ⟨17, 1, false⟩] 2 17 = true :=
  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (win_split five_5_17_w18
      (win_split five_5_17_w257
      five_5_17_w337 rfl rfl) rfl rfl)

set_option maxRecDepth 100000 in
/-- Window `[18, 23)` (mirror nodes: 882). -/
private theorem five_5_w18 : ∀ q ∈ List.range' 18 5,
    isPrimeQ q = true → solve 28 ([⟨3, 2, false⟩, ⟨5, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (3 - 1) q = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Window `[23, 47)` (mirror nodes: 981). -/
private theorem five_5_w23 : ∀ q ∈ List.range' 23 24,
    isPrimeQ q = true → solve 28 ([⟨3, 2, false⟩, ⟨5, 1, false⟩] ++ [⟨q, kmin q, false⟩]) (3 - 1) q = true := by
  decide +kernel

/-- The state `[⟨3, 2, false⟩, ⟨5, 1, false⟩]` with `3` further primes above `5`, through its window. -/
private theorem five_5 : solve 29 [⟨3, 2, false⟩, ⟨5, 1, false⟩] 3 5 = true :=
  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (win_split five_5_w6
      (win_split (win_one (b := 17) five_5_17)
      (win_split five_5_w18
      five_5_w23 rfl rfl) rfl rfl) rfl rfl)

set_option maxRecDepth 100000 in
/-- Window `[6, 15)` (mirror nodes: 471). -/
private theorem five_w6 : ∀ q ∈ List.range' 6 9,
    isPrimeQ q = true → solve 29 ([⟨3, 2, false⟩] ++ [⟨q, kmin q, false⟩]) (4 - 1) q = true := by
  decide +kernel

/-- The state `[⟨3, 2, false⟩]` with `4` further primes above `3`, through its window. -/
private theorem five : solve 30 [⟨3, 2, false⟩] 4 3 = true :=
  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (win_split five_w4
      (win_split (win_one (b := 5) five_5)
      five_w6 rfl rfl) rfl rfl)

/-- The search closes five prime factors. The kernel run is cut along the prime windows of the
search into the checks above, each of at most 1200 search nodes of the Python mirror, so that
each check is small in memory. -/
theorem search_five : solve 30 [⟨3, 2, false⟩] 4 3 = true := five

end OddPerfect.OmegaSixSearch

namespace OddPerfect

open OmegaSixSearch in
/-- Gradshtein (1925), Kühnel (1949): an odd perfect number has at least six distinct prime
factors. -/
theorem six_le_card_primeFactors {N : ℕ} (h : OddPerfect N) : 6 ≤ N.primeFactors.card := by
  have h4 := four_le_card_primeFactors h
  by_contra hlt
  have h3 : 3 ∈ N.primeFactors := by
    by_contra h3
    have := seven_le_card_primeFactors_of_not_three_dvd h
      (fun hd => h3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hd, h.ne_zero⟩))
    omega
  have H := holds_init h h3
  rcases (by omega : N.primeFactors.card - 1 = 3 ∨ N.primeFactors.card - 1 = 4) with hc | hc <;>
    rw [hc] at H
  · exact solve_sound 30 _ _ _ search_four H
  · exact solve_sound 30 _ _ _ search_five H

end OddPerfect

#print axioms OddPerfect.OmegaSixSearch.kmin_le
#print axioms OddPerfect.OmegaSixSearch.enum_sound
#print axioms OddPerfect.OmegaSixSearch.solve_sound
#print axioms OddPerfect.OmegaSixSearch.search_four
#print axioms OddPerfect.OmegaSixSearch.search_five
#print axioms OddPerfect.six_le_card_primeFactors
