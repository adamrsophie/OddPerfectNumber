import OddPerfect.ExponentCap
import OddPerfect.Abundancy

/-!
# A lower bound for the largest prime factor of an odd perfect number

Suppose every prime factor of an odd perfect number `N` is at most `B`. Then the support
of `N` lies in the list `P` of odd primes up to `B`, and for every prime factor `p` with
exponent `e`:

* `2 e + 3 ≤ B` (`two_mul_factorization_add_three_le`);
* `e` is even, or `p ≡ e ≡ 1 (mod 4)` (Euler);
* every prime factor of `σ (p ^ e)` is `2` or lies in `P`, since `σ (p ^ e) ∣ 2 N`;
* no odd prime known not to divide `N` divides `σ (p ^ e)`.

`search` is a depth first search over partial descriptions of `N`: exact exponents,
primes known to divide `N`, and primes known not to divide `N`. A prime known to divide `N`
is branched over its admissible exponents (the conditions above, all checked by the kernel),
and the odd prime factors of `σ (p ^ e)` are added as primes dividing `N`. With no such prime
left, the smallest undecided prime of `P` is split into divides / does not divide. An odd
exponent is rejected when another prime already has an odd exponent (Euler: exactly one
prime of `N` has odd exponent). A branch closes when either bound below contradicts
abundancy two:

* the upper bound `∏ b(q) < 2`, where `q` runs over the primes of `P` not excluded,
  `b(q) = σ (q ^ e) / q ^ e` for an exact exponent `e`, and `b(q) = q / (q - 1)` otherwise;
* the lower bound `∏ σ (q ^ e) / q ^ e > 2` over the exact exponents, which is the abundancy
  of a divisor of `N`.

For speed the upper bound is computed from the full products `M = 2 ∏ P` and
`D = ∏ (q - 1)` over `P`, correcting only the factors of the recorded primes; this is valid
because the search keeps the invariant `Inv` (no repeated primes, recorded and excluded
primes disjoint, all of them in `P`). Membership tests use `Nat.beq`, which the kernel
evaluates directly.

`search_sound` proves that an accepted search excludes every odd perfect number, and the
search for the bound `B` is run by the kernel with `decide +kernel`. The list `P` of odd
primes up to `B`, the numbers `M` and `D`, and a table `T` of rows for the primes the search
branches on are written out explicitly; the kernel checks each of them against its
definition (`primesUpTo`, the products, `row`) before running the search.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace LPF

/-! ## Computable helpers -/

/-- The divisor sum of `p ^ e` for prime `p`, in closed form. -/
def gs (p e : ℕ) : ℕ := (p ^ (e + 1) - 1) / (p - 1)

private theorem sigma_eq_gs {p : ℕ} (hp : p.Prime) (e : ℕ) : σ 1 (p ^ e) = gs p e := by
  rw [sigma_one_apply_prime_pow hp, gs, Nat.geomSum_eq hp.two_le]

private theorem nbeq_iff {a b : ℕ} : (!Nat.beq a b) = true ↔ a ≠ b := by
  cases h : Nat.beq a b
  · simpa using Nat.ne_of_beq_eq_false h
  · simpa using Nat.eq_of_beq_eq_true h

/-- Trial division of `n` by `d, d + 1, …` while `d * d ≤ n`, for at most `f` steps. -/
def noDiv (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, d => Nat.blt n (d * d) || (!Nat.beq (n % d) 0 && noDiv n f (d + 1))

/-- Primality by trial division up to the square root. -/
def isPrimeF (n : ℕ) : Bool := Nat.ble 2 n && noDiv n n 2

private theorem noDiv_sound {n : ℕ} : ∀ {f d : ℕ}, noDiv n f d = true →
    ∀ k, d ≤ k → k < d + f → k * k ≤ n → ¬ k ∣ n
  | 0, d, _, k, h1, h2, _ => by omega
  | f + 1, d, h, k, h1, h2, h3 => by
    simp only [noDiv, Bool.or_eq_true, Bool.and_eq_true,
      ne_eq, Nat.blt_eq, nbeq_iff] at h
    rcases h with h | ⟨hd, h⟩
    · have := Nat.mul_le_mul h1 h1; omega
    · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact fun hk => hd (Nat.mod_eq_zero_of_dvd hk)
      · exact noDiv_sound h k hlt (by omega) h3

private theorem noDiv_complete {n : ℕ} : ∀ {f d : ℕ}, 2 ≤ d → (∀ k, d ≤ k → k < n → ¬ k ∣ n) →
    noDiv n f d = true
  | 0, _, _, _ => rfl
  | f + 1, d, hd, h => by
    simp only [noDiv, Bool.or_eq_true, Bool.and_eq_true, ne_eq, Nat.blt_eq, nbeq_iff]
    by_cases hlt : n < d * d
    · exact Or.inl hlt
    · right
      have hdn : d < n := by nlinarith
      exact ⟨fun h0 => h d le_rfl hdn (Nat.dvd_of_mod_eq_zero h0),
        noDiv_complete (by omega) fun k hk => h k (by omega)⟩

private theorem isPrimeF_iff {n : ℕ} : isPrimeF n = true ↔ n.Prime := by
  simp only [isPrimeF, Bool.and_eq_true, Nat.ble_eq]
  constructor
  · rintro ⟨h2, h⟩
    rw [Nat.prime_def_minFac]
    refine ⟨h2, ?_⟩
    by_contra hne
    have hlt : n.minFac < n := lt_of_le_of_ne (Nat.minFac_le (by omega)) hne
    have hsq := Nat.minFac_sq_le_self (by omega) (fun hp => hne (Nat.Prime.minFac_eq hp))
    have h2m := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
    exact noDiv_sound h n.minFac h2m (by omega) (by rw [← pow_two]; exact hsq)
      (Nat.minFac_dvd n)
  · intro hp
    refine ⟨hp.two_le, noDiv_complete le_rfl fun k hk hkn hd => ?_⟩
    have := (Nat.prime_def_lt.mp hp).2 k hkn hd
    omega

/-- The odd primes up to `B`. -/
def primesUpTo (B : ℕ) : List ℕ :=
  (List.range (B + 1)).filter fun n => !Nat.beq n 2 && isPrimeF n

private theorem mem_primesUpTo {B q : ℕ} : q ∈ primesUpTo B ↔ q ≤ B ∧ q ≠ 2 ∧ q.Prime := by
  simp only [primesUpTo, List.mem_filter, List.mem_range, Bool.and_eq_true, ne_eq,
    isPrimeF_iff, nbeq_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h2, h3⟩

private theorem nodup_primesUpTo (B : ℕ) : (primesUpTo B).Nodup :=
  (List.nodup_range).filter _

/-- Strip the prime factors of `M` from `m`, at most `f` rounds. -/
def cofree (M : ℕ) : ℕ → ℕ → ℕ
  | 0, m => m
  | f + 1, m => cond (Nat.beq (Nat.gcd m M) 1) m (cofree M f (m / Nat.gcd m M))

private theorem cofree_dvd (M : ℕ) : ∀ f m, cofree M f m ∣ m
  | 0, m => dvd_rfl
  | f + 1, m => by
    unfold cofree
    cases Nat.beq (Nat.gcd m M) 1
    · exact (cofree_dvd M f _).trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m M))
    · exact dvd_rfl

/-- `m` has a prime factor not dividing `M`. -/
def bigF (M m : ℕ) : Bool :=
  !Nat.beq (cofree M 100 m) 1 && Nat.beq (Nat.gcd (cofree M 100 m) M) 1

private theorem bigF_sound {M m : ℕ} (hm : m ≠ 0) (h : bigF M m = true) :
    ∃ q, q.Prime ∧ q ∣ m ∧ ¬ q ∣ M := by
  simp only [bigF, Bool.and_eq_true, ne_eq, Nat.beq_eq, nbeq_iff] at h
  set r := cofree M 100 m
  have hr : r ∣ m := cofree_dvd M 100 m
  have hr0 : r ≠ 0 := by rintro h0; rw [h0, zero_dvd_iff] at hr; exact hm hr
  refine ⟨r.minFac, Nat.minFac_prime h.1, (Nat.minFac_dvd r).trans hr, fun hq => ?_⟩
  have := Nat.dvd_gcd (Nat.minFac_dvd r) hq
  rw [h.2] at this
  exact (Nat.minFac_prime h.1).one_lt.ne' (Nat.dvd_one.mp this)

/-- Euler's parity condition for the exponent `e` of `p`. -/
def parityOK (p e : ℕ) : Bool :=
  Nat.beq (e % 2) 0 || (Nat.beq (p % 4) 1 && Nat.beq (e % 4) 1)

/-- The row of `p`: exponents `e` with `1 ≤ e`, `2 e + 3 ≤ B`, Euler's parity condition,
and `σ (p ^ e)` free of prime factors not dividing `M`. -/
def row (B M p : ℕ) : List ℕ :=
  (List.range ((B - 3) / 2 + 1)).filter fun e =>
    Nat.ble 1 e && parityOK p e && !bigF M (gs p e)

/-- Admissible exponents of `p` from its row `r`: no excluded prime divides `σ (p ^ e)`. -/
def cands (nd : List ℕ) (p : ℕ) (r : List ℕ) : List ℕ :=
  r.filter fun e => nd.all fun q => !Nat.beq (gs p e % q) 0

/-- First entry recorded for `q`. -/
def look {β : Type} (q : ℕ) : List (ℕ × β) → Option β
  | [] => none
  | (a, b) :: l => cond (Nat.beq a q) (some b) (look q l)

/-- The row of `p`, from the table `T` when listed there. -/
def getRow (B M : ℕ) (T : List (ℕ × List ℕ)) (p : ℕ) : List ℕ :=
  match look p T with
  | some r => r
  | none => row B M p

private theorem mem_of_look {β : Type} {q : ℕ} {e : β} :
    ∀ {l : List (ℕ × β)}, look q l = some e → (q, e) ∈ l
  | [], h => by simp [look] at h
  | (a, b) :: l, h => by
    unfold look at h
    cases hab : Nat.beq a q <;> rw [hab] at h
    · exact List.mem_cons_of_mem _ (mem_of_look h)
    · rw [Nat.beq_eq] at hab; subst hab; cases h; simp

/-- Membership of `q` in a list, by `Nat.beq`. -/
def memB (q : ℕ) : List ℕ → Bool
  | [] => false
  | a :: l => Nat.beq a q || memB q l

/-- Some entry of the list has first component `q`, by `Nat.beq`. -/
def memF (q : ℕ) : List (ℕ × ℕ) → Bool
  | [] => false
  | a :: l => Nat.beq a.1 q || memF q l

private theorem memB_iff {q : ℕ} : ∀ {l : List ℕ}, memB q l = true ↔ q ∈ l
  | [] => by simp [memB]
  | a :: l => by
    simp only [memB, Bool.or_eq_true, Nat.beq_eq, memB_iff, List.mem_cons]
    exact ⟨fun h => h.elim (fun h => Or.inl h.symm) Or.inr,
      fun h => h.elim (fun h => Or.inl h.symm) Or.inr⟩

private theorem memF_iff {q : ℕ} : ∀ {l : List (ℕ × ℕ)}, memF q l = true ↔ ∃ x ∈ l, x.1 = q
  | [] => by simp [memF]
  | a :: l => by
    simp only [memF, Bool.or_eq_true, Nat.beq_eq, memF_iff, List.mem_cons, exists_eq_or_imp]

/-- The upper bound closing rule. With `M = 2 ∏ P` and `D = ∏ (q - 1)` over `P`, it says that
`∏ b(q) < 2`, where `q` runs over the primes of `P` not excluded, `b(q) = σ (q ^ e) / q ^ e`
for an exact exponent `e`, and `b(q) = q / (q - 1)` otherwise. The product is computed from
the full product over `P` by correcting the factors of `ex` and `nd` only. -/
def upperOK (M D : ℕ) (ex : List (ℕ × ℕ)) (nd : List ℕ) : Bool :=
  Nat.blt (M * (ex.map fun x => gs x.1 x.2 * (x.1 - 1)).prod * (nd.map (· - 1)).prod)
    (4 * D * (ex.map fun x => x.1 ^ x.2 * x.1).prod * nd.prod)

/-- The lower bound closing rule: `∏ σ (q ^ e) / q ^ e > 2` over the exact exponents, so a
divisor of `N` has abundancy above two. -/
def lowerOK (ex : List (ℕ × ℕ)) : Bool :=
  Nat.blt (2 * (ex.map fun x => x.1 ^ x.2).prod) (ex.map fun x => gs x.1 x.2).prod

/-- Odd primes of `P` dividing `m`. -/
def newPrimes (P : List ℕ) (m : ℕ) : List ℕ := P.filter fun q => Nat.beq (m % q) 0

/-- The search. `ex`: exact exponents; `dv`: primes dividing `N`; `nd`: primes not
dividing `N`. `M = 2 ∏ P` and `D = ∏ (q - 1)` over `P`. -/
def search (B : ℕ) (P : List ℕ) (M D : ℕ) (T : List (ℕ × List ℕ)) :
    ℕ → List (ℕ × ℕ) → List ℕ → List ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, ex, dv, nd =>
    lowerOK ex || upperOK M D ex nd ||
      match dv with
      | p :: rest =>
        if memF p ex then search B P M D T fuel ex rest nd
        else (cands nd p (getRow B M T p)).all fun e =>
          (Nat.beq (e % 2) 1 && ex.any fun x => Nat.beq (x.2 % 2) 1) ||
            search B P M D T fuel ((p, e) :: ex) (newPrimes P (gs p e) ++ rest) nd
      | [] =>
        match P.filter (fun q => !memF q ex && !memB q nd) with
        | [] => false
        | q :: _ => search B P M D T fuel ex [q] nd && search B P M D T fuel ex [] (q :: nd)

/-! ## Soundness -/

/-- The meaning of a search state. -/
def Holds (N : ℕ) (ex : List (ℕ × ℕ)) (dv nd : List ℕ) : Prop :=
  (∀ x ∈ ex, N.factorization x.1 = x.2) ∧ (∀ q ∈ dv, q.Prime ∧ q ∣ N) ∧
    (∀ q ∈ nd, q.Prime ∧ q ≠ 2 ∧ ¬ q ∣ N)

variable {N B : ℕ}

private theorem mem_P_of_mem (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B) {q : ℕ}
    (hq : q ∈ N.primeFactors) : q ∈ primesUpTo B := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  refine mem_primesUpTo.mpr ⟨hB q hq, ?_, hqp⟩
  rintro rfl
  exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hq)

/-- The exponent of a prime factor is admissible. -/
private theorem mem_cands (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B) {nd : List ℕ}
    (hnd : ∀ q ∈ nd, q.Prime ∧ q ≠ 2 ∧ ¬ q ∣ N) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    N.factorization p ∈ cands nd p (row B (2 * (primesUpTo B).prod) p) := by
  have hpm : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  set f := N.factorization p with hf
  have he1 : 1 ≤ f := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN
  have hcap := two_mul_factorization_add_three_le h hpm hB
  have hσ : σ 1 (p ^ f) ∣ 2 * N := OPNStarter.component_sigma_dvd h.perfect hp hf.symm
  rw [sigma_eq_gs hp] at hσ
  have hgs0 : gs p f ≠ 0 := by
    rw [← sigma_eq_gs hp]; exact (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'
  simp only [cands, row, List.mem_filter, List.mem_range, Bool.and_eq_true,
    Bool.not_eq_true', List.all_eq_true, Nat.ble_eq]
  refine ⟨⟨by omega, ⟨he1, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨q, -, -, hq4, hqe, hev⟩ := exists_special_prime h
    simp only [parityOK, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq]
    by_cases hpq : p = q
    · subst hpq; exact Or.inr ⟨hq4, hqe⟩
    · exact Or.inl (Nat.even_iff.mp (hev p hp hpq))
  · by_contra hb
    obtain ⟨q, hq, hqd, hqM⟩ := bigF_sound hgs0 (by simpa using hb)
    apply hqM
    rcases (Nat.Prime.dvd_mul hq).mp (hqd.trans hσ) with h2 | hN
    · exact h2.mul_right _
    · exact (List.dvd_prod (mem_P_of_mem h hB
        (Nat.mem_primeFactors.mpr ⟨hq, hN, h.ne_zero⟩))).mul_left 2
  · intro q hq
    rw [Bool.eq_false_iff, Ne, Nat.beq_eq]
    intro h0
    obtain ⟨hqp, hq2, hqN⟩ := hnd q hq
    rw [← sigma_eq_gs hp] at h0
    exact hqN (OPNStarter.force_prime h.perfect hp hf.symm hqp hq2 (Nat.dvd_of_mod_eq_zero h0))

private theorem getRow_eq {B M p : ℕ} {T : List (ℕ × List ℕ)} (hT : ∀ x ∈ T, x.2 = row B M x.1) :
    getRow B M T p = row B M p := by
  unfold getRow
  cases hl : look p T with
  | none => rfl
  | some r => exact hT _ (mem_of_look hl)

/-- Bookkeeping invariant of a search state: no repeated primes, `ex` and `nd` disjoint, and
every prime involved lies in `P`. -/
def Inv (P : List ℕ) (ex : List (ℕ × ℕ)) (dv nd : List ℕ) : Prop :=
  (ex.map Prod.fst).Nodup ∧ nd.Nodup ∧ (∀ x ∈ ex, x.1 ∈ P ∧ x.1 ∉ nd) ∧ (∀ q ∈ nd, q ∈ P) ∧
    ∀ q ∈ dv, q ∈ P

private theorem prod_P_eq_two (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B) :
    ∏ q ∈ (primesUpTo B).toFinset, abundancy (q ^ N.factorization q) = 2 := by
  have hab := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  rw [abundancy_eq_prod_primeFactors h.ne_zero] at hab
  rw [← hab]
  symm
  refine Finset.prod_subset (fun q hq => List.mem_toFinset.mpr (mem_P_of_mem h hB hq)) ?_
  intro q hq hqN
  have hqp := (mem_primesUpTo.mp (List.mem_toFinset.mp hq)).2.2
  have : ¬ q ∣ N := fun hd => hqN (Nat.mem_primeFactors.mpr ⟨hqp, hd, h.ne_zero⟩)
  rw [Nat.factorization_eq_zero_of_not_dvd this]
  simp [abundancy]

private theorem one_le_abundancy_pow {q : ℕ} (hq : q.Prime) (k : ℕ) : 1 ≤ abundancy (q ^ k) := by
  have := abundancy_le_of_dvd (pow_ne_zero k hq.ne_zero) (one_dvd (q ^ k))
  simpa [abundancy] using this

private theorem cast_prod_ex {ex : List (ℕ × ℕ)} (hex : ∀ x ∈ ex, N.factorization x.1 = x.2)
    (hk : (ex.map Prod.fst).Nodup) (G : ℕ → ℕ → ℕ) :
    (((ex.map fun x => G x.1 x.2).prod : ℕ) : ℚ) =
      ∏ q ∈ (ex.map Prod.fst).toFinset, (G q (N.factorization q) : ℚ) := by
  rw [List.prod_toFinset _ hk, Nat.cast_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp [hex x hx]

private theorem cast_prod_map {l : List ℕ} (hl : l.Nodup) (G : ℕ → ℕ) :
    (((l.map G).prod : ℕ) : ℚ) = ∏ q ∈ l.toFinset, (G q : ℚ) := by
  rw [List.prod_toFinset _ hl, Nat.cast_list_prod, List.map_map]
  rfl

private theorem cast_prod {l : List ℕ} (hl : l.Nodup) :
    ((l.prod : ℕ) : ℚ) = ∏ q ∈ l.toFinset, (q : ℚ) := by
  rw [List.prod_toFinset _ hl, Nat.cast_list_prod]

/-- The lower bound closing rule is sound. -/
private theorem lowerOK_sound (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B)
    {ex : List (ℕ × ℕ)} {dv nd : List ℕ} (hex : ∀ x ∈ ex, N.factorization x.1 = x.2)
    (hI : Inv (primesUpTo B) ex dv nd) (hl : lowerOK ex = true) : False := by
  obtain ⟨hk, -, hexP, -, -⟩ := hI
  set K := (ex.map Prod.fst).toFinset with hK
  have hKP : K ⊆ (primesUpTo B).toFinset := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact List.mem_toFinset.mpr (hexP x hx).1
  have hKp : ∀ q ∈ K, q.Prime := fun q hq =>
    (mem_primesUpTo.mp (List.mem_toFinset.mp (hKP hq))).2.2
  have hl' : 2 * (ex.map fun x => x.1 ^ x.2).prod < (ex.map fun x => gs x.1 x.2).prod := by
    unfold lowerOK at hl; rwa [Nat.blt_eq] at hl
  have hl'' : (((2 * (ex.map fun x => x.1 ^ x.2).prod : ℕ)) : ℚ) <
      (((ex.map fun x => gs x.1 x.2).prod : ℕ) : ℚ) := Nat.cast_lt.mpr hl'
  rw [Nat.cast_mul, Nat.cast_ofNat, cast_prod_ex hex hk (fun q e => q ^ e),
    cast_prod_ex hex hk gs] at hl''
  have hpos : (0 : ℚ) < ∏ q ∈ K, ((q ^ N.factorization q : ℕ) : ℚ) :=
    Finset.prod_pos fun q hq => by have := (hKp q hq).pos; positivity
  have hA : ∏ q ∈ K, abundancy (q ^ N.factorization q) =
      (∏ q ∈ K, (gs q (N.factorization q) : ℚ)) /
        ∏ q ∈ K, ((q ^ N.factorization q : ℕ) : ℚ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [abundancy, sigma_eq_gs (hKp q hq)]
  have h2 : 2 < ∏ q ∈ K, abundancy (q ^ N.factorization q) := by
    rw [hA, lt_div_iff₀ hpos]; exact hl''
  have h3 : ∏ q ∈ K, abundancy (q ^ N.factorization q) ≤
      ∏ q ∈ (primesUpTo B).toFinset, abundancy (q ^ N.factorization q) :=
    Finset.prod_le_prod_of_subset_of_one_le hKP
      (fun q _ => by unfold abundancy; positivity)
      (fun q hq _ => one_le_abundancy_pow
        (mem_primesUpTo.mp (List.mem_toFinset.mp hq)).2.2 _)
  rw [prod_P_eq_two h hB] at h3
  linarith

/-- The upper bound closing rule is sound. -/
private theorem upperOK_sound (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B)
    {ex : List (ℕ × ℕ)} {dv nd : List ℕ} (hs : Holds N ex dv nd)
    (hI : Inv (primesUpTo B) ex dv nd)
    (hu : upperOK (2 * (primesUpTo B).prod) ((primesUpTo B).map (· - 1)).prod ex nd = true) :
    False := by
  obtain ⟨hex, -, hnd⟩ := hs
  obtain ⟨hk, hn, hexP, hndP, -⟩ := hI
  have hPn := nodup_primesUpTo B
  set P := primesUpTo B with hP
  set Pf := P.toFinset with hPf
  set K := (ex.map Prod.fst).toFinset with hK
  set Nd := nd.toFinset with hNd
  have hKP : K ⊆ Pf := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact List.mem_toFinset.mpr (hexP x hx).1
  have hNP : Nd ⊆ Pf := fun q hq => List.mem_toFinset.mpr (hndP q (List.mem_toFinset.mp hq))
  have hdisj : Disjoint K Nd := by
    rw [Finset.disjoint_left]
    intro q hqK hqN
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hqK)
    exact (hexP x hx).2 (List.mem_toFinset.mp hqN)
  have hPp : ∀ q ∈ Pf, q.Prime := fun q hq =>
    (mem_primesUpTo.mp (List.mem_toFinset.mp hq)).2.2
  set R := Pf \ (K ∪ Nd) with hR
  have hsplit : ∀ f : ℕ → ℚ,
      ∏ q ∈ Pf, f q = (∏ q ∈ R, f q) * ((∏ q ∈ K, f q) * ∏ q ∈ Nd, f q) := by
    intro f
    rw [← Finset.prod_union hdisj, Finset.prod_sdiff (Finset.union_subset hKP hNP)]
  -- the closing inequality, over the rationals
  have hu1 : 2 * P.prod * (ex.map fun x => gs x.1 x.2 * (x.1 - 1)).prod *
      (nd.map (· - 1)).prod < 4 * (P.map (· - 1)).prod *
      (ex.map fun x => x.1 ^ x.2 * x.1).prod * nd.prod := by
    unfold upperOK at hu; rwa [Nat.blt_eq] at hu
  have hu2 : ((2 * P.prod * (ex.map fun x => gs x.1 x.2 * (x.1 - 1)).prod *
      (nd.map (· - 1)).prod : ℕ) : ℚ) < ((4 * (P.map (· - 1)).prod *
      (ex.map fun x => x.1 ^ x.2 * x.1).prod * nd.prod : ℕ) : ℚ) := Nat.cast_lt.mpr hu1
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hu2
  rw [cast_prod hPn, cast_prod_map hPn, cast_prod hn, cast_prod_map hn,
    cast_prod_ex hex hk (fun q e => gs q e * (q - 1)),
    cast_prod_ex hex hk (fun q e => q ^ e * q)] at hu2
  simp only [Nat.cast_mul, Finset.prod_mul_distrib] at hu2
  rw [hsplit (fun q => (q : ℚ)), hsplit (fun q => ((q - 1 : ℕ) : ℚ))] at hu2
  -- facts about the components
  have hc : ∀ q ∈ Pf, (0 : ℚ) < ((q - 1 : ℕ) : ℚ) := fun q hq => by
    have := (hPp q hq).two_le
    exact_mod_cast (by omega : 0 < q - 1)
  have hq0 : ∀ q ∈ Pf, (0 : ℚ) < (q : ℚ) := fun q hq => by
    exact_mod_cast (hPp q hq).pos
  have hw : ∀ q ∈ Pf, abundancy (q ^ N.factorization q) * ((q - 1 : ℕ) : ℚ) ≤ q := by
    intro q hq
    have hlt := abundancy_prime_pow_lt (hPp q hq) (N.factorization q)
    have h1 : ((q - 1 : ℕ) : ℚ) = (q : ℚ) - 1 := by
      rw [Nat.cast_sub (hPp q hq).one_lt.le]; simp
    have hc' := hc q hq
    rw [h1] at hc' ⊢
    rw [lt_div_iff₀ hc'] at hlt
    exact hlt.le
  have hAll := prod_P_eq_two h hB
  rw [hsplit] at hAll
  have hAn : ∏ q ∈ Nd, abundancy (q ^ N.factorization q) = 1 := by
    refine Finset.prod_eq_one fun q hq => ?_
    rw [Nat.factorization_eq_zero_of_not_dvd (hnd q (List.mem_toFinset.mp hq)).2.2]
    simp [abundancy]
  rw [hAn, mul_one] at hAll
  have hRw : (∏ q ∈ R, abundancy (q ^ N.factorization q)) * ∏ q ∈ R, ((q - 1 : ℕ) : ℚ) ≤
      ∏ q ∈ R, (q : ℚ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun q hq => ?_) (fun q hq => hw q (Finset.sdiff_subset hq))
    have := hc q (Finset.sdiff_subset hq)
    have : 0 ≤ abundancy (q ^ N.factorization q) := by unfold abundancy; positivity
    positivity
  have hKe : (∏ q ∈ K, abundancy (q ^ N.factorization q)) *
      ∏ q ∈ K, ((q ^ N.factorization q : ℕ) : ℚ) = ∏ q ∈ K, (gs q (N.factorization q) : ℚ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q hq => ?_
    have hqp := hPp q (hKP hq)
    have : ((q ^ N.factorization q : ℕ) : ℚ) ≠ 0 := by
      have := pow_pos hqp.pos (N.factorization q); positivity
    rw [abundancy, sigma_eq_gs hqp, div_mul_cancel₀ _ this]
  -- name the pieces
  set Ar := ∏ q ∈ R, abundancy (q ^ N.factorization q)
  set Ak := ∏ q ∈ K, abundancy (q ^ N.factorization q)
  set Cr := ∏ q ∈ R, ((q - 1 : ℕ) : ℚ)
  set Ck := ∏ q ∈ K, ((q - 1 : ℕ) : ℚ)
  set Cn := ∏ q ∈ Nd, ((q - 1 : ℕ) : ℚ)
  set Qr := ∏ q ∈ R, (q : ℚ)
  set Qk := ∏ q ∈ K, (q : ℚ)
  set Qn := ∏ q ∈ Nd, (q : ℚ)
  set Ek := ∏ q ∈ K, ((q ^ N.factorization q : ℕ) : ℚ)
  set Gk := ∏ q ∈ K, (gs q (N.factorization q) : ℚ)
  have hX : 0 < Ck * Cn * Qk * Qn := by
    have := Finset.prod_pos fun q hq => hc q (hKP hq)
    have := Finset.prod_pos fun q hq => hc q (hNP hq)
    have := Finset.prod_pos fun q hq => hq0 q (hKP hq)
    have := Finset.prod_pos fun q hq => hq0 q (hNP hq)
    positivity
  have hGk : 0 ≤ Gk := Finset.prod_nonneg fun q _ => by positivity
  have key : Ar * Cr * (Ak * Ek) ≤ Qr * Gk := by
    rw [hKe]; exact mul_le_mul_of_nonneg_right hRw hGk
  have m := mul_le_mul_of_nonneg_right key hX.le
  have e1 : 4 * (Cr * (Ck * Cn)) * (Ek * Qk) * Qn =
      2 * (Ar * Cr * (Ak * Ek) * (Ck * Cn * Qk * Qn)) := by
    linear_combination (-2 * Cr * Ek * (Ck * Cn * Qk * Qn)) * hAll
  have e2 : 2 * (Qr * (Qk * Qn)) * (Gk * Ck) * Cn = 2 * (Qr * Gk * (Ck * Cn * Qk * Qn)) := by ring
  rw [e1, e2] at hu2
  linarith

/-- At most one prime has an odd exponent (Euler), so a second odd exponent is impossible. -/
private theorem two_odd_false (h : OddPerfect N) {ex : List (ℕ × ℕ)}
    (hex : ∀ x ∈ ex, N.factorization x.1 = x.2) {p : ℕ}
    (hpe : ¬ memF p ex = true) (hp : p.Prime)
    (hodd : (Nat.beq (N.factorization p % 2) 1 && ex.any fun x => Nat.beq (x.2 % 2) 1) = true) :
    False := by
  simp only [Bool.and_eq_true, List.any_eq_true, Nat.beq_eq] at hodd
  rw [memF_iff] at hpe
  obtain ⟨hpo, x, hx, hxo⟩ := hodd
  have hxp : x.1 ≠ p := fun he => hpe ⟨x, hx, he⟩
  have hfx := hex x hx
  have hxprime : x.1.Prime := by
    by_contra hnp
    rw [Nat.factorization_eq_zero_of_not_prime N hnp] at hfx
    omega
  obtain ⟨q, -, -, -, -, hev⟩ := exists_special_prime h
  by_cases hpq : p = q
  · subst hpq
    have := Nat.even_iff.mp (hev x.1 hxprime hxp)
    omega
  · have := Nat.even_iff.mp (hev p hp hpq)
    omega

/-- Soundness of the search: an accepted search excludes every odd perfect number with all
prime factors at most `B` that satisfies the state. -/
theorem search_sound (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B)
    {T : List (ℕ × List ℕ)} (hT : ∀ x ∈ T, x.2 = row B (2 * (primesUpTo B).prod) x.1) :
    ∀ fuel ex dv nd, search B (primesUpTo B) (2 * (primesUpTo B).prod)
      ((primesUpTo B).map (· - 1)).prod T fuel ex dv nd = true →
      Holds N ex dv nd → Inv (primesUpTo B) ex dv nd → False := by
  intro fuel
  induction fuel with
  | zero => intro ex dv nd hs; simp [search] at hs
  | succ fuel ih =>
    intro ex dv nd hs hH hI
    obtain ⟨hex, hdv, hnd⟩ := hH
    obtain ⟨hk, hn, hexP, hndP, hdvP⟩ := hI
    have hI' : Inv (primesUpTo B) ex dv nd := ⟨hk, hn, hexP, hndP, hdvP⟩
    cases dv with
    | cons p rest =>
      simp only [search, Bool.or_eq_true] at hs
      rcases hs with (hl | hu) | hs
      · exact lowerOK_sound h hB hex hI' hl
      · exact upperOK_sound h hB ⟨hex, hdv, hnd⟩ hI' hu
      split_ifs at hs with hpe
      · exact ih _ _ _ hs ⟨hex, fun q hq => hdv q (List.mem_cons_of_mem _ hq), hnd⟩
          ⟨hk, hn, hexP, hndP, fun q hq => hdvP q (List.mem_cons_of_mem _ hq)⟩
      · obtain ⟨hp, hpN⟩ := hdv p (by simp)
        have hm := mem_cands h hB hnd hp hpN
        rw [← getRow_eq hT] at hm
        have hc := List.all_eq_true.mp hs _ hm
        simp only [Bool.or_eq_true] at hc
        rcases hc with hodd | hc
        · exact two_odd_false h hex hpe hp hodd
        refine ih _ _ _ hc ⟨?_, ?_, hnd⟩ ⟨?_, hn, ?_, hndP, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · rfl
          · exact hex x hx
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · obtain ⟨hqP, hq0⟩ := List.mem_filter.mp hq
            obtain ⟨-, hq2, hqp⟩ := mem_primesUpTo.mp hqP
            refine ⟨hqp, OPNStarter.force_prime h.perfect hp rfl hqp hq2 ?_⟩
            rw [sigma_eq_gs hp]
            exact Nat.dvd_of_mod_eq_zero (by simpa using hq0)
          · exact hdv q (List.mem_cons_of_mem _ hq)
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨fun hmem => hpe ?_, hk⟩
          obtain ⟨x, hx, hxp⟩ := List.mem_map.mp hmem
          exact memF_iff.mpr ⟨x, hx, hxp⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hdvP _ (by simp), fun hmem => (hnd _ hmem).2.2 hpN⟩
          · exact hexP x hx
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact (List.mem_filter.mp hq).1
          · exact hdvP q (List.mem_cons_of_mem _ hq)
    | nil =>
      simp only [search, Bool.or_eq_true] at hs
      rcases hs with (hl | hu) | hs
      · exact lowerOK_sound h hB hex hI' hl
      · exact upperOK_sound h hB ⟨hex, hdv, hnd⟩ hI' hu
      split at hs
      · simp at hs
      · rename_i q l hfl
        have hqmem : q ∈ (primesUpTo B).filter
            (fun q => !memF q ex && !memB q nd) := by
          rw [hfl]; simp
        obtain ⟨hqP, hqf⟩ := List.mem_filter.mp hqmem
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, Ne, memF_iff,
          memB_iff] at hqf
        obtain ⟨-, hq2, hqp⟩ := mem_primesUpTo.mp hqP
        simp only [Bool.and_eq_true] at hs
        by_cases hqN : q ∣ N
        · exact ih _ _ _ hs.1 ⟨hex, by simpa using ⟨hqp, hqN⟩, hnd⟩
            ⟨hk, hn, hexP, hndP, by simpa using hqP⟩
        · refine ih _ _ _ hs.2 ⟨hex, by simp, fun r hr => ?_⟩
            ⟨hk, List.nodup_cons.mpr ⟨hqf.2, hn⟩, fun x hx => ⟨(hexP x hx).1, ?_⟩, ?_, by simp⟩
          · rcases List.mem_cons.mp hr with rfl | hr
            · exact ⟨hqp, hq2, hqN⟩
            · exact hnd r hr
          · rw [List.mem_cons, not_or]
            exact ⟨fun he => hqf.1 ⟨x, hx, he⟩, (hexP x hx).2⟩
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact hqP
            · exact hndP r hr

/-- An accepted search for `B` gives a prime factor above `B`. The list `P`, the numbers
`M = 2 ∏ P` and `D = ∏ (q - 1)` over `P` (the odd primes up to `B`), and the row table `T`
are given explicitly and checked. -/
theorem exists_primeFactor_gt_of_search {B : ℕ} {P : List ℕ} {M D : ℕ}
    {T : List (ℕ × List ℕ)}
    (hP : primesUpTo B = P) (hM : 2 * P.prod = M) (hD : (P.map (· - 1)).prod = D)
    (hT : T.all (fun x => x.2 == row B M x.1))
    (hs : search B P M D T 1000 [] [] [] = true)
    (h : OddPerfect N) : ∃ p ∈ N.primeFactors, B < p := by
  subst hP hM hD
  by_contra hne
  push Not at hne
  refine search_sound h hne (T := T) (fun x hx => ?_) _ _ _ _ hs ⟨by simp, by simp, by simp⟩
    ⟨by simp, by simp, by simp, by simp, by simp⟩
  simpa using List.all_eq_true.mp hT x hx

end LPF

set_option maxHeartbeats 0 in
/-- The largest prime factor of an odd perfect number exceeds `10000`. -/
theorem exists_primeFactor_gt {N : ℕ} (h : OddPerfect N) : ∃ p ∈ N.primeFactors, 10000 < p :=
  LPF.exists_primeFactor_gt_of_search (P := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973])
    (M := 59490679579998635868564022242503445659680322440679327938309703916140405638383434744833220555452130558140772894046169700747186409941317550665821619479140098743288335106272856533978719769677794737287419461899922456614256826709727133515885581878614846298251428096512495590545989536239739285290509870860732435109794045491640561011775744617218426011793283330497878491137999673760740717904979730106994180691956740996319139767941335979146924614249205862051182094081815447356600355657858936442589201739350474320966093143098768914226528498860747050474426418211313776073365498029087492308102876323562641651940555529817223923967479711293692697592800750806084802623966596666156361791014935954720420383555300213829134029560826306201326905674141090667002959274513478562033467485802590354539887133866434256562999666615074220857502563011098759348850149774083443643246907501430076141377431759984926248272553982527014011245310690986644461251576837779050124866641531488351016070300247918750613207952783437248236577750579092103591540592540838395240861443615842939673889972504776455114767522430347610500271801944701491874649306605557851914677316523034726044356368337787113190245601235705959816327016988315321850324065292964680148884818699916224411245926491625245571963741062587277736372090007125908660590314049976206281064703285728879581199596401313352724403492043120507597057004633720111008838673185885941472392623805512709896864520875740497617898566981218781313900004406341154884180472153171064617953661517880143988867189622824081729539392205701820144922307223627345876707465251206005262622236311161449785941834002795854996108322186230425179217618301526151712928790928933798369678844576216735378555233905935973195721247604933753363412045618703247367192610615234835041956551569232557323060407648325565048712478527583315981204846341857095134567470182330491262285172727037299211391244340592936174221176781260586188162350081192408213470101717320475998863222409777310443027421196981193126541663212124245716187453863438039402316877152286468198891603632606578778749292403571792687832081974134637014026451921536576338243322267400651083805535119025415817887075652758045539565968044552126338330231434466204888993650859153585380124240540573308417330478048240203241631072371322849430883727355239704116556046700749530006852187064160849175332758172150251213637470549781080491037088372092203085237973008861896576796238915011886636658033019385943299986285181723378096425117379056207797455963451889971988904466449319007760192467211209692128894691704353648198130409333996534250878389064152054828983825841234644875996912485916827004219887033833599723481903489316488764021700996686817244736947119285629049355809027206179193628292018441744552168286541735687924729198455883895791600170372255284216915442808139396541702893732917062958054499525549626455191658842064247047426187897146172971001949767308335268505414284088528125611263685734457560292833389995980698745893243832547007166243476192958601735336260255598581701267151224204461879782815468518040925292817115377696676461775120750971210951527384637825092221708015393564320979357698186262039029460777050248162599194429941464248920952161182024344007059684970270762248243899640259750891406957836740989312390963091260380990901672119736141666856448171380781556117025832312710039041398538035351795267732240730608951176127282191528457681241590895740457571038936173983449289126574141189374690274057472401359482497502067814596008557725079835212621242944853319496441084441343866446380876967613370281793088540430288658573281302876742323336651987699532240686371751448290351615451932054274752105688318766958111191822471878078268490672607804265064578569581247796205593441336042254502454646980009177290888726099355974892680373341371214123450598691915802122913613669446370194221846225597401405625536693874723700374068542217340621938985167525416725638580266200550048001242788847319217369432802469735271132107428204697172144851088692772696511622350096452418244968500432645305761138012204888798724453956720733374364721511323104353496583927094760495687785031050687852300161433757934364774351673531859394855389527851678630166084819717354779333605871648837631164630550613112327670353108353791304451834904017538583880634608113426156225757314283269948216017294095002859515842577481167417167637534527111130468710)
    (D := 3622071730217044156990790695390826760260109366810676374549098777335800637260376721662237047921729096710325518827551194868178855987366523551850965092715319232417353833696997465001685868994190078558088192830580106258127339605101489579969973706483333782872100299263564314631893731462787537560996962185927205581660962431647331932049309808623712758641873108787854903318441198011538604335586079431614960714959598031012427781289259927383394218022186846824950970722716900355684439489646137674332302586833214185159438794852017778992075623879689346974309832950246345926065875160436619608998548829337161565396659157560908274282444676364888802882309924023025434910278477459370881726030867757279853771190656255434212905081121131327434507132143661325491153480649920104929072976557491522000731885118821408064598467215285563920906503444204604935470259115762368591089226054662389785630135686495104983211252753331938581240806655932564942502082650642809743595225606655813719555208958064078552288781076869394134539265999491246130495815234226082084861926073857937726759306380434938237873953409972182336225466895229744757443602814553866344777516362780160666609552271695138449212500121109998240169099085645201758108869190147608692910905474374067828287042438774705223249647587803818574328917906340990816663838309182769925100184830979251965356850552051240258976879756161673906500994638843861332353854902265228351337849866478456699198468966572383483485365381959555711377682619164292750241588644457903140392637369692979923871411021807576007199586812486845202234563839091212701051488179007982962608352682595231838708580105821380234982703798498028595517936529418837904162541728224129107987147866088623737360990352980890033248928607268193251792279747606747317843980379599045283741321344242134453011051731547909804071292090513701158054774893992477925930385006972250658807802786198519432732426585245997483244656351891874460369865107191879113116180869025760466180623763204336432979556264810353855533024776259521244081487654126928873548552242363434405639420276854236770265247354072493685781104237158706674013242139819158587510568386380120125507336940374451114208366737480591147535465864212214524116471463958459102429623886982235321627180447849621873726734142541909489806018924259126239934681097564610790244725861400786447530668508931123614692736943885316769877948768281301967193309450220272626767071036810740957908127523061762803375878092296648066399352259099633601588138454625386363299599795124342430126130682716235737105501667181060363274796616415307092045914205553100333993586213672599632978954046170905556759639491944756623924009130495999504430815091272070817726406029157286079739414963739629716749711299571811693068165146821593244870838658553741287688525095553710261637111454306144870935921730616188862822024566450884508254330735297348805823656146568733523487167022805950245129384765639972478020550656927990248612092977798641694809587259228738503590384355035324907205199650473694628313549834234365282644725098113727767632016565242120375351445857354896439502209895239602696450459045704888904618705297607529755426199750500021862065691131943867980567359316149294687441319923654731554604301987272352892040468121452850576102862069801851006817656306984224291727136081189495209580840464209399118614627757121849832969198727285489061879844278755438858110126863034571398209704471843643356608541759003356743383994761251383376275608283549554194955330906380066837337325868542522867626884301167041936445454612124533531753485447741473130632089437504390664404879355248192541420233005432993563103599567817265900900184096090171850354841480256970719226312530027436491271014198827322332279308234201490002962507294637668885161236212524817423481347780523052214822856037622061986088878517119217749269976678934047271876729210174283815756237317008858032434465370582650836969061580254337542902132521380830692966310578972449283052140464424486642099030134825879540170175283200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
    (T := [(3, [2, 4, 6, 8, 10, 14, 26]), (13, [1, 2, 5]), (7, [2, 4, 6, 8]), (19, [2, 4]), (127, [2]), (5419, [2]), (31, [2]), (331, [2]), (5233, [1]), (151, [2]), (1093, [1]), (2801, [1, 2]), (37, [1, 2, 4, 5]), (67, [2]), (11, [2, 4]), (29, [1, 2, 5]), (61, [1, 2, 5]), (97, [1, 2, 5]), (3169, [1]), (5, [1, 2, 4, 5, 8, 9, 14, 17, 29]), (467, []), (41, [1, 2, 5]), (3221, [1]), (547, [2]), (163, [2, 4]), (911, []), (23, [2]), (2617, [1]), (1723, []), (17, [1, 2, 5]), (307, [2, 4]), (1051, []), (43, [2, 8]), (47, [2]), (53, [1, 2, 4, 5, 9]), (59, [2, 4, 6]), (3541, [1, 2]), (71, [2, 4]), (5113, [1]), (2557, [1, 2]), (73, [1, 2, 5]), (79, [2, 6]), (281, [1, 2]), (109, [1, 2, 5]), (83, [2]), (89, [1, 2, 4, 5]), (8011, []), (131, [])])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) h

end OddPerfect

#print axioms OddPerfect.LPF.search_sound
#print axioms OddPerfect.LPF.exists_primeFactor_gt_of_search
#print axioms OddPerfect.exists_primeFactor_gt
