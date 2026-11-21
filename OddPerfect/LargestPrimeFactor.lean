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
left, the smallest undecided prime of `P` is split into divides / does not divide. A branch
closes when the upper bound `∏ b(q) < 2` holds, where `q` runs over the primes of `P` not
excluded, `b(q) = σ (q ^ e) / q ^ e` for an exact exponent `e`, and `b(q) = q / (q - 1)`
otherwise. Since the abundancy of `N` is two, such a branch is empty.

`search_sound` proves that an accepted search excludes every odd perfect number, and the
search for the bound `B` is run by the kernel with `decide +kernel`. The list `P` of odd
primes up to `B`, the number `M = 2 ∏ P` and a table `T` of rows for the primes the search
branches on are written out explicitly; the kernel checks each of them against its
definition (`primesUpTo`, the product, `row`) before running the search.
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

/-- Trial division of `n` by `d, d + 1, …` while `d * d ≤ n`, for at most `f` steps. -/
def noDiv (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, d => n < d * d || (n % d != 0 && noDiv n f (d + 1))

/-- Primality by trial division up to the square root. -/
def isPrimeF (n : ℕ) : Bool := 2 ≤ n && noDiv n n 2

private theorem noDiv_sound {n : ℕ} : ∀ {f d : ℕ}, noDiv n f d = true →
    ∀ k, d ≤ k → k < d + f → k * k ≤ n → ¬ k ∣ n
  | 0, d, _, k, h1, h2, _ => by omega
  | f + 1, d, h, k, h1, h2, h3 => by
    simp only [noDiv, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at h
    rcases h with h | ⟨hd, h⟩
    · have := Nat.mul_le_mul h1 h1; omega
    · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact fun hk => hd (Nat.mod_eq_zero_of_dvd hk)
      · exact noDiv_sound h k hlt (by omega) h3

private theorem noDiv_complete {n : ℕ} : ∀ {f d : ℕ}, 2 ≤ d → (∀ k, d ≤ k → k < n → ¬ k ∣ n) →
    noDiv n f d = true
  | 0, _, _, _ => rfl
  | f + 1, d, hd, h => by
    simp only [noDiv, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq]
    by_cases hlt : n < d * d
    · exact Or.inl hlt
    · right
      have hdn : d < n := by nlinarith
      exact ⟨fun h0 => h d le_rfl hdn (Nat.dvd_of_mod_eq_zero h0),
        noDiv_complete (by omega) fun k hk => h k (by omega)⟩

private theorem isPrimeF_iff {n : ℕ} : isPrimeF n = true ↔ n.Prime := by
  simp only [isPrimeF, Bool.and_eq_true, decide_eq_true_eq]
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
def primesUpTo (B : ℕ) : List ℕ := (List.range (B + 1)).filter fun n => n != 2 && isPrimeF n

private theorem mem_primesUpTo {B q : ℕ} : q ∈ primesUpTo B ↔ q ≤ B ∧ q ≠ 2 ∧ q.Prime := by
  simp only [primesUpTo, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    isPrimeF_iff]
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
  | f + 1, m => if Nat.gcd m M = 1 then m else cofree M f (m / Nat.gcd m M)

private theorem cofree_dvd (M : ℕ) : ∀ f m, cofree M f m ∣ m
  | 0, m => dvd_rfl
  | f + 1, m => by
    unfold cofree
    split_ifs
    · exact dvd_rfl
    · exact (cofree_dvd M f _).trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m M))

/-- `m` has a prime factor not dividing `M`. -/
def bigF (M m : ℕ) : Bool :=
  cofree M 100 m != 1 && Nat.gcd (cofree M 100 m) M == 1

private theorem bigF_sound {M m : ℕ} (hm : m ≠ 0) (h : bigF M m = true) :
    ∃ q, q.Prime ∧ q ∣ m ∧ ¬ q ∣ M := by
  simp only [bigF, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  set r := cofree M 100 m
  have hr : r ∣ m := cofree_dvd M 100 m
  have hr0 : r ≠ 0 := by rintro h0; rw [h0, zero_dvd_iff] at hr; exact hm hr
  refine ⟨r.minFac, Nat.minFac_prime h.1, (Nat.minFac_dvd r).trans hr, fun hq => ?_⟩
  have := Nat.dvd_gcd (Nat.minFac_dvd r) hq
  rw [h.2] at this
  exact (Nat.minFac_prime h.1).one_lt.ne' (Nat.dvd_one.mp this)

/-- Euler's parity condition for the exponent `e` of `p`. -/
def parityOK (p e : ℕ) : Bool := e % 2 == 0 || (p % 4 == 1 && e % 4 == 1)

/-- The row of `p`: exponents `e` with `1 ≤ e`, `2 e + 3 ≤ B`, Euler's parity condition,
and `σ (p ^ e)` free of prime factors not dividing `M`. -/
def row (B M p : ℕ) : List ℕ :=
  (List.range ((B - 3) / 2 + 1)).filter fun e =>
    1 ≤ e && parityOK p e && !bigF M (gs p e)

/-- Admissible exponents of `p` from its row `r`: no excluded prime divides `σ (p ^ e)`. -/
def cands (nd : List ℕ) (p : ℕ) (r : List ℕ) : List ℕ :=
  r.filter fun e => nd.all fun q => gs p e % q != 0

/-- First entry recorded for `q`. -/
def look {β : Type} (q : ℕ) : List (ℕ × β) → Option β
  | [] => none
  | (a, b) :: l => if a = q then some b else look q l

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
    split_ifs at h with hab
    · subst hab; cases h; simp
    · exact List.mem_cons_of_mem _ (mem_of_look h)

/-- Numerator of the upper bound factor at `q`. -/
def bn (ex : List (ℕ × ℕ)) (q : ℕ) : ℕ :=
  match look q ex with
  | some e => gs q e
  | none => q

/-- Denominator of the upper bound factor at `q`. -/
def bd (ex : List (ℕ × ℕ)) (q : ℕ) : ℕ :=
  match look q ex with
  | some e => q ^ e
  | none => q - 1

/-- The upper bound `∏ b(q)` over the non excluded primes is below two. -/
def upperOK (P : List ℕ) (ex : List (ℕ × ℕ)) (nd : List ℕ) : Bool :=
  let L := P.filter fun q => !nd.contains q
  (L.map (bn ex)).prod < 2 * (L.map (bd ex)).prod

/-- Odd primes of `P` dividing `m`. -/
def newPrimes (P : List ℕ) (m : ℕ) : List ℕ := P.filter fun q => m % q == 0

/-- The search. `ex`: exact exponents; `dv`: primes dividing `N`; `nd`: primes not
dividing `N`. -/
def search (B : ℕ) (P : List ℕ) (M : ℕ) (T : List (ℕ × List ℕ)) :
    ℕ → List (ℕ × ℕ) → List ℕ → List ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, ex, dv, nd =>
    upperOK P ex nd ||
      match dv with
      | p :: rest =>
        if ex.any (·.1 == p) then search B P M T fuel ex rest nd
        else (cands nd p (getRow B M T p)).all fun e =>
          search B P M T fuel ((p, e) :: ex) (newPrimes P (gs p e) ++ rest) nd
      | [] =>
        match P.filter (fun q => !(ex.any (·.1 == q)) && !nd.contains q) with
        | [] => false
        | q :: _ => search B P M T fuel ex [q] nd && search B P M T fuel ex [] (q :: nd)

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
  simp only [cands, row, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', List.all_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨by omega, ⟨he1, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨q, -, -, hq4, hqe, hev⟩ := exists_special_prime h
    simp only [parityOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
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
  · intro q hq h0
    obtain ⟨hqp, hq2, hqN⟩ := hnd q hq
    rw [← sigma_eq_gs hp] at h0
    exact hqN (OPNStarter.force_prime h.perfect hp hf.symm hqp hq2 (Nat.dvd_of_mod_eq_zero h0))

private theorem getRow_eq {B M p : ℕ} {T : List (ℕ × List ℕ)} (hT : ∀ x ∈ T, x.2 = row B M x.1) :
    getRow B M T p = row B M p := by
  unfold getRow
  cases hl : look p T with
  | none => rfl
  | some r => exact hT _ (mem_of_look hl)

/-- The factor of the upper bound at `q`, as a rational. -/
def bq (ex : List (ℕ × ℕ)) (q : ℕ) : ℚ := (bn ex q : ℚ) / (bd ex q)

private theorem prod_div_eq (ex : List (ℕ × ℕ)) : ∀ L : List ℕ,
    ((L.map (bn ex)).prod : ℚ) / ((L.map (bd ex)).prod : ℚ) = (L.map (bq ex)).prod
  | [] => by simp
  | a :: L => by
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ← prod_div_eq ex L, bq]
    rw [mul_div_mul_comm]

private theorem abundancy_le_bq {ex : List (ℕ × ℕ)}
    (hex : ∀ x ∈ ex, N.factorization x.1 = x.2) {p : ℕ} (hp : p.Prime) :
    abundancy (p ^ N.factorization p) ≤ bq ex p := by
  unfold bq bn bd
  cases hl : look p ex with
  | some e =>
    have := hex _ (mem_of_look hl)
    simp only at this
    rw [this, abundancy, sigma_eq_gs hp]
  | none =>
    simp only
    have := abundancy_prime_pow_lt hp (N.factorization p)
    have h1 : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
      rw [Nat.cast_sub hp.one_lt.le]; simp
    rw [h1]; exact this.le

private theorem one_le_bq {ex : List (ℕ × ℕ)} {p : ℕ} (hp : p.Prime) : 1 ≤ bq ex p := by
  unfold bq bn bd
  cases hl : look p ex with
  | some e =>
    simp only
    have h1 : (1 : ℚ) ≤ abundancy (p ^ e) := by
      have := abundancy_le_of_dvd (pow_ne_zero e hp.ne_zero) (one_dvd (p ^ e))
      simpa [abundancy] using this
    rw [abundancy, sigma_eq_gs hp] at h1
    exact_mod_cast h1
  | none =>
    simp only
    have h2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
    rw [Nat.cast_sub hp.one_lt.le, one_le_div (by push_cast; linarith)]
    push_cast; linarith

/-- The upper bound closing rule is sound. -/
private theorem upperOK_sound (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B)
    {ex : List (ℕ × ℕ)} {dv nd : List ℕ} (hs : Holds N ex dv nd)
    (hu : upperOK (primesUpTo B) ex nd = true) : False := by
  obtain ⟨hex, -, hnd⟩ := hs
  set L := (primesUpTo B).filter fun q => !nd.contains q with hL
  have hu' : (L.map (bn ex)).prod < 2 * (L.map (bd ex)).prod := by
    simpa [upperOK, hL] using hu
  have hLp : ∀ q ∈ L, q.Prime := fun q hq =>
    (mem_primesUpTo.mp (List.mem_filter.mp hq).1).2.2
  have hden : 0 < (L.map (bd ex)).prod := by
    apply List.prod_pos
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    have hqp := hLp q hq
    unfold bd
    cases look q ex with
    | some e => exact pow_pos hqp.pos e
    | none => have := hqp.two_le; simp only; omega
  have hlt : (L.map (bq ex)).prod < 2 := by
    rw [← prod_div_eq, div_lt_iff₀ (by exact_mod_cast hden)]
    exact_mod_cast hu'
  have hab := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  rw [abundancy_eq_prod_primeFactors h.ne_zero] at hab
  have hsub : N.primeFactors ⊆ L.toFinset := by
    intro p hp
    rw [List.mem_toFinset, hL, List.mem_filter]
    refine ⟨mem_P_of_mem h hB hp, ?_⟩
    have : p ∉ nd := fun hm => (hnd p hm).2.2 (Nat.dvd_of_mem_primeFactors hp)
    simpa using this
  have h1 : ∏ p ∈ N.primeFactors, abundancy (p ^ N.factorization p) ≤
      ∏ p ∈ N.primeFactors, bq ex p :=
    Finset.prod_le_prod (fun p _ => by unfold abundancy; positivity)
      (fun p hp => abundancy_le_bq hex (Nat.prime_of_mem_primeFactors hp))
  have h2 : ∏ p ∈ N.primeFactors, bq ex p ≤ ∏ p ∈ L.toFinset, bq ex p :=
    Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun p hp => zero_le_one.trans (one_le_bq (Nat.prime_of_mem_primeFactors hp)))
      (fun p hp _ => one_le_bq (hLp p (List.mem_toFinset.mp hp)))
  rw [List.prod_toFinset _ ((nodup_primesUpTo B).filter _)] at h2
  linarith

/-- Soundness of the search: an accepted search excludes every odd perfect number with all
prime factors at most `B` that satisfies the state. -/
theorem search_sound (h : OddPerfect N) (hB : ∀ r ∈ N.primeFactors, r ≤ B)
    {T : List (ℕ × List ℕ)} (hT : ∀ x ∈ T, x.2 = row B (2 * (primesUpTo B).prod) x.1) :
    ∀ fuel ex dv nd, search B (primesUpTo B) (2 * (primesUpTo B).prod) T fuel ex dv nd = true →
      Holds N ex dv nd → False := by
  intro fuel
  induction fuel with
  | zero => intro ex dv nd hs; simp [search] at hs
  | succ fuel ih =>
    intro ex dv nd hs hH
    obtain ⟨hex, hdv, hnd⟩ := hH
    cases dv with
    | cons p rest =>
      simp only [search, Bool.or_eq_true] at hs
      rcases hs with hu | hs
      · exact upperOK_sound h hB ⟨hex, hdv, hnd⟩ hu
      split_ifs at hs with hpe
      · exact ih _ _ _ hs ⟨hex, fun q hq => hdv q (List.mem_cons_of_mem _ hq), hnd⟩
      · obtain ⟨hp, hpN⟩ := hdv p (by simp)
        have hm := mem_cands h hB hnd hp hpN
        rw [← getRow_eq hT] at hm
        have hc := List.all_eq_true.mp hs _ hm
        refine ih _ _ _ hc ⟨?_, ?_, hnd⟩
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
    | nil =>
      simp only [search, Bool.or_eq_true] at hs
      rcases hs with hu | hs
      · exact upperOK_sound h hB ⟨hex, hdv, hnd⟩ hu
      split at hs
      · simp at hs
      · rename_i q l hfl
        have hqmem : q ∈ (primesUpTo B).filter
            (fun q => !(ex.any (·.1 == q)) && !nd.contains q) := by
          rw [hfl]; simp
        obtain ⟨-, hq2, hqp⟩ := mem_primesUpTo.mp (List.mem_filter.mp hqmem).1
        simp only [Bool.and_eq_true] at hs
        by_cases hqN : q ∣ N
        · exact ih _ _ _ hs.1 ⟨hex, by simpa using ⟨hqp, hqN⟩, hnd⟩
        · refine ih _ _ _ hs.2 ⟨hex, by simp, fun r hr => ?_⟩
          rcases List.mem_cons.mp hr with rfl | hr
          · exact ⟨hqp, hq2, hqN⟩
          · exact hnd r hr

/-- An accepted search for `B` gives a prime factor above `B`. The list `P`, the number
`M` (the odd primes up to `B` and twice their product) and the row table `T` are given
explicitly and checked. -/
theorem exists_primeFactor_gt_of_search {B : ℕ} {P : List ℕ} {M : ℕ} {T : List (ℕ × List ℕ)}
    (hP : primesUpTo B = P) (hM : 2 * P.prod = M) (hT : T.all (fun x => x.2 == row B M x.1))
    (hs : search B P M T 1000 [] [] [] = true)
    (h : OddPerfect N) : ∃ p ∈ N.primeFactors, B < p := by
  subst hP hM
  by_contra hne
  push Not at hne
  refine search_sound h hne (T := T) (fun x hx => ?_) _ _ _ _ hs ⟨by simp, by simp, by simp⟩
  simpa using List.all_eq_true.mp hT x hx

end LPF

set_option maxHeartbeats 0 in
/-- The largest prime factor of an odd perfect number exceeds `2000`. -/
theorem exists_primeFactor_gt {N : ℕ} (h : OddPerfect N) : ∃ p ∈ N.primeFactors, 2000 < p :=
  LPF.exists_primeFactor_gt_of_search (P := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999])
    (M := 289374641962945601852615669686352438557198389101635505921978687533534603184099103356713220245045689382193979028466556623300928386426868641265517885761774500699854169800840685305650571905326393891147443503522793860584071591452879655775734323993447280229950516208168456242859704539545043029470723016883062129865188983307445759944131787563777752236534042838736571825768147309875879568648761848492474692269075737993820510968847059797750137738579680583507041487685017149524627916063644375086068999495298981349776540320796738483271972712449573928869390146878678278551706732964746955815021418849063826580384371871911662113251288424597019051505811657455462629184223235168202635751562718522606516698622396025118884934399326179006093117580004591816199377853876305166538715269486496913965338299018641563718412655206993166415109405802877992948356769154670)
    (T := [(3, [2, 4, 6, 8]), (13, [1, 2, 5]), (7, [2, 8]), (19, [2, 4]), (127, []), (151, [2]), (1093, [1]), (547, [2]), (163, [2, 4]), (67, [2]), (31, [2]), (331, []), (11, [2]), (61, [1, 2, 5]), (97, [1]), (911, []), (5, [1, 2, 4, 5, 8, 9, 14]), (17, [1, 2, 5]), (307, [2]), (23, [2]), (29, [1, 2, 5]), (37, [1, 2, 5]), (41, [1, 2, 5]), (1723, [])])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h

end OddPerfect

#print axioms OddPerfect.LPF.search_sound
#print axioms OddPerfect.LPF.exists_primeFactor_gt_of_search
#print axioms OddPerfect.exists_primeFactor_gt
