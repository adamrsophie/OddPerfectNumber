import OddPerfect.EqualExponentChain
import OddPerfect.EqualExponents

/-!
# Equal exponents: a counting certificate checker with unfactored cofactors

Restricted family result; the family of all primes `l` is not excluded. The counting method
with unfactored cofactors follows the approach described in the public repository
`mathdiscoveries/odd-perfect-equal-exponents` (read as text only), which states the cases
`l ≤ 73`; that claim was not verified here. The checker, its soundness proof and every
certificate in this module were produced independently for this library.

Setting: `N` is an odd perfect number with special prime `q`, `l` is an odd prime, `l ≠ q`,
and every prime factor of `N` other than `q` has exponent `l - 1`. Write
`Φ(p) = σ(p ^ (l - 1))`. By the landed `card_mod_one_le`, at most `l - 1` prime factors of `N`
other than `q` are `1` modulo `l`; so at most `l` prime factors of `N` are `1` modulo `l`.

A PARENT is a prime `p` that divides `N` and differs from `q`; then `Φ(p)` divides `2 N`. Every
prime factor of a divisor `m > 1` of `Φ(p)` with `l ∤ m` is `1` modulo `l` and divides `N`.
The checker walks a list of entries `(p, m, a)`, keeps the product `P` of the counted numbers
`m` (pairwise coprime by a gcd test against `P`) and a lower bound `k` for the number of
distinct prime factors of `P`. Each `m` adds `1`, or `2` when the witness `a` shows that `m` is
not a prime power: `gcd(a ^ m - a mod m, m) = 1` with `0 < a < m` fails for every prime power
`m` by Fermat's little theorem. A case closes when `k ≥ l + 1`, or when `q = Q` is known,
`Q ∤ P` and `k ≥ l`.

A parent `p` is accepted when it is prime (trial division or a Pratt certificate) and either
`p = l` (then `p ≠ q` by hypothesis and `p ∣ N` by the landed
`not_all_exponents_eq_pred_prime`), or `p ∣ P` or, in a
case where `q = Q` is known, `p ∣ Q + 1` with `p ≠ 2` (because `σ(q) ∣ σ(q ^ k)` for odd `k`);
and in addition `p ≠ q` is known: `p % 4 = 3` (the special prime is `1` modulo `4`), or `p`
lies in the exclusion list of the main case, or `p ≠ Q` in the case `q = Q`.

The main case assumes that `q` is not in the exclusion list `ex`; for each `Q ∈ ex` a case with
`q = Q` must close as well.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.EqCount

open OddPerfect.Pratt (powMod powMod_eq trialPrime trialPrime_sound)
open OddPerfect.EqChain (gm gm_eq dvd_sigma_of_gm isP isP_sound)

/-! ## Computable checker -/

/-- A number written in base `10 ^ 80` chunks, most significant first (for long literals). -/
def big (cs : List ℕ) : ℕ := cs.foldl (fun a c => a * 10 ^ 80 + c) 0

/-- The residue of `a ^ m + m - a` modulo `m` (meant for `a < m`). -/
def fermatRes (a m : ℕ) : ℕ := (powMod a m m + m - a) % m

/-- The weight of a counted number: `2` with a witness, `1` without. -/
def weight (a : ℕ) : ℕ := if a = 0 then 1 else 2

/-- The witness test: no witness, or `0 < a < m` with `gcd(a ^ m - a mod m, m) = 1`. -/
def witnessOK (m a : ℕ) : Bool := a == 0 || (a < m && Nat.gcd (fermatRes a m) m == 1)

/-- The proof that `p ≠ q`. -/
def neqOK (qs : Option ℕ) (ex : List ℕ) (p : ℕ) : Bool :=
  match qs with
  | some Q => p != Q
  | none => p % 4 == 3 || ex.contains p

/-- The proof that `p ∣ N`, apart from `p = l`. -/
def dvdOK (qs : Option ℕ) (P p : ℕ) : Bool :=
  P % p == 0 ||
    match qs with
    | some Q => p != 2 && (Q + 1) % p == 0
    | none => false

/-- A parent: `l`, or a prime with a reason to divide `N` and a reason to differ from `q`. -/
def parentOK (l : ℕ) (pc : List (ℕ × ℕ × List ℕ)) (qs : Option ℕ) (ex : List ℕ) (P p : ℕ) :
    Bool :=
  p == l || (isP pc p && dvdOK qs P p && neqOK qs ex p)

/-- A counted number `m` from `Φ(p)`, coprime to the product `P` so far. -/
def pieceOK (l p P m a : ℕ) : Bool :=
  1 < m && m % l != 0 && gm p m l == 0 && Nat.gcd m P == 1 && witnessOK m a

/-- The closing test. -/
def finalOK (l : ℕ) (qs : Option ℕ) (P k : ℕ) : Bool :=
  l + 1 ≤ k ||
    match qs with
    | some Q => l ≤ k && P % Q != 0
    | none => false

/-- Walk the entries `(p, m, a)` with product `P` and count `k`. -/
def run (l : ℕ) (pc : List (ℕ × ℕ × List ℕ)) (qs : Option ℕ) (ex : List ℕ) :
    ℕ → ℕ → List (ℕ × ℕ × ℕ) → Bool
  | P, k, [] => finalOK l qs P k
  | P, k, (p, m, a) :: rest =>
    parentOK l pc qs ex P p && pieceOK l p P m a && run l pc qs ex (P * m) (k + weight a) rest

/-- One case: `qs = none` is the main case with exclusion list `ex`, `qs = some Q` the case
`q = Q`. -/
def checkCase (l : ℕ) (pc : List (ℕ × ℕ × List ℕ)) (qs : Option ℕ) (ex : List ℕ)
    (c : List (ℕ × ℕ × ℕ)) : Bool :=
  run l pc qs ex 1 0 c

/-- A whole certificate: the main case and one case per excluded prime. -/
def checkCert (l : ℕ) (pc : List (ℕ × ℕ × List ℕ)) (main : List (ℕ × ℕ × ℕ))
    (cases : List (ℕ × List (ℕ × ℕ × ℕ))) : Bool :=
  trialPrime l && l != 2 && Pratt.check pc && checkCase l pc none (cases.map Prod.fst) main &&
    cases.all fun c => checkCase l pc (some c.1) [] c.2

/-! ## Arithmetic lemmas -/

/-- A prime power `m` has `gcd(a ^ m - a mod m, m) ≠ 1`; so a witness shows that `m > 1` has at
least two distinct prime factors. -/
theorem two_le_card_of_witness {m a : ℕ} (hm : 1 < m) (ha : a < m)
    (h : Nat.gcd (fermatRes a m) m = 1) : 2 ≤ m.primeFactors.card := by
  by_contra hlt
  have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hm
  have h1 : m.primeFactors.card = 1 := by
    have := hne.card_pos
    omega
  obtain ⟨r, e, hr, he, rfl⟩ := isPrimePow_iff_card_primeFactors_eq_one.mpr h1
  have hrN : r.Prime := hr.nat_prime
  have : Fact r.Prime := ⟨hrN⟩
  have hrm : r ∣ r ^ e := dvd_pow_self r he.ne'
  have hdvd : r ∣ powMod a (r ^ e) (r ^ e) + r ^ e - a := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega), Nat.cast_add, powMod_eq]
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hrm, add_zero]
    have hmod : ((a ^ r ^ e % r ^ e : ℕ) : ZMod r) = ((a ^ r ^ e : ℕ) : ZMod r) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((Nat.mod_modEq _ _).of_dvd hrm)
    rw [hmod, Nat.cast_pow, ZMod.pow_card_pow, sub_self]
  have hg : r ∣ Nat.gcd (fermatRes a (r ^ e)) (r ^ e) :=
    Nat.dvd_gcd ((Nat.dvd_mod_iff hrm).mpr hdvd) hrm
  rw [h] at hg
  exact hrN.one_lt.ne' (Nat.dvd_one.mp hg)

/-- The weight of an accepted counted number is at most its number of prime factors. -/
theorem weight_le {m a : ℕ} (hm : 1 < m) (h : witnessOK m a = true) :
    weight a ≤ m.primeFactors.card := by
  unfold weight
  split_ifs with ha
  · exact (Nat.nonempty_primeFactors.mpr hm).card_pos
  · simp only [witnessOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
      at h
    rcases h with h | ⟨h1, h2⟩
    · exact absurd h ha
    · exact two_le_card_of_witness hm h1 h2

/-! ## Soundness -/

section Sound

variable {l N q : ℕ}

/-- The meaning of a state `(P, k)`. -/
abbrev Holds (l N : ℕ) (P k : ℕ) : Prop :=
  P ≠ 0 ∧ (∀ r ∈ P.primeFactors, r ∣ N ∧ r % l = 1) ∧ k ≤ P.primeFactors.card

/-- The meaning of `qs` and `ex`. -/
abbrev Ctx (q : ℕ) (qs : Option ℕ) (ex : List ℕ) : Prop :=
  (∀ Q, qs = some Q → Q = q) ∧ ∀ r ∈ ex, r ≠ q

/-- At most `l` prime factors of `N` are `1` modulo `l`. -/
theorem card_filter_le (h : OddPerfect N) (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) :
    (N.primeFactors.filter (fun p => p % l = 1)).card ≤ l ∧
      (N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1)).card ≤ l - 1 := by
  have hodd : Odd l := hl.odd_of_ne_two hl2
  obtain ⟨β, hβ⟩ := hodd
  have hc := card_mod_one_le (q := q) h.perfect hl hl2 (β := β) hβ.symm
    (fun p hp hpq => by rw [hexp p hp hpq]; omega) hlN hlq
  refine ⟨?_, by omega⟩
  have hsub : N.primeFactors.filter (fun p => p % l = 1) ⊆
      insert q (N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_insert, Finset.mem_filter]
    by_cases hxq : x = q
    · exact Or.inl hxq
    · exact Or.inr ⟨hx.1, hxq, hx.2⟩
  have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  omega

/-- Soundness of `neqOK`. -/
theorem neqOK_sound (hq4 : q % 4 = 1) {qs : Option ℕ} {ex : List ℕ} (hc : Ctx q qs ex)
    {p : ℕ} (h : neqOK qs ex p = true) : p ≠ q := by
  unfold neqOK at h
  cases hqs : qs with
  | some Q =>
    rw [hqs] at h
    simp only [bne_iff_ne, ne_eq] at h
    rw [← hc.1 Q hqs]
    exact h
  | none =>
    rw [hqs] at h
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
    rcases h with h | h
    · rintro rfl
      omega
    · exact hc.2 p h

/-- Soundness of `dvdOK` for a prime `p`. -/
theorem dvdOK_sound (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    {qs : Option ℕ} {ex : List ℕ} (hc : Ctx q qs ex) {P k : ℕ} (hs : Holds l N P k) {p : ℕ}
    (hp : p.Prime) (hd : dvdOK qs P p = true) : p ∣ N := by
  unfold dvdOK at hd
  simp only [Bool.or_eq_true, beq_iff_eq] at hd
  rcases hd with hd | hd
  · have hpP : p ∈ P.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, Nat.dvd_of_mod_eq_zero hd, hs.1⟩
    exact (hs.2.1 p hpP).1
  · cases hqs : qs with
    | none => rw [hqs] at hd; exact absurd hd (by simp)
    | some Q =>
      rw [hqs] at hd
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hd
      obtain ⟨hp2, hpd⟩ := hd
      rw [hc.1 Q hqs] at hpd
      have hk : 1 + 1 ∣ N.factorization q + 1 := by
        obtain ⟨j, hj⟩ := hodd
        exact ⟨j + 1, by omega⟩
      have hσ : p ∣ σ 1 (q ^ 1) := by
        rw [sigma_one_apply_prime_pow hq, Finset.sum_range_succ, Finset.sum_range_one, pow_zero,
          pow_one]
        exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_comm]; exact hpd)
      exact OPNStarter.force_prime h.perfect hq rfl hp hp2
        (hσ.trans (OPNExample.sigma_prime_pow_dvd hq hk))

/-- Soundness of `run`: an accepted walk refutes every state that holds. -/
theorem run_sound {pc : List (ℕ × ℕ × List ℕ)} (hpc : Pratt.check pc = true)
    (hl : l.Prime) (hl2 : l ≠ 2) (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hlN : l ∈ N.primeFactors) (hlq : l ≠ q) {qs : Option ℕ} {ex : List ℕ}
    (hc : Ctx q qs ex) :
    ∀ (c : List (ℕ × ℕ × ℕ)) (P k : ℕ), run l pc qs ex P k c = true → Holds l N P k → False := by
  have hN := h.ne_zero
  have hq4 := (special_mod_four h hq hodd).1
  have hl1 : 1 < l := hl.one_lt
  intro c
  induction c with
  | nil =>
    intro P k hr hs
    obtain ⟨hP0, hPf, hk⟩ := hs
    have hsub : P.primeFactors ⊆ N.primeFactors.filter (fun p => p % l = 1) := by
      intro r hr
      rw [Finset.mem_filter]
      exact ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hr, (hPf r hr).1, hN⟩,
        (hPf r hr).2⟩
    obtain ⟨hc1, hc2⟩ := card_filter_le h hl hl2 hexp hlN hlq
    have hk1 := hk.trans ((Finset.card_le_card hsub).trans hc1)
    simp only [run, finalOK, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with hr | hr
    · omega
    · cases hqs : qs with
      | none => rw [hqs] at hr; exact absurd hr (by simp)
      | some Q =>
        rw [hqs] at hr
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hr
        obtain ⟨hlk, hPQ⟩ := hr
        rw [hc.1 Q hqs] at hPQ
        have hsub' : P.primeFactors ⊆ N.primeFactors.filter (fun p => p ≠ q ∧ p % l = 1) := by
          intro r hr
          rw [Finset.mem_filter]
          refine ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hr, (hPf r hr).1,
            hN⟩, ?_, (hPf r hr).2⟩
          rintro rfl
          exact hPQ (Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_primeFactors hr))
        have := hk.trans ((Finset.card_le_card hsub').trans hc2)
        omega
  | cons e rest ih =>
    obtain ⟨p, m, a⟩ := e
    intro P k hr hs
    simp only [run, Bool.and_eq_true] at hr
    obtain ⟨⟨hpar, hpiece⟩, hnext⟩ := hr
    -- the parent is an ordinary prime factor
    have hpo : p.Prime ∧ p ∈ N.primeFactors ∧ p ≠ q := by
      simp only [parentOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hpar
      rcases hpar with rfl | ⟨⟨hpP, hpd⟩, hpn⟩
      · exact ⟨hl, hlN, hlq⟩
      · have hpP' := isP_sound hpc hpP
        exact ⟨hpP', Nat.mem_primeFactors.mpr ⟨hpP', dvdOK_sound h hq hodd hc hs hpP' hpd, hN⟩,
          neqOK_sound hq4 hc hpn⟩
    obtain ⟨hpP, hpN, hpq⟩ := hpo
    have hpe := hexp p hpN hpq
    simp only [pieceOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      beq_iff_eq] at hpiece
    obtain ⟨⟨⟨⟨hm1, hml⟩, hgm⟩, hcop⟩, hw⟩ := hpiece
    have hmΦ : m ∣ σ 1 (p ^ N.factorization p) := by
      rw [hpe]
      exact dvd_sigma_of_gm hpP hl1.le hgm
    have hm0 : m ≠ 0 := by omega
    have hcop' : Nat.Coprime m P := hcop
    refine ih (P * m) (k + weight a) hnext ⟨mul_ne_zero hs.1 hm0, fun r hr => ?_, ?_⟩
    · rw [Nat.primeFactors_mul hs.1 hm0, Finset.mem_union] at hr
      rcases hr with hr | hr
      · exact hs.2.1 r hr
      · have hrP := Nat.prime_of_mem_primeFactors hr
        have hrm := Nat.dvd_of_mem_primeFactors hr
        have hrl : r % l = 1 := by
          rcases prime_dvd_sigma_prime_pow_of_prime_length hpP hrP hl
            (by rw [← hpe]; exact hrm.trans hmΦ) with h1 | h1
          · subst h1
            exact absurd (Nat.mod_eq_zero_of_dvd hrm) hml
          · exact h1
        have hr2 : r ≠ 2 := by
          rintro rfl
          rw [Nat.mod_eq_of_lt (by have := hl.two_le; omega)] at hrl
          omega
        exact ⟨OPNStarter.force_prime h.perfect hpP rfl hrP hr2 (hrm.trans hmΦ), hrl⟩
    · rw [Nat.Coprime.primeFactors_mul hcop'.symm, Finset.card_union_of_disjoint
        hcop'.symm.disjoint_primeFactors]
      have := weight_le hm1 hw
      have := hs.2.2
      omega

end Sound

/-- Soundness of an accepted certificate, given `l ≠ q`. -/
theorem checkCert_sound_of_ne {l : ℕ} {pc : List (ℕ × ℕ × List ℕ)}
    {main : List (ℕ × ℕ × ℕ)} {cases : List (ℕ × List (ℕ × ℕ × ℕ))}
    (hc : checkCert l pc main cases = true) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) (hlq : l ≠ q) :
    False := by
  simp only [checkCert, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨hlP, hl2⟩, hpc⟩, hmain⟩, hcases⟩ := hc
  have hl := trialPrime_sound hlP
  by_cases hlN : l ∣ N
  · have hlN' : l ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hl, hlN, h.ne_zero⟩
    have hs : Holds l N 1 0 := ⟨one_ne_zero, by simp, by simp⟩
    by_cases hqc : q ∈ cases.map Prod.fst
    · obtain ⟨⟨Q, c⟩, hmem, hQ⟩ := List.mem_map.mp hqc
      exact run_sound hpc hl hl2 h hq hodd hexp hlN' hlq
        ⟨fun Q' hQ' => by rw [← Option.some.inj hQ']; exact hQ, by simp⟩ c 1 0
        (hcases _ hmem) hs
    · exact run_sound hpc hl hl2 h hq hodd hexp hlN' hlq
        ⟨by simp, fun r hr hrq => hqc (hrq ▸ hr)⟩ main 1 0 hmain hs
  · exact not_all_exponents_eq_pred_prime h hq hodd hl hl2 hlN hexp

/-- Acceptance from its parts (so that each part is checked by its own `decide`). -/
theorem checkCert_of {l : ℕ} {pc : List (ℕ × ℕ × List ℕ)}
    {main : List (ℕ × ℕ × ℕ)} {cases : List (ℕ × List (ℕ × ℕ × ℕ))}
    (hl : trialPrime l = true) (hl2 : l ≠ 2) (hpc : Pratt.check pc = true)
    (hmain : checkCase l pc none (cases.map Prod.fst) main = true)
    (hcases : ∀ c ∈ cases, checkCase l pc (some c.1) [] c.2 = true) :
    checkCert l pc main cases = true := by
  simp only [checkCert, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨hl, hl2⟩, hpc⟩, hmain⟩, hcases⟩

/-- An accepted certificate has an odd prime `l`. -/
theorem checkCert_prime {l : ℕ} {pc : List (ℕ × ℕ × List ℕ)}
    {main : List (ℕ × ℕ × ℕ)} {cases : List (ℕ × List (ℕ × ℕ × ℕ))}
    (hc : checkCert l pc main cases = true) : l.Prime ∧ l ≠ 2 := by
  simp only [checkCert, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  exact ⟨trialPrime_sound hc.1.1.1.1, hc.1.1.1.2⟩

/-- Soundness of an accepted certificate for `l ≡ 3 (mod 4)`: then `l` is not the special
prime. -/
theorem checkCert_sound_of_mod_four {l : ℕ} {pc : List (ℕ × ℕ × List ℕ)}
    {main : List (ℕ × ℕ × ℕ)} {cases : List (ℕ × List (ℕ × ℕ × ℕ))}
    (hc : checkCert l pc main cases = true) (hl4 : l % 4 = 3) {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) : False :=
  checkCert_sound_of_ne hc h hq hodd hexp fun hlq => by
    have := (special_mod_four h hq hodd).1
    omega

end OddPerfect.EqCount

#print axioms OddPerfect.EqCount.two_le_card_of_witness
#print axioms OddPerfect.EqCount.weight_le
#print axioms OddPerfect.EqCount.card_filter_le
#print axioms OddPerfect.EqCount.neqOK_sound
#print axioms OddPerfect.EqCount.dvdOK_sound
#print axioms OddPerfect.EqCount.run_sound
#print axioms OddPerfect.EqCount.checkCert_sound_of_ne
#print axioms OddPerfect.EqCount.checkCert_prime
#print axioms OddPerfect.EqCount.checkCert_sound_of_mod_four
