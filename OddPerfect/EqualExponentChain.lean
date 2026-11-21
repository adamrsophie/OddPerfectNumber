import OddPerfect.Pratt
import OddPerfect.Steuerwald
import OddPerfect.SpecialPrime
import OddPerfect.Valuation
import OddPerfect.Cyclotomic

/-!
# Equal exponent chains: a verified certificate checker

Fix an odd prime `l` and an odd perfect number `N` with special prime `q` (the prime with odd
exponent `k`) whose other exponents all equal `l - 1`. We show `False` from a certificate that
the kernel checks by `decide +kernel`.

If `l ∤ N` this is `not_all_exponents_eq_pred_prime`. Otherwise either `l` is ordinary or
`l = q`, and a certificate tree is checked in each case. Its state records

* `known`: primes proved to be ordinary prime factors (exponent `l - 1`);
* `ex`: primes proved to differ from `q`;
* `qs`: the value of `q`, once a branch has fixed it;
* `M`: a number proved to divide `k + 1` (initially `2`).

Step rules:

* `ord p r`: for a known `p`, the prime `r ≠ 2` divides `σ(p ^ (l - 1))`, hence `N`; it is
  ordinary when `r ≢ 1 (mod 4)`, `r ∈ ex`, or `r ≠ q` for the known `q`.
* `spec m r`: for the known `q` and `m ∣ M`, the prime `r ≠ 2, q` divides `σ(q ^ (m - 1))`,
  which divides `σ(q ^ k)`, so `r` is ordinary.
* `branch r`: either `q = r` or `r ∈ ex`.
* `expo s d v`: for a known `s` with `s ≠ l` and `s ≢ 1 (mod l)` no ordinary component
  contributes to the `s`-adic ledger, so `v_s(σ(q ^ k)) = l - 1`. With `d` the order of `q`
  modulo `s` and `v ≥ v_s(q ^ d - 1)`, lifting the exponent gives `d s ^ (l - 1 - v) ∣ k + 1`
  (and `s ^ (l - 1) ∣ k + 1` when `d = 1`).

Closing rules:

* `overflow s ps m k`: the `s`-adic ledger of a known `s` overflows: the listed distinct known
  primes `p` contribute `s ^ j ∣ σ(p ^ (l - 1))`, and the special component contributes
  `s ^ k ∣ σ(q ^ (m - 1))` with `m ∣ M`.
* `mod4`: the known `q` is not `1 (mod 4)`.

Divisibility is checked by Horner evaluation modulo the divisor (`gm`), primality by trial
division or by Pratt certificates (`OddPerfect.Pratt`).
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.EqChain

open OddPerfect.Pratt (powMod powMod_eq trialPrime trialPrime_sound)

/-! ## Computable helpers -/

/-- Horner evaluation of `(∑ i < n, p ^ i) % m`. -/
def gm (p m : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (gm p m n * p + 1) % m

/-- `gm` computes the geometric sum modulo `m`. -/
theorem gm_eq (p m : ℕ) : ∀ n, gm p m n = (∑ i ∈ Finset.range n, p ^ i) % m
  | 0 => by simp [gm]
  | n + 1 => by
    have hs : ∑ i ∈ Finset.range (n + 1), p ^ i = (∑ i ∈ Finset.range n, p ^ i) * p + 1 := by
      rw [Finset.sum_range_succ', Finset.sum_mul]
      simp [pow_succ]
    rw [gm, gm_eq p m n, hs, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
      ← Nat.add_mod]

/-- If `gm p r n = 0` with `n ≥ 1` then `r ∣ σ(p ^ (n - 1))`. -/
theorem dvd_sigma_of_gm {p r n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (h : gm p r n = 0) :
    r ∣ σ 1 (p ^ (n - 1)) := by
  rw [sigma_one_apply_prime_pow hp, Nat.sub_add_cancel hn]
  exact Nat.dvd_of_mod_eq_zero (by rw [← gm_eq]; exact h)

/-- Primality: listed in an accepted Pratt certificate, or trial division. -/
def isP (pc : List (ℕ × ℕ × List ℕ)) (r : ℕ) : Bool :=
  (pc.map Prod.fst).contains r || trialPrime r

/-- Soundness of `isP`. -/
theorem isP_sound {pc : List (ℕ × ℕ × List ℕ)} (hpc : Pratt.check pc = true) {r : ℕ}
    (h : isP pc r = true) : r.Prime := by
  simp only [isP, Bool.or_eq_true, List.contains_iff_mem, List.mem_map] at h
  rcases h with ⟨e, he, rfl⟩ | h
  · exact Pratt.check_sound hpc e he
  · exact trialPrime_sound h

/-- Boolean duplicate freeness. -/
def nodupB : List ℕ → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

/-- The sum of the claimed valuations. -/
def ksum : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (_, k) :: l => k + ksum l

/-- `allNe Q s n`: `Q ^ j % s ≠ 1` for `1 ≤ j ≤ n`. -/
def allNe (Q s : ℕ) : ℕ → Bool
  | 0 => true
  | j + 1 => powMod Q (j + 1) s != 1 && allNe Q s j

/-- Soundness of `allNe`. -/
theorem allNe_sound {Q s : ℕ} : ∀ {n}, allNe Q s n = true → ∀ j, 0 < j → j ≤ n →
    Q ^ j % s ≠ 1
  | 0, _, j, h0, hj => by omega
  | n + 1, h, j, h0, hj => by
    simp only [allNe, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · exact allNe_sound h.2 j h0 (by omega)
    · rw [show j = n + 1 by omega, ← powMod_eq]
      exact h.1

/-- The factor of `k + 1` produced by an `expo` step. -/
def expoFactor (l s d v : ℕ) : ℕ := if d = 1 then s ^ (l - 1) else d * s ^ (l - 1 - v)

/-! ## States and certificates -/

/-- The checker state. -/
structure St where
  /-- Primes known to be ordinary prime factors. -/
  known : List ℕ
  /-- Primes known to differ from the special prime. -/
  ex : List ℕ
  /-- The special prime, if known. -/
  qs : Option ℕ
  /-- A known divisor of `k + 1`, where `k` is the exponent of the special prime. -/
  M : ℕ

/-- A certificate tree. -/
inductive Node where
  /-- Force the prime `r` from the ordinary component of the known prime `p`. -/
  | ord (p r : ℕ) (next : Node)
  /-- Force the prime `r` from `σ(q ^ (m - 1))` with `m ∣ M` and `q` known. -/
  | spec (m r : ℕ) (next : Node)
  /-- Branch: `q = r`, or `q ≠ r`. -/
  | branch (r : ℕ) (yes no : Node)
  /-- Lift the exponent at the known prime `s`, with `d` the order of `q` modulo `s`. -/
  | expo (s d v : ℕ) (next : Node)
  /-- Overflow of the `s`-adic ledger. -/
  | overflow (s : ℕ) (ps : List (ℕ × ℕ)) (m k : ℕ)
  /-- The known special prime is not `1 (mod 4)`. -/
  | mod4

/-- `r` is certainly not the special prime. -/
def neq (st : St) (r : ℕ) : Bool :=
  match st.qs with
  | some Q => r != Q
  | none => r % 4 != 1 || st.ex.contains r

/-- The special component contributes `s ^ k` through `σ(q ^ (m - 1))`. -/
def specOK (st : St) (s m k : ℕ) : Bool :=
  match st.qs with
  | some Q => 1 ≤ m && st.M % m == 0 && gm Q (s ^ k) m == 0
  | none => false

/-- The checker. -/
def run (l : ℕ) (pc : List (ℕ × ℕ × List ℕ)) : St → Node → Bool
  | st, .ord p r c =>
      st.known.contains p && isP pc r && r != 2 && neq st r && gm p r l == 0 &&
        run l pc { st with known := r :: st.known } c
  | st, .spec m r c =>
      match st.qs with
      | some Q => 1 ≤ m && st.M % m == 0 && isP pc r && r != 2 && r != Q && gm Q r m == 0 &&
          run l pc { st with known := r :: st.known } c
      | none => false
  | st, .branch r y n =>
      run l pc { st with qs := some r } y && run l pc { st with ex := r :: st.ex } n
  | st, .expo s d v c =>
      match st.qs with
      | some Q => st.known.contains s && s != 2 && s != l && s % l != 1 && 1 ≤ d &&
          powMod Q d s == 1 && allNe Q s (d - 1) && (d == 1 || powMod Q d (s ^ (v + 1)) != 1) &&
          run l pc { st with M := Nat.lcm st.M (expoFactor l s d v) } c
      | none => false
  | st, .overflow s ps m k =>
      st.known.contains s && s != 2 &&
        ps.all (fun x => st.known.contains x.1 && gm x.1 (s ^ x.2) l == 0) &&
        nodupB (ps.map Prod.fst) && (k == 0 || specOK st s m k) && l - 1 < k + ksum ps
  | st, .mod4 =>
      match st.qs with
      | some Q => Q % 4 != 1
      | none => false

/-- The full check for the prime `l`: `ordT` handles `l` ordinary, `specT` handles `l = q`. -/
def checkAll (l : ℕ) (pc : List (ℕ × ℕ × List ℕ)) (ordT specT : Node) : Bool :=
  trialPrime l && l != 2 && Pratt.check pc &&
    run l pc ⟨[l], [l], none, 2⟩ ordT && run l pc ⟨[], [], some l, 2⟩ specT

/-! ## Soundness -/

/-- The meaning of a state. -/
abbrev Holds (l N q : ℕ) (st : St) : Prop :=
  (∀ p ∈ st.known, p.Prime ∧ N.factorization p = l - 1 ∧ p ≠ q) ∧ (∀ r ∈ st.ex, r ≠ q) ∧
    (∀ Q, st.qs = some Q → Q = q) ∧ st.M ∣ N.factorization q + 1

section Sound

variable {l N q : ℕ} {pc : List (ℕ × ℕ × List ℕ)}

/-- Soundness of `neq`. -/
theorem neq_sound {st : St} (hs : Holds l N q st) (hq4 : q % 4 = 1) {r : ℕ}
    (h : neq st r = true) : r ≠ q := by
  unfold neq at h
  cases hqs : st.qs with
  | some Q =>
    rw [hqs] at h
    simp only [bne_iff_ne, ne_eq] at h
    rw [← hs.2.2.1 Q hqs]
    exact h
  | none =>
    rw [hqs] at h
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at h
    rcases h with h | h
    · rintro rfl
      exact h hq4
    · exact hs.2.1 r h

/-- The `q`-adic contribution of the component of `N` at `p`. -/
abbrev incoming (N s p : ℕ) : ℕ := (σ 1 (p ^ N.factorization p)).factorization s

/-- The contributions claimed by an `overflow` step are bounded by the true ones. -/
theorem over_sum {st : St} (hs : Holds l N q st) (hN : N ≠ 0) {s : ℕ} (hsP : s.Prime)
    (hl : 2 ≤ l) :
    ∀ {ps : List (ℕ × ℕ)}, ps.all (fun x => st.known.contains x.1 && gm x.1 (s ^ x.2) l == 0)
      = true → nodupB (ps.map Prod.fst) = true →
      (ps.map Prod.fst).toFinset ⊆ N.primeFactors ∧ q ∉ (ps.map Prod.fst).toFinset ∧
        ksum ps ≤ ∑ p ∈ (ps.map Prod.fst).toFinset, incoming N s p
  | [], _, _ => by simp [ksum]
  | (p, j) :: ps, h1, h2 => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h1
    simp only [List.map_cons, nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h2
    obtain ⟨⟨hpk, hgm⟩, hrest1⟩ := h1
    obtain ⟨hnc, hrest2⟩ := h2
    have hnot : p ∉ (ps.map Prod.fst).toFinset := by
      rw [List.mem_toFinset]
      intro hm
      rw [List.contains_iff_mem.mpr hm] at hnc
      exact Bool.noConfusion hnc
    obtain ⟨hsub, hqn, hle⟩ := over_sum hs hN hsP hl hrest1 hrest2
    obtain ⟨hpP, hpe, hpq⟩ := hs.1 p hpk
    have hpN : p ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpP, Nat.dvd_of_factorization_pos (by omega), hN⟩
    have hj : j ≤ incoming N s p := by
      have hd : s ^ j ∣ σ 1 (p ^ N.factorization p) := by
        rw [hpe]
        exact dvd_sigma_of_gm hpP (by omega) hgm
      exact (hsP.pow_dvd_iff_le_factorization (sigma_pos 1 _ (pow_ne_zero _ hpP.ne_zero)).ne').mp hd
    simp only [List.map_cons, List.toFinset_cons, Finset.sum_insert hnot, ksum,
      Finset.mem_insert, not_or]
    exact ⟨Finset.insert_subset hpN hsub, ⟨Ne.symm hpq, hqn⟩, by omega⟩

/-- The exponent lifting step: if `s` is a known ordinary prime with `s ≠ l` and
`s ≢ 1 (mod l)`, `d` is the order of `q` modulo `s` and `v ≥ v_s(q ^ d - 1)` (when `d > 1`),
then `expoFactor l s d v ∣ k + 1`. -/
theorem expo_dvd (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1)
    (hl : l.Prime) (hl2 : l ≠ 2) {s d v : ℕ} (hs : s.Prime) (hse : N.factorization s = l - 1)
    (hsq : s ≠ q) (hs2 : s ≠ 2) (hsl : s ≠ l) (hs1 : s % l ≠ 1) (hd1 : 1 ≤ d)
    (hpow : q ^ d % s = 1) (hall : ∀ j, 0 < j → j < d → q ^ j % s ≠ 1)
    (hv : d = 1 ∨ q ^ d % s ^ (v + 1) ≠ 1) :
    expoFactor l s d v ∣ N.factorization q + 1 := by
  have : Fact s.Prime := ⟨hs⟩
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨j, hj⟩ := hodd; omega)
  have key : padicValNat s (σ 1 (q ^ N.factorization q)) = l - 1 := by
    have hsum := factorization_eq_sum_erase h.perfect hs hs2
    rw [hse, Finset.sum_eq_single_of_mem q (Finset.mem_erase.mpr ⟨Ne.symm hsq, hqmem⟩)] at hsum
    · exact hsum.symm
    · intro p hp hpq
      obtain ⟨-, hpN⟩ := Finset.mem_erase.mp hp
      rw [hexp p hpN hpq]
      refine padicValNat.eq_zero_of_not_dvd fun hd => ?_
      rcases prime_dvd_sigma_prime_pow_of_prime_length (Nat.prime_of_mem_primeFactors hpN) hs
        hl hd with h1 | h1
      · exact hsl h1
      · exact hs1 h1
  have h1s : 1 % s = 1 := Nat.mod_eq_of_lt hs.one_lt
  have hkey : ∀ j, (q : ZMod s) ^ j = 1 ↔ q ^ j % s = 1 := fun j => by
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', h1s]
  have hord : orderOf (q : ZMod s) = d := by
    rw [orderOf_eq_iff (by omega)]
    exact ⟨(hkey d).2 hpow, fun j hj hj0 => by rw [Ne, hkey]; exact hall j hj0 hj⟩
  by_cases hd : d = 1
  · subst hd
    simp only [expoFactor, if_true]
    have hdvd : s ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_lt.le).mp (by
      rw [Nat.ModEq, h1s]
      rw [pow_one] at hpow
      exact hpow.symm)
    have hv' := padicValNat_sigma_prime_pow_of_dvd_pred hq hs hs2 hdvd (a := N.factorization q)
    rw [key] at hv'
    rw [hv']
    exact pow_padicValNat_dvd
  · have hd2 : 1 < d := by omega
    have hdk : d ∣ N.factorization q + 1 := by
      by_contra hnd
      have := padicValNat_sigma_prime_pow_of_not_orderOf_dvd hq hs (a := N.factorization q)
        (by rw [hord]; exact hnd)
      omega
    have hf := padicValNat_sigma_prime_pow_of_orderOf_dvd hq hs hs2 (Ne.symm hsq)
      (by rw [hord]; exact hd2) (by rw [hord]; exact hdk)
    rw [hord, key] at hf
    have hqd : 1 < q ^ d := Nat.one_lt_pow (by omega) hq.one_lt
    have hvle : padicValNat s (q ^ d - 1) ≤ v := by
      by_contra hlt
      push Not at hlt
      have hdv : s ^ (v + 1) ∣ q ^ d - 1 := (padicValNat_dvd_iff_le (by omega)).mpr hlt
      have hm := (Nat.modEq_iff_dvd' hqd.le).mpr hdv
      have h1v : 1 % s ^ (v + 1) = 1 := Nat.mod_eq_of_lt (Nat.one_lt_pow (by omega) hs.one_lt)
      rw [Nat.ModEq, h1v] at hm
      exact (hv.resolve_left hd) hm.symm
    obtain ⟨t, ht⟩ := hdk
    have ht0 : t ≠ 0 := by rintro rfl; omega
    rw [ht, Nat.mul_div_cancel_left _ (by omega)] at hf
    have hst : s ^ (l - 1 - v) ∣ t := (padicValNat_dvd_iff_le ht0).mpr (by omega)
    simp only [expoFactor, if_neg hd]
    rw [ht]
    exact Nat.mul_dvd_mul_left d hst

/-- Soundness of the checker: an accepted tree refutes every state that holds. -/
theorem run_sound (hpc : Pratt.check pc = true) (hl : l.Prime) (hl2 : l ≠ 2) (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    ∀ (c : Node) (st : St), run l pc st c = true → Holds l N q st → False := by
  have hN := h.ne_zero
  have hq4 := (special_mod_four h hq hodd).1
  have hqN : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨j, hj⟩ := hodd; omega)
  intro c
  induction c with
  | ord p r c ih =>
    intro st hc hs
    simp only [run, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.contains_iff_mem] at hc
    obtain ⟨⟨⟨⟨⟨hp, hr⟩, hr2⟩, hne⟩, hgm⟩, hnext⟩ := hc
    obtain ⟨hpP, hpe, -⟩ := hs.1 p hp
    have hrP := isP_sound hpc hr
    have hrq := neq_sound hs hq4 hne
    have hrN : r ∣ N := OPNStarter.force_prime h.perfect hpP hpe hrP hr2
      (dvd_sigma_of_gm hpP hl.one_lt.le hgm)
    have hre := hexp r (Nat.mem_primeFactors.mpr ⟨hrP, hrN, hN⟩) hrq
    refine ih _ hnext ⟨fun x hx => ?_, hs.2.1, hs.2.2.1, hs.2.2.2⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hrP, hre, hrq⟩
    · exact hs.1 x hx
  | spec m r c ih =>
    intro st hc hs
    cases hqs : st.qs with
    | none => simp [run, hqs] at hc
    | some Q =>
      simp only [run, hqs, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
        decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨hm, hM⟩, hr⟩, hr2⟩, hrQ⟩, hgm⟩, hnext⟩ := hc
      have hQ := hs.2.2.1 Q hqs
      subst hQ
      have hrP := isP_sound hpc hr
      have hmk : m - 1 + 1 ∣ N.factorization Q + 1 := by
        rw [Nat.sub_add_cancel hm]
        exact (Nat.dvd_of_mod_eq_zero hM).trans hs.2.2.2
      have hrN : r ∣ N := OPNStarter.force_prime h.perfect hq rfl hrP hr2
        ((dvd_sigma_of_gm hq hm hgm).trans (OPNExample.sigma_prime_pow_dvd hq hmk))
      have hre := hexp r (Nat.mem_primeFactors.mpr ⟨hrP, hrN, hN⟩) hrQ
      refine ih _ hnext ⟨fun x hx => ?_, hs.2.1, fun Q' hQ' => hs.2.2.1 Q' (hqs.trans hQ'),
        hs.2.2.2⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hrP, hre, hrQ⟩
      · exact hs.1 x hx
  | branch r y n ihy ihn =>
    intro st hc hs
    simp only [run, Bool.and_eq_true] at hc
    by_cases hrq : r = q
    · refine ihy _ hc.1 ⟨hs.1, hs.2.1, fun Q hQ => ?_, hs.2.2.2⟩
      rw [← Option.some.inj hQ, hrq]
    · refine ihn _ hc.2 ⟨hs.1, fun x hx => ?_, hs.2.2.1, hs.2.2.2⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hrq
      · exact hs.2.1 x hx
  | expo s d v c ih =>
    intro st hc hs
    cases hqs : st.qs with
    | none => simp [run, hqs] at hc
    | some Q =>
      simp only [run, hqs, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq,
        List.contains_iff_mem, Bool.or_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsk, hs2⟩, hsl⟩, hs1⟩, hd1⟩, hpow⟩, hall⟩, hv⟩, hnext⟩ := hc
      have hQ := hs.2.2.1 Q hqs
      subst hQ
      obtain ⟨hsP, hse, hsq⟩ := hs.1 s hsk
      have hdiv := expo_dvd h hq hodd hexp hl hl2 hsP hse hsq hs2 hsl hs1 hd1
        (by rw [← powMod_eq]; exact hpow) (fun j hj0 hj => allNe_sound hall j hj0 (by omega))
        (hv.imp id fun h' => by rwa [powMod_eq] at h')
      exact ih _ hnext ⟨hs.1, hs.2.1, fun Q' hQ' => hs.2.2.1 Q' (hqs.trans hQ'),
        Nat.lcm_dvd hs.2.2.2 hdiv⟩
  | overflow s ps m k =>
    intro st hc hs
    simp only [run, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨hsk, hs2⟩, hall⟩, hnd⟩, hspec⟩, hlt⟩ := hc
    simp only [bne_iff_ne, ne_eq] at hs2
    obtain ⟨hsP, hse, hsq⟩ := hs.1 s (List.contains_iff_mem.mp hsk)
    obtain ⟨hsub, hqn, hle⟩ := over_sum hs hN hsP hl.two_le hall hnd
    have hk : k ≤ incoming N s q := by
      simp only [Bool.or_eq_true, beq_iff_eq] at hspec
      rcases hspec with h0 | h0
      · omega
      · unfold specOK at h0
        cases hqs : st.qs with
        | none => simp [hqs] at h0
        | some Q =>
          simp only [hqs, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h0
          obtain ⟨⟨hm, hM⟩, hgm⟩ := h0
          have hQ := hs.2.2.1 Q hqs
          subst hQ
          have hmk : m - 1 + 1 ∣ N.factorization Q + 1 := by
            rw [Nat.sub_add_cancel hm]
            exact (Nat.dvd_of_mod_eq_zero hM).trans hs.2.2.2
          have hd : s ^ k ∣ σ 1 (Q ^ N.factorization Q) :=
            (dvd_sigma_of_gm hq hm hgm).trans (OPNExample.sigma_prime_pow_dvd hq hmk)
          exact (hsP.pow_dvd_iff_le_factorization
            (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne').mp hd
    have hbal := OPNStarter.valuation_balance h.perfect s
    have h2 : Nat.factorization 2 s = 0 := by
      rw [Nat.prime_two.factorization, Finsupp.single_apply, if_neg (Ne.symm hs2)]
    have hsum := Finset.sum_le_sum_of_subset (f := incoming N s)
      (Finset.insert_subset hqN hsub)
    rw [Finset.sum_insert hqn] at hsum
    have htot : ∑ x ∈ N.primeFactors, incoming N s x = l - 1 := by
      rw [← hse, ← zero_add (N.factorization s), ← h2]
      exact hbal.symm
    have hlt' : l - 1 < k + ksum ps := of_decide_eq_true hlt
    omega
  | mod4 =>
    intro st hc hs
    cases hqs : st.qs with
    | none => simp [run, hqs] at hc
    | some Q =>
      simp only [run, hqs, bne_iff_ne, ne_eq] at hc
      exact hc (by rw [hs.2.2.1 Q hqs]; exact hq4)

end Sound

/-- Soundness of `checkAll`: an accepted certificate for `l` shows that the ordinary
exponents of an odd perfect number cannot all equal `l - 1`. -/
theorem checkAll_sound {l : ℕ} {pc : List (ℕ × ℕ × List ℕ)} {ordT specT : Node}
    (hc : checkAll l pc ordT specT = true) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) : False := by
  simp only [checkAll, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨⟨hlP, hl2⟩, hpc⟩, ho⟩, hsp⟩ := hc
  have hl := trialPrime_sound hlP
  have hM : 2 ∣ N.factorization q + 1 := by
    obtain ⟨j, hj⟩ := hodd
    exact ⟨j + 1, by omega⟩
  by_cases hlN : l ∣ N
  · by_cases hlq : l = q
    · refine run_sound hpc hl hl2 h hq hodd hexp specT _ hsp
        ⟨by simp, by simp, fun Q hQ => ?_, hM⟩
      rw [← Option.some.inj hQ, hlq]
    · have hle := hexp l (Nat.mem_primeFactors.mpr ⟨hl, hlN, h.ne_zero⟩) hlq
      refine run_sound hpc hl hl2 h hq hodd hexp ordT _ ho ⟨fun p hp => ?_, fun r hr => ?_,
        by simp, hM⟩
      · rw [List.mem_singleton.mp hp]
        exact ⟨hl, hle, hlq⟩
      · rw [List.mem_singleton.mp hr]
        exact hlq
  · exact not_all_exponents_eq_pred_prime h hq hodd hl hl2 hlN hexp

end OddPerfect.EqChain

/-! ## Instances -/

namespace OddPerfect.EqChain

/-- Pratt certificates for `l = 5`. -/
def pc5 : List (ℕ × ℕ × List ℕ) :=
  [(1361, 3, [2, 2, 2, 2, 5, 17]),
    (11831, 7, [2, 5, 7, 13, 13])]

/-- The tree for `l = 5` when `5` is ordinary. -/
def ord5 : Node :=
  .ord 5 11 <|
  .ord 5 71 <|
  .ord 71 211 <|
  .branch 1361
    (
    .spec 2 3 <|
    .expo 3 2 1 <|
    .spec 6 7 <|
    .expo 7 6 1 <|
    .spec 3 13 <|
    .expo 13 3 1 <|
    .spec 13 53 <|
    .overflow 11 [(3, 2), (71, 1), (53, 1), (5, 1)] 0 0
    )
    (
    .ord 211 1361 <|
    .ord 1361 11831 <|
    .overflow 5 [(11831, 1), (1361, 1), (211, 1), (71, 1), (11, 1)] 0 0
    )

/-- The tree for `l = 5` when `5` is the special prime. -/
def spec5 : Node :=
  .spec 2 3 <|
  .expo 3 2 1 <|
  .spec 6 7 <|
  .expo 7 6 1 <|
  .ord 3 11 <|
  .spec 9 19 <|
  .expo 19 9 1 <|
  .spec 14 29 <|
  .expo 29 14 1 <|
  .spec 3 31 <|
  .spec 29 59 <|
  .spec 54 163 <|
  .overflow 11 [(3, 2), (163, 1), (59, 1), (31, 1)] 0 0

/-- The certificate for `l = 5` is accepted. -/
theorem check5 : checkAll 5 pc5 ord5 spec5 = true := by
  decide +kernel

/-- Pratt certificates for `l = 7`. -/
def pc7 : List (ℕ × ℕ × List ℕ) :=
  [(4733, 5, [2, 2, 7, 13, 13]),
    (50359, 3, [2, 3, 7, 11, 109]),
    (70001, 3, [2, 2, 2, 2, 5, 5, 5, 5, 7])]

/-- The tree for `l = 7` when `7` is ordinary. -/
def ord7 : Node :=
  .branch 29
    (
    .spec 2 3 <|
    .expo 3 2 1 <|
    .spec 2 5 <|
    .expo 5 2 1 <|
    .spec 10 11 <|
    .expo 11 10 1 <|
    .spec 3 13 <|
    .expo 13 3 1 <|
    .spec 18 19 <|
    .expo 19 18 1 <|
    .spec 11 23 <|
    .expo 23 11 1 <|
    .spec 10 31 <|
    .expo 31 10 1 <|
    .ord 11 43 <|
    .spec 46 47 <|
    .expo 47 46 1 <|
    .spec 26 53 <|
    .expo 53 26 1 <|
    .spec 3 67 <|
    .expo 67 3 1 <|
    .spec 78 79 <|
    .expo 79 78 1 <|
    .spec 53 107 <|
    .expo 107 53 1 <|
    .spec 54 109 <|
    .expo 109 54 1 <|
    .ord 109 113 <|
    .spec 130 131 <|
    .expo 131 130 1 <|
    .ord 131 127 <|
    .spec 190 191 <|
    .ord 191 197 <|
    .spec 99 199 <|
    .ord 199 211 <|
    .spec 262 263 <|
    .ord 263 239 <|
    .ord 79 281 <|
    .overflow 7 [(281, 1), (239, 1), (211, 1), (197, 1), (127, 1), (113, 1), (43, 1)] 0 0
    )
    (
    .ord 7 29 <|
    .branch 4733
      (
      .spec 2 3 <|
      .expo 3 2 2 <|
      .spec 9 37 <|
      .ord 37 71 <|
      .spec 6 109 <|
      .ord 109 113 <|
      .spec 18 199 <|
      .ord 199 211 <|
      .spec 2 263 <|
      .ord 263 239 <|
      .ord 109 281 <|
      .spec 9 379 <|
      .overflow 7 [(379, 1), (281, 1), (239, 1), (211, 1), (113, 1), (71, 1), (29, 1)] 0 0
      )
      (
      .ord 7 4733 <|
      .branch 70001
        (
        .spec 2 3 <|
        .expo 3 2 2 <|
        .spec 3 13 <|
        .expo 13 3 1 <|
        .spec 9 19 <|
        .expo 19 9 1 <|
        .spec 9 37 <|
        .expo 37 9 1 <|
        .ord 37 71 <|
        .spec 78 79 <|
        .expo 79 78 1 <|
        .spec 18 127 <|
        .ord 127 43 <|
        .spec 26 131 <|
        .expo 131 26 1 <|
        .spec 131 263 <|
        .ord 263 239 <|
        .ord 79 281 <|
        .overflow 7 [(4733, 1), (281, 1), (239, 1), (127, 1), (71, 1), (43, 1), (29, 1)] 0 0
        )
        (
        .ord 4733 70001 <|
        .ord 70001 50359 <|
        .ord 50359 71 <|
        .ord 71 883 <|
        .ord 883 379 <|
        .overflow 7 [(70001, 1), (50359, 1), (4733, 1), (883, 1), (379, 1), (71, 1), (29, 1)] 0 0
        )
      )
    )

/-- The tree for `l = 7` when `7` is the special prime. -/
def spec7 : Node :=
  .mod4

/-- The certificate for `l = 7` is accepted. -/
theorem check7 : checkAll 7 pc7 ord7 spec7 = true := by
  decide +kernel

/-- Pratt certificates for `l = 11`. -/
def pc11 : List (ℕ × ℕ × List ℕ) :=
  [(5479, 3, [2, 3, 11, 83]),
    (15797, 2, [2, 2, 11, 359]),
    (2347, 3, [2, 3, 17, 23]),
    (2530067, 5, [2, 7, 7, 11, 2347]),
    (52009301, 2, [2, 2, 5, 5, 7, 191, 389]),
    (211677855071, 7, [2, 5, 11, 37, 52009301]),
    (30187, 5, [2, 3, 3, 3, 13, 43]),
    (619256119, 3, [2, 3, 13, 263, 30187]),
    (3937230404603, 5, [2, 11, 17, 17, 619256119]),
    (149627, 2, [2, 79, 947]),
    (1197017, 3, [2, 2, 2, 149627]),
    (208280959, 3, [2, 3, 29, 1197017]),
    (781053596251, 3, [2, 3, 5, 5, 5, 5, 208280959]),
    (7810535962511, 7, [2, 5, 781053596251]),
    (1890149702927663, 5, [2, 11, 11, 7810535962511])]

/-- The tree for `l = 11` when `11` is ordinary. -/
def ord11 : Node :=
  .branch 15797
    (
    .spec 2 3 <|
    .expo 3 2 1 <|
    .spec 6 7 <|
    .expo 7 6 3 <|
    .spec 6 19 <|
    .expo 19 6 1 <|
    .ord 3 23 <|
    .spec 7 43 <|
    .expo 43 7 1 <|
    .spec 63 127 <|
    .expo 127 63 1 <|
    .spec 162 163 <|
    .expo 163 162 1 <|
    .spec 86 173 <|
    .expo 173 86 1 <|
    .spec 49 197 <|
    .spec 7 337 <|
    .spec 173 347 <|
    .ord 337 353 <|
    .ord 337 463 <|
    .spec 486 487 <|
    .spec 38 647 <|
    .overflow 23 [(647, 2), (487, 2), (463, 1), (353, 1), (347, 1), (197, 1), (173, 1), (163, 1), (127, 1)] 0 0
    )
    (
    .ord 11 15797 <|
    .ord 15797 463 <|
    .ord 463 23 <|
    .ord 463 5479 <|
    .ord 463 211677855071 <|
    .ord 211677855071 67 <|
    .ord 23 3937230404603 <|
    .ord 67 1890149702927663 <|
    .branch 89
      (
      .spec 2 3 <|
      .expo 3 2 2 <|
      .spec 2 5 <|
      .expo 5 2 1 <|
      .spec 6 7 <|
      .expo 7 6 1 <|
      .spec 10 31 <|
      .spec 35 71 <|
      .spec 9 73 <|
      .spec 42 127 <|
      .spec 5 131 <|
      .spec 150 151 <|
      .spec 162 163 <|
      .overflow 23 [(1890149702927663, 1), (211677855071, 1), (463, 1), (163, 1), (151, 1), (131, 1), (127, 1), (73, 1), (71, 1), (31, 1), (3, 1)] 0 0
      )
      (
      .ord 67 89 <|
      .ord 89 2530067 <|
      .branch 353
        (
        .spec 2 3 <|
        .expo 3 2 1 <|
        .spec 6 61 <|
        .ord 61 199 <|
        .overflow 11 [(1890149702927663, 1), (3937230404603, 1), (211677855071, 1), (2530067, 1), (15797, 1), (5479, 1), (463, 1), (199, 1), (89, 1), (67, 1), (23, 1)] 0 0
        )
        (
        .ord 211677855071 353 <|
        .overflow 11 [(1890149702927663, 1), (3937230404603, 1), (211677855071, 1), (2530067, 1), (15797, 1), (5479, 1), (463, 1), (353, 1), (89, 1), (67, 1), (23, 1)] 0 0
        )
      )
    )

/-- The tree for `l = 11` when `11` is the special prime. -/
def spec11 : Node :=
  .mod4

/-- The certificate for `l = 11` is accepted. -/
theorem check11 : checkAll 11 pc11 ord11 spec11 = true := by
  decide +kernel

/-- Pratt certificates for `l = 13`. -/
def pc13 : List (ℕ × ℕ × List ℕ) :=
  [(1093, 5, [2, 2, 3, 7, 13]),
    (1103, 5, [2, 19, 29]),
    (1667, 2, [2, 7, 7, 17]),
    (1741, 2, [2, 2, 3, 5, 29]),
    (1789, 6, [2, 2, 3, 149]),
    (1847, 5, [2, 13, 71]),
    (2939, 2, [2, 13, 113]),
    (7151, 7, [2, 5, 5, 11, 13]),
    (7723, 3, [2, 3, 3, 3, 11, 13]),
    (8867, 2, [2, 11, 13, 31]),
    (10141, 2, [2, 2, 3, 5, 13, 13]),
    (10271, 7, [2, 5, 13, 79]),
    (10739, 6, [2, 7, 13, 59]),
    (18617, 3, [2, 2, 2, 13, 179]),
    (1931, 2, [2, 5, 193]),
    (50207, 5, [2, 13, 1931]),
    (81953, 3, [2, 2, 2, 2, 2, 13, 197]),
    (82013, 11, [2, 2, 7, 29, 101]),
    (85853, 2, [2, 2, 13, 13, 127]),
    (134681, 3, [2, 2, 2, 5, 7, 13, 37]),
    (251057, 3, [2, 2, 2, 2, 13, 17, 71]),
    (264031, 12, [2, 3, 5, 13, 677]),
    (273997, 2, [2, 2, 3, 3, 3, 43, 59]),
    (284701, 2, [2, 2, 3, 5, 5, 13, 73]),
    (1013, 3, [2, 2, 11, 23]),
    (2027, 2, [2, 1013]),
    (316213, 5, [2, 2, 3, 13, 2027]),
    (1334737, 7, [2, 2, 2, 2, 3, 3, 13, 23, 31]),
    (1129, 11, [2, 2, 2, 3, 47]),
    (1379639, 7, [2, 13, 47, 1129]),
    (69371, 2, [2, 5, 7, 991]),
    (1803647, 5, [2, 13, 69371]),
    (6211, 2, [2, 3, 3, 3, 5, 23]),
    (2745263, 5, [2, 13, 17, 6211]),
    (1889, 3, [2, 2, 2, 2, 2, 59]),
    (3779, 2, [2, 1889]),
    (2751113, 3, [2, 2, 2, 7, 13, 3779]),
    (3297113, 3, [2, 2, 2, 7, 7, 13, 647]),
    (3821, 3, [2, 2, 5, 191]),
    (7643, 2, [2, 3821]),
    (4173079, 6, [2, 3, 7, 13, 7643]),
    (8346157, 19, [2, 2, 3, 7, 13, 7643]),
    (6113, 3, [2, 2, 2, 2, 2, 191]),
    (379007, 10, [2, 31, 6113]),
    (2128503313, 5, [2, 2, 2, 2, 3, 3, 3, 13, 379007]),
    (48817, 5, [2, 2, 2, 2, 3, 3, 3, 113]),
    (2497868257, 5, [2, 2, 2, 2, 2, 3, 13, 41, 48817]),
    (14081, 3, [2, 2, 2, 2, 2, 2, 2, 2, 5, 11]),
    (53226181, 18, [2, 2, 3, 3, 3, 5, 7, 14081]),
    (2767761413, 3, [2, 2, 13, 53226181]),
    (29251, 2, [2, 3, 3, 5, 5, 5, 13]),
    (877531, 2, [2, 3, 5, 29251]),
    (877531001, 3, [2, 2, 2, 5, 5, 5, 877531]),
    (1755062003, 2, [2, 877531001]),
    (11681692691969, 3, [2, 2, 2, 2, 2, 2, 2, 2, 2, 13, 1755062003]),
    (20021, 3, [2, 2, 5, 7, 11, 13]),
    (1523, 2, [2, 761]),
    (94427, 2, [2, 31, 1523]),
    (29569, 17, [2, 2, 2, 2, 2, 2, 2, 3, 7, 11]),
    (354829, 2, [2, 2, 3, 29569]),
    (1888399939, 2, [2, 3, 887, 354829]),
    (56651998171, 2, [2, 3, 5, 1888399939]),
    (25061845458479893445539, 10, [2, 3, 3, 13, 20021, 94427, 56651998171])]

/-- The tree for `l = 13` when `13` is ordinary. -/
def ord13 : Node :=
  .ord 13 264031 <|
  .ord 13 1803647 <|
  .ord 1803647 131 <|
  .ord 131 79 <|
  .ord 131 25061845458479893445539 <|
  .branch 53
    (
    .spec 2 3 <|
    .expo 3 2 3 <|
    .spec 3 7 <|
    .expo 7 3 1 <|
    .spec 18 19 <|
    .expo 19 18 1 <|
    .spec 7 29 <|
    .expo 29 7 1 <|
    .spec 9 37 <|
    .expo 37 9 1 <|
    .spec 21 43 <|
    .expo 43 21 1 <|
    .spec 29 59 <|
    .expo 59 29 2 <|
    .spec 126 127 <|
    .expo 127 126 1 <|
    .spec 74 149 <|
    .expo 149 74 1 <|
    .spec 9 163 <|
    .expo 163 9 1 <|
    .spec 49 197 <|
    .expo 197 49 1 <|
    .spec 111 223 <|
    .expo 223 111 1 <|
    .spec 19 229 <|
    .expo 229 19 1 <|
    .spec 9 307 <|
    .expo 307 9 1 <|
    .spec 378 379 <|
    .expo 379 378 1 <|
    .spec 3 409 <|
    .expo 409 3 1 <|
    .spec 243 487 <|
    .expo 487 243 1 <|
    .ord 487 157 <|
    .spec 98 491 <|
    .expo 491 98 1 <|
    .ord 29 521 <|
    .ord 19 599 <|
    .spec 326 653 <|
    .ord 653 313 <|
    .ord 491 911 <|
    .ord 911 937 <|
    .spec 491 983 <|
    .ord 983 859 <|
    .spec 551 1103 <|
    .ord 1103 677 <|
    .overflow 13 [(25061845458479893445539, 1), (1803647, 1), (264031, 1), (937, 1), (911, 1), (859, 1), (677, 1), (599, 1), (521, 1), (313, 1), (157, 1), (131, 1), (79, 1)] 0 0
    )
    (
    .ord 13 53 <|
    .branch 3297113
      (
      .spec 2 3 <|
      .expo 3 2 2 <|
      .spec 9 19 <|
      .expo 19 9 1 <|
      .spec 27 109 <|
      .expo 109 27 1 <|
      .spec 2 113 <|
      .expo 113 2 1 <|
      .spec 226 227 <|
      .spec 54 271 <|
      .ord 113 313 <|
      .spec 486 487 <|
      .ord 487 157 <|
      .ord 19 599 <|
      .spec 18 631 <|
      .ord 631 443 <|
      .spec 6 823 <|
      .ord 823 521 <|
      .ord 227 937 <|
      .ord 271 1093 <|
      .overflow 13 [(25061845458479893445539, 1), (1803647, 1), (264031, 1), (1093, 1), (937, 1), (599, 1), (521, 1), (443, 1), (313, 1), (157, 1), (131, 1), (79, 1), (53, 1)] 0 0
      )
      (
      .ord 53 3297113 <|
      .branch 8346157
        (
        .spec 2 4173079 <|
        .ord 53 11681692691969 <|
        .ord 11681692691969 18617 <|
        .ord 18617 313 <|
        .ord 18617 50207 <|
        .ord 50207 10271 <|
        .overflow 13 [(25061845458479893445539, 1), (11681692691969, 1), (4173079, 1), (3297113, 1), (1803647, 1), (264031, 1), (50207, 1), (18617, 1), (10271, 1), (313, 1), (131, 1), (79, 1), (53, 1)] 0 0
        )
        (
        .ord 79 8346157 <|
        .branch 2128503313
          (
          .spec 2 7 <|
          .expo 7 2 1 <|
          .spec 2 29 <|
          .expo 29 2 1 <|
          .spec 14 43 <|
          .expo 43 14 1 <|
          .spec 29 59 <|
          .expo 59 29 1 <|
          .spec 7 281 <|
          .expo 281 7 1 <|
          .spec 29 349 <|
          .expo 349 29 1 <|
          .spec 49 491 <|
          .expo 491 49 1 <|
          .ord 29 521 <|
          .ord 491 911 <|
          .ord 911 937 <|
          .ord 937 599 <|
          .spec 982 983 <|
          .ord 983 313 <|
          .overflow 13 [(25061845458479893445539, 1), (8346157, 1), (3297113, 1), (1803647, 1), (264031, 1), (937, 1), (911, 1), (599, 1), (521, 1), (313, 1), (131, 1), (79, 1), (53, 1)] 0 0
          )
          (
          .ord 8346157 2128503313 <|
          .branch 2497868257
            (
            .spec 2 127 <|
            .expo 127 2 1 <|
            .spec 127 509 <|
            .ord 509 547 <|
            .ord 547 313 <|
            .ord 509 1847 <|
            .ord 1847 521 <|
            .overflow 13 [(25061845458479893445539, 1), (2128503313, 1), (8346157, 1), (3297113, 1), (1803647, 1), (264031, 1), (1847, 1), (547, 1), (521, 1), (313, 1), (131, 1), (79, 1), (53, 1)] 0 0
            )
            (
            .ord 8346157 2497868257 <|
            .branch 2767761413
              (
              .spec 2 3 <|
              .expo 3 2 4 <|
              .spec 3 7 <|
              .expo 7 3 1 <|
              .spec 2 11 <|
              .expo 11 2 1 <|
              .spec 9 19 <|
              .spec 33 67 <|
              .ord 67 157 <|
              .spec 462 463 <|
              .ord 463 313 <|
              .ord 19 599 <|
              .overflow 13 [(25061845458479893445539, 1), (2497868257, 1), (2128503313, 1), (8346157, 1), (3297113, 1), (1803647, 1), (264031, 1), (599, 1), (313, 1), (157, 1), (131, 1), (79, 1), (53, 1)] 0 0
              )
              (
              .ord 8346157 2767761413 <|
              .ord 2767761413 2939 <|
              .branch 1334737
                (
                .spec 2 17 <|
                .expo 17 2 1 <|
                .spec 2 37 <|
                .expo 37 2 1 <|
                .spec 74 149 <|
                .expo 149 74 1 <|
                .spec 149 1789 <|
                .ord 1789 521 <|
                .overflow 13 [(25061845458479893445539, 1), (2767761413, 1), (2497868257, 1), (2128503313, 1), (8346157, 1), (3297113, 1), (1803647, 1), (264031, 1), (2939, 1), (521, 1), (131, 1), (79, 1), (53, 1)] 0 0
                )
                (
                .ord 2767761413 1334737 <|
                .overflow 13 [(25061845458479893445539, 1), (2767761413, 1), (2497868257, 1), (2128503313, 1), (8346157, 1), (3297113, 1), (1803647, 1), (1334737, 1), (264031, 1), (2939, 1), (131, 1), (79, 1), (53, 1)] 0 0
                )
              )
            )
          )
        )
      )
    )

/-- The tree for `l = 13` when `13` is the special prime. -/
def spec13 : Node :=
  .spec 2 7 <|
  .expo 7 2 1 <|
  .spec 14 29 <|
  .expo 29 14 1 <|
  .spec 58 59 <|
  .expo 59 58 1 <|
  .ord 29 521 <|
  .ord 521 53 <|
  .spec 49 1667 <|
  .spec 58 1741 <|
  .ord 1741 157 <|
  .spec 413 10739 <|
  .ord 10739 8867 <|
  .ord 8867 7723 <|
  .ord 7723 937 <|
  .ord 937 599 <|
  .ord 599 10141 <|
  .ord 10141 7151 <|
  .spec 203 82013 <|
  .ord 157 251057 <|
  .spec 59 273997 <|
  .ord 273997 81953 <|
  .ord 273997 134681 <|
  .ord 134681 85853 <|
  .ord 251057 284701 <|
  .ord 284701 316213 <|
  .ord 85853 2745263 <|
  .ord 2745263 1379639 <|
  .ord 82013 2751113 <|
  .overflow 53 [(521, 2), (2751113, 1), (1379639, 1), (316213, 1), (251057, 1), (85853, 1), (81953, 1), (8867, 1), (7151, 1), (1667, 1), (937, 1), (599, 1)] 0 0

/-- The certificate for `l = 13` is accepted. -/
theorem check13 : checkAll 13 pc13 ord13 spec13 = true := by
  decide +kernel

/-- Pratt certificates for `l = 17`. -/
def pc17 : List (ℕ × ℕ × List ℕ) :=
  [(1021, 10, [2, 2, 3, 5, 17]),
    (1123, 2, [2, 3, 11, 17]),
    (1249, 7, [2, 2, 2, 2, 2, 3, 13]),
    (1361, 3, [2, 2, 2, 2, 5, 17]),
    (1373, 2, [2, 2, 7, 7, 7]),
    (1531, 2, [2, 3, 3, 5, 17]),
    (1559, 19, [2, 19, 41]),
    (1667, 2, [2, 7, 7, 17]),
    (1871, 14, [2, 5, 11, 17]),
    (2687, 5, [2, 17, 79]),
    (2789, 2, [2, 2, 17, 41]),
    (3163, 3, [2, 3, 17, 31]),
    (3299, 2, [2, 17, 97]),
    (3499, 2, [2, 3, 11, 53]),
    (3571, 2, [2, 3, 5, 7, 17]),
    (3613, 2, [2, 2, 3, 7, 43]),
    (4421, 3, [2, 2, 5, 13, 17]),
    (4871, 11, [2, 5, 487]),
    (5849, 3, [2, 2, 2, 17, 43]),
    (8171, 2, [2, 5, 19, 43]),
    (10949, 2, [2, 2, 7, 17, 23]),
    (11969, 3, [2, 2, 2, 2, 2, 2, 11, 17]),
    (21149, 3, [2, 2, 17, 311]),
    (23563, 2, [2, 3, 3, 7, 11, 17]),
    (24379, 2, [2, 3, 17, 239]),
    (34511, 7, [2, 5, 7, 17, 29]),
    (61031, 22, [2, 5, 17, 359]),
    (109481, 3, [2, 2, 2, 5, 7, 17, 23]),
    (124679, 7, [2, 17, 19, 193]),
    (149873, 5, [2, 2, 2, 2, 17, 19, 29]),
    (2803, 2, [2, 3, 467]),
    (11213, 2, [2, 2, 2803]),
    (291539, 2, [2, 13, 11213]),
    (600203, 2, [2, 17, 127, 139]),
    (652699, 2, [2, 3, 3, 3, 3, 3, 17, 79]),
    (1749233, 3, [2, 2, 2, 2, 17, 59, 109]),
    (3295723, 2, [2, 3, 17, 79, 409]),
    (15052447, 3, [2, 3, 3, 3, 17, 19, 863]),
    (1113401, 3, [2, 2, 2, 5, 5, 19, 293]),
    (643545779, 2, [2, 17, 17, 1113401]),
    (1061, 2, [2, 2, 5, 53]),
    (7957501, 6, [2, 2, 3, 5, 5, 5, 5, 1061]),
    (2434995307, 5, [2, 3, 3, 17, 7957501]),
    (101113, 5, [2, 2, 2, 3, 11, 383]),
    (6607, 3, [2, 3, 3, 367]),
    (74830883, 2, [2, 7, 809, 6607]),
    (2371, 2, [2, 3, 5, 79]),
    (279779, 2, [2, 59, 2371]),
    (2238233, 3, [2, 2, 2, 279779]),
    (13429399, 3, [2, 3, 2238233]),
    (966916729, 19, [2, 2, 2, 3, 3, 13429399]),
    (2364223, 5, [2, 3, 7, 181, 311]),
    (1081518539797, 2, [2, 2, 3, 3, 97, 131, 2364223]),
    (129782224775641, 17, [2, 2, 2, 3, 5, 1081518539797]),
    (144852882342494444412106185630639022235099, 2, [2, 7, 17, 641, 101113, 74830883, 966916729, 129782224775641]),
    (21191, 7, [2, 5, 13, 163]),
    (1652899, 2, [2, 3, 13, 21191]),
    (59771, 2, [2, 5, 43, 139]),
    (266711, 11, [2, 5, 149, 179]),
    (1151, 17, [2, 5, 5, 23]),
    (45828217, 5, [2, 2, 2, 3, 3, 7, 79, 1151]),
    (2922297333369673109, 2, [2, 2, 59771, 266711, 45828217]),
    (1908417962746398502524887, 5, [2, 347, 941, 2922297333369673109]),
    (1075025976747056254689393855413435837368711, 3, [2, 3, 5, 17, 19, 23, 29, 67, 787, 1652899, 1908417962746398502524887])]

/-- The tree for `l = 17` when `17` is ordinary. -/
def ord17 : Node :=
  .branch 10949
    (
    .spec 2 3 <|
    .spec 2 5 <|
    .spec 2 73 <|
    .ord 73 137 <|
    .ord 137 103 <|
    .ord 5 409 <|
    .ord 409 307 <|
    .ord 409 443 <|
    .ord 443 953 <|
    .ord 953 647 <|
    .ord 3 1871 <|
    .ord 443 2687 <|
    .ord 2687 919 <|
    .ord 2687 1531 <|
    .ord 2687 2789 <|
    .ord 409 3163 <|
    .ord 919 4421 <|
    .ord 953 5849 <|
    .ord 5849 1361 <|
    .ord 1361 239 <|
    .overflow 17 [(5849, 1), (4421, 1), (3163, 1), (2789, 1), (2687, 1), (1871, 1), (1531, 1), (1361, 1), (953, 1), (919, 1), (647, 1), (443, 1), (409, 1), (307, 1), (239, 1), (137, 1), (103, 1)] 0 0
    )
    (
    .ord 17 10949 <|
    .branch 1749233
      (
      .spec 2 3 <|
      .ord 3 1871 <|
      .ord 1871 24379 <|
      .ord 24379 11969 <|
      .ord 11969 137 <|
      .ord 137 103 <|
      .ord 3 34511 <|
      .spec 2 291539 <|
      .ord 291539 23563 <|
      .ord 23563 124679 <|
      .ord 124679 1123 <|
      .ord 1123 1667 <|
      .ord 1667 600203 <|
      .ord 600203 1021 <|
      .ord 600203 109481 <|
      .ord 109481 61031 <|
      .ord 1871 15052447 <|
      .ord 15052447 149873 <|
      .overflow 17 [(15052447, 1), (600203, 1), (149873, 1), (124679, 1), (109481, 1), (61031, 1), (34511, 1), (24379, 1), (23563, 1), (11969, 1), (10949, 1), (1871, 1), (1667, 1), (1123, 1), (1021, 1), (137, 1), (103, 1)] 0 0
      )
      (
      .ord 17 1749233 <|
      .ord 1749233 652699 <|
      .branch 21149
        (
        .spec 2 3 <|
        .spec 2 5 <|
        .spec 2 47 <|
        .ord 5 409 <|
        .ord 409 103 <|
        .ord 409 307 <|
        .ord 409 443 <|
        .ord 443 953 <|
        .ord 953 647 <|
        .ord 3 1871 <|
        .ord 443 2687 <|
        .ord 2687 919 <|
        .ord 2687 1531 <|
        .ord 2687 2789 <|
        .ord 409 3163 <|
        .ord 47 3571 <|
        .ord 919 4421 <|
        .overflow 17 [(1749233, 1), (652699, 1), (10949, 1), (4421, 1), (3571, 1), (3163, 1), (2789, 1), (2687, 1), (1871, 1), (1531, 1), (953, 1), (919, 1), (647, 1), (443, 1), (409, 1), (307, 1), (103, 1)] 0 0
        )
        (
        .ord 652699 21149 <|
        .ord 21149 103 <|
        .ord 21149 307 <|
        .ord 21149 647 <|
        .ord 21149 3299 <|
        .ord 3299 2687 <|
        .ord 2687 919 <|
        .ord 2687 1531 <|
        .ord 647 3295723 <|
        .ord 3299 643545779 <|
        .ord 21149 2434995307 <|
        .ord 2434995307 239 <|
        .ord 21149 144852882342494444412106185630639022235099 <|
        .ord 2687 1075025976747056254689393855413435837368711 <|
        .overflow 17 [(1075025976747056254689393855413435837368711, 1), (144852882342494444412106185630639022235099, 1), (2434995307, 1), (643545779, 1), (3295723, 1), (1749233, 1), (652699, 1), (21149, 1), (10949, 1), (3299, 1), (2687, 1), (1531, 1), (919, 1), (647, 1), (307, 1), (239, 1), (103, 1)] 0 0
        )
      )
    )

/-- The tree for `l = 17` when `17` is the special prime. -/
def spec17 : Node :=
  .spec 2 3 <|
  .expo 3 2 2 <|
  .spec 6 7 <|
  .expo 7 6 1 <|
  .spec 6 13 <|
  .expo 13 6 1 <|
  .spec 9 19 <|
  .expo 19 9 1 <|
  .spec 21 43 <|
  .expo 43 21 1 <|
  .spec 26 53 <|
  .expo 53 26 1 <|
  .spec 26 79 <|
  .expo 79 26 1 <|
  .ord 13 103 <|
  .spec 106 107 <|
  .expo 107 106 1 <|
  .spec 63 127 <|
  .expo 127 63 1 <|
  .spec 39 157 <|
  .expo 157 39 1 <|
  .spec 54 163 <|
  .expo 163 54 1 <|
  .spec 19 229 <|
  .expo 229 19 1 <|
  .spec 378 379 <|
  .expo 379 378 1 <|
  .spec 27 433 <|
  .expo 433 27 1 <|
  .ord 13 443 <|
  .spec 38 457 <|
  .expo 457 38 1 <|
  .spec 486 487 <|
  .expo 487 486 1 <|
  .spec 49 491 <|
  .ord 491 409 <|
  .spec 189 757 <|
  .ord 757 137 <|
  .ord 443 953 <|
  .ord 487 1123 <|
  .spec 78 1249 <|
  .spec 686 1373 <|
  .spec 38 1559 <|
  .ord 443 2687 <|
  .ord 2687 2789 <|
  .spec 318 3499 <|
  .spec 903 3613 <|
  .spec 487 4871 <|
  .ord 953 5849 <|
  .spec 86 8171 <|
  .overflow 103 [(8171, 1), (5849, 1), (4871, 1), (3613, 1), (3499, 1), (2789, 1), (2687, 1), (1559, 1), (1373, 1), (1249, 1), (1123, 1), (491, 1), (409, 1), (229, 1), (137, 1), (79, 1), (13, 1)] 0 0

/-- The certificate for `l = 17` is accepted. -/
theorem check17 : checkAll 17 pc17 ord17 spec17 = true := by
  decide +kernel

/-- Pratt certificates for `l = 19`. -/
def pc19 : List (ℕ × ℕ × List ℕ) :=
  [(1103, 5, [2, 19, 29]),
    (1217, 3, [2, 2, 2, 2, 2, 2, 19]),
    (1483, 2, [2, 3, 13, 19]),
    (1559, 19, [2, 19, 41]),
    (1597, 11, [2, 2, 3, 7, 19]),
    (1787, 2, [2, 19, 47]),
    (1901, 2, [2, 2, 5, 5, 19]),
    (2129, 3, [2, 2, 2, 2, 7, 19]),
    (2281, 7, [2, 2, 2, 3, 5, 19]),
    (3041, 3, [2, 2, 2, 2, 2, 5, 19]),
    (4219, 2, [2, 3, 19, 37]),
    (4409, 3, [2, 2, 2, 19, 29]),
    (4637, 2, [2, 2, 19, 61]),
    (6271, 11, [2, 3, 5, 11, 19]),
    (7069, 2, [2, 2, 3, 19, 31]),
    (9463, 3, [2, 3, 19, 83]),
    (15467, 5, [2, 11, 19, 37]),
    (20939, 2, [2, 19, 19, 29]),
    (22573, 6, [2, 2, 3, 3, 3, 11, 19]),
    (23599, 3, [2, 3, 3, 3, 19, 23]),
    (37963, 2, [2, 3, 3, 3, 19, 37]),
    (40357, 5, [2, 2, 3, 3, 19, 59]),
    (1307, 2, [2, 653]),
    (49667, 2, [2, 19, 1307]),
    (54493, 2, [2, 2, 3, 19, 239]),
    (73303, 5, [2, 3, 19, 643]),
    (77711, 14, [2, 5, 19, 409]),
    (93329, 3, [2, 2, 2, 2, 19, 307]),
    (96331, 10, [2, 3, 5, 13, 13, 19]),
    (96749, 2, [2, 2, 19, 19, 67]),
    (99371, 2, [2, 5, 19, 523]),
    (8663, 5, [2, 61, 71]),
    (17327, 5, [2, 8663]),
    (103963, 2, [2, 3, 17327]),
    (3191, 11, [2, 5, 11, 29]),
    (121259, 2, [2, 19, 3191]),
    (124717, 5, [2, 2, 3, 19, 547]),
    (136193, 3, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 19]),
    (172331, 2, [2, 5, 19, 907]),
    (183503, 5, [2, 11, 19, 439]),
    (3217, 5, [2, 2, 2, 2, 3, 67]),
    (244493, 2, [2, 2, 19, 3217]),
    (251941, 6, [2, 2, 3, 5, 13, 17, 19]),
    (365257, 5, [2, 2, 2, 3, 3, 3, 19, 89]),
    (2767, 3, [2, 3, 461]),
    (525731, 10, [2, 5, 19, 2767]),
    (562021, 18, [2, 2, 3, 5, 17, 19, 29]),
    (1951, 3, [2, 3, 5, 5, 13]),
    (667243, 2, [2, 3, 3, 19, 1951]),
    (753617, 3, [2, 2, 2, 2, 19, 37, 67]),
    (2801, 3, [2, 2, 2, 2, 5, 5, 7]),
    (756271, 23, [2, 3, 3, 3, 5, 2801]),
    (8527, 5, [2, 3, 7, 7, 29]),
    (972079, 3, [2, 3, 19, 8527]),
    (1124041, 31, [2, 2, 2, 3, 5, 17, 19, 29]),
    (2683, 2, [2, 3, 3, 149]),
    (1223449, 7, [2, 2, 2, 3, 19, 2683]),
    (2502719, 7, [2, 19, 67, 983]),
    (1013, 3, [2, 2, 11, 23]),
    (2027, 2, [2, 1013]),
    (2849963, 2, [2, 19, 37, 2027]),
    (3262949, 2, [2, 2, 13, 131, 479]),
    (3981071, 17, [2, 5, 19, 23, 911]),
    (4642423, 3, [2, 3, 19, 193, 211]),
    (17681, 3, [2, 2, 2, 2, 5, 13, 17]),
    (35363, 2, [2, 17681]),
    (5375177, 3, [2, 2, 2, 19, 35363]),
    (10825013, 2, [2, 2, 11, 347, 709]),
    (1721, 3, [2, 2, 2, 5, 43]),
    (13995173, 2, [2, 2, 19, 107, 1721]),
    (24151, 6, [2, 3, 5, 5, 7, 23]),
    (18354761, 3, [2, 2, 2, 5, 19, 24151]),
    (14797, 2, [2, 2, 3, 3, 3, 137]),
    (20242297, 10, [2, 2, 2, 3, 3, 19, 14797]),
    (4099, 2, [2, 3, 683]),
    (21962443, 3, [2, 3, 19, 47, 4099]),
    (34570387, 2, [2, 3, 3, 19, 271, 373]),
    (47564981, 2, [2, 2, 5, 17, 19, 37, 199]),
    (2399, 11, [2, 11, 109]),
    (682621057, 10, [2, 2, 2, 2, 2, 2, 2, 3, 3, 13, 19, 2399]),
    (1033, 5, [2, 2, 2, 3, 43]),
    (4133, 2, [2, 2, 1033]),
    (827360473, 5, [2, 2, 2, 3, 19, 439, 4133]),
    (207497, 3, [2, 2, 2, 37, 701]),
    (1277351533, 2, [2, 2, 3, 3, 3, 3, 19, 207497]),
    (29989, 2, [2, 2, 3, 3, 7, 7, 17]),
    (236377, 10, [2, 2, 2, 3, 3, 7, 7, 67]),
    (109912203092239643840221, 10, [2, 2, 3, 3, 5, 7, 7, 7, 19, 127, 199, 523, 29989, 236377]),
    (22193, 3, [2, 2, 2, 2, 19, 73]),
    (11629133, 2, [2, 2, 131, 22193]),
    (3325629680543, 5, [2, 13, 17, 647, 11629133]),
    (3701, 2, [2, 2, 5, 5, 37]),
    (3005213, 2, [2, 2, 7, 29, 3701]),
    (51064579297, 5, [2, 2, 2, 2, 2, 3, 3, 59, 3005213]),
    (11234207445341, 2, [2, 2, 5, 11, 51064579297]),
    (4740414766116926933918204081767, 3, [2, 3, 3, 7, 19, 53, 3325629680543, 11234207445341])]

/-- The tree for `l = 19` when `19` is ordinary. -/
def ord19 : Node :=
  .branch 109912203092239643840221
    (
    .spec 2 3262949 <|
    .ord 3262949 365257 <|
    .ord 365257 457 <|
    .ord 365257 99371 <|
    .ord 99371 229 <|
    .ord 229 1103 <|
    .ord 1103 9463 <|
    .ord 9463 2129 <|
    .ord 229 23599 <|
    .ord 23599 419 <|
    .ord 23599 4637 <|
    .ord 419 22573 <|
    .ord 9463 49667 <|
    .ord 229 54493 <|
    .ord 54493 3041 <|
    .ord 2129 77711 <|
    .ord 77711 571 <|
    .ord 54493 244493 <|
    .ord 419 251941 <|
    .ord 251941 4409 <|
    .overflow 19 [(365257, 1), (251941, 1), (244493, 1), (99371, 1), (77711, 1), (54493, 1), (49667, 1), (23599, 1), (22573, 1), (9463, 1), (4637, 1), (4409, 1), (3041, 1), (2129, 1), (1103, 1), (571, 1), (457, 1), (419, 1), (229, 1)] 0 0
    )
    (
    .ord 19 109912203092239643840221 <|
    .branch 682621057
      (
      .spec 2 7 <|
      .ord 7 419 <|
      .ord 419 22573 <|
      .spec 2 103963 <|
      .ord 419 251941 <|
      .ord 251941 4409 <|
      .ord 251941 37963 <|
      .ord 37963 647 <|
      .ord 103963 2502719 <|
      .ord 22573 5375177 <|
      .ord 5375177 1217 <|
      .ord 1217 15467 <|
      .ord 15467 172331 <|
      .ord 172331 457 <|
      .ord 5375177 525731 <|
      .ord 15467 20242297 <|
      .ord 2502719 21962443 <|
      .ord 103963 34570387 <|
      .ord 34570387 1223449 <|
      .ord 457 47564981 <|
      .overflow 19 [(109912203092239643840221, 1), (47564981, 1), (34570387, 1), (21962443, 1), (20242297, 1), (5375177, 1), (2502719, 1), (1223449, 1), (525731, 1), (251941, 1), (172331, 1), (37963, 1), (22573, 1), (15467, 1), (4409, 1), (1217, 1), (647, 1), (457, 1), (419, 1)] 0 0
      )
      (
      .ord 109912203092239643840221 682621057 <|
      .branch 1124041
        (
        .spec 2 562021 <|
        .ord 562021 1559 <|
        .ord 1559 40357 <|
        .ord 40357 229 <|
        .ord 229 1103 <|
        .ord 1103 9463 <|
        .ord 9463 2129 <|
        .ord 229 23599 <|
        .ord 23599 419 <|
        .ord 23599 4637 <|
        .ord 419 22573 <|
        .ord 9463 49667 <|
        .ord 229 54493 <|
        .ord 54493 3041 <|
        .ord 2129 77711 <|
        .ord 77711 571 <|
        .ord 571 457 <|
        .overflow 19 [(109912203092239643840221, 1), (682621057, 1), (562021, 1), (77711, 1), (54493, 1), (49667, 1), (40357, 1), (23599, 1), (22573, 1), (9463, 1), (4637, 1), (3041, 1), (2129, 1), (1559, 1), (1103, 1), (571, 1), (457, 1), (419, 1), (229, 1)] 0 0
        )
        (
        .ord 682621057 1124041 <|
        .ord 1124041 191 <|
        .ord 191 4740414766116926933918204081767 <|
        .branch 7069
          (
          .spec 2 5 <|
          .spec 2 7 <|
          .ord 7 419 <|
          .ord 5 6271 <|
          .ord 419 22573 <|
          .ord 419 251941 <|
          .ord 251941 4409 <|
          .ord 251941 37963 <|
          .ord 37963 647 <|
          .ord 5 3981071 <|
          .ord 3981071 571 <|
          .ord 571 457 <|
          .ord 3981071 1901 <|
          .ord 3981071 121259 <|
          .ord 3981071 124717 <|
          .ord 1901 2849963 <|
          .overflow 19 [(4740414766116926933918204081767, 1), (109912203092239643840221, 1), (682621057, 1), (3981071, 1), (2849963, 1), (1124041, 1), (251941, 1), (124717, 1), (121259, 1), (37963, 1), (22573, 1), (6271, 1), (4409, 1), (1901, 1), (647, 1), (571, 1), (457, 1), (419, 1), (191, 1)] 0 0
          )
          (
          .ord 1124041 7069 <|
          .branch 827360473
            (
            .spec 2 756271 <|
            .ord 756271 457 <|
            .ord 756271 96749 <|
            .ord 96749 419 <|
            .ord 419 22573 <|
            .ord 419 251941 <|
            .ord 251941 4409 <|
            .ord 251941 37963 <|
            .ord 37963 647 <|
            .ord 756271 753617 <|
            .ord 753617 136193 <|
            .ord 136193 73303 <|
            .ord 73303 1787 <|
            .ord 73303 1901 <|
            .overflow 19 [(4740414766116926933918204081767, 1), (109912203092239643840221, 1), (682621057, 1), (1124041, 1), (753617, 1), (251941, 1), (136193, 1), (96749, 1), (73303, 1), (37963, 1), (22573, 1), (7069, 1), (4409, 1), (1901, 1), (1787, 1), (647, 1), (457, 1), (419, 1), (191, 1)] 0 0
            )
            (
            .ord 7069 827360473 <|
            .branch 1277351533
              (
              .spec 2 59 <|
              .ord 59 571 <|
              .ord 571 457 <|
              .ord 59 183503 <|
              .spec 2 10825013 <|
              .ord 10825013 647 <|
              .ord 10825013 13995173 <|
              .ord 13995173 18354761 <|
              .ord 18354761 419 <|
              .ord 18354761 20939 <|
              .ord 419 22573 <|
              .ord 18354761 93329 <|
              .ord 93329 1103 <|
              .ord 1103 9463 <|
              .overflow 19 [(4740414766116926933918204081767, 1), (109912203092239643840221, 1), (827360473, 1), (682621057, 1), (18354761, 1), (13995173, 1), (1124041, 1), (183503, 1), (93329, 1), (22573, 1), (20939, 1), (9463, 1), (7069, 1), (1103, 1), (647, 1), (571, 1), (457, 1), (419, 1), (191, 1)] 0 0
              )
              (
              .ord 191 1277351533 <|
              .ord 1277351533 667243 <|
              .branch 2129
                (
                .spec 2 3 <|
                .spec 2 5 <|
                .ord 3 1597 <|
                .ord 1597 1103 <|
                .ord 1597 2281 <|
                .ord 2281 457 <|
                .ord 1597 4219 <|
                .ord 5 6271 <|
                .ord 1103 9463 <|
                .ord 2281 15467 <|
                .ord 9463 49667 <|
                .ord 49667 229 <|
                .overflow 19 [(4740414766116926933918204081767, 1), (109912203092239643840221, 1), (1277351533, 1), (827360473, 1), (682621057, 1), (1124041, 1), (667243, 1), (49667, 1), (15467, 1), (9463, 1), (7069, 1), (6271, 1), (4219, 1), (2281, 1), (1597, 1), (1103, 1), (457, 1), (229, 1), (191, 1)] 0 0
                )
                (
                .ord 1277351533 2129 <|
                .ord 2129 77711 <|
                .ord 77711 571 <|
                .ord 77711 1103 <|
                .ord 1103 9463 <|
                .ord 9463 49667 <|
                .ord 49667 972079 <|
                .ord 2129 4642423 <|
                .ord 4642423 1483 <|
                .ord 4642423 96331 <|
                .overflow 19 [(4740414766116926933918204081767, 1), (109912203092239643840221, 1), (1277351533, 1), (827360473, 1), (682621057, 1), (4642423, 1), (1124041, 1), (972079, 1), (667243, 1), (96331, 1), (77711, 1), (49667, 1), (9463, 1), (7069, 1), (2129, 1), (1483, 1), (1103, 1), (571, 1), (191, 1)] 0 0
                )
              )
            )
          )
        )
      )
    )

/-- The tree for `l = 19` when `19` is the special prime. -/
def spec19 : Node :=
  .mod4

/-- The certificate for `l = 19` is accepted. -/
theorem check19 : checkAll 19 pc19 ord19 spec19 = true := by
  decide +kernel

/-- Pratt certificates for `l = 23`. -/
def pc23 : List (ℕ × ℕ × List ℕ) :=
  [(1013, 3, [2, 2, 11, 23]),
    (1289, 6, [2, 2, 2, 7, 23]),
    (1381, 2, [2, 2, 3, 5, 23]),
    (1459, 3, [2, 3, 3, 3, 3, 3, 3]),
    (1493, 2, [2, 2, 373]),
    (1933, 5, [2, 2, 3, 7, 23]),
    (1999, 3, [2, 3, 3, 3, 37]),
    (2311, 3, [2, 3, 5, 7, 11]),
    (2609, 3, [2, 2, 2, 2, 163]),
    (2917, 5, [2, 2, 3, 3, 3, 3, 3, 3]),
    (3083, 2, [2, 23, 67]),
    (19919, 7, [2, 23, 433]),
    (28751, 14, [2, 5, 5, 5, 5, 23]),
    (37123, 3, [2, 3, 23, 269]),
    (44851, 10, [2, 3, 5, 5, 13, 23]),
    (77419, 2, [2, 3, 3, 11, 17, 23]),
    (133723, 2, [2, 3, 3, 17, 19, 23]),
    (224251, 10, [2, 3, 5, 5, 5, 13, 23]),
    (226367, 5, [2, 7, 19, 23, 37]),
    (964207, 3, [2, 3, 3, 17, 23, 137]),
    (2258831, 17, [2, 5, 7, 23, 23, 61]),
    (3581, 2, [2, 2, 5, 179]),
    (21487, 3, [2, 3, 3581]),
    (12849227, 2, [2, 13, 23, 21487]),
    (28076239, 3, [2, 3, 3, 23, 73, 929]),
    (1091, 2, [2, 5, 109]),
    (45920191, 3, [2, 3, 5, 23, 61, 1091]),
    (418321, 11, [2, 2, 2, 2, 3, 3, 5, 7, 83]),
    (519554683, 2, [2, 3, 3, 3, 23, 418321]),
    (3797, 2, [2, 2, 13, 73]),
    (1511207, 5, [2, 199, 3797]),
    (625639699, 2, [2, 3, 3, 23, 1511207]),
    (145681, 11, [2, 2, 2, 2, 3, 5, 607]),
    (1789254043, 2, [2, 3, 23, 89, 145681]),
    (185711, 7, [2, 5, 7, 7, 379]),
    (72427291, 12, [2, 3, 5, 13, 185711]),
    (9994966159, 3, [2, 3, 23, 72427291])]

/-- The tree for `l = 23` when `23` is ordinary. -/
def ord23 : Node :=
  .branch 461
    (
    .spec 2 3 <|
    .expo 3 2 1 <|
    .spec 2 7 <|
    .expo 7 2 1 <|
    .spec 2 11 <|
    .expo 11 2 1 <|
    .spec 9 19 <|
    .expo 19 9 1 <|
    .spec 21 43 <|
    .expo 43 21 1 <|
    .ord 3 47 <|
    .spec 11 67 <|
    .expo 67 11 1 <|
    .spec 11 89 <|
    .expo 89 11 1 <|
    .spec 27 109 <|
    .expo 109 27 1 <|
    .spec 42 127 <|
    .expo 127 42 1 <|
    .spec 27 163 <|
    .expo 163 27 1 <|
    .spec 178 179 <|
    .expo 179 178 1 <|
    .spec 11 199 <|
    .expo 199 11 1 <|
    .spec 57 229 <|
    .expo 229 57 1 <|
    .ord 19 277 <|
    .spec 179 359 <|
    .expo 359 179 1 <|
    .spec 3 373 <|
    .expo 373 3 1 <|
    .spec 378 379 <|
    .spec 22 397 <|
    .spec 38 457 <|
    .spec 81 487 <|
    .spec 54 541 <|
    .spec 3 571 <|
    .spec 359 719 <|
    .spec 121 727 <|
    .spec 81 811 <|
    .spec 441 883 <|
    .spec 473 947 <|
    .spec 198 991 <|
    .spec 729 1459 <|
    .spec 373 1493 <|
    .ord 727 1933 <|
    .spec 18 1999 <|
    .ord 1999 1381 <|
    .spec 231 2311 <|
    .spec 326 2609 <|
    .spec 729 2917 <|
    .overflow 47 [(2917, 1), (2609, 1), (2311, 1), (1999, 1), (1933, 1), (1493, 1), (1459, 1), (1381, 1), (991, 1), (947, 1), (883, 1), (811, 1), (719, 1), (571, 1), (541, 1), (487, 1), (457, 1), (397, 1), (379, 1), (277, 1), (89, 1), (7, 1), (3, 1)] 0 0
    )
    (
    .ord 23 461 <|
    .ord 461 139 <|
    .ord 461 133723 <|
    .ord 133723 47 <|
    .ord 133723 37123 <|
    .ord 133723 2258831 <|
    .ord 37123 12849227 <|
    .ord 37123 45920191 <|
    .ord 133723 519554683 <|
    .ord 519554683 44851 <|
    .ord 44851 625639699 <|
    .ord 625639699 3083 <|
    .ord 3083 77419 <|
    .ord 3083 28076239 <|
    .ord 28076239 226367 <|
    .ord 226367 224251 <|
    .ord 224251 19919 <|
    .ord 19919 28751 <|
    .ord 44851 1789254043 <|
    .ord 133723 9994966159 <|
    .branch 1013
      (
      .spec 2 3 <|
      .expo 3 2 1 <|
      .spec 6 7 <|
      .expo 7 6 1 <|
      .spec 2 13 <|
      .expo 13 2 2 <|
      .spec 9 19 <|
      .expo 19 9 1 <|
      .spec 21 43 <|
      .expo 43 21 1 <|
      .spec 26 53 <|
      .expo 53 26 1 <|
      .spec 3 73 <|
      .expo 73 3 1 <|
      .spec 13 79 <|
      .expo 79 13 1 <|
      .spec 106 107 <|
      .expo 107 106 1 <|
      .spec 7 113 <|
      .expo 113 7 1 <|
      .spec 63 127 <|
      .expo 127 63 1 <|
      .spec 39 157 <|
      .expo 157 39 1 <|
      .spec 81 163 <|
      .expo 163 81 1 <|
      .spec 43 173 <|
      .expo 173 43 1 <|
      .spec 49 197 <|
      .ord 19 277 <|
      .spec 21 337 <|
      .spec 173 347 <|
      .spec 21 379 <|
      .spec 438 439 <|
      .spec 27 487 <|
      .spec 26 521 <|
      .overflow 47 [(3083, 2), (53, 2), (9994966159, 1), (45920191, 1), (28076239, 1), (224251, 1), (133723, 1), (28751, 1), (521, 1), (487, 1), (439, 1), (379, 1), (347, 1), (337, 1), (277, 1), (197, 1), (173, 1), (157, 1), (79, 1), (7, 1), (3, 1)] 0 0
      )
      (
      .ord 3083 1013 <|
      .ord 1013 964207 <|
      .branch 1289
        (
        .spec 2 3 <|
        .expo 3 2 1 <|
        .spec 9 19 <|
        .ord 19 277 <|
        .overflow 23 [(9994966159, 1), (1789254043, 1), (625639699, 1), (519554683, 1), (45920191, 1), (28076239, 1), (12849227, 1), (2258831, 1), (964207, 1), (226367, 1), (224251, 1), (133723, 1), (77419, 1), (44851, 1), (37123, 1), (28751, 1), (19919, 1), (3083, 1), (1013, 1), (461, 1), (277, 1), (139, 1), (47, 1)] 0 0
        )
        (
        .ord 23 1289 <|
        .overflow 23 [(9994966159, 1), (1789254043, 1), (625639699, 1), (519554683, 1), (45920191, 1), (28076239, 1), (12849227, 1), (2258831, 1), (964207, 1), (226367, 1), (224251, 1), (133723, 1), (77419, 1), (44851, 1), (37123, 1), (28751, 1), (19919, 1), (3083, 1), (1289, 1), (1013, 1), (461, 1), (139, 1), (47, 1)] 0 0
        )
      )
    )

/-- The tree for `l = 23` when `23` is the special prime. -/
def spec23 : Node :=
  .mod4

/-- The certificate for `l = 23` is accepted. -/
theorem check23 : checkAll 23 pc23 ord23 spec23 = true := by
  decide +kernel

/-- Pratt certificates for `l = 29`. -/
def pc29 : List (ℕ × ℕ × List ℕ) :=
  [(1103, 5, [2, 19, 29]),
    (1567, 3, [2, 3, 3, 3, 29]),
    (1973, 2, [2, 2, 17, 29]),
    (2089, 7, [2, 2, 2, 3, 3, 29]),
    (2843, 2, [2, 7, 7, 29]),
    (3229, 6, [2, 2, 3, 269]),
    (3539, 2, [2, 29, 61]),
    (4931, 6, [2, 5, 17, 29]),
    (7193, 3, [2, 2, 2, 29, 31]),
    (7309, 6, [2, 2, 3, 3, 7, 29]),
    (7541, 2, [2, 2, 5, 13, 29]),
    (10499, 2, [2, 29, 181]),
    (10789, 2, [2, 2, 3, 29, 31]),
    (10847, 5, [2, 11, 17, 29]),
    (11311, 3, [2, 3, 5, 13, 29]),
    (11717, 2, [2, 2, 29, 101]),
    (16763, 2, [2, 17, 17, 29]),
    (19373, 2, [2, 2, 29, 167]),
    (20011, 12, [2, 3, 5, 23, 29]),
    (24071, 11, [2, 5, 29, 83]),
    (28537, 5, [2, 2, 2, 3, 29, 41]),
    (31379, 2, [2, 29, 541]),
    (32887, 3, [2, 3, 3, 3, 3, 7, 29]),
    (34337, 3, [2, 2, 2, 2, 2, 29, 37]),
    (35671, 3, [2, 3, 5, 29, 41]),
    (52201, 17, [2, 2, 2, 3, 3, 5, 5, 29]),
    (60727, 5, [2, 3, 29, 349]),
    (72559, 3, [2, 3, 3, 29, 139]),
    (84449, 3, [2, 2, 2, 2, 2, 7, 13, 29]),
    (91873, 5, [2, 2, 2, 2, 2, 3, 3, 11, 29]),
    (118901, 2, [2, 2, 5, 5, 29, 41]),
    (152657, 3, [2, 2, 2, 2, 7, 29, 47]),
    (158747, 5, [2, 7, 17, 23, 29]),
    (2972791, 6, [2, 3, 3, 5, 17, 29, 67]),
    (243301, 6, [2, 2, 3, 5, 5, 811]),
    (14111459, 2, [2, 29, 243301]),
    (17805943, 11, [2, 3, 3, 7, 11, 29, 443]),
    (26671591, 7, [2, 3, 3, 5, 11, 29, 929]),
    (94327, 3, [2, 3, 79, 199]),
    (38296763, 2, [2, 7, 29, 94327]),
    (2137, 10, [2, 2, 2, 3, 89]),
    (1269379, 2, [2, 3, 3, 3, 11, 2137]),
    (73623983, 5, [2, 29, 1269379]),
    (66491, 2, [2, 5, 61, 109]),
    (80986039, 14, [2, 3, 7, 29, 66491]),
    (8969, 3, [2, 2, 2, 19, 59]),
    (394637, 2, [2, 2, 11, 8969]),
    (9471289, 17, [2, 2, 2, 3, 394637]),
    (549334763, 2, [2, 29, 9471289]),
    (25253, 2, [2, 2, 59, 107]),
    (301269697, 10, [2, 2, 2, 2, 2, 2, 3, 7, 13, 43, 401]),
    (147411262742101, 10, [2, 2, 3, 5, 5, 7, 233, 301269697]),
    (2113, 5, [2, 2, 2, 2, 2, 2, 3, 11]),
    (71843, 2, [2, 17, 2113]),
    (459220457, 3, [2, 2, 2, 17, 47, 71843]),
    (7333, 6, [2, 2, 3, 13, 47]),
    (10613, 2, [2, 2, 7, 379]),
    (445747, 2, [2, 3, 7, 10613]),
    (215731741567, 3, [2, 3, 11, 7333, 445747]),
    (198136857903607272239, 7, [2, 459220457, 215731741567]),
    (299927907373620235129328599560708872640564547, 2, [2, 3, 3, 19, 29, 41, 25253, 147411262742101, 198136857903607272239])]

/-- The tree for `l = 29` when `29` is ordinary. -/
def ord29 : Node :=
  .ord 29 59 <|
  .ord 29 16763 <|
  .ord 29 14111459 <|
  .ord 16763 73623983 <|
  .ord 73623983 60727 <|
  .ord 59 80986039 <|
  .ord 29 549334763 <|
  .branch 19373
    (
    .spec 2 3 <|
    .spec 2 3229 <|
    .ord 3229 349 <|
    .ord 349 1103 <|
    .ord 349 2843 <|
    .ord 349 11311 <|
    .ord 1103 11717 <|
    .ord 11717 20011 <|
    .ord 20011 1567 <|
    .ord 1567 2089 <|
    .ord 2089 523 <|
    .ord 11311 24071 <|
    .ord 3 28537 <|
    .ord 11311 31379 <|
    .ord 14111459 34337 <|
    .ord 28537 35671 <|
    .ord 549334763 52201 <|
    .ord 34337 72559 <|
    .ord 29 84449 <|
    .ord 34337 118901 <|
    .ord 118901 233 <|
    .ord 118901 152657 <|
    .ord 152657 10789 <|
    .ord 10789 7541 <|
    .overflow 29 [(549334763, 1), (80986039, 1), (73623983, 1), (14111459, 1), (152657, 1), (118901, 1), (84449, 1), (72559, 1), (60727, 1), (52201, 1), (35671, 1), (34337, 1), (31379, 1), (28537, 1), (24071, 1), (20011, 1), (16763, 1), (11717, 1), (11311, 1), (10789, 1), (7541, 1), (2843, 1), (2089, 1), (1567, 1), (1103, 1), (523, 1), (349, 1), (233, 1), (59, 1)] 0 0
    )
    (
    .ord 80986039 19373 <|
    .ord 19373 38296763 <|
    .ord 38296763 4931 <|
    .ord 38296763 10847 <|
    .ord 10847 523 <|
    .ord 4931 17805943 <|
    .ord 17805943 32887 <|
    .ord 4931 26671591 <|
    .branch 233
      (
      .spec 2 3 <|
      .spec 2 13 <|
      .ord 17805943 349 <|
      .ord 349 1103 <|
      .ord 13 1973 <|
      .ord 13 2843 <|
      .ord 13 3539 <|
      .ord 349 11311 <|
      .ord 1103 11717 <|
      .ord 11717 20011 <|
      .ord 20011 1567 <|
      .ord 1567 2089 <|
      .ord 11311 24071 <|
      .ord 3 28537 <|
      .ord 11311 31379 <|
      .ord 14111459 34337 <|
      .overflow 29 [(549334763, 1), (80986039, 1), (73623983, 1), (38296763, 1), (26671591, 1), (17805943, 1), (14111459, 1), (60727, 1), (34337, 1), (32887, 1), (31379, 1), (28537, 1), (24071, 1), (20011, 1), (19373, 1), (16763, 1), (11717, 1), (11311, 1), (10847, 1), (4931, 1), (3539, 1), (2843, 1), (2089, 1), (1973, 1), (1567, 1), (1103, 1), (523, 1), (349, 1), (59, 1)] 0 0
      )
      (
      .ord 4931 233 <|
      .ord 233 2972791 <|
      .ord 233 299927907373620235129328599560708872640564547 <|
      .branch 349
        (
        .spec 2 5 <|
        .ord 38296763 1973 <|
        .ord 2972791 7309 <|
        .ord 14111459 34337 <|
        .ord 5 35671 <|
        .ord 549334763 52201 <|
        .ord 34337 72559 <|
        .ord 29 84449 <|
        .ord 10847 91873 <|
        .ord 34337 118901 <|
        .ord 118901 152657 <|
        .ord 152657 10789 <|
        .overflow 29 [(299927907373620235129328599560708872640564547, 1), (549334763, 1), (80986039, 1), (73623983, 1), (38296763, 1), (26671591, 1), (17805943, 1), (14111459, 1), (2972791, 1), (152657, 1), (118901, 1), (91873, 1), (84449, 1), (72559, 1), (60727, 1), (52201, 1), (35671, 1), (34337, 1), (32887, 1), (19373, 1), (16763, 1), (10847, 1), (10789, 1), (7309, 1), (4931, 1), (1973, 1), (523, 1), (233, 1), (59, 1)] 0 0
        )
        (
        .ord 17805943 349 <|
        .ord 349 1103 <|
        .ord 349 2843 <|
        .ord 349 11311 <|
        .ord 11311 24071 <|
        .ord 11311 31379 <|
        .ord 2843 158747 <|
        .branch 1973
          (
          .ord 2972791 7309 <|
          .ord 1103 11717 <|
          .ord 11717 20011 <|
          .ord 20011 1567 <|
          .overflow 29 [(299927907373620235129328599560708872640564547, 1), (549334763, 1), (80986039, 1), (73623983, 1), (38296763, 1), (26671591, 1), (17805943, 1), (14111459, 1), (2972791, 1), (158747, 1), (60727, 1), (32887, 1), (31379, 1), (24071, 1), (20011, 1), (19373, 1), (16763, 1), (11717, 1), (11311, 1), (10847, 1), (7309, 1), (4931, 1), (2843, 1), (1567, 1), (1103, 1), (523, 1), (349, 1), (233, 1), (59, 1)] 0 0
          )
          (
          .ord 38296763 1973 <|
          .branch 7309
            (
            .spec 2 17 <|
            .spec 2 43 <|
            .ord 17 7193 <|
            .ord 43 10499 <|
            .ord 1103 11717 <|
            .overflow 29 [(299927907373620235129328599560708872640564547, 1), (549334763, 1), (80986039, 1), (73623983, 1), (38296763, 1), (26671591, 1), (17805943, 1), (14111459, 1), (2972791, 1), (158747, 1), (60727, 1), (32887, 1), (31379, 1), (24071, 1), (19373, 1), (16763, 1), (11717, 1), (11311, 1), (10847, 1), (10499, 1), (7193, 1), (4931, 1), (2843, 1), (1973, 1), (1103, 1), (523, 1), (349, 1), (233, 1), (59, 1)] 0 0
            )
            (
            .ord 2972791 7309 <|
            .branch 11717
              (
              .spec 2 31 <|
              .ord 31 10789 <|
              .ord 10789 7541 <|
              .overflow 29 [(299927907373620235129328599560708872640564547, 1), (549334763, 1), (80986039, 1), (73623983, 1), (38296763, 1), (26671591, 1), (17805943, 1), (14111459, 1), (2972791, 1), (158747, 1), (60727, 1), (32887, 1), (31379, 1), (24071, 1), (19373, 1), (16763, 1), (11311, 1), (10847, 1), (10789, 1), (7541, 1), (7309, 1), (4931, 1), (2843, 1), (1973, 1), (1103, 1), (523, 1), (349, 1), (233, 1), (59, 1)] 0 0
              )
              (
              .ord 1103 11717 <|
              .ord 11717 20011 <|
              .overflow 29 [(299927907373620235129328599560708872640564547, 1), (549334763, 1), (80986039, 1), (73623983, 1), (38296763, 1), (26671591, 1), (17805943, 1), (14111459, 1), (2972791, 1), (158747, 1), (60727, 1), (32887, 1), (31379, 1), (24071, 1), (20011, 1), (19373, 1), (16763, 1), (11717, 1), (11311, 1), (10847, 1), (7309, 1), (4931, 1), (2843, 1), (1973, 1), (1103, 1), (523, 1), (349, 1), (233, 1), (59, 1)] 0 0
              )
            )
          )
        )
      )
    )

/-- The tree for `l = 29` when `29` is the special prime. -/
def spec29 : Node :=
  .spec 2 3 <|
  .expo 3 2 1 <|
  .spec 2 5 <|
  .expo 5 2 1 <|
  .spec 10 11 <|
  .expo 11 10 1 <|
  .spec 3 13 <|
  .expo 13 3 1 <|
  .spec 18 19 <|
  .expo 19 18 1 <|
  .spec 11 23 <|
  .expo 23 11 1 <|
  .spec 10 31 <|
  .expo 31 10 1 <|
  .spec 46 47 <|
  .expo 47 46 1 <|
  .spec 26 53 <|
  .expo 53 26 1 <|
  .ord 3 59 <|
  .spec 3 67 <|
  .expo 67 3 1 <|
  .spec 78 79 <|
  .expo 79 78 1 <|
  .spec 53 107 <|
  .expo 107 53 1 <|
  .spec 54 109 <|
  .expo 109 54 1 <|
  .spec 130 131 <|
  .expo 131 130 1 <|
  .spec 69 139 <|
  .expo 139 69 1 <|
  .spec 25 151 <|
  .expo 151 25 1 <|
  .spec 162 163 <|
  .expo 163 162 1 <|
  .spec 15 181 <|
  .expo 181 15 1 <|
  .spec 190 191 <|
  .expo 191 190 1 <|
  .spec 99 199 <|
  .spec 250 251 <|
  .spec 262 263 <|
  .spec 6 271 <|
  .spec 138 277 <|
  .spec 310 311 <|
  .spec 330 331 <|
  .spec 93 373 <|
  .spec 191 383 <|
  .spec 81 487 <|
  .spec 13 521 <|
  .ord 11 523 <|
  .spec 278 557 <|
  .spec 598 599 <|
  .spec 321 643 <|
  .spec 66 661 <|
  .spec 66 727 <|
  .spec 393 787 <|
  .spec 906 907 <|
  .overflow 59 [(53, 2), (907, 1), (787, 1), (727, 1), (661, 1), (643, 1), (599, 1), (557, 1), (523, 1), (521, 1), (487, 1), (383, 1), (373, 1), (331, 1), (311, 1), (277, 1), (271, 1), (263, 1), (251, 1), (199, 1), (181, 1), (163, 1), (139, 1), (107, 1), (79, 1), (19, 1), (5, 1), (3, 1)] 0 0

/-- The certificate for `l = 29` is accepted. -/
theorem check29 : checkAll 29 pc29 ord29 spec29 = true := by
  decide +kernel

end OddPerfect.EqChain

namespace OddPerfect

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `4`. -/
theorem not_all_exponents_eq_four {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 4) : False :=
  EqChain.checkAll_sound EqChain.check5 h hq hodd hexp

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `6`. -/
theorem not_all_exponents_eq_six {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 6) : False :=
  EqChain.checkAll_sound EqChain.check7 h hq hodd hexp

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `10`. -/
theorem not_all_exponents_eq_ten {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 10) : False :=
  EqChain.checkAll_sound EqChain.check11 h hq hodd hexp

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `12`. -/
theorem not_all_exponents_eq_twelve {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 12) : False :=
  EqChain.checkAll_sound EqChain.check13 h hq hodd hexp

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `16`. -/
theorem not_all_exponents_eq_sixteen {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 16) : False :=
  EqChain.checkAll_sound EqChain.check17 h hq hodd hexp

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `18`. -/
theorem not_all_exponents_eq_eighteen {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 18) : False :=
  EqChain.checkAll_sound EqChain.check19 h hq hodd hexp

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `22`. -/
theorem not_all_exponents_eq_twenty_two {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 22) : False :=
  EqChain.checkAll_sound EqChain.check23 h hq hodd hexp

/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `28`. -/
theorem not_all_exponents_eq_twenty_eight {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 28) : False :=
  EqChain.checkAll_sound EqChain.check29 h hq hodd hexp

end OddPerfect

#print axioms OddPerfect.EqChain.gm_eq
#print axioms OddPerfect.EqChain.dvd_sigma_of_gm
#print axioms OddPerfect.EqChain.isP_sound
#print axioms OddPerfect.EqChain.allNe_sound
#print axioms OddPerfect.EqChain.neq_sound
#print axioms OddPerfect.EqChain.over_sum
#print axioms OddPerfect.EqChain.expo_dvd
#print axioms OddPerfect.EqChain.run_sound
#print axioms OddPerfect.EqChain.checkAll_sound
#print axioms OddPerfect.EqChain.check5
#print axioms OddPerfect.EqChain.check7
#print axioms OddPerfect.EqChain.check11
#print axioms OddPerfect.EqChain.check13
#print axioms OddPerfect.EqChain.check17
#print axioms OddPerfect.EqChain.check19
#print axioms OddPerfect.EqChain.check23
#print axioms OddPerfect.EqChain.check29
#print axioms OddPerfect.not_all_exponents_eq_four
#print axioms OddPerfect.not_all_exponents_eq_six
#print axioms OddPerfect.not_all_exponents_eq_ten
#print axioms OddPerfect.not_all_exponents_eq_twelve
#print axioms OddPerfect.not_all_exponents_eq_sixteen
#print axioms OddPerfect.not_all_exponents_eq_eighteen
#print axioms OddPerfect.not_all_exponents_eq_twenty_two
#print axioms OddPerfect.not_all_exponents_eq_twenty_eight
