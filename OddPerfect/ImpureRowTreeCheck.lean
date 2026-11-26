import OddPerfect.EqualExponentCount
import OddPerfect.PureRows
import OddPerfect.KanoldGeneral

/-!
# Impure rows for small lengths: a tree certificate checker and its soundness

Setting: `N` is an odd perfect number with special prime `q`, `l` is an odd prime with
`l ∣ e_p + 1` for every ordinary prime `p` (a prime factor `p ≠ q`, `e_p = N.factorization p`).
The row of `p` is `σ(p ^ e_p)`; it is impure when it is not a prime power. Write
`R(x) = ∑ i ∈ Finset.range l, x ^ i`. `M` is a finite set containing every ordinary prime with
an impure row. An accepted certificate proves `4 ≤ M.card`.

Facts used, for an ordinary prime `p`:
* `R(p)` divides `σ(p ^ e_p)`, which divides `2 N`; every prime factor of `R(p)` other than
  `l` divides `N` and is `1` modulo `l`;
* an ordinary prime that is `1` modulo `l` has an impure row (`impure_of_mod_one`);
* an ordinary prime `p` such that `R(p)` has two distinct prime factors has an impure row
  (`impure_of_two`).

A tree walks through cases. Its state is a list of parents (proved ordinary primes) and
possibly the value `Q` of the special prime. A node adds a prime `t` as a parent (`add`), or
splits on `t = q` (`split`); `t` must be prime and divide `N` (it is `l`, or divides `R(s)` for
a parent `s`, or divides `Q + 1` when `q = Q`), and an added parent must differ from `q`
(`t % 4 = 3`, or `t ≠ Q`). A leaf lists counted numbers `m`, each dividing `R(t)` for a parent
`t`, coprime to `l` and to the earlier ones; each contributes one distinct prime factor, or two
with a witness that `m` is not a prime power. All these primes are ordinary with an impure
row, except possibly `q`, which is subtracted unless it is excluded. The leaf adds the parents
`t` with `t % l ≠ 1` whose `R(t)` has two distinct prime factors. The leaf closes when the
total is at least `4`.

Restricted result (one odd prime divides every ordinary index); no published source was
checked; novelty not verified. The odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.ImpTree

open OddPerfect.Pratt (trialPrime trialPrime_sound)
open OddPerfect.EqChain (gm gm_eq)
open OddPerfect.EqCount (witnessOK weight weight_le)

/-! ## Computable checker -/

/-- The geometric sum `∑ i < n, t ^ i` by Horner's rule. -/
def gsum (t : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => gsum t n * t + 1

theorem gsum_eq (t : ℕ) : ∀ n, gsum t n = ∑ i ∈ Finset.range n, t ^ i
  | 0 => by simp [gsum]
  | n + 1 => by
    have hs : ∑ i ∈ Finset.range (n + 1), t ^ i = (∑ i ∈ Finset.range n, t ^ i) * t + 1 := by
      rw [Finset.sum_range_succ', Finset.sum_mul]
      simp [pow_succ]
    rw [gsum, gsum_eq t n, hs]

/-- Primality: listed in a Pratt certificate, or trial division below `5000`. -/
def isPr (pc : List (ℕ × ℕ × List ℕ)) (t : ℕ) : Bool :=
  (pc.map Prod.fst).contains t || (decide (t < 5000) && trialPrime t)

theorem isPr_sound {pc : List (ℕ × ℕ × List ℕ)} (hpc : Pratt.check pc = true) {t : ℕ}
    (h : isPr pc t = true) : t.Prime := by
  simp only [isPr, Bool.or_eq_true, List.contains_iff_mem, List.mem_map, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with ⟨e, he, rfl⟩ | ⟨-, h⟩
  · exact Pratt.check_sound hpc e he
  · exact trialPrime_sound h

/-- A counted number: an explicit divisor `f` of `R(t)`, or the quotient `R(t) / d` with a
witness `a` (`a = 0`: no witness). -/
inductive Item
  | pr (t f : ℕ)
  | cof (t d a : ℕ)

/-- The parent of an item. -/
def Item.src : Item → ℕ
  | pr t _ => t
  | cof t _ _ => t

/-- The counted number. -/
def Item.val (l : ℕ) : Item → ℕ
  | pr _ f => f
  | cof t d _ => gsum t l / d

/-- The claimed number of distinct prime factors. -/
def Item.wt : Item → ℕ
  | pr _ _ => 1
  | cof _ _ a => weight a

/-- The test of an item against the product `P` of the earlier ones. -/
def Item.ok (l P : ℕ) : Item → Bool
  | pr t f => 1 < f && f % l != 0 && gm t f l == 0 && Nat.gcd f P == 1
  | cof t d a =>
    1 < gsum t l / d && gsum t l / d % l != 0 && gsum t l % d == 0 &&
      Nat.gcd (gsum t l / d) P == 1 && witnessOK (gsum t l / d) a

/-- Walk the items, with product `P` and count `k`. -/
def walk (l : ℕ) : ℕ → ℕ → List Item → Option (ℕ × ℕ)
  | P, k, [] => some (P, k)
  | P, k, it :: rest =>
    cond (Item.ok l P it) (walk l (P * Item.val l it) (k + Item.wt it) rest) none

/-- The count of an accepted walk from `(1, 0)`, or `0`. -/
def walkCount (l : ℕ) (items : List Item) : ℕ :=
  match walk l 1 0 items with
  | some Pk => Pk.2
  | none => 0

/-- An item whose number is a prime known to differ from `q`. -/
def safe (pc : List (ℕ × ℕ × List ℕ)) (par : List ℕ) : Item → Bool
  | Item.pr _ f => par.contains f || (f % 4 == 3 && isPr pc f)
  | Item.cof _ _ _ => false

/-- The amount subtracted for the special prime. -/
def subOf (pc : List (ℕ × ℕ × List ℕ)) (qs : Option ℕ) (par : List ℕ) (items : List Item)
    (P : ℕ) : ℕ :=
  match qs with
  | some Q => if P % Q == 0 then 1 else 0
  | none => if items.all (safe pc par) then 0 else 1

/-- A parent `t` with `t % l ≠ 1` whose `R(t)` has two distinct prime factors (evidence `ev`). -/
def impOK (l : ℕ) (par : List ℕ) (e : ℕ × List Item) : Bool :=
  par.contains e.1 && e.1 % l != 1 && e.2.all (fun it => (Item.src it) == e.1) &&
    decide (2 ≤ walkCount l e.2)

/-- The leaf test. -/
def leafOK (l : ℕ) (pc : List (ℕ × ℕ × List ℕ)) (qs : Option ℕ) (par : List ℕ)
    (imps : List (ℕ × List Item)) (items : List Item) : Bool :=
  match walk l 1 0 items with
  | none => false
  | some (P, k) =>
    items.all (fun it => par.contains (Item.src it)) && decide (imps.map Prod.fst).Nodup &&
      imps.all (impOK l par) && decide (4 + subOf pc qs par items P ≤ imps.length + k)

/-- Divisibility of `Q + 1` when `q = Q` is known. -/
def qdvd (qs : Option ℕ) (t : ℕ) : Bool :=
  match qs with
  | some Q => (Q + 1) % t == 0
  | none => false

/-- `t ≠ Q` when `q = Q` is known. -/
def qne (qs : Option ℕ) (t : ℕ) : Bool :=
  match qs with
  | some Q => t != Q
  | none => false

/-- A reason for `t ∣ N`. -/
def dvdR (l : ℕ) (qs : Option ℕ) (par : List ℕ) (t : ℕ) : Bool :=
  t != 2 && (t == l || par.any (fun s => gm s t l == 0) || qdvd qs t)

/-- A reason for `t ≠ q`. -/
def neR (qs : Option ℕ) (t : ℕ) : Bool := t % 4 == 3 || qne qs t

/-- A case tree. -/
inductive Tree
  | leaf (imps : List (ℕ × List Item)) (items : List Item)
  | add (t : ℕ) (k : Tree)
  | split (t : ℕ) (y n : Tree)

/-- The tree test. -/
def chk (l : ℕ) (pc : List (ℕ × ℕ × List ℕ)) : Option ℕ → List ℕ → Tree → Bool
  | qs, par, Tree.leaf imps items => leafOK l pc qs par imps items
  | qs, par, Tree.add t k => isPr pc t && dvdR l qs par t && neR qs t && chk l pc qs (t :: par) k
  | qs, par, Tree.split t y n =>
    isPr pc t && dvdR l qs par t && chk l pc (some t) par y && chk l pc qs (t :: par) n

/-- A certificate for the length `l` and the seed `s`. -/
def checkTree (l : ℕ) (pc : List (ℕ × ℕ × List ℕ)) (s : ℕ) (tr : Tree) : Bool :=
  Pratt.check pc && chk l pc none [s] tr

/-! ## Arithmetic facts -/

/-- For an ordinary index divisible by `l`: `R(p) ∣ σ(p ^ e_p) ∣ 2 N`. -/
theorem row_dvd {N p l : ℕ} (h : OddPerfect N) (hp : p.Prime) (hl : 1 ≤ l)
    (hdvd : l ∣ N.factorization p + 1) :
    ∑ i ∈ Finset.range l, p ^ i ∣ σ 1 (p ^ N.factorization p) ∧
      σ 1 (p ^ N.factorization p) ∣ 2 * N := by
  refine ⟨?_, OPNStarter.component_sigma_dvd h.perfect hp rfl⟩
  have h1 : σ 1 (p ^ (l - 1)) = ∑ i ∈ Finset.range l, p ^ i := by
    rw [sigma_one_apply_prime_pow hp, Nat.sub_add_cancel hl]
  rw [← h1]
  exact OPNExample.sigma_prime_pow_dvd (e := N.factorization p) hp
    (by rwa [Nat.sub_add_cancel hl])

/-- An odd prime dividing `2 N` divides `N`. -/
theorem dvd_of_dvd_two_mul {N r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h : r ∣ 2 * N) : r ∣ N :=
  (hr.dvd_mul.mp h).resolve_left fun h2 =>
    hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)

/-- An odd prime factor of `q + 1` divides `N`. -/
theorem dvd_of_dvd_special_succ {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) {t : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) (hd : t ∣ q + 1) :
    t ∣ N := by
  have hk : 1 + 1 ∣ N.factorization q + 1 := by
    obtain ⟨j, hj⟩ := hodd
    exact ⟨j + 1, by omega⟩
  have hσ : t ∣ σ 1 (q ^ 1) := by
    rw [sigma_one_apply_prime_pow hq, Finset.sum_range_succ, Finset.sum_range_one, pow_zero,
      pow_one, Nat.add_comm]
    exact hd
  exact OPNStarter.force_prime h.perfect hq rfl ht ht2
    (hσ.trans (OPNExample.sigma_prime_pow_dvd hq hk))

/-- The standing hypotheses. -/
structure Hyp (N q l : ℕ) (M : Finset ℕ) : Prop where
  h : OddPerfect N
  hq : q.Prime
  hodd : Odd (N.factorization q)
  hl : l.Prime
  hl2 : l ≠ 2
  hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1
  hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
    ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w
  hlN : l ∣ N

section Sound

variable {N q l : ℕ} {M : Finset ℕ}

theorem Hyp.idx (H : Hyp N q l M) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpq : p ≠ q) :
    l ∣ N.factorization p + 1 :=
  H.hidx p (Nat.mem_primeFactors.mpr ⟨hp, hpN, H.h.ne_zero⟩) hpq

/-- An ordinary prime with an impure row lies in `M`. -/
theorem Hyp.mem (H : Hyp N q l M) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpq : p ≠ q)
    (himp : ¬ ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : p ∈ M := by
  by_contra hpM
  exact himp (H.hM p (Nat.mem_primeFactors.mpr ⟨hp, hpN, H.h.ne_zero⟩) hpq hpM)

/-- A prime factor `r ≠ l` of `R(p)`, `p` ordinary, divides `N` and is `1` modulo `l`. -/
theorem Hyp.row_prime (H : Hyp N q l M) {p r : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpq : p ≠ q)
    (hr : r.Prime) (hrR : r ∣ ∑ i ∈ Finset.range l, p ^ i) (hrl : r ≠ l) :
    r ∣ N ∧ r % l = 1 := by
  have hl1 := H.hl.one_lt
  have hσ : r ∣ σ 1 (p ^ (l - 1)) := by
    rw [sigma_one_apply_prime_pow hp, Nat.sub_add_cancel hl1.le]
    exact hrR
  rcases prime_dvd_sigma_prime_pow_of_prime_length hp hr H.hl hσ with h1 | h1
  · exact absurd h1 hrl
  · have hl3 : 3 ≤ l := by have := H.hl.two_le; have := H.hl2; omega
    have hr2 : r ≠ 2 := by
      rintro rfl
      rw [Nat.mod_eq_of_lt (by omega)] at h1
      omega
    have hrow := row_dvd H.h hp hl1.le (H.idx hp hpN hpq)
    exact ⟨dvd_of_dvd_two_mul hr hr2 (hrR.trans (hrow.1.trans hrow.2)), h1⟩

/-- An ordinary prime that is `1` modulo `l` has an impure row. -/
theorem Hyp.impure_of_mod_one (H : Hyp N q l M) {r : ℕ} (hr : r.Prime) (hrN : r ∣ N)
    (hrq : r ≠ q) (h1 : r % l = 1) :
    ¬ ∃ r' w, r'.Prime ∧ σ 1 (r ^ N.factorization r) = r' ^ w := by
  rintro ⟨r', w, hr', hrow⟩
  have hl := H.hl
  have : Fact l.Prime := ⟨hl⟩
  have hl3 : 3 ≤ l := by have := hl.two_le; have := H.hl2; omega
  have hr2 : r ≠ 2 := by
    rintro rfl
    rw [Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have he0 : N.factorization r ≠ 0 := (hr.factorization_pos_of_dvd H.h.ne_zero hrN).ne'
  have hpr := prime_succ_of_sigma_prime_pow_eq_prime_pow hr hr2
    (even_factorization_of_ne H.h H.hq H.hodd hr hrq) he0 hr' hrow
  have he : N.factorization r + 1 = l :=
    ((Nat.prime_dvd_prime_iff_eq hl hpr).mp (H.idx hr hrN hrq)).symm
  have hv := padicValNat_sigma_of_mod_eq_one (a := N.factorization r) hr hl H.hl2 h1
  rw [he, Nat.padicValNat_def (p := l) (n := l), Nat.Prime.multiplicity_self,
    Nat.padicValNat_def] at hv
  have hdvd : l ∣ r' ^ w := hrow ▸ dvd_of_one_le_multiplicity (by omega)
  have hlr : l = r' := (Nat.prime_dvd_prime_iff_eq hl hr').mp (hl.dvd_of_dvd_pow hdvd)
  have hmod := receiver_mod_index_of_pure hr hr2 (by omega) hr' hrow
  rw [he, ← hlr, Nat.mod_self] at hmod
  exact absurd hmod (by norm_num)

/-- An ordinary prime `p` such that `R(p)` has two distinct prime factors has an impure row. -/
theorem Hyp.impure_of_two (H : Hyp N q l M) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hpq : p ≠ q) (h2 : 2 ≤ (∑ i ∈ Finset.range l, p ^ i).primeFactors.card) :
    ¬ ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w := by
  rintro ⟨r, w, hr, hrow⟩
  have hd := (row_dvd H.h hp H.hl.one_lt.le (H.idx hp hpN hpq)).1
  rw [hrow] at hd
  have hsub : (∑ i ∈ Finset.range l, p ^ i).primeFactors ⊆ {r} := by
    intro x hx
    have hx' := Nat.prime_of_mem_primeFactors hx
    rw [Finset.mem_singleton]
    exact (Nat.prime_dvd_prime_iff_eq hx' hr).mp
      (hx'.dvd_of_dvd_pow ((Nat.dvd_of_mem_primeFactors hx).trans hd))
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at this
  omega

end Sound

/-! ## Soundness of the checker -/

theorem Item.ok_spec {l P : ℕ} {it : Item} (h : Item.ok l P it = true) :
    1 < Item.val l it ∧ ¬ l ∣ Item.val l it ∧
      Item.val l it ∣ ∑ i ∈ Finset.range l, Item.src it ^ i ∧
      Nat.Coprime (Item.val l it) P ∧ (Item.wt it) ≤ (Item.val l it).primeFactors.card := by
  cases it with
  | pr t f =>
    simp only [Item.ok, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    simp only [Item.val, Item.src, Item.wt]
    refine ⟨h1, fun hd => h2 (Nat.mod_eq_zero_of_dvd hd), ?_, h4,
      (Nat.nonempty_primeFactors.mpr h1).card_pos⟩
    exact Nat.dvd_of_mod_eq_zero (by rw [← gm_eq]; exact h3)
  | cof t d a =>
    simp only [Item.ok, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    simp only [Item.val, Item.src, Item.wt]
    refine ⟨h1, fun hd => h2 (Nat.mod_eq_zero_of_dvd hd), ?_, h4, weight_le h1 h5⟩
    rw [← gsum_eq]
    exact Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h3)

theorem walk_spec (l : ℕ) : ∀ (items : List Item) (P k P' k' : ℕ),
    walk l P k items = some (P', k') → P ≠ 0 → k ≤ P.primeFactors.card →
    P' ≠ 0 ∧ k' ≤ P'.primeFactors.card ∧ ∀ r ∈ P'.primeFactors, r ∈ P.primeFactors ∨
      ∃ it ∈ items, r ∣ (Item.val l it) ∧ ¬ l ∣ (Item.val l it) ∧
        (Item.val l it) ∣ ∑ i ∈ Finset.range l, (Item.src it) ^ i
  | [], P, k, P', k', hw, hP, hk => by
    simp only [walk, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨hP, hk, fun r hr => Or.inl hr⟩
  | it :: rest, P, k, P', k', hw, hP, hk => by
    cases hok : Item.ok l P it with
    | false => simp [walk, hok] at hw
    | true =>
      simp only [walk, hok, Bool.cond_true] at hw
      obtain ⟨hm1, hml, hmR, hcop, hwt⟩ := Item.ok_spec hok
      have hm0 : (Item.val l it) ≠ 0 := by omega
      have hcop' : Nat.Coprime P (Item.val l it) := hcop.symm
      have hpf : (P * Item.val l it).primeFactors =
          P.primeFactors ∪ (Item.val l it).primeFactors :=
        Nat.Coprime.primeFactors_mul hcop'
      obtain ⟨h1, h2, h3⟩ := walk_spec l rest _ _ _ _ hw (mul_ne_zero hP hm0) (by
        rw [hpf, Finset.card_union_of_disjoint hcop'.disjoint_primeFactors]
        omega)
      refine ⟨h1, h2, fun r hr => ?_⟩
      rcases h3 r hr with hr' | ⟨it', hit', hh⟩
      · rw [hpf, Finset.mem_union] at hr'
        rcases hr' with hr' | hr'
        · exact Or.inl hr'
        · exact Or.inr ⟨it, by simp, Nat.dvd_of_mem_primeFactors hr', hml, hmR⟩
      · exact Or.inr ⟨it', by simp [hit'], hh⟩

/-- The meaning of a state: `qs` is the special prime when known, parents are ordinary. -/
abbrev Inv (N q : ℕ) (qs : Option ℕ) (par : List ℕ) : Prop :=
  (∀ Q, qs = some Q → Q = q) ∧ ∀ p ∈ par, p.Prime ∧ p ∣ N ∧ p ≠ q

section Sound2

variable {N q l : ℕ} {M : Finset ℕ}

theorem leafOK_sound (H : Hyp N q l M) {pc : List (ℕ × ℕ × List ℕ)}
    (hpc : Pratt.check pc = true) {qs : Option ℕ} {par : List ℕ} (hI : Inv N q qs par)
    {imps : List (ℕ × List Item)} {items : List Item}
    (hc : leafOK l pc qs par imps items = true) : 4 ≤ M.card := by
  unfold leafOK at hc
  cases hw : walk l 1 0 items with
  | none => rw [hw] at hc; exact absurd hc (by simp)
  | some Pk =>
    obtain ⟨P, k⟩ := Pk
    rw [hw] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    obtain ⟨⟨⟨hsrc, hnd⟩, himps⟩, hcount⟩ := hc
    obtain ⟨hP0, hk, hall⟩ := walk_spec l items 1 0 P k hw one_ne_zero (by simp)
    -- an item's number: its prime factors divide `N` and are `1` modulo `l`
    have hval : ∀ it, par.contains (Item.src it) = true → ∀ r, r.Prime → r ∣ (Item.val l it) →
        ¬ l ∣ (Item.val l it) → (Item.val l it) ∣ ∑ i ∈ Finset.range l, (Item.src it) ^ i →
        r ∣ N ∧ r % l = 1 := by
      intro it hits r hr hrv hlv hvR
      rw [List.contains_iff_mem] at hits
      obtain ⟨htp, htN, htq⟩ := hI.2 _ hits
      exact H.row_prime htp htN htq hr (hrv.trans hvR) fun hrl => hlv (hrl ▸ hrv)
    have hPf : ∀ r ∈ P.primeFactors, r ∣ N ∧ r % l = 1 ∧ ∃ it ∈ items, r ∣ (Item.val l it) := by
      intro r hr
      rcases hall r hr with h0 | ⟨it, hit, hrv, hlv, hvR⟩
      · simp at h0
      · exact ⟨(hval it (hsrc it hit) r (Nat.prime_of_mem_primeFactors hr) hrv hlv hvR).1,
          (hval it (hsrc it hit) r (Nat.prime_of_mem_primeFactors hr) hrv hlv hvR).2,
          it, hit, hrv⟩
    have hq4 := (special_mod_four H.h H.hq H.hodd).1
    -- the special prime is subtracted when it may be counted
    have hsub : q ∈ P.primeFactors → subOf pc qs par items P = 1 := by
      intro hqP
      have hqd := Nat.dvd_of_mem_primeFactors hqP
      unfold subOf
      cases hqs : qs with
      | some Q =>
        rw [hI.1 Q hqs]
        simp [Nat.mod_eq_zero_of_dvd hqd]
      | none =>
        simp only
        rw [ite_eq_right_iff]
        intro hall'
        exfalso
        obtain ⟨it, hit, hqv⟩ := (hPf q hqP).2.2
        have hs := List.all_eq_true.mp hall' it hit
        cases it with
        | cof t d a => simp [safe] at hs
        | pr t f =>
          simp only [safe, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem,
            beq_iff_eq] at hs
          simp only [Item.val] at hqv
          rcases hs with hf | ⟨hf4, hfp⟩
          · obtain ⟨hfP, -, hfq⟩ := hI.2 f hf
            exact hfq ((Nat.prime_dvd_prime_iff_eq H.hq hfP).mp hqv).symm
          · have hfP := isPr_sound hpc hfp
            have := (Nat.prime_dvd_prime_iff_eq H.hq hfP).mp hqv
            rw [← this] at hf4
            omega
    set A := P.primeFactors.erase q with hAdef
    set B := (imps.map Prod.fst).toFinset with hBdef
    have hA : P.primeFactors.card ≤ A.card + subOf pc qs par items P := by
      by_cases hqP : q ∈ P.primeFactors
      · rw [hAdef, Finset.card_erase_of_mem hqP, hsub hqP]
        have := Finset.card_pos.mpr ⟨q, hqP⟩
        omega
      · rw [hAdef, Finset.erase_eq_of_notMem hqP]
        omega
    have hAM : A ⊆ M := by
      intro r hr
      obtain ⟨hrq, hrP⟩ := Finset.mem_erase.mp hr
      obtain ⟨hrN, hr1, -⟩ := hPf r hrP
      have hrp := Nat.prime_of_mem_primeFactors hrP
      exact H.mem hrp hrN hrq (H.impure_of_mod_one hrp hrN hrq hr1)
    have hBprop : ∀ t ∈ B, t ∈ M ∧ t % l ≠ 1 := by
      intro t ht
      rw [hBdef, List.mem_toFinset, List.mem_map] at ht
      obtain ⟨⟨t', ev⟩, hmem, rfl⟩ := ht
      have hi := himps _ hmem
      simp only [impOK, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq,
        List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
      obtain ⟨⟨⟨htpar, htl⟩, hev⟩, h2⟩ := hi
      show t' ∈ M ∧ t' % l ≠ 1
      refine ⟨?_, htl⟩
      obtain ⟨htp, htN, htq⟩ := hI.2 _ htpar
      unfold walkCount at h2
      cases hw2 : walk l 1 0 ev with
      | none => rw [hw2] at h2; simp at h2
      | some Pk' =>
        obtain ⟨P', k'⟩ := Pk'
        rw [hw2] at h2
        obtain ⟨-, hk', hall'⟩ := walk_spec l ev 1 0 P' k' hw2 one_ne_zero (by simp)
        have hR0 : ∑ i ∈ Finset.range l, t' ^ i ≠ 0 :=
          (Finset.sum_pos (fun i _ => pow_pos htp.pos i)
            ⟨0, Finset.mem_range.mpr H.hl.pos⟩).ne'
        have hsub' : P'.primeFactors ⊆ (∑ i ∈ Finset.range l, t' ^ i).primeFactors := by
          intro r hr
          rcases hall' r hr with h0 | ⟨it, hit, hrv, -, hvR⟩
          · simp at h0
          · rw [hev it hit] at hvR
            exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hr,
              hrv.trans hvR, hR0⟩
        have := Finset.card_le_card hsub'
        exact H.mem htp htN htq (H.impure_of_two htp htN htq (by simp at h2; omega))
    have hBc : B.card = imps.length := by
      rw [hBdef, List.toFinset_card_of_nodup hnd, List.length_map]
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro r hrA hrB
      exact (hBprop r hrB).2 (hPf r (Finset.mem_erase.mp hrA).2).2.1
    have hU := Finset.card_le_card (Finset.union_subset hAM fun t ht => (hBprop t ht).1)
    rw [Finset.card_union_of_disjoint hdisj] at hU
    have hk1 : k ≤ P.primeFactors.card := hk
    omega

theorem dvdR_sound (H : Hyp N q l M) {qs : Option ℕ} {par : List ℕ} (hI : Inv N q qs par)
    {t : ℕ} (ht : t.Prime) (hd : dvdR l qs par t = true) : t ∣ N := by
  simp only [dvdR, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    List.any_eq_true] at hd
  obtain ⟨ht2, (hd | ⟨s, hs, hgm⟩) | hd⟩ := hd
  · rw [hd]
    exact H.hlN
  · obtain ⟨hsp, hsN, hsq⟩ := hI.2 s hs
    have hrow := row_dvd H.h hsp H.hl.one_lt.le (H.idx hsp hsN hsq)
    have htR : t ∣ ∑ i ∈ Finset.range l, s ^ i :=
      Nat.dvd_of_mod_eq_zero (by rw [← gm_eq]; exact hgm)
    exact dvd_of_dvd_two_mul ht ht2 (htR.trans (hrow.1.trans hrow.2))
  · cases hqs : qs with
    | none => rw [hqs] at hd; simp [qdvd] at hd
    | some Q =>
      rw [hqs] at hd
      simp only [qdvd, beq_iff_eq] at hd
      rw [hI.1 Q hqs] at hd
      exact dvd_of_dvd_special_succ H.h H.hq H.hodd ht ht2 (Nat.dvd_of_mod_eq_zero hd)

theorem neR_sound (H : Hyp N q l M) {qs : Option ℕ} (hI : ∀ Q, qs = some Q → Q = q) {t : ℕ}
    (hn : neR qs t = true) : t ≠ q := by
  have hq4 := (special_mod_four H.h H.hq H.hodd).1
  simp only [neR, Bool.or_eq_true, beq_iff_eq] at hn
  rcases hn with hn | hn
  · rintro rfl
    omega
  · cases hqs : qs with
    | none => rw [hqs] at hn; simp [qne] at hn
    | some Q =>
      rw [hqs] at hn
      simp only [qne, bne_iff_ne, ne_eq] at hn
      rw [← hI Q hqs]
      exact hn

theorem chk_sound (H : Hyp N q l M) {pc : List (ℕ × ℕ × List ℕ)}
    (hpc : Pratt.check pc = true) (tr : Tree) :
    ∀ (qs : Option ℕ) (par : List ℕ), Inv N q qs par → chk l pc qs par tr = true →
      4 ≤ M.card := by
  induction tr with
  | leaf imps items => exact fun qs par hI hc => leafOK_sound H hpc hI hc
  | add t k ih =>
    intro qs par hI hc
    simp only [chk, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hp, hd⟩, hn⟩, hk⟩ := hc
    have htp := isPr_sound hpc hp
    refine ih qs (t :: par) ⟨hI.1, fun p hp' => ?_⟩ hk
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact ⟨htp, dvdR_sound H hI htp hd, neR_sound H hI.1 hn⟩
    · exact hI.2 p hp'
  | split t y n ihy ihn =>
    intro qs par hI hc
    simp only [chk, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hp, hd⟩, hy⟩, hn⟩ := hc
    have htp := isPr_sound hpc hp
    by_cases htq : t = q
    · exact ihy (some t) par ⟨fun Q hQ => (Option.some.inj hQ).symm.trans htq, hI.2⟩ hy
    · refine ihn qs (t :: par) ⟨hI.1, fun p hp' => ?_⟩ hn
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact ⟨htp, dvdR_sound H hI htp hd, htq⟩
      · exact hI.2 p hp'

end Sound2

/-- **Soundness of a tree certificate.** Let `N` be an odd perfect number with special prime
`q`, `l` an odd prime dividing `e_p + 1` for every prime factor `p ≠ q`, `M` a finite set such
that every prime factor `p ≠ q` outside `M` has a row that is a prime power, and `s` an
ordinary prime factor of `N`. An accepted certificate for `(l, s)` gives `4 ≤ M.card`. -/
theorem checkTree_sound {l s : ℕ} {pc : List (ℕ × ℕ × List ℕ)} {tr : Tree}
    (hc : checkTree l pc s tr = true) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w)
    (hs : s.Prime) (hsN : s ∣ N) (hsq : s ≠ q) : 4 ≤ M.card := by
  simp only [checkTree, Bool.and_eq_true] at hc
  have H : Hyp N q l M := ⟨h, hq, hodd, hl, hl2, hidx, hM, dvd_of_dvd_succ h hq hodd hl hl2 hidx⟩
  exact chk_sound H hc.1 tr none [s] ⟨by simp, by simpa using ⟨hs, hsN, hsq⟩⟩ hc.2

/-- A table of certificates: for each entry `(l, T3, T5)` the trees for the seeds `3` and `5`
share the Pratt list `pc`. -/
def tableOK (pc : List (ℕ × ℕ × List ℕ)) (tab : List (ℕ × Tree × Tree)) : Bool :=
  tab.all fun e => checkTree e.1 pc 3 e.2.1 && checkTree e.1 pc 5 e.2.2

theorem tableOK_nil (pc : List (ℕ × ℕ × List ℕ)) : tableOK pc [] = true := rfl

theorem tableOK_cons {pc : List (ℕ × ℕ × List ℕ)} {e : ℕ × Tree × Tree}
    {tab : List (ℕ × Tree × Tree)} (h1 : tableOK pc [e] = true) (h2 : tableOK pc tab = true) :
    tableOK pc (e :: tab) = true := by
  simp only [tableOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h1 h2 ⊢
  exact ⟨h1, h2⟩

/-- **Soundness of a table.** For a length `l` listed in an accepted table, `4 ≤ M.card`
whenever `3 ∣ N`, or `5 ∣ N` with `5 ≠ q`. -/
theorem tableOK_sound {pc : List (ℕ × ℕ × List ℕ)} {tab : List (ℕ × Tree × Tree)}
    (htab : tableOK pc tab = true) {l : ℕ} (hmem : l ∈ tab.map Prod.fst) {N q : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hl2 : l ≠ 2) (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w)
    (hseed : 3 ∣ N ∨ (5 ∣ N ∧ 5 ≠ q)) : 4 ≤ M.card := by
  obtain ⟨⟨l', T3, T5⟩, he, rfl⟩ := List.mem_map.mp hmem
  have hc := List.all_eq_true.mp htab _ he
  simp only [Bool.and_eq_true] at hc
  rcases hseed with h3 | ⟨h5, h5q⟩
  · have hq4 := (special_mod_four h hq hodd).1
    exact checkTree_sound hc.1 h hq hodd hl hl2 hidx M hM Nat.prime_three h3
      (by rintro rfl; omega)
  · exact checkTree_sound hc.2 h hq hodd hl hl2 hidx M hM Nat.prime_five h5 h5q

/-- Converse of trial division. -/
theorem trialPrime_of_prime {n : ℕ} (hn : n.Prime) : trialPrime n = true := by
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range'_1, bne_iff_ne, ne_eq]
  refine ⟨hn.two_le, fun d hd h0 => ?_⟩
  have := hn.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h0)
  omega

end OddPerfect.ImpTree

#print axioms OddPerfect.ImpTree.gsum_eq
#print axioms OddPerfect.ImpTree.isPr_sound
#print axioms OddPerfect.ImpTree.row_dvd
#print axioms OddPerfect.ImpTree.dvd_of_dvd_special_succ
#print axioms OddPerfect.ImpTree.Hyp.row_prime
#print axioms OddPerfect.ImpTree.Hyp.impure_of_mod_one
#print axioms OddPerfect.ImpTree.Hyp.impure_of_two
#print axioms OddPerfect.ImpTree.dvd_of_dvd_two_mul
#print axioms OddPerfect.ImpTree.Hyp.idx
#print axioms OddPerfect.ImpTree.Hyp.mem
#print axioms OddPerfect.ImpTree.Item.ok_spec
#print axioms OddPerfect.ImpTree.dvdR_sound
#print axioms OddPerfect.ImpTree.neR_sound
#print axioms OddPerfect.ImpTree.tableOK_nil
#print axioms OddPerfect.ImpTree.walk_spec
#print axioms OddPerfect.ImpTree.leafOK_sound
#print axioms OddPerfect.ImpTree.chk_sound
#print axioms OddPerfect.ImpTree.checkTree_sound
#print axioms OddPerfect.ImpTree.tableOK_cons
#print axioms OddPerfect.ImpTree.tableOK_sound
#print axioms OddPerfect.ImpTree.trialPrime_of_prime
