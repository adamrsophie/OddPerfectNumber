import OddPerfect.EqualExponentsBound
import OddPerfect.UpperBound

/-!
# A common prime divisor of the ordinary indices: the number of prime factors

Let `l` be an odd prime and `N` an odd perfect number with special prime `q` such that `l`
divides every ordinary index `e_p + 1` (`p ≠ q`); the indices may have arbitrary other factors.

* `card_primeFactors_le_sum_of_common_index`: `ω(N) ≤ 1 + Σ_{r ∣ N, r ≡ 1 (mod l)} e_r`. For an
  ordinary prime `p` the cyclotomic value `Φ_l(p)` divides `σ(p ^ e_p)`, and Bang's theorem
  (`exists_prime_dvd_sigma_orderOf_eq`) gives a prime `r ∣ σ(p ^ e_p)` with `r ≡ 1 (mod l)`;
  `r ∣ N` and `r ≠ p`. The prime `r` receives from at most `e_r` senders (`card_feeders_le`,
  the exact ledger at `r`). No condition on `q` is needed here.
* `card_primeFactors_le_of_common_index`: if moreover `q ≢ 1 (mod l)`, `e_l ≤ E` and
  `e_r ≤ E` for every prime factor `r ≡ 1 (mod l)`, then `ω(N) ≤ E ^ 2 + 1`. Every prime
  factor `r ≡ 1 (mod l)` is ordinary, so `l ∣ e_r + 1` and `r` contributes at least one factor
  `l` to `σ(N)` (`sum_padicValNat_succ_le`); there are at most `e_l ≤ E` of them.
* `lt_two_pow_four_pow_of_common_index`: then `N < 2 ^ (4 ^ (E ^ 2 + 1))`.

These results bound `ω(N)` and exclude nothing. The case `q ≡ 1 (mod l)` is open here: the
ordinary primes whose value `Φ_l(p)` is a power of `q` escape the capped count, and a bound for
them is known only through S-unit theorems, which are not in the library. For `l = 3` and
`l = 5` the family is empty by the Main Theorem of Fletcher, Nielsen and Ochem (Math. Comp. 81
(2012)) together with Kanold's theorem (`OddPerfect.dvd_of_dvd_succ`); this library proves only
instances of the common `5` case by kernel certificates (`OddPerfect/CommonFamily.lean` and
the modules for the common `55`, `65`, `85`, `95` and `115` families). Whether the present
bounds are new was not verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open Classical in
/-- Weighted form. If the odd prime `l` divides `e_p + 1` for every prime factor `p ≠ q` of the
odd perfect number `N`, then `N` has at most `1 + Σ e_r` distinct prime factors, the sum over
the prime factors `r ≡ 1 (mod l)`: each `p ≠ q` sends a prime `r ≡ 1 (mod l)` (Bang), and `r`
receives from at most `e_r` primes. No hypothesis on `q` is used. -/
theorem card_primeFactors_le_sum_of_common_index {N q l : ℕ} (h : OddPerfect N)
    (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) :
    N.primeFactors.card ≤
      1 + ∑ r ∈ N.primeFactors.filter (fun r => r % l = 1), N.factorization r := by
  have hN0 := h.ne_zero
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hpf2 : ∀ p ∈ N.primeFactors, p ≠ 2 := fun p hp h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)
  set G := N.primeFactors.filter (fun r => r % l = 1) with hG
  set A : ℕ → Finset ℕ := fun s =>
    (N.primeFactors.erase s).filter (fun p => s ∣ σ 1 (p ^ N.factorization p)) with hA
  have hcover : N.primeFactors.erase q ⊆ G.biUnion A := by
    intro p hp
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hp3 : 3 ≤ p := by have := hpp.two_le; have := hpf2 p hpN; omega
    obtain ⟨t, ht, htd, -, htm⟩ :=
      exists_prime_dvd_sigma_orderOf_eq hpp hp3 hl3 (hidx p hpN hpq)
    have ht2 : t ≠ 2 := by rintro rfl; rw [Nat.mod_eq_of_lt (by omega)] at htm; omega
    have htN := OPNStarter.force_prime h.perfect hpp rfl ht ht2 htd
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨ht, htN, hN0⟩, htm⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨(prime_dvd_sigma_prime_pow hpp ht htd).1.symm, hpN⟩, htd⟩⟩
  have hAle : ∀ s ∈ G, (A s).card ≤ N.factorization s := fun s hs => by
    have hsN := (Finset.mem_filter.mp hs).1
    exact card_feeders_le h.perfect (Nat.prime_of_mem_primeFactors hsN) (hpf2 s hsN)
  have h1 := Finset.pred_card_le_card_erase (s := N.primeFactors) (a := q)
  have h2 : (N.primeFactors.erase q).card ≤ ∑ s ∈ G, N.factorization s :=
    calc (N.primeFactors.erase q).card ≤ (G.biUnion A).card := Finset.card_le_card hcover
      _ ≤ ∑ s ∈ G, (A s).card := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum hAle
  omega

open Classical in
/-- Capped form. If the odd prime `l` divides `e_p + 1` for every prime factor `p ≠ q` of the
odd perfect number `N`, `q ≢ 1 (mod l)`, `e_l ≤ E`, and `e_r ≤ E` for every prime factor
`r ≡ 1 (mod l)`, then `N` has at most `E ^ 2 + 1` distinct prime factors. There are at most
`e_l` prime factors `r ≡ 1 (mod l)`, each counted with weight `e_r` in the weighted form. -/
theorem card_primeFactors_le_of_common_index {N q l E : ℕ} (h : OddPerfect N)
    (hl : l.Prime) (hl2 : l ≠ 2) (hq1 : q % l ≠ 1)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (hEl : N.factorization l ≤ E)
    (hE : ∀ r ∈ N.primeFactors, r % l = 1 → N.factorization r ≤ E) :
    N.primeFactors.card ≤ E ^ 2 + 1 := by
  have : Fact l.Prime := ⟨hl⟩
  have hw := card_primeFactors_le_sum_of_common_index h hl hl2 hidx
  set G := N.primeFactors.filter (fun r => r % l = 1) with hG
  have hGle : G.card ≤ E := by
    rw [Finset.card_eq_sum_ones]
    calc ∑ p ∈ G, 1 ≤ ∑ p ∈ G, padicValNat l (N.factorization p + 1) :=
          Finset.sum_le_sum fun p hp => by
            obtain ⟨hpN, h1⟩ := Finset.mem_filter.mp hp
            rw [Nat.padicValNat_def]
            exact one_le_padicValNat_of_dvd (by omega)
              (hidx p hpN (by rintro rfl; exact hq1 h1))
      _ ≤ N.factorization l := sum_padicValNat_succ_le h.perfect hl hl2
      _ ≤ E := hEl
  have hs : ∑ r ∈ G, N.factorization r ≤ G.card * E := by
    have := Finset.sum_le_card_nsmul G (fun r => N.factorization r) E fun r hr =>
      hE r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2
    rwa [smul_eq_mul] at this
  have hGE : G.card * E ≤ E * E := Nat.mul_le_mul_right E hGle
  have : E ^ 2 = E * E := by ring
  omega

/-- The size bound: under the hypotheses of `card_primeFactors_le_of_common_index`,
`N < 2 ^ (4 ^ (E ^ 2 + 1))` (Nielsen's bound `N < 2 ^ (4 ^ ω(N))`). -/
theorem lt_two_pow_four_pow_of_common_index {N q l E : ℕ} (h : OddPerfect N)
    (hl : l.Prime) (hl2 : l ≠ 2) (hq1 : q % l ≠ 1)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (hEl : N.factorization l ≤ E)
    (hE : ∀ r ∈ N.primeFactors, r % l = 1 → N.factorization r ≤ E) :
    N < 2 ^ (4 ^ (E ^ 2 + 1)) :=
  lt_of_lt_of_le (lt_two_pow_four_pow h)
    (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num)
      (card_primeFactors_le_of_common_index h hl hl2 hq1 hidx hEl hE)))

end OddPerfect

#print axioms OddPerfect.card_primeFactors_le_sum_of_common_index
#print axioms OddPerfect.card_primeFactors_le_of_common_index
#print axioms OddPerfect.lt_two_pow_four_pow_of_common_index
