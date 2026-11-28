import OddPerfect.EqualExponentSupportIndex
import OddPerfect.SpecialPrime

/-!
# Equal exponents: the index prime 197 with a wider source bound

Let `N = q ^ a * m ^ 2` be an odd perfect number with special prime `q`, `q ∤ m`, and suppose
every ordinary exponent equals `l - 1` for an odd prime `l`. Write `J = eulerIndex q a m`.
`OddPerfect.EqualExponentSupportIndex` proves for `a ≤ 49` that `J` has at least six prime
factors, or `l = 179`, or `l = 197`; its certificates use the source bound `10 ^ 6`.

For `l = 197` and `a ≤ 49`, an Euler index with at most five prime factors forces the special
prime above `3 * 10 ^ 8` (`special_gt_of_small_eulerIndex`). With that source bound `l = 197`
has a certificate: the seed row `σ(197 ^ 196)` has the prime factors `111191923` and
`278022161`, and the cofactors of the three rows are pairwise coprime and not prime powers.
So:

* `six_le_card_primeFactors_eulerIndex_or_eq_of_special_le_forty_nine`: for `a ≤ 49`, `J` has
  at least six prime factors, or `l = 179` and `33 ≤ a` (the special exponent is `1` modulo
  `4`, and `a ≤ 29` is settled).
* `six_le_card_primeFactors_eulerIndex_of_special_le_forty_nine_of_ne`: for `a ≤ 49` and
  `l ≠ 179`, `J` has at least six prime factors.

The certificate comes from a search outside Lean; only the kernel check is trusted. The prime
`179` stays an explicit exception, and this module proves nothing about it: a search outside
Lean found no prime factor of its seed row below `2 * 10 ^ 9`, and larger source bounds, which
smaller special exponents allow, were not searched to the end. That is a limit of the search,
not a statement about `179`.

These are restricted results for the family where all ordinary exponents equal `l - 1`. The
family is not excluded; the special exponent and the number of prime factors of `J` are not
bounded here, and `l` is bounded only through that number. Restricted result; no published
source was checked; novelty not verified.
-/

namespace OddPerfect.EqSupport

open OddPerfect.EqCount (big witnessOK)

/-- The sources for `l = 197` with source bound `3 * 10 ^ 8`: pairs (new source, earlier
source whose row it divides). -/
def srcs197 : List (ℕ × ℕ) :=
  [(111191923, 197),
   (278022161, 197)]

/-- The pieces for `l = 197`: (source, divisor of its row, witness or `0`). -/
def pieces197 : List (ℕ × ℕ × ℕ) :=
  [(197, 111191923, 0),
   (197, 278022161, 0),
   (197,
    big [1688254152598499853153840452451573,
        13561265812444025571485886395210803028948195337707927320910184967665781970111545,
        51605956900692606869643054348953589192753074987942126543682914423267205204819356,
        92670176298857192166577742446603606225216304701568531885450854980928540974202649,
        4706526550315558830685685584727097548778456648477478945961977401990161304450115,
        1126354500323934733552862215993126297473346218037255115414320425467181511735247],
    2),
   (111191923,
    big [5443635612401778628451087671831727833298695003288720940,
        45745259889237600941718439962730356413589784182649742001257105070606945684979103,
        50794242441274108686466528625726885690673652844279583339754474305587391138129980,
        23053201024787476953309475788824894753920715933824837745285873935613141099930443,
        16520625911295840736185167000939278552270282233258752042362957165934423760846931,
        51344394403042048886539008800736803340866692039601297104424588891371578467264894,
        39211464449843481603224418554476469950294303249732654127105532183093030222151209,
        21883091439063246924626240898444901472477537119443699728918806483953911889115783,
        69969528179451720721516403247410813367891884610512071524239801874988170813109411,
        60159478825150827746825378740955232266344936474855971474360509540804628206541367,
        77128987148272977539617205991894036040053244093232585995121696888010191143161203,
        25486002309218914331020333153027249349259414256731262526945122713582409419804970,
        63337380325027282311248788621291116649039711694802004111432281257593354828642839,
        33723565981913786102404018961741085886066841672296091786076757473905186099164362,
        10687546090939635596118120459188391096146050387692492322794724776221530947885093,
        24810569734414548024391994629736176150450388555596928194335945281935449901527388,
        14539200142534216414884163133099010365459888933959148062570896206844935270048876,
        24230060726381867146462825346805566713438453340313069317466138112407365749945391,
        45431694759012866209052356137296608115430831030194020612521163122398661084590623,
        49642110788042796222090044837309587578025547958377781011777662038161588368886853],
    2),
   (278022161,
    big [55603106138212633792617625839264993790996010519611324,
        16170546769090792241986815779197919678479507510126353677404673868343605698817272,
        48354962495671843778201093965899179306501123862254049693756672384458354985982203,
        48942091827270925575388360502292578712391815939359313163825805621360481250027911,
        49948115550248228417970649933696230104107357103858705258524295952227227771511617,
        64941703957961790888196388325166758393690781514602848936895210912747512002591398,
        32391553436194444552798443376261009986786221521899023128650316289573240374208229,
        69248083814089369526976622144239404966572220779794169961726504355534674233093018,
        86914793724348257099636582149339491902894493006744383069555682625743679267857212,
        18745298683730260116868558935723235911992256778373871389326524657123236239829715,
        55699660215180222514306685748128344500084576215502010495271492720137907116185217,
        96910602873822409684264039495563288940133977554202924157600279923013405270742251,
        96673086149096087454900194607369340576897875548075337944883926854703173919003181,
        96990839274155453203040948460522470717303195056073365778751885607114830713311071,
        22529843085550103448560386320449141828131630033704341977783871972787755685914136,
        65376937179460685286781314171180690499075173171280093283455966692721654938210091,
        97638081566717173810894238393941404118857999803084868737573036763467257681091502,
        76023823670961753113270051988417655001469738931030458769736755653516208163725313,
        85504853798820466759274099507998363144293522200096425016496276652612624959392004,
        27267243123927633960509870765218018264385784280059432632566128174398995631186507,
        77627855388896933413318499780284028502612791552113346829407246767876683753883681],
    2)]

/-- The support certificate for `l = 197` with source bound `3 * 10 ^ 8` is accepted. -/
theorem check197 : supportCheck 197 (3 * 10 ^ 8) 7 srcs197 pieces197 = true := by
  decide +kernel

/-- Control: the certificate for `l = 197` without its last piece is rejected. -/
example : supportCheck 197 (3 * 10 ^ 8) 7 srcs197 pieces197.dropLast = false := by
  decide +kernel

/-- Control: with the source bound `10 ^ 6` the certificate for `l = 197` is rejected. -/
example : supportCheck 197 (10 ^ 6) 7 srcs197 pieces197 = false := by
  decide +kernel

/-- The geometric sum bound for the special prime at `l = 197`. -/
theorem geom_lt_wide :
    ∑ j ∈ Finset.range (49 + 1), (3 * 10 ^ 8) ^ j < (2 * 197 + 1) ^ (197 - 1) := by
  decide +kernel

end OddPerfect.EqSupport

namespace OddPerfect

/-- For special exponent `a ≤ 49` and equal ordinary exponents `l - 1` (`l` an odd prime), the
Euler index has at least six prime factors, or `l = 179` and `33 ≤ a`. The exception is left
open. Restricted result: the family is not excluded. Restricted result; no published source
was checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_or_eq_of_special_le_forty_nine {N q a m l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (ha : a ≤ 49)
    (hl : l.Prime) (hl2 : l ≠ 2)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card ∨ (l = 179 ∧ 33 ≤ a) := by
  by_cases hk : 6 ≤ (eulerIndex q a m).primeFactors.card
  · exact Or.inl hk
  have hk5 : (eulerIndex q a m).primeFactors.card ≤ 5 := by omega
  rcases six_le_card_primeFactors_eulerIndex_or_of_special_le_forty_nine h hq hN hqm ha hl hl2
    hexp with hk6 | hc | hc
  · exact Or.inl hk6
  · by_cases h29 : a ≤ 29
    · exact Or.inl (six_le_card_primeFactors_eulerIndex_of_special_le_twenty_nine h hq hN hqm
        h29 hl hl2 hexp)
    obtain ⟨-, hqa, hao, -⟩ := EqSupport.euler_frame h hq hN hqm
    have h4 := (special_mod_four h hq (hqa ▸ hao)).2
    rw [hqa] at h4
    exact Or.inr ⟨hc, by omega⟩
  · subst hc
    have hla : ¬ 197 ∣ a + 1 := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    have hBq : 3 * 10 ^ 8 < q := special_gt_of_small_eulerIndex (A := 49) (B := 3 * 10 ^ 8) h hq
      hN hqm hl hl2 hexp hla (by omega) ha EqSupport.geom_lt_wide
    exact (EqSupport.supportCheck_sound (k := 5) h hq hN hqm hl hl2 hexp hk5 hBq
      EqSupport.check197).elim

/-- For special exponent `a ≤ 49` and equal ordinary exponents `l - 1` with `l ≠ 179` an odd
prime, the Euler index has at least six prime factors. Restricted result: the number of prime
factors is not bounded and the family is not excluded. Restricted result; no published source
was checked; novelty not verified. -/
theorem six_le_card_primeFactors_eulerIndex_of_special_le_forty_nine_of_ne {N q a m l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ a * m ^ 2) (hqm : ¬ q ∣ m) (ha : a ≤ 49)
    (hl : l.Prime) (hl2 : l ≠ 2) (hl179 : l ≠ 179)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = l - 1) :
    6 ≤ (eulerIndex q a m).primeFactors.card := by
  rcases six_le_card_primeFactors_eulerIndex_or_eq_of_special_le_forty_nine h hq hN hqm ha hl
    hl2 hexp with hk | hc
  · exact hk
  · exact absurd hc.1 hl179

end OddPerfect

#print axioms OddPerfect.EqSupport.check197
#print axioms OddPerfect.EqSupport.geom_lt_wide
#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_or_eq_of_special_le_forty_nine
#print axioms OddPerfect.six_le_card_primeFactors_eulerIndex_of_special_le_forty_nine_of_ne
