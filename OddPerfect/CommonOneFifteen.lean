import OddPerfect.CommonOneFifteenPrime

/-!
# Common exponent families: the common `115` family

Let `N` be an odd perfect number with special prime `q`. A common `d` family means that `d`
divides `v_p(N) + 1` for every ordinary prime `p`. This file proves that the common `115`
family is impossible, with the table of `OddPerfect.CommonOneFifteenData`, the primality in
`OddPerfect.CommonOneFifteenPrime`, the reach and abundance checkers of
`OddPerfect.CommonFiveSeven`, and the reach checks with blocked sets of
`OddPerfect.CommonFastChecks`. Known: the statement follows from the Main Theorem of Fletcher,
Nielsen and Ochem (Math. Comp. 81, 2012) together with Kanold's theorem
(`OddPerfect.dvd_of_dvd_succ`); the proof here is an independent certificate checked by the kernel.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

/-- The divisibility checks of all rows. -/
theorem hrows115 : ∀ e ∈ nodes115.zip rows115, rowChk 115 nodes115 e = true := fun e he =>
  rowChk_of_rowChkP (K := 100) (parts := ndp115) (by decide) nd115_eq ndp115_lens
    (all_of_parts _ zp115_eq (by
    exact List.forall_mem_cons.mpr ⟨rows115_0, List.forall_mem_cons.mpr ⟨rows115_1,
      List.forall_mem_cons.mpr ⟨rows115_2, List.forall_mem_cons.mpr ⟨rows115_3,
      List.forall_mem_cons.mpr ⟨rows115_4, List.forall_mem_cons.mpr ⟨rows115_5,
      List.forall_mem_cons.mpr ⟨rows115_6, List.forall_mem_cons.mpr ⟨rows115_7,
      List.forall_mem_cons.mpr ⟨rows115_8, List.forall_mem_cons.mpr ⟨rows115_9,
      List.forall_mem_cons.mpr ⟨rows115_10, List.forall_mem_cons.mpr ⟨rows115_11,
      List.forall_mem_cons.mpr ⟨rows115_12, List.forall_mem_cons.mpr ⟨rows115_13,
      List.forall_mem_cons.mpr ⟨rows115_14, List.forall_mem_cons.mpr ⟨rows115_15,
      List.forall_mem_cons.mpr ⟨rows115_16, List.forall_mem_cons.mpr ⟨rows115_17,
      List.forall_mem_cons.mpr ⟨rows115_18, List.forall_mem_cons.mpr ⟨rows115_19,
      List.forall_mem_cons.mpr ⟨rows115_20, List.forall_mem_cons.mpr ⟨rows115_21,
      List.forall_mem_cons.mpr ⟨rows115_22, List.forall_mem_cons.mpr ⟨rows115_23,
      List.forall_mem_cons.mpr ⟨rows115_24, List.forall_mem_cons.mpr ⟨rows115_25,
      List.forall_mem_cons.mpr ⟨rows115_26, List.forall_mem_cons.mpr ⟨rows115_27,
      List.forall_mem_cons.mpr ⟨rows115_28, List.forall_mem_cons.mpr ⟨rows115_29,
      List.forall_mem_cons.mpr ⟨rows115_30, List.forall_mem_cons.mpr ⟨rows115_31,
      List.forall_mem_cons.mpr ⟨rows115_32, List.forall_mem_cons.mpr ⟨rows115_33,
      List.forall_mem_cons.mpr ⟨rows115_34, List.forall_mem_cons.mpr ⟨rows115_35,
      List.forall_mem_cons.mpr ⟨rows115_36, List.forall_mem_cons.mpr ⟨rows115_37,
      List.forall_mem_cons.mpr ⟨rows115_38, List.forall_mem_cons.mpr ⟨rows115_39, fun _ h =>
      absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩) e he)

/-- The blocked candidates. -/
def cand115 (b : ℕ) : Bool := b % 12 == 1

/-- Blocked set 0: the candidates whose residue modulo `4099` is a set bit of
the number below. -/
def blk115_0 (x : ℕ) : Bool :=
  cand115 x && Nat.testBit 8159350508051523518034133757752603799606710813667031808290430056963901483792053237888267635823587338393370063643528928899052503204091386491458666062935792627915434430222309660400019512334371665114442308589515903763740962606110294660879709601719195380422414711010370425353233747566143657862110747261994639538813175246450138776089212659696451267682539409257845290626952080086807218704204706088161817454397879555716905378650519016860797981628725473390009367948087087604668179815893389825886744291501560718151476298536566656444870338311407509848742721411677441553206108869252217782557724141617507259261407710463371498794923383254288563732191441387600299864485185409853179684665524580513974179058536827088586847400481704779340306078649875369790595204613604876665074109239989426495816073081077979368327861798549327420110080974505477361267424169736548327994080517208531829410183494042651433541823773001875709367809740501010897643172916022338275279837034960422474928845127519370305697970818820441692018890597000180780302140710214963328734953701857883598545881811911985779060778609825345411110200738935400825056829311511830021877136004746488731254662668045256648150408302747669609778408559281791142769599725118078016678730504576901790826496 (x % 4099)

/-- Blocked set 1: the candidates whose residue modulo `4099` is a set bit of
the number below. -/
def blk115_1 (x : ℕ) : Bool :=
  cand115 x && Nat.testBit 130548610176644063336704069159440716120283181193832695434249937524718606258333554651255343943653422656777568924262040967903522120580943601591636699903638086449340595765273802143254484633617684309841449346665201660698714585474929780629610328000701073054638360247429461929618194193396999681497353364416910701713418965876674642651013619354520507880164142766311462070916899894812586344730302445116318272926616168844136946203706199872213693522648221813770066550018222839244738481290825387564003838271301142008851805470659925998159858413652078691816799449471813586682993560126802956959539923287298281835150945796954304742488991576218574385420057647994278124519776285063003256806464978292924654832575181908446715940366146442856493502023989474084534139913855868115821961028859877669347642620261522691434178526440717258466676360229897880476883028412567411383238880098658717501023238666209176586996086046295624122290752391985186547226344130451118251429941057337612133858965390920618677777808204194505342378679317150929897017741639150803257715093035075263279453547721654545781045591675219369457610144509597304186090082260612639437797744962428367468342271495970377523175105503436456636283819553964538081767887833229849401115394533739664032940032 (x % 4099)

/-- Blocked set 2: the candidates whose residue modulo `4099` is a set bit of
the number below. -/
def blk115_2 (x : ℕ) : Bool :=
  cand115 x && Nat.testBit 178649967737238950201116478638491593054746561477789457584212756331182545891159317793774183999624162361818788365161771267396489144109924516824947974041148003456474394624814139610884890697466774503066238724530425322182852303479677390107945641574363907135865299758275070055736126871064242974368639229623256140729850470672702508335487007023739342352893655294635033548283596304649141627875665663510709424485007506871621250984868401379676340447640780986279896808361194524700377845031013434647516684775308042170502231232012261690304356434978275670475087385588288274820009742586962044836811842368200415417666097796865200458069513609023464694114052163169607261468702607266565359670169918622602263746944304304114948105602151271678270680069681181614075553851405515909369859631034613524984442452528842550495425479711458542906384694651421708358623102633127122945790371439252525242975494042578288465527053516209240905127983158349795506100839226222078053084478746031645024774250783713564377161601849625196190070301951526018903366453748887484903167306048317149082310635731030413268129823668187705322795306407818547293551735565659582756786631695094356727632894023560024072692777383952626162726594412544 (x % 4099)

/-- Blocked set 3: the candidates whose residue modulo `4099` is a set bit of
the number below. -/
def blk115_3 (x : ℕ) : Bool :=
  cand115 x && Nat.testBit 10155074945409931597087536666466950317826036491777175760353782554734306101446538171059699551044822098344678141735439979187817331282032780311838364869842838448535405738075826739820401531065545096562940075297889047116923947303735193958439716886959027496846353267315070859165411499130895640821930526516372745020031899837277402191709574236448175591237693361010192241544927183357950761226913410195123803281809437769205663383570207231563813010745384897855051115977242528503655504934888438645227135226038146394343295820704003502927604514038114401404706102451555429826829192811292884691887344505185434138723979090740893784669961682497237352720484824213763560152221912652044522018236390011684163051284784219690252280752978904546322126064327327865806983490099877017275025703968660674660504271078561188042272969788901524653486829055965516242000032378082232309979193906909741189008711844697864241161215757507737871172455000337297294262274163752172598449413750633403544232483096988529533337854235731172282871832569153329376735407122611650350594014158593289758042968240523896707967192979651817334188032942652529460488548783953678741715684155785204548081358900054785964823353334924574720 (x % 4099)

/-- Reach check with the blocked set 0. -/
theorem reach115_0 : reachS nodes115 rows115 2 tm115 3 blk115_0 = true := by
  decide +kernel

/-- Reach check with the blocked set 1. -/
theorem reach115_1 : reachS nodes115 rows115 2 tm115 3 blk115_1 = true := by
  decide +kernel

/-- Reach check with the blocked set 2. -/
theorem reach115_2 : reachS nodes115 rows115 2 tm115 3 blk115_2 = true := by
  decide +kernel

/-- Reach check with the blocked set 3. -/
theorem reach115_3 : reachS nodes115 rows115 2 tm115 3 blk115_3 = true := by
  decide +kernel

/-- Reach check with no source blocked. -/
theorem reach115_none : reach nodes115 rows115 2 tm115 3 0 = true := by decide +kernel

/-- Every blocked candidate lies in one of the blocked sets. -/
theorem blk115_cover : (nodes115.take rows115.length).all
    (fun b => !cand115 b || [blk115_0, blk115_1, blk115_2, blk115_3].any fun f => f b) = true := by
  decide +kernel

/-- Every blocked source node passes the reach check. -/
theorem hcand115 : ∀ b ∈ nodes115.take rows115.length, cand115 b = true →
    reach nodes115 rows115 2 tm115 3 b = true :=
  hcand_of_groups [blk115_0, blk115_1, blk115_2, blk115_3] (by
    exact List.forall_mem_cons.mpr ⟨reach115_0, List.forall_mem_cons.mpr ⟨reach115_1,
      List.forall_mem_cons.mpr ⟨reach115_2, List.forall_mem_cons.mpr ⟨reach115_3, fun _ h =>
      absurd h List.not_mem_nil⟩⟩⟩⟩) blk115_cover

/-- Abundance: the target primes with fourth powers, and with any one of them `≡ 1 (mod 12)` to
the first power. -/
theorem ab115 : abOK2 vals115 (fun b : ℕ => b % 12 == 1) P115 G115 = true := by decide +kernel

end FamInst

open FamInst in
/-- The common `115` family is impossible. Let `N` be an odd perfect number with special prime
`q`. Then `115 ∣ v_p(N) + 1` cannot hold for every ordinary prime `p`. Here `5 ∣ N`,
`23 ∣ N` and `q ≡ 1 (mod 12)`; the forcing table from the seeds `5, 23` reaches all target primes whichever
source node `≡ 1 (mod 12)` is special, and they give an abundant divisor. Known: the statement
follows from the Main Theorem of Fletcher, Nielsen and Ochem (Math. Comp. 81, 2012) together with
Kanold's theorem (`OddPerfect.dvd_of_dvd_succ`); the proof here is an independent certificate
checked by the kernel. -/
theorem not_common_one_fifteen {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → 115 ∣ N.factorization p + 1) : False := by
  have hexp5 : ∀ p ∈ N.primeFactors, p ≠ q → 5 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 5 ∣ 115).trans (hexp p hp hpq)
  have hexp23 : ∀ p ∈ N.primeFactors, p ≠ q → 23 ∣ N.factorization p + 1 := fun p hp hpq =>
    (by norm_num : 23 ∣ 115).trans (hexp p hp hpq)
  have h5N := (five_dvd_and_ne_special_of_common h hq hodd hexp5).1
  have h23N := dvd_of_dvd_succ h hq hodd (by norm_num) (by norm_num) hexp23
  have hq12 := special_mod_twelve_of_common_five h hq hodd hexp5
  have hcq : cand115 q = true := by simp [cand115, hq12]
  have hcq' : (fun b : ℕ => b % 12 == 1) q = true := by simp [hq12]
  have hseed : ∀ t ∈ nodes115.take 2, t ∣ N := by
    intro t ht
    have : nodes115.take 2 = [5, 23] := by decide +kernel
    rw [this] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h5N
    · exact h23N
  exact false_of_reach h hexp (by norm_num) hcq hcq' nodes115_prime nodes115_ne2 hseed
    (by decide +kernel) hrows115 hcand115 reach115_none vals115_sel vals115_nodup PG115 ab115

/-- The ordinary exponents of an odd perfect number cannot all equal one `E` with
`115 ∣ E + 1`. -/
theorem not_all_exponents_eq_of_one_fifteen_dvd_succ {N q E : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hE : 115 ∣ E + 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = E) : False :=
  not_common_one_fifteen h hq hodd fun p hp hpq => hexp p hp hpq ▸ hE

end OddPerfect

#print axioms OddPerfect.FamInst.hrows115
#print axioms OddPerfect.FamInst.reach115_0
#print axioms OddPerfect.FamInst.reach115_1
#print axioms OddPerfect.FamInst.reach115_2
#print axioms OddPerfect.FamInst.reach115_3
#print axioms OddPerfect.FamInst.reach115_none
#print axioms OddPerfect.FamInst.blk115_cover
#print axioms OddPerfect.FamInst.hcand115
#print axioms OddPerfect.FamInst.ab115
#print axioms OddPerfect.not_common_one_fifteen
#print axioms OddPerfect.not_all_exponents_eq_of_one_fifteen_dvd_succ
