-- {-# OPTIONS --subtyping #-}

module Trial where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
open import Data.Nat using (ℕ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

CN = Set

postulate
  bank manager accountant car meeting humantypes city nobel_prize distance mammal report student diamond delegate location time duration mouse survey swede scandinavian contract door window institution Phy Info factory woman man object president surgeon animal human : CN

postulate
  t0 t1 t2 t3 : time
  a_factory : factory
  birmingham : city
  chairman_of_itel : man
  cars : car
  surgeon1 : human -> Set
  scandinavian1 : object -> Set
  john : man
  walk : animal -> Set


some : (A : CN) → (P : A → Set) → Set
some A P = Σ[ x ∈ A ] P x 

all : (A : CN) → (P : A → Set) → Set
all A P = (x : A) → P x

record Coercion {a} (x y : Set a) : Set a where
  constructor ⌞_⌟
  field coe : x → y

open Coercion

_⊚_ : ∀ {a} {A B C : Set a} → Coercion A B → Coercion B C → Coercion A C
_⊚_ c d = ⌞ (λ x → coe d (coe c x)) ⌟

_$_ : ∀ {a b} {A A′ : Set a} {B : Set b} → (A → B) →
      {{c : Coercion A′ A }} → A′ → B
_$_ f {{c}} a = f (coe c a)

-- coercions
postulate
  ao : animal → object
  ha : human → animal
  mh : man → human
  dh : delegate → human
  so : survey → object

instance
  aoc = ⌞ ao ⌟
  hac = ⌞ ha ⌟
  mhc = ⌞ mh ⌟
  dhc = ⌞ dh ⌟
  soc = ⌞ so ⌟

  mac = mhc ⊚ hac
  hoc = hac ⊚ aoc
  doc = (dhc ⊚ hac) ⊚ aoc

manwalk : man → Set
manwalk m = walk $ m

humanwalk : human → Set
humanwalk h = walk $ h

johnwalk : Set
johnwalk = manwalk john

allmanwalk : Set
allmanwalk = all man manwalk

somemanwalk = some man manwalk
-- can we make man implicit?

thm1' : allmanwalk → johnwalk
thm1' x = x john

thm2' : johnwalk → somemanwalk
thm2' jw = john , jw

-- thm2 : johnWalks → some man walk|ₘ
-- thm3 : some human humanwalk → some animal walk 
-- thm3 : some human (λ h → walk $ h) → some animal walk 
thm3 : some human (λ h → walk $ h) → some animal walk
thm3 (fst , snd) = (ha fst) , snd

thm4 : some man (λ m → walk $ m) → some animal walk
thm4 (fst , snd) = ha (mh fst) , snd

postulate
  irish : object → Set
  finish : object → human → Set
  ontime1 : (A : CN) → (A → Set) → (A → Set)
  the : (A : CN) →  A

-- perhaps call isIrish
irishdel : delegate → Set
irishdel x = irish $ x

dobj : delegate → object
dobj del = ao (ha (dh del))

record irishdelegate : CN where
  constructor 
    mkIrishdelegate 
  field
    c : delegate
    ic : irishdel c

postulate
  idd : irishdelegate → delegate

instance
  iddc = ⌞ idd ⌟
  idh = iddc ⊚ dhc

finishobj : survey → human → Set
finishobj s = finish $ s

id2human : irishdelegate → human
id2human id = dh (idd id)

ts : survey
ts = the survey

fts' : human → Set
fts' = finishobj ts

sid : (irishdelegate → Set) → Set
sid = some irishdelegate

finishedTheSurveyOnTime : delegate → Set
finishedTheSurveyOnTime x = ontime1 human fts' $ x

finishedTheSurveyOnTime' : irishdelegate → Set
finishedTheSurveyOnTime' x = ontime1 human fts' $ x


someIRISHDELEGATEfinishedthesurveyontime : Set
someIRISHDELEGATEfinishedthesurveyontime = some irishdelegate finishedTheSurveyOnTime' -- λ x → finishedTheSurveyOnTime $ x

someDELEGATEfinishedthesurveyontime : Set
someDELEGATEfinishedthesurveyontime = some delegate finishedTheSurveyOnTime

fc55'' :
  someIRISHDELEGATEfinishedthesurveyontime → someDELEGATEfinishedthesurveyontime
  -- (some irishdelegate) (λ x → finishedTheSurveyOnTime (id2human x))
  -- → (some delegate) (λ x →  finishedTheSurveyOnTime (dh x))
fc55'' (irishDelegate , finishedOnTime) = (idd irishDelegate) , finishedOnTime



-- -- Definition Year:= nat.
-- -- Definition Month:= nat.
-- -- Definition Day:= nat.
-- -- Parameter default_y:Year.
-- -- Parameter default_m:Month.
-- -- Parameter default_d: Day.
-- -- Parameter DATE : Year -> Month -> Day -> time.
-- -- Let default_t:= DATE default_y default_m default_d.
-- -- Definition currently:=fun P : time -> Prop=>fun t:time=> P default_t.

-- Year = ℕ
-- Month = ℕ
-- Day = ℕ

-- postulate
--   defY : Year
--   defM : Month
--   defD : Day
--   DATE : Year → Month → Day → time
--   itel : human
--   have : object → human → time → Set
--   fo : factory → object

-- defaultTime = DATE defY defM defD

-- has1 : (x : object) (y : human) (t : time) → Set
-- has1 x y t = have x y t × t ≡ defaultTime

-- -- Definition has1:=fun (x : object)(y : human) (t : time)=>
-- -- have x y t /\ t = default_t.


-- -- Definition currently:=fun P : time -> Prop=>fun t:time=> P default_t.
-- currently : (P : time → Set) → (t : time) → Set
-- currently P t = P defaultTime

-- Currently : (has1 (fo a_factory) itel defaultTime) → currently (has1 (fo a_factory) itel) defaultTime
-- Currently (fst , snd) = fst , snd
-- -- (has1 (a_factory)itel) t-> currently (((has1 (a_factory)itel)))t.

-- -- investigate later
-- -- fc55 :
-- --   some irishdelegate (ontime1 irishdelegate λ x → finish (so (the survey)) (dh (idd x) ))
-- --   → some delegate (ontime1 delegate λ x → finish (so (the survey)) (dh x))
-- -- fc55 (fst , snd) = (idd fst) , {!!}



-- -- on_time : (A : CN) (v : A → Set) → (A → Set)
-- -- on_time A v = proj₁ (ADV A v)

--   -- Parameter ADV: forall (A : CN) (v : A -> Prop),sigT  (fun p : A -> Prop =>
--   -- forall x : A, p x -> v x).
--   -- Definition on_time:= fun A:CN=> fun v:A->Prop=> projT1 (ADV(v)).

-- -- no:= fun A:CN=> fun P:A->Prop=> forall x:A, not(P(x)).



-- -- Theorem IRISH:
-- --   (some irishdelegate)(on_time1 human(finish(the survey)))
-- -- ->(some delegate)(on_time1 human(finish(the survey))). (**AUTOa x x x.*)
