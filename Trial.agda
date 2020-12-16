-- {-# OPTIONS --subtyping #-}


module Trial where

open import Data.Product using (Σ; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)

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

-- coercions
postulate
  ao : animal → object
  ha : human → animal
  mh : man → human
  dh : delegate → human
  so : survey → object

c1 : man → animal
c1 x = ha (mh x)


walk|ₘ : man → Set
walk|ₘ m1 = walk (c1 m1)

johnWalks : Set
johnWalks = walk|ₘ john

thm1 : all man walk|ₘ → johnWalks
thm1 allMenWalk = allMenWalk john

-- thm1 : all man (λ x → walk (ha (mh x))) → walk (ha (mh john))
-- thm1 : all man (λ man₀ → walk|ₘ man₀) → johnWalks

thm2 : johnWalks → some man walk|ₘ
thm2 johnWalks = john , johnWalks

postulate
  irish : object → Set
  ADV : (A : CN) (v : A → Set) → Σ[ p ∈ (A → Set) ] ((x : A) → p x → v x)
  finish : object → human → Set
  ontime1 : (A : CN) → (A → Set) → (A → Set)
  the : (A : CN) →  A
  -- finish : object → human → Set

-- a : proj₁ ADV

-- Record irishdelegate : CN := mkIrishdelegate { c :> delegate; _ : irish c }.

dobj : delegate → object
dobj del = ao (ha (dh del))

record irishdelegate : CN where
  constructor 
    mkIrishdelegate 
  field
    c : delegate
    ic : irish (dobj c)

-- fracas-055	answer: yes
-- P1	Some Irish delegates finished the survey on time.
-- Q 	Did any delegates finish the survey on time?
-- H 	Some delegates finished the survey on time. 

-- Theorem IRISH:
--   (some irishdelegate)(on_time1 human(finish(the survey)))
-- ->(some delegate)(on_time1 human(finish(the survey))). (**AUTOa x x x.*)

fc55 :
  -- some irishdelegate {!ontime1 delegate!} 
  some irishdelegate (ontime1 irishdelegate λ x → finish (so (the survey)) (dh (irishdelegate.c x)))
  → some delegate (ontime1 delegate λ x → finish (so (the survey)) (dh x))
fc55 (fst , snd) = irishdelegate.c fst , {!snd!}

-- Goal: ontime1 delegate (λ x → finish (so (the survey)) (dh x))
-- (irishdelegate.c fst)
-- ————————————————————————————————————————————————————————————
-- snd : ontime1 irishdelegate
-- (λ x → finish (so (the survey)) (dh (irishdelegate.c x))) fst
-- fst : irishdelegate

-- on_time : (A : CN) (v : A → Set) → (A → Set)
-- on_time A v = proj₁ (ADV A v)

  -- Parameter ADV: forall (A : CN) (v : A -> Prop),sigT  (fun p : A -> Prop =>
  -- forall x : A, p x -> v x).
  -- Definition on_time:= fun A:CN=> fun v:A->Prop=> projT1 (ADV(v)).

-- no:= fun A:CN=> fun P:A->Prop=> forall x:A, not(P(x)).


