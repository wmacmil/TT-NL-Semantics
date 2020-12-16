module toy where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


open import Data.List
open import Data.Sum using (_⊎_ ; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
-- open import Data.Product using (_×_; _,_)
open import Data.Unit
open import Data.Empty

binRel : Set → Set → Set₁
binRel A B = A → B → Set

record CFG : Set₁ where
  field
    V : Set -- non-terminal, or variable
    Σ' : Set -- terminals
    R : binRel V (List (V ⊎ Σ'))-- rules
    S : V -- start symbol

module ManyStep where
  open CFG

  rule : CFG → Set
  rule cfg = List (V cfg ⊎ Σ' cfg)

  data ↦* (cfg : CFG) : rule cfg → rule cfg → Set where
    refl' : {r : (rule cfg)} → ↦* cfg r r --∀ {σ : Σ' cfg} → {!!}
    trans' : {r1 r2 r3 : (rule cfg)} {v : V cfg} {X : (rule cfg)} → R cfg v X
            → ↦* cfg r1 (r2 ++ (inj₁ v) ∷ r3)
            → ↦* cfg r1 (r2 ++ X ++ r3)

  derives : (cfg : CFG) → rule cfg → Set
  derives cfg x = ↦* cfg (inj₁ (S cfg) ∷ []) x

  generates : (cfg : CFG) → List (Σ' cfg) → Set
  generates cfg xs = derives cfg (map inj₂ xs)

open ManyStep public

data V0 : Set where
  A0 : V0
  B0 : V0

data Σ0 : Set where
  a0 : Σ0
  a1 : Σ0
  a# : Σ0

data _⟶_ : V0 → List (V0 ⊎ Σ0) → Set where
  r0 : A0 ⟶ (inj₂ a0 ∷ inj₁ A0 ∷ inj₂ a1 ∷ [])
  r1 : A0 ⟶ (inj₁ B0 ∷ [])
  r2 : B0 ⟶ (inj₂ a# ∷ [])

Sipser1 : CFG
Sipser1 = record { V = V0 ; Σ' = Σ0 ; R = _⟶_ ; S = A0 }

-- ex : 3 ∷ [] ≡ [] ++ 3 ∷ []
-- ex = refl


×comm : {A B : Set} → A × B → B × A
×comm {A} {B} (fst , snd) = lemma1 , lemma0
  where
    lemma0 : A
    lemma0 = fst
    lemma1 : B
    lemma1 = snd

×comm' : {A B : Set} → A × B → B × A
×comm' {A} {B} x = lemma1 , lemma0
  where
    lemma0 : A
    lemma0 = proj₁ x
    lemma1 : B
    lemma1 = proj₂ x


-- SipserExample1 : generates Sipser1 (a0 ∷ a# ∷ a1 ∷ [])
SipserExample1 : generates Sipser1 (a# ∷ [])
SipserExample1 = trans' {r2 = []} {r3 = []} r2 (trans' {r2 = []} {r3 = []} r1 refl') -- trans' {r2 = {!!}} r1 (trans' {r2 = {![]!}} {r3 = []} r2 refl') -- trans {r3 = inj₂ a1 ∷ []} r1 refl 


SipserExample2 : generates Sipser1 (a0 ∷ a# ∷ a1 ∷ [])
SipserExample2 = trans' {r2 = inj₂ a0 ∷ []} {r3 = inj₂ a1 ∷ []} r2 (trans' {r2 = inj₂ a0 ∷ []} {r3 = inj₂ a1 ∷ []} r1 (trans' {r2 = []} {r3 = []} r0 refl'))

SipserExample3 : generates Sipser1 (a0 ∷ a0 ∷ a# ∷ a1 ∷ a1 ∷ [])
SipserExample3 = trans' {r2 = inj₂ a0 ∷ inj₂ a0 ∷ []} {r3 = inj₂ a1 ∷ inj₂ a1 ∷ []} r2
                 (trans' {r2 = inj₂ a0 ∷ inj₂ a0 ∷ []} {r3 = inj₂ a1 ∷ inj₂ a1 ∷ []} r1
                 (trans' {r2 = inj₂ a0 ∷ []} {r3 = inj₂ a1 ∷ []} r0
                 (trans' {r2 = []} {r3 = []} r0 refl')))
-- {r2 = {!(inj₂ a0) ∷ []!}}
