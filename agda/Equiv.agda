{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; Level; _⊔_)

open import Lib
open import Kan
open import Interval
open import Prop
open import Cofibs
open import Path
open import Contractible
import ComInternal

module Equiv where

  -- normal definition

  isEquiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) → Set (l1 ⊔ l2)
  isEquiv A B f = (b : B) → Contractible (HFiber f b)

  Equiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
  Equiv A B = Σ \ (f : A → B) → isEquiv A B f

  id-Equiv : ∀ {l} {A : Set l} → hasHCom A → isEquiv A A (\ x → x)
  id-Equiv hcomA = λ a → (a , (\ _ → a) , id , id) , (s a) where
    abstract
      s = \ a → (\ hf → snd (scontr hcomA a) hf )

  QEquiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
  QEquiv A B = Σ \ (f : A → B) → Σ \ (g : B → A) → ((x : A) → Path A ((g o f) x) x) × ((y : B) → Path B ((f o g) y) y)

  -- ----------------------------------------------------------------------
  -- other definitions of equivalence

  -- flip orientation of path

  isEquiv' : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) → Set (l1 ⊔ l2)
  isEquiv' A B f = (b : B) → Contractible (HFiber' f b)


  -- filling instead of normal def of contractibility

  isEquivFill : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) → Set (ℓ₁ ⊔ l1 ⊔ l2)
  isEquivFill A B f = (b : B) → ContractibleFill (HFiber f b)

  isEquiv-isEquivFill : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) → isEquiv A B f → ((b : B) → hasHCom (HFiber f b)) → isEquivFill A B f
  isEquiv-isEquivFill A B f e hcomHFB b = contr-extend-partial (hcomHFB b) (e b)

  EquivFill : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set _
  EquivFill A B = Σ \ (f : A → B) → isEquivFill A B f

  -- ----------------------------------------------------------------------

  isEquivFill-hprop : {l1 l2 : Level} → (A : Set l1) (B : Set l2) (f : A → B) 
                → (e1 e2 : isEquivFill A B f)
                → Path (isEquivFill A B f) e1 e2
  isEquivFill-hprop A B f e1 e2 = (\ z → \ b → fst (ContractibleFill-hprop _ (e1 b) (e2 b)) z) ,
                                  (λ= \ b → fst (snd (ContractibleFill-hprop (HFiber f b) (e1 b) (e2 b)))) ,
                                  (λ= \ b → snd (snd (ContractibleFill-hprop (HFiber f b) (e1 b) (e2 b))))

  fix-isEquiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) 
              → (isEquivFill A B f)
              → ContractibleFill (isEquivFill A B f)
  fix-isEquiv A B f b = inhabited-hprop-contractible _ (ComInternal.hcomΠ _ _ (\ x → hcomContractibleFill _)) b (isEquivFill-hprop A B f)

  abstract
    idEquiv-from-= : ∀ {l}{A B : Set l}(comA : hasHCom A)(f : A → B)(eq : A == B) → f == coe (ap (λ X → (A → X)) eq) (λ x → x) → isEquiv A B f
    idEquiv-from-= comA f id id a = scontr comA a


  
