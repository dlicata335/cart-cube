{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; Level; _⊔_)

open import Lib
open import Kan
open import Interval
open import Cofibs
open import Path
open import Pi
open import Sigma

module Equiv where

  isEquiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) → Set (l1 ⊔ l2)
  isEquiv A B f = (b : B) → Contractible (HFiber f b)

  Equiv : {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
  Equiv A B = Σ \ (f : A → B) → isEquiv A B f

  comisEquiv : {l1 l2 l3 : Level} {Γ : Set l3} (A : Γ → Set l1) (B : Γ → Set l2) (f : (γ : Γ) → A γ → B γ) 
             → relCom A
             → relCom B
             → relCom (\ γ → isEquiv (A γ) (B γ) (f γ))
  comisEquiv A B f comA comB = 
    comΠ {A = B} {B = \ (p : Σ B) → Contractible (HFiber (f (fst p)) (snd p))} 
         comB 
         (comContractible (\ (p : Σ B) → (HFiber (f (fst p)) (snd p))) (comHFiber A B f comA comB)) 

  abstract
    id-Equiv : ∀ {l} {A : Set l} → hasHCom A → isEquiv A A (\ x → x)
    id-Equiv hcomA = λ a → (a , (\ _ → a) , id , id) , (\ hf → snd (scontr hcomA a) hf )

  coe-rr-equiv : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
            → (comA : relCom A) → (r : I)
            → (p : I → Γ) → isEquiv _ _ (\ b → fst (relCom-relCoe A comA p r r b))
  coe-rr-equiv {Γ = Γ} A comA r p = transport (λ h → isEquiv _ _ h) (λ= \ b → (snd (relCom-relCoe A comA p r r b)) id ) (id-Equiv (relCom-hasHCom A comA (p r))) 
  
  abstract
    coe-equiv : ∀ {l1 l2} {Γ : Set l1} {A : Γ → Set l2} 
              → (comA : relCom A) → (r r' : I)
              → (p : I → Γ) 
              → isEquiv (A (p r)) (A (p r')) (\ b → fst (relCom-relCoe A comA p r r' b)) 
                 [ r == r' ↦ ( \ r=r' → ⇒ (coe-rr-equiv A comA r p) r=r')  ]
    coe-equiv {Γ = Γ}{A} comA r r' p = (coeIsEquivA r r' (coe-rr-equiv A comA r p)) where
  
      coeA = \ r r' b → fst (relCom-relCoe A comA p r r' b)
      hcomA = relCom-hasHCom A comA
  
      coeIsEquivA : hasCoe (\ (x : I) → isEquiv (A (p r)) (A (p x)) (coeA r x))
      coeIsEquivA = relCom-relCoe (λ (x : I) → isEquiv (A (p r)) (A (p x)) (coeA r x))
                      (comisEquiv (λ _ → A (p r)) (A o p) (coeA r) (comPre (\ _ → p r) A comA) (comPre p A comA)) (\ x → x)

