{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Kan

module Pi where

  -- ----------------------------------------------------------------------
  -- Pi types

  comΠ : ∀ {l1 l2 l3 : Level} {Γ : Set l1} {A : Γ → Set l2} {B : Σ A → Set l3} → relCom A → relCom B → relCom (\ γ → (x : A γ) → B (γ , x))
  comΠ {A = A} {B = B} comA comB γ r r' α t b = 
    (\ a' →  transport (\ h → B (γ r' , h)) (! (snd (fillback a' r') id))
             (fst (forward a'))  ) , 
    (λ pα → λ= \ a' →  ! (ap= (transport-ap-assoc' B (λ h → γ r' , h) (! (snd (fillback a' r') id)))) ∘ ap (transport B (ap (\ h → γ r' , h) (! (snd (fillback a' r') id)))) (fst (snd (forward a')) pα) ∘ ap= (transport-ap-assoc' B (λ h → γ r' , h) (! (snd (fillback a' r') id))) ∘ apd! (t r' pα) (snd (fillback a' r') id)) , 
    (λ {id → λ= \ a' → ! (ap= (transport-ap-assoc' B (λ h → γ r' , h) (! (snd (fillback a' r') id)))) ∘ ( ap (transport B (ap (λ h → γ r' , h) (! (snd (fillback a' r') id)))) (snd (snd (forward a')) id) ∘ ap= (transport-ap-assoc' B (λ h → γ r' , h) (! (snd (fillback a' r') id)))) ∘ apd! (fst b) (snd (fillback a' r) id)}) where
    
    fillback : (a' : _) (z : I) → _
    fillback a' z = relCom-relCoe A comA γ r' z a'
    
    forward : (a' : _) → _
    forward a' = 
      (comB (\ z → γ z , (fst (fillback a' z)))
            r r' 
            α (\ z pα → t z pα (fst (fillback a' z)))
            (fst b (fst (fillback a' r)) , 
             (\ pα → ap (\ f → f _) (snd b pα))))

  comΠcoherent : ∀ {l1 l2 l3} {Δ : Set l1} {Γ : Set l2} {θ : Δ → Γ} {A : Γ → Set l3} {B : Σ A → Set l3}
               → (comA : relCom A) (comB : relCom B)
               → comPre θ (\ γ → (x : A γ) → B (γ , x)) (comΠ {_}{_}{_} {_} {A} {B} comA comB) == 
                  comΠ {_} {_}{_}{_} {A o θ} {\ γ → B (θ (fst γ) , snd γ)} 
                      (comPre θ A comA) (comPre ( \ p → θ (fst p) , snd p) B comB) 
  comΠcoherent {θ = θ} {A = A} {B = B} comA comB = 
    relCom= ((\ γ → (x : A γ) → B (γ , x)) o θ) _ _ 
              (\ p r r' α {{ cα }} t b → λ= \ a' → id)

