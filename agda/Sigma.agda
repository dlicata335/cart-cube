{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Kan

module Sigma where

  comΣ : ∀ {l1 l2 l3 : Level} {Γ : Set l1} {A : Γ → Set l2} {B : Σ A → Set l3} → relCom A → relCom B → relCom (\ γ → Σ \ (x : A γ) → B (γ , x))
  comΣ {B = B} comA comB γ r r' α t b = ((fst (filla b r')) , fst (comb b)) , 
                                        (\ pα → pair= (fst (snd (filla b r')) pα) (fst (snd (comb b)) pα)) ,
                                        ((\ {id → pair= (snd (snd (filla b r')) id) (snd (snd (comb b)) id)})) where

    filla : (b : _) (z : I) → _
    filla b z = (comA γ r z α (\ pα z → fst (t pα z)) (fst (fst b) , (\ pα → ap fst (snd b pα))))

    comb : (b : _) → _
    comb b = 
      (comB (\ z → γ z , (fst (filla b z)))
            r r' 
            α (\ z pα →  transport (B o \ h → (γ z , h)) (fst (snd (filla b z)) pα) (snd (t z pα)) )
            (transport (B o \ h → (γ r , h)) (snd (snd (filla b r)) id) (snd (fst b)) , 
             (\ pα → ap (transport (B o (λ h → γ r , h)) (snd (snd (filla b r)) id)) (apd snd (snd b pα) ∘ ! (ap= (transport-ap-assoc' (λ z → B (γ r , z)) fst (snd b pα))) ) ∘ ap= (transport-∘ (B o (λ h → γ r , h)) (snd (snd (filla b r)) id) (ap fst (snd b pα))) ∘ ap {M = (fst (snd (filla b r)) pα)} {N = (snd (snd (filla b r)) id ∘ ap fst (snd b pα))} (\ h → transport (B o (λ h → γ r , h)) h (snd (t r pα))) uip)))

  comΣcoherent : ∀ {l1 l2 l3} {Δ : Set l1} {Γ : Set l2} {θ : Δ → Γ} {A : Γ → Set l3} {B : Σ A → Set l3}
               → (comA : relCom A) (comB : relCom B)
               → comPre θ (\ γ → Σ \ (x : A γ) → B (γ , x)) (comΣ {_}{_}{_} {_} {A} {B} comA comB) == 
                  comΣ {_} {_}{_}{_} {A o θ} {\ γ → B (θ (fst γ) , snd γ)} 
                      (comPre θ A comA) (comPre ( \ p → θ (fst p) , snd p) B comB) 
  comΣcoherent {θ = θ} {A = A} {B = B} comA comB = 
    relCom= ((\ γ → Σ \ (x : A γ) → B (γ , x)) o θ) _ _ 
              (\ p r r' α {{ cα }} t b → id)
