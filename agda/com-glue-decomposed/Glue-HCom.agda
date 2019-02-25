{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Kan
open import Glue
open import Prop

module com-glue-decomposed.Glue-HCom where 

  abstract
    hcomGlue : ∀ {l} (α : Set)
            {{_ : Cofib α}}
            (T : α → Set l)
            (B : Set l)
            (f : (u : α) → T u → B)
            → ((u : α) → hasHCom (T u))
            → hasHCom B
            → hasHCom (Glue α T B f)
    hcomGlue α T B f hcomT hcomB s s' β u v-boundary = 
      glue α T B f 
          (\ pα → fst (t-fill pα s')) 
          (fst b0 , (\ pα →  fst (snd b0) (inr pα) )) , 
          ( (\ pβ → glue-cong α T B f _ _ ((λ= (\ pα → fst (snd (t-fill pα s')) pβ))) ((fst (snd b0) (inl pβ))) ∘ Glueη (u s' pβ)) ) , 
          (λ { id → glue-cong α T B f _ _ (λ= (λ pα → snd (snd (t-fill pα s)) id)) (snd (snd b0) id) ∘ Glueη (fst v-boundary)})
        where
      v = fst v-boundary
  
      t-fill : (x : α) (w : I) → _
      t-fill pα w = hcomT pα s w β 
                   (\ w pβ → coe (Glue-α α T B f pα) (u w pβ) )
                   (coe (Glue-α α T B f pα) v , 
                    (\ pβ → ap (coe (Glue-α α T B f pα)) (snd v-boundary pβ)))

      -- compose in β, consistently with t on α
      b0 = hcomB s s'
                 (β ∨ α)
                 (\ w → case (\ pβ → unglue (u w pβ))
                                            (\ pα → f pα (fst (t-fill pα w)) )
                                            (\ pβ pα → ap (f pα) (fst (snd (t-fill pα w)) pβ) ∘ ! (unglue-α (u w pβ) pα)))
                 (unglue v , ∨-elim _ (\ pβ → ap unglue (snd v-boundary pβ))
                                      (\ pα → (unglue-α v pα) ∘ ap (f pα) (! (snd (snd (t-fill pα s)) id) ))
                                      (\ _ _ → uip))
