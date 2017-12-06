{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Kan
open import Glue
open import Prop

module Glue-HCom where 

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
                  (fst b1 , (\ pα → fst (snd b1) (inl pα) ∘ fst (snd (pres `1 pα)) (inl (inr id)) )) , 
             (\ pβ → glue-cong α T B f _ _ (λ= (\ pα → fst (snd (t-fill pα s')) pβ)) (fst (snd b1) (inr (inl pβ))) ∘ Glueη (u s' pβ)) , 
             (\ {id → glue-cong α T B f _ _ (λ= (\ pα → snd (snd (t-fill pα s)) id)) (fst (snd b1) (inr (inr id))) ∘ Glueη (fst v-boundary) }) where
      v = fst v-boundary
      b0 = hcomB s s' β (\ w pβ → unglue (u w pβ)) (unglue v , (\ pβ → ap unglue (snd v-boundary pβ)))
  
      t-fill : (x : α) (w : I) → _
      t-fill pα w = hcomT pα s w β 
                   (\ w pβ → coe (Glue-α α T B f pα) (u w pβ) )
                   (coe (Glue-α α T B f pα) v , 
                    (\ pβ → ap (coe (Glue-α α T B f pα)) (snd v-boundary pβ)))
  
      -- pres without the x=1 constraint
      pres-hcom0 : (x : I) (pα : α) (w : I) → _ 
      pres-hcom0 x pα w = 
        hcomB s w β (\ w pβ → f pα (coe (Glue-α α T B f pα) (u w pβ))) (f pα (coe (Glue-α α T B f pα) v) , 
                     (\ pβ → (ap (\ h → f pα (coe (Glue-α α T B f pα) h)) (snd v-boundary pβ))))
  
      -- extra x=0 to avoid needing propositional univalence
      pres : (x : I) → (pα : α) → _
      pres x pα = hcomB s s' (((x == `0) ∨ (x == `1)) ∨ β)
                        (\ w → case (case 
                                      (\ x=0 →  fst (pres-hcom0 x pα w) ) 
                                      (\ _ → (f pα (fst (t-fill pα w)))) 
                                      (λ p q → abort (iabort (q ∘ ! p))))
                                    (\ pβ → f pα (coe (Glue-α α T B f pα) (u w pβ)))
                                    (∨-elim _ (\ x0 pβ → ! (fst (snd (pres-hcom0 x pα w)) pβ)) 
                                              (\ x=1 pβ →  ap (f pα) (! (fst (snd (t-fill pα w)) pβ)) )
                                              (\ _ _ → λ= (\ _ → uip))))
                        ((f pα (coe (Glue-α α T B f pα) v)) , 
                         ∨-elim _ (∨-elim _ 
                                          (\ x=0 → ! (snd (snd (pres-hcom0 x pα s)) id)) 
                                          (\ x=1 → ap (f pα) (! (snd (snd (t-fill pα s)) id) )) 
                                          (\ _ _ → uip))
                                  (\ pβ →  ap (\ z → f pα (coe (Glue-α α T B f pα) z)) (snd v-boundary pβ) ) 
                                  (\ _ _ → uip))

      -- this step is almost an instance of glue-weak with b0 t0 and pres,
      -- but we'd need to generalize the lemma
      -- so that it takes a cofibration on which the path in the hfiber is constant,
      -- and outputs something that is unchanged on that.  Not sure that's worth the
      -- conceptual overhead for one use, so just inlining it here.  
      b1 = hcomB `0 `1 (α ∨ (β ∨ (s == s'))) 
                 (\ x → case (\ pα → fst (pres x pα)) 
                             (case (unglue o (u s')) 
                                   (\ _ → unglue v) 
                                   (\ pβ → \ s=s' → ap unglue (snd v-boundary pβ) ∘ ap (\ h → unglue (u h pβ)) (! s=s'))) 
                             (\ pα → ∨-elim _ (\ pβ → unglue-α (u s' pβ) pα ∘ ! (fst (snd (pres x pα)) (inr pβ))) 
                                              ((\ s=s' → unglue-α v pα ∘ ! (snd (snd (pres x pα)) s=s'))) 
                                              (\ _ _ → uip)))
                 (fst b0 , 
                  ∨-elim _ ((\ pα → ap (\ h' → fst (hcomB s s' β (λ w pβ → h' (u w pβ)) (h' (fst v-boundary) , (λ pβ → ap h' (snd v-boundary pβ))))) 
                                        (λ= (\ v → unglue-α v pα)) 
                                     ∘ ! (fst (snd (pres `0 pα)) (inl (inl id))))) 
                           (∨-elim _ (\ pβ → fst (snd b0) pβ) (\ s=s' → snd (snd b0) s=s') (\ _ _ → uip) ) (\ _ _ → uip))

  -- TODO: can prove coherence on α
  
