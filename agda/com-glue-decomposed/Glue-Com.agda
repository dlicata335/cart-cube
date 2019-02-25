{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Glue
open import com-glue-decomposed.Glue-HCom
open import Path

module com-glue-decomposed.Glue-Com where

  private
    module GlueComInternal {l1 l : Level} {Γ : Set l1}
        (α : Γ → Cofibs)
        (T : (x : Γ) → fst (α x) → Set l)
        (B : Γ → Set l)
        (f : (x : Γ) (u : fst (α x)) → T x u → B x) 
        (comT : relCom (\ (p : Σ \ (x : Γ) → fst (α x)) → T (fst p) (snd p)))
        (comB : relCom B)
        (wCoeGlue : relWCoe (GlueF α T B f)) where 
    
      hcom-Glue-fiberwise : (x : Γ) → _
      hcom-Glue-fiberwise x = hcomGlue _ {{ snd (α x) }} _ _ (f x)
                              ((\ u → relCom-hasHCom (\ (p : Σ \ (x : _) → fst (α x)) → T (fst p) (snd p)) comT (x , u)))
                              (relCom-hasHCom B comB x)
      
      GlueF-coe : relCoe (GlueF α T B f)
      GlueF-coe = coe-from-wcoe ((GlueF α T B f)) hcom-Glue-fiberwise wCoeGlue
      
      icom : relCom (GlueF α T B f)
      icom = decompose-com (GlueF α T B f) hcom-Glue-fiberwise GlueF-coe
  
  
      -- what we would do on the fiber
      fill-Glue-fiber : ∀ (p : I → Γ) (p∀α : (x : _) → (fst o α o p) x) 
                     → ∀ (s w : I) (β : Set) {{ cβ : Cofib β }} 
                         (t : (z : I) → β → (GlueF α T B f o p) z) 
                         (b : ((GlueF α T B f o p) s) [ β ↦ (t s) ]) 
                     → ((T (p w) (p∀α w)) [ β ↦ (\ pβ → coe (Glue-α _ {{ (snd (α (p w))) }} _ _ _ ((p∀α w))) (t w pβ)) , s == w ↦ (\ s=s' -> ⇒ (coe (Glue-α _ {{ (snd (α (p s))) }} _ _ _ ((p∀α s))) (fst b)) s=s' ) ])
      fill-Glue-fiber p p∀α s w β {{ cβ }} t b = 
                            (comT (\ x → p x , p∀α x) s w β 
                                   (\ w pβ → coe (Glue-α _ {{ (snd (α (p w))) }} _ _ _ ((p∀α w))) 
                                                 (t w pβ))
                                   ((coe (Glue-α _ {{ (snd (α (p s))) }} _ _ _ ((p∀α s))) (fst b)) , 
                                    (\ pβ → ap (coe (Glue-α _ {{ (snd (α (p s))) }} _ _ _ (p∀α s))) ((snd b) pβ))))
  
      use-incoh : ∀ (p : I → Γ) (s s' : I) (β : Set) {{cβ : Cofib β}} (t : (z : I) → β → (GlueF α T B f o p) z) (b : ((GlueF α T B f o p) s) [ β ↦ (t s) ]) 
                  → _[_↦_,_↦_] ((GlueF α T B f o p) s')
                               -- first constraint
                               (β ∨ ∀i (fst o α o p)) {{ Cofib∨ cβ (Cofib∀ (\ x → snd (α (p x)))) }}
                               -- ↦ 
                                 (case (λ pβ → t s' pβ)
                                   (λ p∀α →
                                      coe (! (Glue-α _ {{snd (α (p s'))}} _ _ _ (p∀α s')))
                                      (fst (fill-Glue-fiber p p∀α s s' β {{cβ}} t b)))
                                   (λ pβ p∀α →
                                      move-transport-right (λ X → X)
                                      (Glue-α (fst (α (p s'))) {{snd (α (p s'))}} (T (p s')) (B (p s'))
                                       (f (p s')) (p∀α s'))
                                      (fst (snd (fill-Glue-fiber p p∀α s s' β {{cβ}} t b)) pβ)))
                               -- second constraint
                               (s == s')
                               -- ↦
                                  (⇒ (fst b))
      use-incoh p s s' β {{cβ}} t b =
         hasCom-hasCom2 ((GlueF α T B f) o p) (icom p) s s'
                        β {{ cβ }} t
                        (∀i (fst o α o p)) {{(Cofib∀ (\ x → snd (α (p x)))) }} 
                           (\ w p∀α → coe (! (Glue-α _ {{ (snd (α (p w))) }} _ _ _ (p∀α w)))
                                          (fst (fill-Glue-fiber p p∀α s w β {{ cβ }} t b)))
                       (\ w pβ p∀α →  move-transport-right (\ X → X) (Glue-α (fst (α (p w))) {{ (snd (α (p w))) }}  (T (p w)) (B (p w)) (f (p w)) (p∀α w)) (fst (snd (fill-Glue-fiber p p∀α s w β {{ cβ }} t b)) pβ) )
                       (fst b , 
                         ∨-elim _ (snd b) (\ p∀α → move-transport-left! (\ X → X) (Glue-α (fst (α (p s))) {{ (snd (α (p s))) }} (T (p s)) (B (p s)) (f (p s)) (p∀α s)) (! (snd (snd (fill-Glue-fiber p p∀α s s β {{ cβ }} t b)) id))) (\ _ _ → uip)) 
  
      comGlue : relCom (GlueF α T B f)
      comGlue p s s' β {{ cβ }} t b = fst (use-incoh p s s' β t b) , (\ pβ → fst (snd (use-incoh p s s' β t b)) (inl pβ)) , ((\ s=s' → snd (snd (use-incoh p s s' β t b)) s=s'))
      
      comGlue-∀α : (p : _) (p∀α : ∀i (fst o α o p)) → ∀ s s' β {{cβ}} t b → 
                fst (comGlue p s s' β {{cβ}} t b)
                == (coe (! (Glue-α _ {{ (snd (α (p s'))) }} _ _ _ (p∀α s'))) (fst ((fill-Glue-fiber p p∀α s s' β {{ cβ }} t b))))
      comGlue-∀α = (\ p p∀α s s' β {{ cβ }} t b → ! (fst (snd (use-incoh p s s' β {{ cβ }} t b)) (inr p∀α)) ) 


      -- needed for ua β reduction
      
      coe-icom-0-1 : ∀ p b → Path ((GlueF α T B f) (p `1))
                                  (fst (relCom-relCoe (GlueF α T B f) icom p `0 `1 b))
                                  (fst (wCoeGlue p `0 `1) b)
      coe-icom-0-1 p b = ∘Path {A = GlueF α T B f (p `1)} (hcom-Glue-fiberwise (p `1))
                               (coe-from-wcoe-0-1 (GlueF α T B f) hcom-Glue-fiberwise wCoeGlue p b )
                               (coe-in-decomposeCom-pointwise (GlueF α T B f) hcom-Glue-fiberwise GlueF-coe p `0 `1 b)

      coe-comGlue-0-1-is-icom :
        ∀ p b →
        (not∀α : ((x : I) → fst (α (p x))) → ⊥{lzero}) → 
        Path ((GlueF α T B f) (p `1))
                     (fst (relCom-relCoe (GlueF α T B f) comGlue p `0 `1 b))
                     (fst (relCom-relCoe (GlueF α T B f) icom p `0 `1 b))
      coe-comGlue-0-1-is-icom p b0 not∀ = path where
        s = `0
        s' = `1
        β = ⊥
        cβ = Cofib⊥
        t = (\ _ → abort)
        b = b0 , (\ x → abort x)
        -- ENH: copied and pasted from use-incoh, gives names above instead
        path = hasCom-hasCom2-path ((GlueF α T B f) o p) (icom p) s s'
                        β {{ cβ }} t
                        (∀i (fst o α o p)) {{(Cofib∀ (\ x → snd (α (p x)))) }} 
                           (\ w p∀α → coe (! (Glue-α _ {{ (snd (α (p w))) }} _ _ _ (p∀α w)))
                                          (fst (fill-Glue-fiber p p∀α s w β {{ cβ }} t b)))
                       (\ w pβ p∀α →  move-transport-right (\ X → X) (Glue-α (fst (α (p w))) {{ (snd (α (p w))) }}  (T (p w)) (B (p w)) (f (p w)) (p∀α w)) (fst (snd (fill-Glue-fiber p p∀α s w β {{ cβ }} t b)) pβ) )
                       (fst b , 
                         ∨-elim _ (snd b) (\ p∀α → move-transport-left! (\ X → X) (Glue-α (fst (α (p s))) {{ (snd (α (p s))) }} (T (p s)) (B (p s)) (f (p s)) (p∀α s)) (! (snd (snd (fill-Glue-fiber p p∀α s s β {{ cβ }} t b)) id))) (\ _ _ → uip))
                       (\ x p∀α → abort (not∀ p∀α))
  
      coe-comGlue-0-1 :
        ∀ p b
        → (not∀α : ((x : I) → fst (α (p x))) → ⊥{lzero}) 
        → Path ((GlueF α T B f) (p `1))
               (fst (relCom-relCoe (GlueF α T B f) comGlue p `0 `1 b))
               (fst (wCoeGlue p `0 `1) b)
      coe-comGlue-0-1 p b not∀α  = ∘Path {A = GlueF α T B f (p `1)} (hcom-Glue-fiberwise (p `1))
                                  (coe-icom-0-1 p b)
                                  (coe-comGlue-0-1-is-icom p b not∀α)
      

  module GlueCom  where 

      open GlueComInternal using (fill-Glue-fiber) public

      -- things get too slow later if we let these reduce;
      -- (note: would be nicer to have α .. wcoeGlue as a module paramater,
      --  but GlueF needs these to vary and to be in the same scope because of the way Agda does abstract, sigh)
      abstract
        comGlue : {l1 l : Level} {Γ : Set l1}
                  (α : Γ → Cofibs)
                  (T : (x : Γ) → fst (α x) → Set l)
                  (B : Γ → Set l)
                  (f : (x : Γ) (u : fst (α x)) → T x u → B x) 
                  (comT : relCom (\ (p : Σ \ (x : Γ) → fst (α x)) → T (fst p) (snd p)))
                  (comB : relCom B)
                  (wCoeGlue : relWCoe (GlueF α T B f)) 
                → relCom (GlueF α T B f)
        comGlue = GlueComInternal.comGlue
      
        comGlue-∀α : {l1 l : Level} {Γ : Set l1}
                  (α : Γ → Cofibs)
                  (T : (x : Γ) → fst (α x) → Set l)
                  (B : Γ → Set l)
                  (f : (x : Γ) (u : fst (α x)) → T x u → B x) 
                  (comT : relCom (\ (p : Σ \ (x : Γ) → fst (α x)) → T (fst p) (snd p)))
                  (comB : relCom B)
                  (wCoeGlue : relWCoe (GlueF α T B f)) (p : I → Γ) (p∀α : ∀i (fst o α o p)) → ∀ s s' β {{cβ}} t b → 
                  fst (comGlue α T B f comT comB wCoeGlue p s s' β {{cβ}} t b)
                  == (coe (! (Glue-α _ {{ (snd (α (p s'))) }} _ _ _ (p∀α s'))) (fst ((fill-Glue-fiber  α T B f comT comB wCoeGlue p p∀α s s' β {{ cβ }} t b))))
        comGlue-∀α = GlueComInternal.comGlue-∀α

        GlueF-stable : ∀ {l1 l2 l} {Γ : Set l1} {Δ : Set l2} {θ : Δ → Γ}
          (α : Γ → Cofibs)
          (T : (x : Γ) → fst (α x) → Set l)
          (B : Γ → Set l)
          (f : (x : Γ) (u : fst (α x)) → T x u → B x)
          (comT : relCom (\ (p : Σ \ (x : Γ) → fst (α x)) → T (fst p) (snd p)))
          (comB : relCom B)
          (wCoeGlue : relWCoe (GlueF α T B f))
          → comPre θ (GlueF α T B f) (comGlue α T B f comT comB wCoeGlue) == 
             comGlue (α o θ) (\ z → T (θ z) ) (B o θ) (\ z → f (θ z)) 
                       (comPre (\ p → (θ (fst p), snd p)) (\ (p : Σ \ (x : Γ) → fst (α x)) → T (fst p) (snd p)) comT)
                       (comPre θ B comB)
                       (wcoePre θ (GlueF α T B f) wCoeGlue)
        GlueF-stable {Γ = Γ} {θ = θ} α T B f comT comB wCoeGlue =
          relCom= ((GlueF α T B f) o θ) _ _ (\ p r r' α {{ cα }} t b → id) 

        coe-comGlue-0-1 : {l1 l : Level} {Γ : Set l1}
                          (α : Γ → Cofibs)
                          (T : (x : Γ) → fst (α x) → Set l)
                          (B : Γ → Set l)
                          (f : (x : Γ) (u : fst (α x)) → T x u → B x) 
                          (comT : relCom (\ (p : Σ \ (x : Γ) → fst (α x)) → T (fst p) (snd p)))
                          (comB : relCom B)
                          (wCoeGlue : relWCoe (GlueF α T B f)) 
                          (p : I → Γ)
                          (b : (GlueF α T B f) (p `0))
                        → (not∀α : ((x : I) → fst (α (p x))) → ⊥{lzero}) 
                        → Path ((GlueF α T B f) (p `1))
                               (fst (relCom-relCoe (GlueF α T B f) (comGlue α T B f comT comB wCoeGlue) p `0 `1 b))
                               (fst (wCoeGlue p `0 `1) b)
        coe-comGlue-0-1 = GlueComInternal.coe-comGlue-0-1




