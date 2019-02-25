{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Kan
open import Glue
open import Prop

module Glue-Com-NoCofib where

module αReallyConstant {l1 l : Level} {Γ : Set l1}
                       (α : Set)
                       {{cα : Cofib α}}
                       (T : (x : Γ) → α → Set l)
                       (B : Γ → Set l)
                       (f : (x : Γ) (u : α) → T x u → B x) 
                       (comT : relCom (\ (p : Γ × α) → T (fst p) (snd p)))
                       (comB : relCom B) where

  {- the proof for hcom Glue actually works for com, 
     as long as the cofibration doesn't vary
   -}

  -- bits of comGglue; need names for them below when proving it restricts appropriately
  module ComGlue (p : I → Γ) (s s' : I) (β : Set) {{cβ : Cofib β}} (u : (i : I) → β → (GlueF (\ _ → α , cα) T B f) (p i)) (v : (GlueF (\ _ → α , cα) T B f) (p s) [ β ↦ _ ]) where 
      t-fill : (x : α) (w : I) → _
      t-fill pα w = comT (\ x → p x , pα) s w β 
                   (\ w pβ → coe (Glue-α _ _ _ _ pα) (u w pβ) )
                   (coe (Glue-α _ _ _ _ pα) (fst v) , 
                    (\ pβ → ap (coe (Glue-α _ _ _ _ pα)) (snd v pβ)))

      -- compose in β, consistently with t on α
      b0 = comB p s s'
                 (β ∨ α)
                 (\ w → case (\ pβ → unglue (u w pβ))
                                            (\ pα → f (p w) pα (fst (t-fill pα w)) )
                                            (\ pβ pα → ap (f (p w) pα) (fst (snd (t-fill pα w)) pβ) ∘ ! (unglue-α (u w pβ) pα)))
                 (unglue (fst v) , ∨-elim _ (\ pβ → ap unglue (snd v pβ))
                                      (\ pα → (unglue-α (fst v) pα) ∘ ap (f (p s) pα) (! (snd (snd (t-fill pα s)) id) ))
                                      (\ _ _ → uip))

  -- FIXME: I feel like I'm writing this a lot -- make into a lemma somewhere
  comGlue-α : (pα : α) → relCom (GlueF (\ _ → α , cα) T B f)
  comGlue-α pα p s s' β u v = coe (! (Glue-α _ _ _ _ pα)) (fst c) , (\ pβ → ap (coe (! (Glue-α _ _ _ _ pα))) (fst (snd c) pβ) ∘ ! (ap= (transport-inv (\ X → X) (Glue-α _ _ _ _ pα)))) ,
                                                                    (\ {id → ap (coe (! (Glue-α _ _ _ _ pα))) (snd (snd c) id) ∘ ! (ap= (transport-inv (\ X → X) (Glue-α _ _ _ _ pα)))}) where
    c = ComGlue.t-fill p s s' β u v pα s'

  abstract
    comGlue : relCom (GlueF (\ _ → α , cα) T B f)
    comGlue p s s' β u v = 
          glue _ _ _ _
            (\ pα → fst (t-fill pα s')) 
            (fst b0  , (\ pα →  fst (snd b0) (inr pα) )) , 
            ( (\ pβ → glue-cong _ _ _ _  _ _ ((λ= (\ pα → fst (snd (t-fill pα s')) pβ))) ((fst (snd b0) (inl pβ))) ∘ Glueη (u s' pβ)) ) , 
            (λ { id → glue-cong _ _ _ _ _ _ (λ= (λ pα → snd (snd (t-fill pα s)) id)) (snd (snd b0) id) ∘ Glueη (fst v)}) where
      b0 = ComGlue.b0 p s s' β u v
      t-fill  = \ pα s' → (ComGlue.t-fill p s s' β u v pα s')
    
    comGlue-restricts-α : (pα : α) → comGlue == comGlue-α pα
    comGlue-restricts-α pα = relCom= ((GlueF (\ _ → α , cα) T B f)) comGlue (comGlue-α pα)
                          (\ p s s' β u v → ! (Glue-α-! pα _) ∘
                                            glue-cong _ _ _ _ _ _
                                                     (λ= \ z → ! (apd (\ H → fst (ComGlue.t-fill p s s' β u v H s')) (Cofib.eq cα pα z)) )
                                                     (! (fst (snd (ComGlue.b0 p s s' β u v)) (inr pα))) )

module αConstant 
        {l : Level} 
        (α : I → Cofibs)
        (T : (x : I) → fst (α x) → Set l)
        (B : I → Set l)
        (f : (x : I) (u : fst (α x)) → T x u → B x) 
        (comT : relCom (\ (p : Σ \ (x : I) → fst (α x)) → T (fst p) (snd p)))
        (comB : relCom B)
        (α' : Set)
        (α-constant : (x : I) → fst (α x) == α') where

   α'-cofib : Cofib α'
   α'-cofib = cofib (transport isCofib (((α-constant `0))) (Cofib.is (snd (α `0))))
                    ((transport (\ h → (x y : h) → x == y) (((α-constant `0))) ((Cofib.eq (snd (α `0))))))

   ctx = Σ \ (α : I → Cofibs) →
         Σ \ (T : (x : I) → fst (α x) → Set l) → 
             (x : I) (u : fst (α x)) → T x u → B x

   transport-ctx : ∀ {α α' : I → Cofibs} (eq : α == α')
                   (Q : Σ \ (T : (x : I) → fst (α x) → Set l) → (x : I) (u : fst (α x)) → T x u → B x)
                 → 
     transport (\ α → Σ \ (T : (x : I) → fst (α x) → Set l) → (x : I) (u : fst (α x)) → T x u → B x)
               eq
               Q
     == ( ((\ x pα' → fst Q x (coe (! (ap (\ h → fst (h x)) eq)) pα')) ) ,
          (((\ x pα' t → snd Q x (coe (! (ap (\ h → fst (h x)) eq)) pα') t) )))
   transport-ctx id Q = id

   α'-Cofib : I → Cofibs
   α'-Cofib = (\ _ → α' , α'-cofib)

   T' = (\ x pα' → T x (coe (! ( (α-constant x))) pα'))

   f' = (\ x u t → f x (coe (! ( (α-constant x))) u) t)

   eq : _==_ {_}{ctx} (α'-Cofib , T' , f') (α , (\ x → T x) , (\ x → f x))
   eq = pair= (λ= \ x → pair= (! ((α-constant x)))  Cofib-prop  )
              (pair= (λ= \ x → λ= \ pα' → ap (T x) (Cofib.eq (snd (α x)) _ _))
                     (het-to-hom (λ=o (\ x y x=y → λ=o (\ pa pa' pa=pa' → apdo2 f ((het-to-hom x=y)) ((pa=pa' ∘h transport-=h (\ X → X) (! (ap (λ h → fst (h x)) (λ= (λ x₁ → pair= (! ((α-constant x₁))) Cofib-prop))))) ∘h transport-=h (\ X → X) (! ((α-constant x))) ))) ∘h transport-=h (λ T₁ → (x : I) (u : fst (α (x))) → T₁ x u → B (x)) (λ= (λ x → λ= (λ pα' → ap (T (x)) ( (Cofib.eq (snd (α (x))) (coe (! ((α-constant x))) (coe (! (ap (λ h → fst (h x)) (λ= (λ x₁ → pair= (! ((α-constant x₁))) Cofib-prop)))) pα')) pα') ))))))
               ∘ transport-ctx (λ= (λ x → pair= (! ((α-constant x))) Cofib-prop)) _ ) 

   -- H : ctx → Set _
   -- H (α , T , f) =   (r r' : I) (β : Set) {{_ : Cofib β}} 
   --                   → (t : (z : I) → β → (GlueF α T B f) z) 
   --                   → (b : (GlueF α T (B) f) r [ β ↦ t r ]) 
   --                   → (GlueF α T (B) f) r' [ β ↦ t r' , (r == r') ↦ ⇒ (fst b) ]

   G : ctx → I → Set _
   G (α , T , f) r = (GlueF α T (B) f) r

   Geq : (z : I) → G (α'-Cofib , T' , f') z == G  (α , (\ x → T x) , (\ x → f x)) z
   Geq z =  (ap= ((ap G eq))) 

   module R = αReallyConstant
                 α'
                 {{α'-cofib}}
                 T'
                 (B)
                 f'
                 (comPre (\ q → (fst q) , ((coe (! ((α-constant (fst q)))) (snd q)))) (\ (p : Σ \ (x : I) → fst (α x)) → T (fst p) (snd p)) comT)
                 (comB)

   hasComGlue : hasCom (GlueF α T B f)
   hasComGlue r r' β t b = coe (Geq _) (fst c) , (\ pβ →  ap (coe (Geq (r'))) (fst (snd c) pβ) ∘ ! (ap= (transport-inv-2 (\ x → x) (Geq _)))) ,
                                              (\ {id → ap (coe (Geq (r'))) (snd (snd c) id) ∘ ! (ap= (transport-inv-2 (\ x → x) (Geq _)))}) where
       c = R.comGlue (\ x → x) r r' β (\ z pβ → coe (! (Geq _)) (t z pβ)) (coe ((! (Geq _))) (fst b) , (\ p → ap (coe ((! (Geq _) ))) (snd b p)))


     -- transport H eq (R.comGlue (\ x → x))

     -- comGlue-restricts : (pα' : α') → comGlue == transport H eq (R.comGlue-α pα' (\ x → x))
     -- comGlue-restricts pα' = ap (transport H eq) (ap= (R.comGlue-restricts-α pα') {(\ x → x)}) 

   
