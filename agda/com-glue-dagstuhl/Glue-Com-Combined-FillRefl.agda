-- see universe/Glue-Com-For-Lines-Directly for analogous stab at doing this for lines directly

{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Glue
open import Path
open import universe.Universe
open import Glue-Weak
open import Equiv
open import com-glue-dagstuhl.IsEquiv-FillRefl

module com-glue-dagstuhl.Glue-Com-Combined-FillRefl where

  -- note: different def of isEquiv than in universe.Glue
  record GlueData (l :{♭} Level) : Set (ℓ₂ ⊔ lsuc l) where
    constructor gluedata
    field
      α : Set
      c : Cofib α -- would be nice if this could be treated as an instance
      T : α → U{l}
      B : U{l}
      f : (pα : α) → El (T pα) → El B
      feq : (pα : α) → isEquiv'FillRefl (f pα)

  Glue-from-data : {l :{♭} Level} → GlueData l → Set l
  Glue-from-data (gluedata α cα T B f feq) = Glue α {{ cα }} (El o T) (El B) f

  abstract 
    comGlue-unaligned : {l :{♭} Level} → relCom (Glue-from-data{l})
    comGlue-unaligned G s s' β u v = fst g ,
                           (\ pβ → snd g (inl pβ)) ,
                           (\ s=s' → snd g (inr s=s') ) where
      module Gs = GlueData (G s)
      module Gs' = GlueData (G s')
  
      b' : (El (Gs'.B)) [ β ↦ _ , _ ↦ _ ]
      b' = comEl' (\x → (GlueData.B x))
                  G s s'
                  β (\ z pα → unglue (u z pα))
                  (unglue (fst v) , (\ pβ → ap unglue (snd v pβ)))
  
      c' : (pαs' : Gs'.α) → _
      c' pαs' = Gs'.feq pαs' {(β ∨ (s == s'))}
                             (case (\ pβ → coe (Glue-α _ {{Gs'.c}} _ _ _ pαs') (u s' pβ))
                                   (\ s=s' → coe (Glue-α _ {{Gs'.c}} _ _ _ pαs') (transport (Glue-from-data o G) s=s' (fst v)))
                                   (\ {pβ id → ap (coe (Glue-α _ {{Gs'.c}} _ _ _ pαs')) (snd v pβ)}))
                             (((fst b')) ,
                              ∨-elim _
                                     (\ pβ → fst (snd b') pβ ∘ unglue-α (u s' pβ) pαs')
                                     (\ s=s' → snd (snd b') s=s' ∘ (⇒GlueF-unglue (\ x → x) s=s' (fst v) ∘ unglue-α (transport (Glue-from-data o G) s=s' (fst v)) pαs'))
                                     (\ _ _ → uip))   
  
      g = glue-weak-better' {α = Gs'.α} {{cα = Gs'.c}} (hcomEl Gs'.B)
                     (β ∨ (s == s'))
                     (case (\ pβ → u s' pβ)
                           (\ s=s' → transport (Glue-from-data o G) s=s' (fst v) )
                           (\ pβ s=s' → ap (transport (Glue-from-data o G) s=s') (snd v pβ) ∘ ! (apd (\ x → u x pβ) s=s')))
                          (fst b' ,
                            ∨-elim _
                                   (\ pβ → fst (snd b') pβ)
                                   (\ s=s' → snd (snd b') s=s' ∘ ⇒GlueF-unglue (\ x → x) s=s' (fst v) )
                                   (\ _ _ → uip))
                          (\ pαs' → fst (c' pαs') ,
                                    ∨-elim _
                                           (\ pβ → snd (c' pαs') (inl pβ) ∘
                                                   =HFiber' ( fst-transport-HFiber'-base (Gs'.f pαs') (fst (snd (comEl (GlueData.B o G) s s' β (λ z pα → unglue (u z pα)) (unglue (fst v) , (λ pβ₁ → ap unglue (snd v pβ₁))))) pβ) (Glue-to-fiber' (u s' pβ) pαs') )
                                                            ((λ= \ _ → fst (snd b') pβ) ∘ ( fst-snd-transport-HFiber'-base (Gs'.f pαs') (fst (snd (comEl (GlueData.B o G) s s' β (λ z pα → unglue (u z pα)) (unglue (fst v) , (λ pβ₁ → ap unglue (snd v pβ₁))))) pβ) (Glue-to-fiber' (u s' pβ) pαs') )))
                                           (\ s=s' → snd (c' pαs') (inr s=s') ∘
                                                     =HFiber' (fst-transport-HFiber'-base (Gs'.f pαs') (snd (snd b') s=s' ∘ ⇒GlueF-unglue (λ x → x) s=s' (fst v)) (Glue-to-fiber' (transport (Glue-from-data o G) s=s' (fst v)) pαs'))
                                                              (λ= (\ x → snd (snd b') s=s' ∘ ⇒GlueF-unglue (\x → x) s=s' (fst v)) ∘ (fst-snd-transport-HFiber'-base (Gs'.f pαs') (snd (snd b') s=s' ∘ ⇒GlueF-unglue (λ x → x) s=s' (fst v)) (Glue-to-fiber' (transport (Glue-from-data o G) s=s' (fst v)) pαs'))) )
                                           (\ _ _ → uip))


  -- FIXME: port finished version of this from universe.Glue

  -- transport relCom T along Glue-α equality
  fill-Glue-fiber : ∀ {l :{♭} Level} (G : I → GlueData l) (p∀α : (x : I) → (GlueData.α (G x) ))
                  → hasCom (Glue-from-data o G) 
  fill-Glue-fiber G p∀α r r' β t b = coe (! (Glue-α _ {{ GlueData.c (G r') }} _ _ _ (p∀α r'))) (fst comT) ,
                                     (\ pβ → ap (coe (! (Glue-α (GlueData.α (G r')) {{GlueData.c (G r')}} (λ v → (El o GlueData.T (G r')) v) (El (GlueData.B (G r'))) (GlueData.f (G r')) (p∀α r')))) (fst (snd comT) pβ) ∘ ! (ap= (transport-inv (\ x → x) (Glue-α (GlueData.α (G r')) {{GlueData.c (G r')}} (λ v → (El o GlueData.T (G r')) v) (El (GlueData.B (G r'))) (GlueData.f (G r')) (p∀α r'))))) , 
                                     (\ r=r' → ap (coe (! (Glue-α (GlueData.α (G r')) {{GlueData.c (G r')}} (λ v → (El o GlueData.T (G r')) v) (El (GlueData.B (G r'))) (GlueData.f (G r')) (p∀α r')))) ((snd (snd comT) r=r') ∘ {!!}) ∘ ! (ap= (transport-inv (\ x → x) (Glue-α (GlueData.α (G r')) {{GlueData.c (G r')}} (λ v → (El o GlueData.T (G r')) v) (El (GlueData.B (G r'))) (GlueData.f (G r')) (p∀α r')))) ) where
    comT = comEl (\ x → GlueData.T (G x) (p∀α x)) r r'
             β ( \ w pβ → coe (Glue-α _ {{ (GlueData.c (G w)) }} _ _ _ (p∀α w)) (t w pβ) )
             (coe (Glue-α _ {{ GlueData.c (G r) }} _ _ _ (p∀α r)) (fst b) ,
              (\ pβ → ap (coe (Glue-α _ {{ GlueData.c (G r) }} _ _ _ (p∀α r))) (snd b pβ)))

  align : ∀ {l :{♭} Level} (G : I → GlueData l)
        → _[_↦_] (hasCom (Glue-from-data o G)) ((x : I) → (GlueData.α (G x) )) {{ Cofib∀ (\ x → GlueData.c (G x)) }} (fill-Glue-fiber G)
  align G = (λ r r' β t b →  (fst (use-incoh r r' β t b))  ,
               -- rearrange equations
               (\ pβ → fst (snd (use-incoh r r' β t b)) (inl pβ)) ,
               (\ r=r' →  snd (snd (use-incoh r r' β t b)) (r=r'))) ,
               (\ p∀α → λ= \ r → λ= \ r' → λ= \ β → λ=inf \ cβ → λ= \ t → λ= \ b → pair= (fst (snd (use-incoh r r' β {{cβ}} t b)) (inr p∀α)) (pair= (λ= \ _ → uip) ((λ= \ _ → uip)))) where

    use-incoh : ∀ r r' β {{cβ : Cofib β}} t b → _
    use-incoh r r' β {{cβ}} t b = comGlue-unaligned G r r'
                                             (β ∨ ((x : I) → (GlueData.α (G x) )))
                                             {{ Cofib∨ cβ (Cofib∀ (\ x → GlueData.c (G x))) }}
                                             (\ z → case (\ pβ → t z pβ)
                                                         (\ p∀α → fst (fill-Glue-fiber G p∀α r z β t b))
                                                         (\ pβ p∀α → fst (snd (fill-Glue-fiber G p∀α r z β t b)) pβ))
                                             (fst b , ∨-elim _
                                                             (\ pβ → snd b pβ)
                                                             (\ p∀α → ! (snd (snd (fill-Glue-fiber G p∀α r r β t b)) id))
                                                             (\ _ _ → uip))

