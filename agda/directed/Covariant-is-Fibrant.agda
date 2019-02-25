{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Prop
open import directed.DirInterval
open import universe.LibFlat
open import Equiv
open import Cofibs
open import Kan
open import Path
open import Interval
open import universe.Sigma
open import directed.Covariant

module directed.Covariant-is-Fibrant where

  com-hasCov : ∀ {l0 l2} {Δ : Set l0}
                    (A : (x : Δ) → 𝟚 → Set l2)
                  → relCom (\ p → A (fst p) (snd p))
                  → relCom (\ x → hasCov (A x))
  com-hasCov A comA p r r' β dcomrβ dcomr =
      dcomr' ,
        (\ pβ → λ= \ s → λ= \ α → λ=inf \ cα → λ= \ t → λ= \ b →
           pair= (fst (snd (coefw s α {{cα}} t b)) (inr (inl pβ)) ∘ snd (fillAback r' s r' (fst (dcomrβ r' pβ s α {{cα}} t b))) id)
                 (pair= ((λ= \ _ → uip)) ((λ= \ _ → uip)))) ,
        (\ {id → λ= \ s → λ= \ α → λ=inf \ cα → λ= \ t → λ= \ b →
                  pair= ((snd (snd (coefw s α {{cα}} t b)) id) ∘ fst (snd (use s α {{ cα }} t b)) (inr (inr id)) ∘ ap (\ H → fst (fst dcomr s α {{cα}} (λ z pα → t z pα) (fst b , H))) (λ= \ _ → uip) )
                        ((pair= ((λ= \ _ → uip)) ((λ= \ _ → uip))))  }) where
      fillAback : ∀ r' z w c → _
      fillAback r' z w c = relCom-relCoe (\ p → A (fst p) (snd p))
                                      comA (\ y → p y , z) r' w c

      whenr=r' : ∀ r' s α {{cα}} (t : (x : 𝟚) → α → A (p r') x) b → r == r' → A (p r) s
      whenr=r' r' s α {{cα}} t b r=r' = (fst ((fst dcomr) s α
                                          (\ z pα → transport (\ x → A (p x) z) (! r=r') (t z pα))
                                          (transport (\ x → A (p x) ``0) (! r=r') (fst b) ,
                                           (\ pα → ap (transport (\ x → A (p x) ``0) (! r=r')) (snd b pα) )))) 

      use : ∀ s α {{cα}} ta b → _
      use s α {{cα}} t b =
        fst dcomr
              s
              (α ∨ (β ∨ (r == r')))
              ( (\ z → case (\ pα → fst (fillAback r' z r (t z pα)))
                          (case
                              (\ pβ → fst (fillAback r' z r (fst (dcomrβ r' pβ z α t b))))
                              (\ r=r' →  whenr=r' r' z α {{cα}} t b r=r' )
                              (\ pβ r=r' →  coh1 r' r=r' z pβ α {{cα}} t b 
                                          ∘ ap (\ H → transport (λ x → A (p x) z) (! r=r') (fst (H z α t b))) (! (apd (\ x → dcomrβ x pβ) (r=r')))
                                          ∘ ! ((snd (fillAback r' z r (fst (dcomrβ r' pβ z α t b)))) (! r=r')) ))
                          (\ pα → ∨-elim _
                             (\ pβ → ap (\ H → fst (fillAback r' z r H)) (fst (snd (dcomrβ r' pβ z α t b)) pα))
                             (\ r=r' → coh2 r' r=r' z α t b pα )
                             (\ _ _ → uip))) )
              (fst (fillAback r' ``0 r (fst b)) ,
               boundary) where
        abstract
          coh1 : ∀ r' (r=r' : r == r') z pβ α {{cα : Cofib α}} t b
           → transport (λ x → A (p x) z) (! r=r') 
             (fst
             (transport
             (λ z₁ → (r'' : 𝟚) (α₁ : Set) {{z₂ : Cofib α₁}} (t₁ : (z₃ : 𝟚) → α₁ → A (p z₁) z₃) (b₁ : A (p z₁) ``0 [ α₁ ↦ t₁ ``0 ]) → A (p z₁) r'' [ α₁ ↦ t₁ r'' , ``0 == r'' ↦ (λ p₁ → transport (A (p z₁)) p₁ (fst b₁)) ]) r=r' (dcomrβ r pβ) z α t b))
           == whenr=r' r' z α t b r=r'
          coh1 .r id z pβ α t b = ap (\ Q → fst (fst dcomr z α t (fst b , Q))) (λ= \ _ → uip) ∘ ap (\ H → fst (H z α t b)) (snd dcomr pβ)

          coh2 : ∀ r' (r=r' : r == r') z α {{cα : Cofib α}} (t : (x : 𝟚) → α → A (p r') x) b pα → 
                 fst (fillAback r' z r (t z pα)) ==
                 (whenr=r' r' z α {{cα}} t b r=r')
          coh2 r' id z α t b pα = fst (snd (fst dcomr z α (λ z₁ pα₁ → t z₁ pα₁) (fst b , (λ pα₁ → ap (λ x → x) (snd b pα₁))))) pα ∘ ! (snd (fillAback r z r (t z pα)) id)

          coh3 : ∀ r' (r=r' : r == r') α {{cα : Cofib α}} (t : (x : 𝟚) → α → A (p r') x) b → 
                 fst (fillAback r' ``0 r (fst b)) ==
                 (whenr=r' r' ``0 α {{cα}} t b r=r')
          coh3 r' id α t b = snd (snd (fst dcomr ``0 α (λ z₁ pα → t z₁ pα) (fst b , (λ pα → ap (λ x → x) (snd b pα))))) id ∘
                             ! (snd (fillAback r ``0 r (fst b)) id) 

          boundary = ∨-elim _
                      ((\ pα → ap (\ h → fst (fillAback r' ``0 r h)) (snd b pα)))
                      (∨-elim _
                              (\ pβ → ap (\ H → fst (fillAback r' ``0 r H)) (! (snd (snd (dcomrβ r' pβ ``0 α t b)) id) ))
                              (\ r=r' → ! (coh3 r' r=r' α t b))
                              (\ _ _ → uip))
                      (\ _ _ → uip)

      coefw :  ∀ s α {{cα}} t b → _
      coefw s α {{cα}} t b =
        (comA
          (\ z → p z , s)
          r r'
          (α ∨ (β ∨ (``0 == s)))
          (\ z →  case (\ pα → fst (fillAback r' s z (t s pα)))
                      (case (\ pβ → fst (fillAback r' s z (fst (dcomrβ r' pβ s α t b))))
                            (\ 0=s →  transport (A (p z)) 0=s ((fst (fillAback r' ``0 z (fst b)))) )
                            (\ pβ → \ {id → ! (ap (\ H →  fst (fillAback r' ``0 z H)) (snd (snd (dcomrβ r' pβ s α t b)) id))}))
                      (\ pα → ∨-elim _ (\ pβ → ap (\ H → fst (fillAback r' s z H)) (fst (snd (dcomrβ r' pβ s α t b)) pα) )
                                       (\ 0=s → ap (\ H → transport (λ z₁ → A (p z) z₁) 0=s (fst (fillAback r' ``0 z H))) (snd b pα) ∘ ! (apd (\ s → fst (fillAback r' s z (t s pα))) 0=s))
                                       (\ _ _ → uip)) )
          (fst (use s α {{cα}} t b),
           boundary))
        where
         abstract
           boundary = 
            ∨-elim _ (λ pα → fst (snd (use s α t b)) (inl pα))
                    (∨-elim _ (\ pβ → fst (snd (use s α t b)) (inr (inl pβ)) )
                              (\ 0=s → snd (snd (use s α t b)) 0=s)
                              (λ _ _ → uip) )
                    (λ _ _ → uip)
                     

      dcomr' : ∀ s α {{cα}} t b → _
      dcomr' s α {{cα}} t b =
          (fst (coefw s α {{cα}} t b)) ,
           boundary1 ,
           boundary2 where
        abstract
         boundary1 = (\ pα → (fst (snd (coefw s α t b)) (inl pα)) ∘ snd (fillAback r' s r' (t s pα)) id)
         boundary2 = ( (λ { id →   (fst (snd (coefw s α t b)) (inr (inr id))) ∘ snd (fillAback r' ``0 r' (fst b)) id   }))
           



{-
  abstract
    relCov-relCom : ∀ {l0 l1 l2} {Δ : Set l0}
                      {Γ : Δ → Set l1}
                      (A : (x : Δ) → Γ x → Set l2)
                   → relCom Γ
                   → relCom (\ p → A (fst p) (snd p))
                   → relCom (\ x → relCov (A x))
    relCov-relCom {Γ = Γ} A comΓ comA p r r' β dcomrβ dcomr =
      folows from fibrancy of hasCom, Pi, and 𝟚 → something 

    -- relCov-code-universal : ∀ {l1 l2 :{♭} Level}
    --                         → (Σ \ (Γ : U {l1}) → El Γ → U {l2})
    --                         → U {lmax (lsuc lzero) (lmax l2 l1)}
    -- relCov-code-universal = code _ (\ ΓA → relCov (El o snd ΓA))
    --                              (relCov-relCom {Δ = (Σ \ (Γ : U) → El Γ → U )} {El o fst}
    --                                             (\ ΓA x → El (snd ΓA x))
    --                                             (comEl' fst)
    --                                             ( (comEl' (λ p → (snd (fst p) (snd p)))) ))

    -- relCov-code : ∀ {l1 l2 :{♭} Level}
    --                         → (Γ : U {l1})
    --                         → (El Γ → U {l2})
    --                         → U {lmax (lsuc lzero) (lmax l2 l1)}
    -- relCov-code Γ A = relCov-code-universal (Γ , A)

    -- relCovU : {l l' : Level}
    --           (Γ : Set l')
    --           (A : Γ → U0 l)
    --         → Set (ℓ₁ ⊔ l ⊔ l')
    -- relCovU Γ A = (p : 𝟚 → Γ) → El0 (C (A ∘ p))

-}
