{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Glue
open import Equiv
open import Path
open import Equiv
open import universe.Universe
open import universe.Sigma
open import universe.Path
open import universe.Pi
open import universe.Glue

module universe.U where

  -- ----------------------------------------------------------------------
  -- code for the universe itself in the next universe

  record Composable (l :{♭} Level) : Set (ℓ₂ ⊔ (lsuc l)) where
    constructor HCom
    field
      r r' : I 
      α : Set
      c : Cofib α
      T : I → α → U{l}
      B : _[_↦_] (U{l}) α {{c}} (T r)

  get-T : {l :{♭} Level} → (Σ \(c : Composable l) → Composable.α c) → U{l}
  get-T p = (Composable.T (fst p) (Composable.r' (fst p)) (snd p))


  -- made helper functions because these get used twice

  GlueT-Cofib : {l :{♭} Level} → Composable l → Cofibs
  GlueT-Cofib (HCom r r' α c T B) = (α ∨ (r == r')) , Cofib∨ c Cofib= 

  GlueT-T : {l :{♭} Level} → (c : Composable l) → (fst (GlueT-Cofib c)) → U {l}
  GlueT-T (HCom r r' α c T B) = (case (\ pα → (T r' pα))
                                      (\ r=r' → (fst B)) 
                                      (\ pα r=r' → (snd B pα) ∘ ap (\ x → (T x pα)) (! r=r'))) 

  GlueT-B : {l :{♭} Level} (c : Composable l) → U{l}
  GlueT-B (HCom r r' α c T B) = (fst B)

  GlueT-f : {l :{♭} Level} (c : Composable l) → (pα : (fst (GlueT-Cofib c))) → El (GlueT-T c pα) → El (GlueT-B c)
  GlueT-f {l} (HCom r r' α c T B) =  
           (∨-elim _ (\ pα t → transport El (snd B pα) ( fst (coeT pα t) )) 
                     (\ _ → \ b → b )
                     coh) where

        coeT : (pα : _) → (t : _) → _
        coeT pα t = coeU (\ x → T x pα) r' r t

        coeT-r=r' : (pα : _) → (t : _) (eq : r == r') → fst (coeT pα t) == ⇒ {A = (\ x → El (T x pα))} t (! eq)
        coeT-r=r' pα t r=r' = ! ((snd (coeT pα t)) (! r=r'))
        
        abstract
          coh = (\ pα r=r' →  
                   λ= \ b → (((  (ap {M = (snd B pα ∘ ap (λ x → T x pα) (! r=r')) ∘ (ap (λ z → GlueT-T (HCom r r' α c T B) z) (! (trunc {_}{_}{_}{inl pα}{inr r=r'})))} {N = id} (\ h → transport El h b) uip ∘ 
                                ! (ap= (transport-∘ {lsuc (lsuc lzero) ⊔ lsuc l}{l} {A = U} El (snd B pα ∘ ap (λ x → T x pα) (! r=r')) (ap (GlueT-T (HCom r r' α c T B)) (! (trunc{_}{_}{_}{inl pα}{inr r=r'})))))) ∘  
                                ! (ap= (transport-∘ El (snd B pα) (ap (λ x → T x pα) (! r=r'))))  
                                ) ∘ 
                                ap (transport El (snd B pα)) (ap (transport El (ap (λ x → T x pα) (! r=r'))) (ap= (transport-ap-assoc' El (\ z → GlueT-T (HCom r r' α c T B) z) (! trunc))) ∘ ap= (transport-ap-assoc' El (\ x → T x pα) (! r=r')) )) 
                                ∘ ap (transport El (snd B pα)) (coeT-r=r' pα _ r=r' )) 
                            ∘ ap= (transport-→-pre' (\ z → El (GlueT-T (HCom r r' α c T B) z)) trunc (λ t → transport El (snd B pα) (fst (coeT pα t)))) ) 

  
  coe-rr-equiv : ∀ {l2 :{♭} Level} (A : I → U{ l2})
            → (r : I)
            → isEquiv _ _ (\ b → fst (coeU A r r b))
  coe-rr-equiv A r = transport (λ h → isEquiv _ _ h) ((λ= \ b → (snd (coeU A r r b)) id )) (id-Equiv (hcomEl (A r)))

  coe-equiv : ∀ {l2 :{♭} Level} (A : I → U{ l2})
            → (r r' : I)
            → isEquiv (El (A r)) (El (A r')) (\ b →  fst (coeU A r r' b)  ) 
                      [ r == r' ↦ ( \ r=r' →  ⇒ (coe-rr-equiv A r) r=r' )  ]
  coe-equiv A r r' =  coeU (\ r' → isEquiv-code (A r) (A r') (λ v → fst (coeU A r r' v))) r r' (coe-rr-equiv A r)

  GlueT-f-isEquiv : ∀ {l :{♭} Level} (x : Composable l) (u : fst (GlueT-Cofib x)) →
                    isEquiv (El (GlueT-T x u)) 
                            ((El o (λ c → GlueT-B c)) x)
                            (GlueT-f x u)
  GlueT-f-isEquiv (HCom r r' α cα T B) = 
    ∨-elim _ (\ pα → transport (\ (p : Σ \(A : U {_}) → _ → El A)  → isEquiv _ (El (fst p)) (snd p)) 
                               (pair= (snd B pα) ((λ= (\ z → ! (ap= (transport-ap-assoc' (\ X → X) El (snd B pα)))) ∘ transport-→-post ((ap El (snd B pα))) _) ∘ ap= (transport-ap-assoc' (\ H → El (T r' pα) → H) El (snd B pα)) )) 
                               (fst (coe-equiv (\ z → (T z pα)) r' r))) 
             (\ r=r' → id-Equiv {A = El (fst B)} 
                                (relCom-hasHCom ((\ _ → El (fst B))) (comPre (\ _ → (fst B)) El comEl) ((\ (x : Unit{lzero}) → x))))
             coh where
    coh : (x : α) (y : r == r') → _ 
    coh pα id = het-to-hom ((((apdo2 (\ X y → id-Equiv{A = X} y) (ap El (snd B pα)) (hCom=h ((ap El (snd B pα))) _ _ (\ s s' β {t}{t'} t=t' {b}{b'} b=b' → apdo3 {A = U} {B = λ X → I → β → El X} {C = λ X t₁ → El X [ β ↦ (λ v → t₁ s v) ]} {D = λ X t₁ b₁ → El X} {T r pα} (λ a b₁ c → fst (comEl (λ _ → a) s s' β b₁ c)) (snd B pα) t=t' b=b' )) 
                             ∘h transport-=h (λ h → isEquiv _ _ h) ((λ= \ b → (snd (coeU (λ z → T z pα) r r b)) id ))  )
                             ∘h hom-to-het (! (snd (coe-equiv (λ z → T z pα) r r) id)))
                             ∘h (transport-=h (λ p → isEquiv (El (T r pα)) (El (fst p)) (snd p))(pair= (snd B pα) ((λ= (λ z → ! (ap= (transport-ap-assoc' (λ X → X) El (snd B pα)))) ∘ transport-→-post (ap El (snd B pα)) (λ z → fst (coeU (λ z₁ → T z₁ pα) r r z))) ∘ ap= (transport-ap-assoc' (λ H → El (T r pα) → H) El (snd B pα))))))
                             ∘h (transport-=h (λ z → isEquiv (El (GlueT-T (HCom r r α cα T B) z)) ((El o GlueT-B) (HCom r r α cα T B)) (GlueT-f (HCom r r α cα T B) z)) trunc))
  
  GlueT-f-isEquivFill : ∀ {l :{♭} Level} (x : Composable l) (u : fst (GlueT-Cofib x)) →
                    isEquivFill (El (GlueT-T x u)) 
                                ((El o (λ c → GlueT-B c)) x)
                                (GlueT-f x u)
  GlueT-f-isEquivFill x u = isEquiv-isEquivFill _ _ _ (GlueT-f-isEquiv x u)
                            (\ b → hcomEl (HFiber-code {A = (GlueT-T x u)} {B = (GlueT-B x)} (GlueT-f x u) b))

  Glue-data : {l :{♭} Level} → Composable l → GlueData l
  Glue-data c = gluedata (fst (GlueT-Cofib c)) (snd (GlueT-Cofib c)) (GlueT-T c) (GlueT-B c) (GlueT-f c) ( (GlueT-f-isEquivFill c) )

  Glue-Composable : {l :{♭} Level} → (Composable l → U {l})
  Glue-Composable {l} = Glue-code-universal o Glue-data 

  U-code : {l :{♭} Level} → U {ℓ₂ ⊔ lsuc l}
  U-code {l} = (code (Unit{lzero}) 
                     (\ _ → U{l}) 
                     (λ p r r' α {{ c }} T B →  (Glue-Composable{l}) (HCom r r' α c T B) , 
                                                  (\ pα →   ! (Glue-code-universal-α (Glue-data (HCom r r' α c T B)) (inl pα)) ) , 
                                                  (λ r=r' →  ! (Glue-code-universal-α (Glue-data (HCom r r' α c T B)) (inr r=r')) ∘ ap= (transport-constant r=r') ) ))
               <>


  U-code-El : {l :{♭} Level} → El (U-code{l}) == U
  U-code-El = id
