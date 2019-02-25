{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Equiv
open import universe.Universe
open import Glue
open import Path
open import universe.Glue
open import universe.Path
open import Contractible

module universe.Univalence where

  
  ua : {l :{♭} Level} {A B : U{l}} (e : Equiv (El A) (El B)) → Path U A B
  ua {l}{A}{B} e = (\ x → Glue-code-universal (V-to-Glue (Vc A B e x)))  , 
                          Glue-code-universal-α (V-to-Glue (Vc A B e `0)) (inl id) , 
                          Glue-code-universal-α (V-to-Glue (Vc A B e `1)) (inr id)

  uaβ : {l :{♭} Level} {A B : U{l}} (e : Equiv (El A) (El B)) (a : El A)
        → Path _ (coePathU (ua{_}{A}{B} e) a) (fst e a)
  uaβ {l}{A}{B} e a =  (\ z → coe (ap El (snd (snd UA))) (fst combined z)) ,
                       ! (ap (coe (ap El (snd (snd UA)))) reduce) ∘ ap (coe (ap El (snd (snd UA)))) (fst (snd combined)) ,
                       (ap {M = (ap El (snd (snd UA)) ∘ ap El (! (snd (snd UA))))} {N = id} (\ H → coe H (fst e a)) uip ∘ ! (ap= (transport-∘ (\ X → X) (ap El (snd (snd UA))) (ap El (! (snd (snd UA)))))) ) ∘ ap (coe (ap El (snd (snd UA)))) (snd (snd combined))   where
    UA = (ua{_}{A}{B} e)
    a' = (coe (ap El (! (fst (snd UA)))) a)

    reduce : fst (coeU (fst UA) `0 `1 a') == fst (comGlue (\ x → (V-to-Glue (Vc A B e x))) `0 `1 ⊥ (\ x → abort) (a' , \ x → abort x))
    reduce = fst (coeU (fst UA) `0 `1 a') =〈 id 〉
              fst (relCom-relCoe (El o (fst UA)) (comEl' (fst UA)) (\ x → x) `0 `1 a') =〈 ap (\ H → fst (relCom-relCoe (El o (fst UA)) H (\ x → x) `0 `1 a')) reduce2 〉
              fst (relCom-relCoe (El o (fst UA)) (comPre (\ x → (V-to-Glue (Vc A B e x))) (Glue-from-data) comGlue) (\ x → x) `0 `1 a') =〈 id 〉
              fst (comPre (\ x → (V-to-Glue (Vc A B e x))) (Glue-from-data) comGlue (\ x → x) `0 `1 ⊥ (\ x → abort) (a' , \ x → abort x)) =〈 id 〉
              (fst (comGlue (\ x → (V-to-Glue (Vc A B e x))) `0 `1 ⊥ (\ x → abort) (a' , \ x → abort x)) ∎) where
        reduce2 : (comEl' (fst UA)) == comPre (\ x → (V-to-Glue (Vc A B e x))) (Glue-from-data) comGlue 
        reduce2 = comEl-code-subst {A = Glue-from-data} {comA = comGlue} (\ x → (V-to-Glue (Vc A B e x)))

    -- would be an equality with propositional univalence for cofibs
    eq : Path _ (fst (comGlue (\ x → (V-to-Glue (Vc A B e x))) `0 `1 ⊥ (\ x → abort) (a' , \ x → abort x)))
                (fst (comGlue-unaligned (\ x → (V-to-Glue (Vc A B e x))) `0 `1 ⊥ (\ x → abort) (a' , \ x → abort x)))
    eq = comGlue-not∀α (\ x → (V-to-Glue (Vc A B e x))) (not0∨1) `0 `1 ⊥ (\ x → abort) (a' , \ x → abort x)

    unaligned : Path _
                (fst (comGlue-unaligned (\ x → (V-to-Glue (Vc A B e x))) `0 `1 ⊥ (\ x → abort) (a' , \ x → abort x)))
                (coe (ap El (! (snd (snd UA)))) (fst e a))
    unaligned = (\ z → coe (ap El (! (snd (snd UA)))) (fst (comGlue-unaligned-β-V-coe {A = A}{B} e a) z)) ,
                ( ( ap {M = (! (Glue-α ((`0 == `0) ∨ (`0 == `1)) (El o GlueData.T (V-to-Glue (Vc A B ((λ z → fst e z) , snd e) `0))) (El (GlueData.B (V-to-Glue (Vc A B ((λ z → fst e z) , snd e) `0)))) (GlueData.f (V-to-Glue (Vc A B ((λ z → fst e z) , snd e) `0))) (inl id)))} {N = (ap El (! (fst (snd UA))))} (\ H → (fst (comGlue-unaligned (λ x → V-to-Glue (Vc A B ((λ z → fst e z) , snd e) x)) `0 `1 ⊥ (λ x → abort) (coe H a , (λ x → abort x))))) uip ∘ ap {M = (ap El (! (snd (snd UA))) ∘ Glue-α ((`1 == `0) ∨ (`1 == `1)) (El o GlueData.T (V-to-Glue (Vc A B e `1))) (El (GlueData.B (V-to-Glue (Vc A B e `1)))) (GlueData.f (V-to-Glue (Vc A B e `1))) (inr id))} {N = id} (\ H → coe H (fst (comGlue-unaligned (λ x → V-to-Glue (Vc A B ((λ z → fst e z) , snd e) x)) `0 `1 ⊥ (λ x → abort) (coe (! (Glue-α ((`0 == `0) ∨ (`0 == `1)) (El o GlueData.T (V-to-Glue (Vc A B ((λ z → fst e z) , snd e) `0))) (El (GlueData.B (V-to-Glue (Vc A B ((λ z → fst e z) , snd e) `0)))) (GlueData.f (V-to-Glue (Vc A B ((λ z → fst e z) , snd e) `0))) (inl id))) a , (λ x → abort x))))) uip ) ∘ ! (ap= (transport-∘ (\ X → X) (ap El (! (snd (snd UA)))) (Glue-α ((`1 == `0) ∨ (`1 == `1)) (El o GlueData.T (V-to-Glue (Vc A B e `1))) (El (GlueData.B (V-to-Glue (Vc A B e `1)))) (GlueData.f (V-to-Glue (Vc A B e `1))) (inr id)))) ) ∘ ap (coe (ap El (! (snd (snd UA))))) (fst (snd (comGlue-unaligned-β-V-coe e a)))  ,
                ap (coe (ap El (! (snd (snd UA))))) (snd (snd (comGlue-unaligned-β-V-coe e a)))

    combined = ∘Path (hcomEl (Glue-code (\ (_ : Unit{lzero}) → (V-to-Glue (Vc A B e `1))) <>) ) unaligned eq





  idEquivU : {l :{♭} Level} (A : U{l}) → Equiv (El A) (El A)
  idEquivU A = _ , id-Equiv {A = (El A)} (hcomEl A)

  abstract
    idEquivFillU : {l :{♭} Level} (A : U{l}) → isEquivFill (El A) (El A) (\ x → x)
    idEquivFillU A =  \ a → contr-extend-partial (hcomEl (HFiber-code {A = A}{A} (\ x → x) a)) (snd (idEquivU A) a)

  module UARefl {l :{♭} Level} (A : U {l}) where
    eqv :  (x : I) → isEquivFill (El (fst (ua {A = A} {A} (idEquivU A)) x)) (El A) unglue
    eqv x a α t = ((glue _ _ _ _ (∨-elim01 _ (\ x=0 → fst fixa  )
                                               (\ x=1 → fst fixa ))
                                   (fst fixa ,
                                        ∨-elim01 _ (\ _ → id) (\ _ → id))) ,
                     ( \ z → fst (filla z)) , ! (Glueβ _ _)  , ! (snd (snd (filla `1)) (id))) ,
                     (\ pα → pair= (p pα ∘ Glueη _)
                                    (pair= (λ= (\ z → fst (snd (filla z)) pα ) ∘ (fst-transport-Path-left {A = El A} {a0 = unglue} (p pα ∘ Glueη _) _)  ) (pair= uip uip))) where
        filla : ∀ z → _
        filla z = (hcomEl A `1 z α (\ z pα →  fst (snd (t pα)) z) (a , ((\ pα → snd (snd (snd (t pα)))))))
        fixa =  filla `0
    
        p : (pα : _) → _
        p pα =  glue-cong _ _ _ _ _ _
                          (λ= (∨-elim01 _ (\ x=0 → fst (snd fixa) pα ∘ ! (fst (snd (snd (t pα)))) ∘ unglue-α _ (inl x=0)) ((\ x=1 → fst (snd fixa) pα ∘ ! (fst (snd (snd (t pα)))) ∘ unglue-α _ (inr x=1)))))
                          (fst (snd fixa) pα ∘ ! (fst (snd (snd (t pα)))))

    Ctx = Σ \ (B : Set l) → B → El A
    E : Ctx → Set _
    E (B , f) = isEquivFill B (El A) f 

    eqv0 : (x : I) → (x == `0) → isEquivFill (El (fst (ua {A = A} {A} (idEquivU A)) x)) (El A) unglue
    eqv0 x x=0 = transport E (pair= (! (Glue-α _ _ _ _ (inl x=0))) ((λ= \ z → unglue-α z (inl x=0)) ∘ transport-→-pre-inv (\ X → X) (Glue-α _ _ _ _ (inl x=0)) (\x → x) ))
                             (idEquivFillU A)

    eqv1 : (x : I) → (x == `1) → isEquivFill (El (fst (ua {A = A} {A} (idEquivU A)) x)) (El A) unglue
    eqv1 x x=1 = transport E (pair= (! (Glue-α _ _ _ _ (inr x=1))) ((λ= \ z → unglue-α z (inr x=1)) ∘ transport-→-pre-inv (\ X → X) (Glue-α _ _ _ _ (inr x=1)) (\x → x) ))
                             (idEquivFillU A)

    abstract
      fixed-eqv : (x : I) →
                (isEquivFill (El (fst (ua {A = A} {A} (idEquivU A)) x)) (El A) unglue) [ ((x == `0) ∨ (x == `1)) ↦ case01 (eqv0 x) (eqv1 x) ]
      fixed-eqv x = fix-isEquiv _ _ _ (eqv x) ((x == `0) ∨ (x == `1)) (case01 (eqv0 x) (eqv1 x)) 

    module C (x y : I) where
      cof : Cofibs
      cof = (((x == `0) ∨ (x == `1)) ∨ ((y == `0) ∨ (y == `1))) , (Cofib∨ (Cofib∨ Cofib= Cofib=) ((Cofib∨ Cofib= Cofib=)))

      T : fst cof → U
      T = (case (case01 (\ x=0 → (fst (ua {A = A} {A} (idEquivU A)) y))
                                                     (\ x=1 → A))
                                             (case01 (\ _ → A)
                                                     (\ _ → A))
                                             (∨-elim01 _
                                                       (\ x=0 → ∨-elim01 _
                                                                         (\ y=0 → fst (snd (ua {A = A} {A} (idEquivU A))) ∘ ap (fst (ua {A = A} {A} (idEquivU A))) y=0)
                                                                         (\ y=1 → snd (snd (ua {A = A} {A} (idEquivU A))) ∘ ap (fst (ua {A = A} {A} (idEquivU A))) y=1))
                                                       (\ x=1 → ∨-elim01 _
                                                                         (\ y=0 → id)
                                                                         (\ y=1 → id))))

      down : (pα : fst cof) → El (T pα) → El A
      down = (∨-elim _ (∨-elim01 _ (\ _ → unglue)
                                   (\ _ a → a))
                       (∨-elim01 _ (\ _ a → a)
                                   (\ _ a → a))
                       agree) where
         abstract
           agree =  (∨-elim01 _
                         (\ x=0 → ∨-elim01 _
                                           (\ y=0 → het-to-hom (λ=o (\ x x' xeq → (xeq ∘h (transport-=h (\ x → x) (Glue-α _ _ _ _ (inl y=0)))) ∘h !h (hom-to-het (unglue-α x (inl y=0))))  ∘h (transport-=h _ trunc) ))
                                           (\ y=1 → het-to-hom (λ=o (\ x x' xeq → (xeq ∘h (transport-=h (\ x → x) (Glue-α _ _ _ _ (inr y=1)))) ∘h !h (hom-to-het (unglue-α x (inr y=1))))  ∘h (transport-=h _ trunc) )))
                         (\ x=1 → ∨-elim01 _
                                           (\ y=0 → het-to-hom ((transport-=h _ trunc) ))
                                           (\ y=1 → het-to-hom ((transport-=h _ trunc) ))))

      downeq : (pα : fst cof) → isEquivFill _ _ (down pα)
      downeq = (∨-elim _ (∨-elim01 _ (\ _ → fst (fixed-eqv y))
                                     (\ _ a → idEquivFillU A a))
                         (∨-elim01 _
                                   (\ _ a → idEquivFillU A a)
                                   (\ _ a → idEquivFillU A a))
                         (∨-elim01 _
                                   (\ x=0 → ∨-elim01 _
                                                     (\ y=0 → het-to-hom (((( (transport-=h E (((pair= (! (Glue-α _ _ _ _ (inl id))) ((λ= \ z → unglue-α z (inl id)) ∘ transport-→-pre-inv (\ X → X) (Glue-α _ _ _ _ (inl id)) (\x → x) )))))
                                                                             ∘h hom-to-het (! (snd (fixed-eqv `0) (inl id))))
                                                                             ∘h apdo (\ z → fst (fixed-eqv z)) y=0) ) ∘h transport-=h (λ z → isEquivFill (El (T z)) (El A) (down z)) (trunc {x = inl (inl x=0)} {y = inr (inl y=0)} ) ) )
                                                     (\ y=1 → het-to-hom ((( (transport-=h E ((pair= (! (Glue-α _ _ _ _ (inr id))) ((λ= \ z → unglue-α z (inr id)) ∘ transport-→-pre-inv (\ X → X) (Glue-α _ _ _ _ (inr id)) (\x → x) ))))
                                                                             ∘h hom-to-het (! (snd (fixed-eqv `1) (inr id))))
                                                                             ∘h apdo (\ z → fst (fixed-eqv z)) y=1)
                                                                           ∘h transport-=h (λ z → isEquivFill (El (T z)) (El A) (down z)) (trunc {x = inl (inl x=0)} {y = inr (inr y=1)} ) )))
                                   (\ x=1 → ∨-elim01 _
                                                     (\ y=0 → het-to-hom (transport-=h (λ z → isEquivFill (El (T z)) (El A) (down z)) (trunc {x = inl (inr x=1)} {y = inr (inl y=0)} ) )  )
                                                     (\ y=1 → het-to-hom (transport-=h (λ z → isEquivFill (El (T z)) (El A) (down z)) (trunc {x = inl (inr x=1)} {y = inr (inr y=1)} ) )))))

      c : U
      c = Glue-code-universal (gluedata (fst cof) (snd cof) T A down downeq) 

    uarefl : Path (Path U A A) (ua (idEquivU A)) (( \ _ → A) , id , id)
    uarefl = (\ x → (\ y → (C.c x y)) ,   Glue-code-universal-α _ (inr (inl id))   ,  Glue-code-universal-α _ (inr (inr id)) ) ,
                   (pair= (  λ= (\ y →    Glue-code-universal-α _ (inl (inl id))  )  ) (pair= uip uip)) ,
                   pair= (λ= \ y →   Glue-code-universal-α _ (inl (inr id)) ) (pair= uip uip) 
