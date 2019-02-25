
{-# OPTIONS --rewriting  #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Prop
open import Cofibs
open import Kan
open import Path
open import Equiv
open import Interval
open import Glue
open import universe.Universe
open import universe.Path
open import universe.LibFlat
open import directed.DirInterval
open import directed.Covariant
open import directed.Covariant-is-Fibrant
open import directed.UCov
open import directed.universe.Glue-Equiv-Covariant
open import directed.universe.Hom
open import universe.Univalence

module directed.UCov-Univalence where
  open Layered
    
  uacdata : {l :{♭} Level} (A B : UCov l) → Equiv (ElC A) (ElC B) → I → GlueDataUCov l
  uacdata A B eq i = mkGlueDataUCov ((i == `0) ∨ (i == `1))
                                     (case01 (λ _ → A) (λ _ → B))
                                     B
                                     (∨-elim01 _ (λ _ → (fst eq)) (λ _ x → x))
                                     iseq where
     abstract
       iseq =  (∨-elim01 _ (λ _ → isEquiv-isEquivFill _ _ _
                                                     (snd eq)
                                                     (λ b → hcomEl (HFiber-code {A = ElCov A} {ElCov B} (fst eq) b)))
                           (λ _ → isEquiv-isEquivFill _ _ _
                                                      (id-Equiv (hcomEl (ElCov B)))
                                                      (λ b → hcomEl (HFiber-code {A = ElCov B} {ElCov B} (λ z → z) b))))

  uac :  {l :{♭} Level} {A B : UCov l} → Equiv (ElC A) (ElC B) → Path (UCov l) A B
  uac {A = A}{B} eq = (λ i → GlueUCov (uacdata A B eq i)) , GlueUCov-α (uacdata A B eq `0) (inl id) , GlueUCov-α (uacdata A B eq `1) (inr id)

  
  
  
  
  -- don't seem to need to know that these are related...
  idEquivUCov : {l :{♭} Level} (A : UCov l) → Equiv (ElC A) (ElC A)
  idEquivUCov A =  _ , idEquiv-from-= {A = ElC A}{ ElC A} (hcomEl (ElCov A)) (\ x → x) id id 
    
  idEquivFillUCov : {l :{♭} Level} (A : UCov l) → isEquivFill (ElC A) (ElC A) (\ x → x)
  idEquivFillUCov A = idEquivFillU (ElCov A)



  -- FIXME: eliminate the copy and paste with universe.Univalence for UKan
  -- conceptually, we could prove the full univalence axiom for UKan and UCov, and then this should be easy.
  -- but here we do it directly for expedience.

  module UAReflC {l :{♭} Level} (A : UCov l) where

    abstract
      eqv :  (x : I) → isEquivFill (ElC (fst (uac {A = A} {A} (idEquivUCov A)) x)) (ElC A) unglue
      eqv x a α t = ((glue _ _ _ _ (∨-elim01 _ (\ x=0 → fst fixa  )
                                               (\ x=1 → fst fixa ))
                                   (fst fixa ,
                                        ∨-elim01 _ (\ _ → id) (\ _ → id))) ,
                     ( \ z → fst (filla z)) , ! (Glueβ _ _)  , ! (snd (snd (filla `1)) (id))) ,
                     (\ pα → pair= (p pα ∘ Glueη _)
                                    (pair= (λ= (\ z → fst (snd (filla z)) pα ) ∘ (fst-transport-Path-left {A = ElC A} {a0 = unglue} (p pα ∘ Glueη _) _)  ) (pair= uip uip))) where
        filla : ∀ z → _
        filla z = (hcomEl (ElCov A) `1 z α (\ z pα →  fst (snd (t pα)) z) (a , ((\ pα → snd (snd (snd (t pα)))))))
        fixa =  filla `0
    
        p : (pα : _) → _
        p pα =  glue-cong _ _ _ _ _ _
                          (λ= (∨-elim01 _ (\ x=0 → fst (snd fixa) pα ∘ ! (fst (snd (snd (t pα)))) ∘ unglue-α _ (inl x=0)) ((\ x=1 → fst (snd fixa) pα ∘ ! (fst (snd (snd (t pα)))) ∘ unglue-α _ (inr x=1)))))
                          (fst (snd fixa) pα ∘ ! (fst (snd (snd (t pα)))))

    Ctx = Σ \ (B : Set l) → B → ElC A
    E : Ctx → Set _
    E (B , f) = isEquivFill B (ElC A) f 

    eqv0 : (x : I) → (x == `0) → isEquivFill (ElC (fst (uac {A = A} {A} (idEquivUCov A)) x)) (ElC A) unglue
    eqv0 x x=0 = transport E (pair= (! (Glue-α _ _ _ _ (inl x=0))) ((λ= \ z → unglue-α z (inl x=0)) ∘ transport-→-pre-inv (\ X → X) (Glue-α _ _ _ _ (inl x=0)) (\x → x) ))
                             (idEquivFillUCov A)

    eqv1 : (x : I) → (x == `1) → isEquivFill (ElC (fst (uac {A = A} {A} (idEquivUCov A)) x)) (ElC A) unglue
    eqv1 x x=1 = transport E (pair= (! (Glue-α _ _ _ _ (inr x=1))) ((λ= \ z → unglue-α z (inr x=1)) ∘ transport-→-pre-inv (\ X → X) (Glue-α _ _ _ _ (inr x=1)) (\x → x) ))
                             (idEquivFillUCov A)

    abstract
      fixed-eqv : (x : I) →
                (isEquivFill (ElC (fst (uac {A = A} {A} (idEquivUCov A)) x)) (ElC A) unglue) [ ((x == `0) ∨ (x == `1)) ↦ case01 (eqv0 x) (eqv1 x) ]
      fixed-eqv x = fix-isEquiv _ _ _ (eqv x) ((x == `0) ∨ (x == `1)) (case01 (eqv0 x) (eqv1 x)) 

    module C (x y : I) where
      cof : Cofibs
      cof = (((x == `0) ∨ (x == `1)) ∨ ((y == `0) ∨ (y == `1))) , (Cofib∨ (Cofib∨ Cofib= Cofib=) ((Cofib∨ Cofib= Cofib=)))

      T : fst cof → UCov l
      T = (case (case01 (\ x=0 → (fst (uac {A = A} {A} (idEquivUCov A)) y))
                                                     (\ x=1 → A))
                                             (case01 (\ _ → A)
                                                     (\ _ → A))
                                             (∨-elim01 _
                                                       (\ x=0 → ∨-elim01 _
                                                                         (\ y=0 → fst (snd (uac {A = A} {A} (idEquivUCov A))) ∘ ap (fst (uac {A = A} {A} (idEquivUCov A))) y=0)
                                                                         (\ y=1 → snd (snd (uac {A = A} {A} (idEquivUCov A))) ∘ ap (fst (uac {A = A} {A} (idEquivUCov A))) y=1))
                                                       (\ x=1 → ∨-elim01 _
                                                                         (\ y=0 → id)
                                                                         (\ y=1 → id))))

      down : (pα : fst cof) → ElC (T pα) → ElC A
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
                                     (\ _ a → idEquivFillUCov A a))
                         (∨-elim01 _
                                   (\ _ a → idEquivFillUCov A a)
                                   (\ _ a → idEquivFillUCov A a))
                         (∨-elim01 _
                                   (\ x=0 → ∨-elim01 _
                                                     (\ y=0 → het-to-hom (((( (transport-=h E (((pair= (! (Glue-α _ _ _ _ (inl id))) ((λ= \ z → unglue-α z (inl id)) ∘ transport-→-pre-inv (\ X → X) (Glue-α _ _ _ _ (inl id)) (\x → x) )))))
                                                                             ∘h hom-to-het (! (snd (fixed-eqv `0) (inl id))))
                                                                             ∘h apdo (\ z → fst (fixed-eqv z)) y=0) ) ∘h transport-=h (λ z → isEquivFill (ElC (T z)) (ElC A) (down z)) (trunc {x = inl (inl x=0)} {y = inr (inl y=0)} ) ) )
                                                     (\ y=1 → het-to-hom ((( (transport-=h E ((pair= (! (Glue-α _ _ _ _ (inr id))) ((λ= \ z → unglue-α z (inr id)) ∘ transport-→-pre-inv (\ X → X) (Glue-α _ _ _ _ (inr id)) (\x → x) ))))
                                                                             ∘h hom-to-het (! (snd (fixed-eqv `1) (inr id))))
                                                                             ∘h apdo (\ z → fst (fixed-eqv z)) y=1)
                                                                           ∘h transport-=h (λ z → isEquivFill (ElC (T z)) (ElC A) (down z)) (trunc {x = inl (inl x=0)} {y = inr (inr y=1)} ) )))
                                   (\ x=1 → ∨-elim01 _
                                                     (\ y=0 → het-to-hom (transport-=h (λ z → isEquivFill (ElC (T z)) (ElC A) (down z)) (trunc {x = inl (inr x=1)} {y = inr (inl y=0)} ) )  )
                                                     (\ y=1 → het-to-hom (transport-=h (λ z → isEquivFill (ElC (T z)) (ElC A) (down z)) (trunc {x = inl (inr x=1)} {y = inr (inr y=1)} ) )))))

      c : UCov l
      c = GlueUCov (Gluedata-cov (fst cof) (snd cof) T A down downeq)

    abstract
      uarefl : Path (Path (UCov l) A A) (uac (idEquivUCov A)) (( \ _ → A) , id , id)
      uarefl = (\ x → (\ y → (C.c x y)) ,   GlueUCov-α _ (inr (inl id))   ,  GlueUCov-α _ (inr (inr id)) ) ,
                    (pair= (  λ= (\ y →    GlueUCov-α _ (inl (inl id))  )  ) (pair= uip uip)) ,
                    pair= (λ= \ y →   GlueUCov-α _ (inl (inr id)) ) (pair= uip uip) 

