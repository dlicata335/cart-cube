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
open import directed.Segal
open import directed.Covariant-is-Fibrant
open import directed.UCov
open import directed.universe.Glue-Equiv-Covariant
open import directed.universe.FunGlue
open import directed.universe.Hom

module directed.DirUnivalenceReflection where

  open Layered

  duahom :  {l :{♭} Level} (A B : UCov l) → (f : ElC A → ElC B) → Hom (UCov l) A B
  duahom A B f = (λ i → FunGlueUCov (fungluedata A B f i)) ,
                        FunGlueUCov0 (fungluedata A B f ``0) id , 
                        FunGlueUCov1 (fungluedata A B f ``1) id

  abstract
    -- FIXME: why didn't this need to change with aligning the Kan operation for funglue ?
    duaβ : {l :{♭} Level} (A B : UCov l) → (f : ElC A → ElC B) → Path _ f (dcoe A B (duahom A B f))
    duaβ {l} A B f = (λ i a → coe (ap ElC (FunGlueUCov1 (fungluedata A B f ``1) id)) (fst (path a i))) , patheq0 , patheq1 where
  
      p : 𝟚 → Set l
      p = ElC o (fst (duahom A B f))
  
      covp : relCov p
      covp = dcomEl' (fst (duahom A B f))
  
      patht : (a : ElC A) (j : I) (i : 𝟚)  → (j == `0) ∨ (j == `1) → (p i)
      patht a j i = ∨-elim _ (λ _ → glue _ _ _ _ (∨-elim _ (λ _ → a) (λ _ → f a) (λ i=0 i=1 → abort (diabort (i=1 ∘ ! i=0)))) (f a , ∨-elim _ (λ _ → id) (λ _ → id) (λ _ _ → uip)))
                            (λ _ → (fst (dcoetoi (fst (duahom A B f)) i (coe (ap ElC (! (FunGlueUCov0 (fungluedata A B f ``0) id))) a))))
                            (λ j=0 j=1 → abort (iabort (j=1 ∘ ! j=0)))
  
      path : (a : ElC A) (j : I) → _
      path a j = covp (λ x → x) ``1 ((j == `0) ∨ (j == `1)) (patht a j)
                     (glue _ _ _ _ (∨-elim _ (λ _ → a) (λ _ → f a) (λ i=0 i=1 → abort (diabort (i=1 ∘ ! i=0)))) (f a , ∨-elim _ (λ _ → id) (λ _ → id) (λ _ _ → uip))
                     , ∨-elim _ (λ _ → id)
                                (λ _ →  ! (move-transport-right (λ X → X) (Glue-α _ _ _ _ (inl id)) (glue-α _ _ (inl id)) )
                                        ∘ (het-to-hom (_∘h_ (!h (transport-=h (λ X → X) (! (Glue-α _ _ _ _ (inl id))) {a}))
                                          (transport-=h (λ X → X) (ap ElC (! (FunGlueUCov0 (fungluedata A B f ``0) id))) {a})))
                                        ∘ ! (snd (snd (dcoetoi (fst (duahom A B f)) ``0 (coe (ap ElC (! (FunGlueUCov0 (fungluedata A B f ``0) id))) a))) id))
                                (λ j=0 j=1 → abort (iabort (j=1 ∘ ! j=0))))
  
      patheq0 : _
      patheq0 = λ= λ a → het-to-hom (_∘h_ (_∘h_ (transport-=h (λ X → X) (! (Glue-α _ _ _ _ (inr id))))
                                    (hom-to-het ((move-transport-right (λ X → X) (Glue-α _ _ _ _ (inr id)) (glue-α _ _ (inr id))))))
                                    (transport-=h (λ X → X) (ap ElC (FunGlueUCov1 (fungluedata A B f ``1) id))))
                         ∘ ! (ap (coe (ap ElC (FunGlueUCov1 (fungluedata A B f ``1) id))) (fst (snd (path a `0)) (inl id)))
  
      patheq1 : _
      patheq1 = λ= λ a → ! (ap (coe (ap ElC (FunGlueUCov1 (fungluedata A B f ``1) id))) (fst (snd (path a `1)) (inr id)))

    duaηfun' : {l :{♭} Level} → (A : 𝟚 → UCov l) → (x : 𝟚) → ElC (A x) → ElC (fst (duahom (A ``0) (A ``1) (dcoe𝟚U A)) x)
    duaηfun' A x a = glue _ _ _ _ (∨-elimd01 _
                                            (\ x=0 → transport (ElC o A) x=0 a)
                                            (\ x=1 → transport (ElC o A) x=1 a))
                                            (fst useh ,
                                            ∨-elimd01 _ (\ x=0 → fst (snd (snd useh)) x=0 ∘ pf x a x=0) (snd (snd (snd useh)))) where
      -- FIXME: make homogEl : hasHomog El a lemma
      h = relCov-relHomog' (ElC o A) (dcomEl' A)
  
      useh = (h (\ x → x) x ⊥ (\ z x → abort x) (a , (\ x → abort x)))
  
      pf : (x : 𝟚) (a : ElC (A x)) → (x=0 : x == ``0) →
           dcoe𝟚U A (transport (λ x₁ → El (ElCov (A x₁))) x=0 a)  ==
           fst
             (dcomEl (A o (λ x₁ → x₁)) ``1 ⊥ (λ z x₁ → abort x₁)
              (transport
               (λ x₁ → ((ElC o A) o (λ x₂ → x₂)) x₁ [ ⊥ ↦ (λ x₂ → abort x₂) ]) x=0
               (a , (λ x₁ → abort x₁))))
      pf .``0 a id = id
  
    duaηfun : {l :{♭} Level} → (A B : UCov l) → (p : Hom _ A B) → (i : 𝟚) → ElC ((fst p) i) → ElC (fst (duahom A B (dcoe A B p)) i)
    duaηfun {l} A B p i x = coe (-- (FunGlue-eq (fungluedata A B (dcoe A B p) i)) ∘
                                    ap (λ X → preduafun i (fst (fst X)) (snd (fst X)) (snd X))
                                              (pair= (×= (ap ElC (fst (snd p))) (ap ElC (snd (snd p))))
                                                     (het-to-hom (_∘h_ (λ=o (λ a1 a2 aeq →
                                                                       _∘h_ (!h (transport-=h (λ X → X) (ap (λ x₁ → El (fst (ElCov'{l}) x₁)) (snd (snd p)))))
                                                                       (apdo (λ a → fst (dcomEl' (fst p) (λ x₁ → x₁) ``1 ⊥ (λ z → abort) (a , (λ x₁ → abort x₁))))
                                                                       (! (het-to-hom (_∘h_ (!h aeq) (transport-=h (λ X → X) (ap ElC (! (fst (snd p)))))))))))
                                                                 (transport-=h (λ v → fst v → snd v) (×= (ap ElC (fst (snd p))) (ap ElC (snd (snd p))))))))
                                         -- ∘ ! (FunGlue-eq (fungluedata ((fst p) ``0) ((fst p) ``1) _ i))
                                         )
                            (duaηfun' (fst p) i x)


    ηeq0 : {l :{♭} Level} (A B : UCov l) → (p : Hom _ A B) →
          (duaηfun A B p ``0) == coe (ap (λ X → ((ElC (fst p ``0)) → X)) (! (Glue-α _ _ _ _ (inl id)) ∘ ap ElC (fst (snd p)))) (λ x → x) 
    ηeq0 {l} A B p = het-to-hom (_∘h_ (!h (transport-=h (λ X → X) (ap (λ X → El (ElCov (fst p ``0)) → X)
                               (!
                                (Glue-α _ _ _ _ (inl id))
                                ∘ ap ElC (fst (snd p))))))
                           (λ=o λ a a' aeq → _∘h_ (_∘h_ aeq
                                                  (_∘h_ (hom-to-het (glue-α _ _ (inl id))) (!h (transport-=h (λ X → X) (Glue-α _ _ _ _ (inl id))))))
                                                  (transport-=h (λ X → X) (-- (FunGlue-eq (fungluedata A B (dcoe A B p) ``0)) ∘
                                                  ap (λ X → preduafun ``0 (fst (fst X)) (snd (fst X)) (snd X))
                                                       (pair= (×= (ap ElC (fst (snd p))) (ap ElC (snd (snd p))))
                                                              (het-to-hom (_∘h_ (λ=o (λ a1 a2 aeq →
                                                                                _∘h_ (!h (transport-=h (λ X → X) (ap (λ x₁ → El (fst (ElCov'{l}) x₁)) (snd (snd p)))))
                                                                                (apdo (λ a → fst (dcomEl' (fst p) (λ x₁ → x₁) ``1 ⊥ (λ z → abort) (a , (λ x₁ → abort x₁))))
                                                                                (! (het-to-hom (_∘h_ (!h aeq) (transport-=h (λ X → X) (ap ElC (! (fst (snd p)))))))))))
                                                                          (transport-=h (λ v → fst v → snd v) (×= (ap ElC (fst (snd p))) (ap ElC (snd (snd p))))))))
                                                  -- ∘ ! (FunGlue-eq (fungluedata ((fst p) ``0) ((fst p) ``1) _ ``0))
                                                  ))))
  
    ηeq1 : {l :{♭} Level} (A B : UCov l) → (p : Hom _ A B) →
          (duaηfun A B p ``1) == coe (ap (λ X → ((ElC (fst p ``1)) → X)) (! (Glue-α _ _ _ _ (inr id)) ∘ ap ElC (snd (snd p)))) (λ x → x)
    ηeq1 {l} A B p = het-to-hom (_∘h_ (!h (transport-=h (λ X → X) (ap (λ X → El (ElCov (fst p ``1)) → X)
                               (!
                                (Glue-α _ _ _ _ (inr id))
                                ∘ ap ElC (snd (snd p))))))
                           (λ=o λ b b' beq → _∘h_ (_∘h_ beq
                                                  (_∘h_ (hom-to-het (glue-α _ _ (inr id))) (!h (transport-=h (λ X → X) (Glue-α _ _ _ _ (inr id))))))
                                                  ((transport-=h (λ X → X) (-- (FunGlue-eq (fungluedata A B (dcoe A B p) ``1)) ∘
                                                  ap (λ X → preduafun ``1 (fst (fst X)) (snd (fst X)) (snd X))
                                                       (pair= (×= (ap ElC (fst (snd p))) (ap ElC (snd (snd p))))
                                                              (het-to-hom (_∘h_ (λ=o (λ a1 a2 aeq →
                                                                                _∘h_ (!h (transport-=h (λ X → X) (ap (λ x₁ → El (fst (ElCov'{l}) x₁)) (snd (snd p)))))
                                                                                (apdo (λ a → fst (dcomEl' (fst p) (λ x₁ → x₁) ``1 ⊥ (λ z → abort) (a , (λ x₁ → abort x₁))))
                                                                                (! (het-to-hom (_∘h_ (!h aeq) (transport-=h (λ X → X) (ap ElC (! (fst (snd p)))))))))))
                                                                          (transport-=h (λ v → fst v → snd v) (×= (ap ElC (fst (snd p))) (ap ElC (snd (snd p))))))))
                                                  -- ∘ ! (FunGlue-eq (fungluedata ((fst p) ``0) ((fst p) ``1) _ ``1))
                                                  )))))

