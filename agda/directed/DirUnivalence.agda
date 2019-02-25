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
open import universe.Pi
open import universe.LibFlat
open import directed.DirInterval
open import directed.Covariant
open import directed.Covariant-is-Fibrant
open import directed.UCov
open import directed.universe.Glue-Equiv-Covariant
open import directed.universe.FunGlue
open import directed.universe.Hom
import directed.DirUnivalenceReflection
open import directed.universe.UCov-Com
import directed.UCov-Univalence

module directed.DirUnivalence where

  open Layered

  private
    -- path univalence for UCov
    ua :  {l :{♭} Level} {A B : UCov l} → Equiv (ElC A) (ElC B) → Path (UCov l) A B
    ua {A = A}{B} eq = directed.UCov-Univalence.uac eq

    duahom :  {l :{♭} Level} (A B : UCov l) → (f : ElC A → ElC B) → Hom (UCov l) A B
    duahom = directed.DirUnivalenceReflection.duahom

    duaβ : {l :{♭} Level} (A B : UCov l) → (f : ElC A → ElC B) → Path _ f (dcoe A B (duahom A B f))
    duaβ = directed.DirUnivalenceReflection.duaβ

    duaηfun : {l :{♭} Level} → (A B : UCov l) → (p : Hom _ A B) → (i : 𝟚) → ElC ((fst p) i) → ElC (fst (duahom A B (dcoe A B p)) i)
    duaηfun = directed.DirUnivalenceReflection.duaηfun

  open directed.DirUnivalenceReflection using (ηeq0;ηeq1)

  postulate
    covEquivAx : {l :{♭} Level} 
      (p q : 𝟚 → UCov l)
      (f : (i : 𝟚) → ElC (p i) → ElC (q i))
      (eq0 : isEquiv _ _ (f ``0))
      (eq1 : isEquiv _ _ (f ``1))
      → --------------------------------------------------------------------------------------------------
      (i : 𝟚) → isEquiv _ _ (f i) [ i == ``0 ↦ (λ i=0 → coe (ap (λ i → isEquiv _ _ (f i)) (! i=0)) eq0) ,
                                    i == ``1 ↦ (λ i=1 → coe (ap (λ i → isEquiv _ _ (f i)) (! i=1)) eq1) ]
    -- Note: the fact that this restricts to eq0 and eq1 on 0 and 1 is not essential:
    -- if it didn't, we could make one that did using Equiv.fix-isEquiv

  uac-refl-from-= : {l :{♭} Level}{A B : UCov l}(f : ElC A → ElC B)
                      (eq : A == B)
                    → (eq2 : f == coe (ap (λ X → (ElC A → ElC X)) eq) (λ x → x))
                    → Path (Path (UCov l) A B)
                           (ua {A = A} {B} (_ , idEquiv-from-= {A = (ElC A)} {(ElC B)} (hcomEl (ElCov A)) f (ap ElC eq) eq2))
                           ((\ _ → A) , id , eq)
  uac-refl-from-= {A = A} f id id = directed.UCov-Univalence.UAReflC.uarefl A

  pathPathExchange : ∀ {l : Level} {A : Set l} {a0 a1 : A} → (f g : Path A a0 a1)
          → (PathO (\ x → Path A (fst f x) (fst g x)) ((λ _ → a0) , ! (fst (snd f))  , ! (fst (snd g))) ((λ _ → a1) , ! (snd (snd f)) ,  ! (snd (snd g))))
          → Path (Path A a0 a1) f g
  pathPathExchange f g h = (λ x → (\ z → fst (fst h z) x) , ap (\ Z → fst Z x) (fst (snd h))  , ap (\ Z → fst Z x) (snd (snd h))) , pair= (λ= \ x → fst (snd (fst h x))) (pair= uip uip) , pair= ((λ= \ x → snd (snd (fst h x)))) (pair= uip uip)

  duaη : {l :{♭} Level} (A B : UCov l) → (p : Hom _ A B) → Path _ p (duahom A B (dcoe A B p))
  duaη {l} A B p = pathHomExchange _ _
                                   ((λ i → fst (fixpath i))
                                   , fixpath0eq1  
                                   , fixpath1eq1) where

    equiv0 : isEquiv (ElC (fst p ``0)) (ElC (fst (duahom A B (dcoe A B p)) ``0)) (duaηfun A B p ``0)
    equiv0 = idEquiv-from-= (hcomEl (ElCov (fst p ``0))) (duaηfun A B p ``0) (! (Glue-α _ _ _ _ (inl id)) ∘ ap ElC (fst (snd p))) (ηeq0 A B p)

    equiv1 : isEquiv (ElC (fst p ``1)) (ElC (fst (duahom A B (dcoe A B p)) ``1)) (duaηfun A B p ``1)
    equiv1 = idEquiv-from-= (hcomEl (ElCov (fst p ``1))) (duaηfun A B p ``1) (! (Glue-α _ _ _ _ (inr id)) ∘ ap ElC (snd (snd p))) (ηeq1 A B p)

    equiv : ∀ i → _
    equiv i = covEquivAx (fst p) (fst (duahom A B (dcoe A B p))) (duaηfun A B p) equiv0 equiv1 i

    path : ∀ i → Path (UCov l) ((fst p) i) (fst (duahom A B (dcoe A B p)) i)
    path i = ua {A = ((fst p) i)} {((fst (duahom A B (dcoe A B p))) i)} (duaηfun A B p i , fst (equiv i))

    path0 : Path (UCov l) ((fst p) ``0) (fst (duahom A B (dcoe A B p)) ``0)
    path0 = ua {A = ((fst p) ``0)} {(fst (duahom A B (dcoe A B p)) ``0)} (duaηfun A B p ``0 , equiv0)

    path0eq : path0 == path ``0
    path0eq = ap (ua {A = ((fst p) ``0)} {(fst (duahom A B (dcoe A B p)) ``0)}) (pair= id (fst (snd (equiv ``0)) id))

    path1 : Path (UCov l) ((fst p) ``1) (fst (duahom A B (dcoe A B p)) ``1)
    path1 = ua {A = (fst p) ``1} {(fst (duahom A B (dcoe A B p)) ``1)} (duaηfun A B p ``1 , equiv1)

    path1eq : path1 == path ``1
    path1eq = ap (ua {A = ((fst p) ``1)} {(fst (duahom A B (dcoe A B p)) ``1)}) (pair= id (snd (snd (equiv ``1)) id))

    fixpath0' : Path _ path0 ((λ _ → A) , ! (fst (snd p)) , ! (FunGlueUCov0 (fungluedata A B (dcoe A B p) ``0) id))
    fixpath0' =  (\ x → fst q x ) ,
                 ap (\ H → ua (duaηfun A B p ``0 , H)) (ap (\ H → idEquiv-from-= (hcomEl (ElCov (fst p ``0))) (duaηfun A B p ``0) (fst H) (snd H)) (pair= uip uip)) ∘ fst (snd q)  ,
                 pair= (λ= \ _ → fst (snd p) ) (pair= uip uip) ∘ snd (snd q)  where 
      ηeq0' : (duaηfun A B p ``0) == coe (ap (λ X → ((ElC (fst p ``0)) → ElC X)) (! (fst (snd (duahom A B (dcoe A B p)))) ∘ fst (snd p) )) (λ x → x)
      ηeq0' =  het-to-hom (!h (transport-=h (\ X → X) ((ap (λ X → ElC (fst p ``0) → ElC X) (! (FunGlueUCov0 (fungluedata A B (dcoe A B p) ``0) id)) ∘ ap (λ X → ElC (fst p ``0) → ElC X) (fst (snd p)))) {\ x → x}) ∘h transport-=h (\ x → x) (ap (λ X → ElC (fst p ``0) → X) (! (Glue-α _ _ _ _ (inl id))) ∘ ap (λ x → ElC (fst p ``0) → ElC x) (fst (snd p))) {\ x → x})  ∘ ηeq0 A B p

      equiv0' : isEquiv (ElC (fst p ``0)) (ElC (fst (duahom A B (dcoe A B p)) ``0)) (duaηfun A B p ``0)
      equiv0' = idEquiv-from-= (hcomEl (ElCov (fst p ``0))) (duaηfun A B p ``0) (ap ElC (! (fst (snd (duahom A B (dcoe A B p)))) ∘ fst (snd p))) ηeq0'

      path0' : Path (UCov l) ((fst p) ``0) (fst (duahom A B (dcoe A B p)) ``0)
      path0' = ua {A = ((fst p) ``0)} {(fst (duahom A B (dcoe A B p)) ``0)} (duaηfun A B p ``0 , equiv0')

      q = uac-refl-from-= {A = ((fst p) ``0)} {(fst (duahom A B (dcoe A B p)) ``0)} (duaηfun A B p ``0)
                          (! (fst (snd (duahom A B (dcoe A B p)))) ∘ fst (snd p) )
                          (  ηeq0'  )

    fixpath1' : Path _ path1 ((λ _ → B) , ! (snd (snd p)) , ! (FunGlueUCov1 (fungluedata A B (dcoe A B p) ``1) id))
    fixpath1' =  (\ x → fst q x ) ,
                 ap (\ H → ua (duaηfun A B p ``1 , H)) (ap (\ H → idEquiv-from-= (hcomEl (ElCov (fst p ``1))) (duaηfun A B p ``1) (fst H) (snd H)) (pair= uip uip)) ∘ fst (snd q)  ,
                 pair= (λ= \ _ → snd (snd p) ) (pair= uip uip) ∘ snd (snd q)  where 
      ηeq1' : (duaηfun A B p ``1) == coe (ap (λ X → ((ElC (fst p ``1)) → ElC X)) (! (snd (snd (duahom A B (dcoe A B p)))) ∘ snd (snd p) )) (λ x → x)
      ηeq1' = het-to-hom (!h (transport-=h (\ X → X) ((ap (λ X → ElC (fst p ``1) → ElC X) (! (FunGlueUCov1 (fungluedata A B (dcoe A B p) ``1) id)) ∘ ap (λ X → ElC (fst p ``1) → ElC X) (snd (snd p)))) {\ x → x}) ∘h transport-=h (\ x → x) (ap (λ X → ElC (fst p ``1) → X) (! (Glue-α _ _ _ _ (inr id))) ∘ ap (λ x → ElC (fst p ``1) → ElC x) (snd (snd p))) {\ x → x})  ∘ ηeq1 A B p

      equiv1' : isEquiv (ElC (fst p ``1)) (ElC (fst (duahom A B (dcoe A B p)) ``1)) (duaηfun A B p ``1)
      equiv1' = idEquiv-from-= (hcomEl (ElCov (fst p ``1))) (duaηfun A B p ``1) (ap ElC (! (snd (snd (duahom A B (dcoe A B p)))) ∘ snd (snd p))) ηeq1'

      path1' : Path (UCov l) ((fst p) ``1) (fst (duahom A B (dcoe A B p)) ``1)
      path1' = ua {A = ((fst p) ``1)} {(fst (duahom A B (dcoe A B p)) ``1)} (duaηfun A B p ``1 , equiv1')

      q = uac-refl-from-= {A = ((fst p) ``1)} {(fst (duahom A B (dcoe A B p)) ``1)} (duaηfun A B p ``1)
                          (! (snd (snd (duahom A B (dcoe A B p)))) ∘ snd (snd p) )
                          (  ηeq1'  )

    fixpath0 : ∀ i (i=0 : i == ``0) j → Path (UCov l) ((fst p) i) (fst (duahom A B (dcoe A B p)) i)
    fixpath0 .``0 id j = fst fixpath0' j

    fixpath1 : ∀ i (i=1 : i == ``1) j → Path (UCov l) ((fst p) i) (fst (duahom A B (dcoe A B p)) i)
    fixpath1 .``1 id j = fst fixpath1' j

    fixpath0eq0 : ∀ i (i=0 : i == ``0) → fixpath0 i i=0 `0 == path i
    fixpath0eq0 .``0 id = path0eq ∘ fst (snd fixpath0')

    fixpath1eq0 : ∀ i (i=1 : i == ``1) → fixpath1 i i=1 `0 == path i
    fixpath1eq0 .``1 id = path1eq ∘ fst (snd fixpath1')

    fixpath : ∀ i → _
    fixpath i = hcomEl (Path-code-universal ((λ _ → UCovU l) , ((fst p) i) , (fst (duahom A B (dcoe A B p)) i)))
                       `0 `1 ((i == ``0) ∨ (i == ``1))
                       (λ j → cased01 (λ i=0 → fixpath0 i i=0 j) (λ i=1 → fixpath1 i i=1 j))
                       (path i , ∨-elimd01 _ (fixpath0eq0 i) (fixpath1eq0 i))

    fixpath0eq1 : fst (fixpath ``0) == ((λ _ → A) , ! (fst (snd p)) , ! (FunGlueUCov0 (fungluedata A B (dcoe A B p) ``0) id))
    fixpath0eq1 = (snd (snd fixpath0')) ∘ ! (fst (snd (fixpath ``0)) (inl id)) 

    fixpath1eq1 : fst (fixpath ``1) == ((λ _ → B) , ! (snd (snd p)) , ! (FunGlueUCov1 (fungluedata A B (dcoe A B p) ``1) id))
    fixpath1eq1 = (snd (snd fixpath1')) ∘ ! (fst (snd (fixpath ``1)) (inr id))  


  dua : {l :{♭} Level} (A B : UCov l) → QEquiv (ElC A → ElC B) (Hom _ A B)
  dua {l} A B = duahom A B ,
                (dcoe A B) ,
                (λ f → !Path (hcomEl (Πcode-universal (ElCov A , λ _ → ElCov B))) (duaβ A B f)) ,
                (λ p → !Path (hcomEl (Hom-code-universal (UCovU l , A , B))) (duaη A B p))

  -- UCovSegal : {l :{♭} Level} → hasDHCom (UCov l)
  -- UCovSegal = {!!}

