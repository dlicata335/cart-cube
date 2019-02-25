{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Prop
open import Cofibs
open import Kan
open import Path
open import Interval
open import directed.DirInterval
open import directed.Covariant
open import universe.Universe
open import directed.Covariant-is-Fibrant
open import universe.LibFlat
open import directed.UCov
open import directed.universe.Glue-Equiv-Covariant
open import universe.U
open import universe.Path
open import Equiv

module directed.universe.UCov-Com where

  open Layered

  private
  
    -- Note: adjustments were getting pretty heavy below,
    -- so threw in enough rewrites to make it easy

    -- FIXME are these in scope in importing files?

    ElCov-case : ∀ {l :{♭} Level} {α β : Set} {{ cα : Cofib α}} {{ cβ : Cofib β}}
            → {A : α → UCov l} {B : β → UCov l}
              {compat : (x : α) → (y : β) → A x == B y}
              (x : α ∨ β)
              → ElCov (case A B compat x) ==
                case (\ x → ElCov (A x)) (\ y → ElCov (B y)) (\ x y → ap ElCov (compat x y)) x
    ElCov-case = ∨-elim _ (\ _ → id) ((\ _ → id)) (\ _ _ → uip)
    {-# REWRITE ElCov-case #-}
  
    ap-∘ :  {l1 l2 : Level} {A : Set l1} {B : Set l2} {M N P : A}
            (f : A → B) (p : M == N) (q : N == P)
            → ap f (q ∘ p) == (ap f q ∘ ap f p)
    ap-∘ f id id = id
    {-# REWRITE ap-∘ #-}
  
    ap-o :  {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3} {M N : A}
            (f : A → B) (g : B → C) (p : M == N)
            → ap g (ap f p) == ap (\x → g (f x)) p
    ap-o f g id = id
    {-# REWRITE ap-o #-}


  -- a composition problem in UCov

  record ComposableUCov (l :{♭} Level) : Set (lmax ℓ₂ (lsuc l)) where
    constructor HComCov
    field
      r r' : I 
      α : Set
      c : Cofib α
      T : I → α → UCov l
      B : _[_↦_] (UCov l) α {{c}} (T r)

  module _ {l :{♭} Level} where

    -- underlying composition problem in U
    forget-composable : ComposableUCov l → Composable l
    forget-composable (HComCov r r' α c T B) =
      HCom r r' α c (\ z pα → ElCov (T z pα)) (ElCov (fst B) , (\ pα → ap ElCov (snd B pα))) 

    -- have to copy and paste to prove they land in UCov
    GlueT-T-Cov : (c : ComposableUCov l) → (fst (GlueT-Cofib (forget-composable c))) → UCov l
    GlueT-T-Cov (HComCov r r' α c T B) = (case (\ pα → (T r' pα))
                                         (\ r=r' → (fst B)) 
                                         (\ pα r=r' → (snd B pα) ∘ ap (\ x → (T x pα)) (! r=r'))) 

    GlueT-B-Cov : (c : ComposableUCov l) → UCov l
    GlueT-B-Cov (HComCov r r' α c T B) = (fst B)

    Composable-to-data : ComposableUCov l → GlueDataUCov l
    Composable-to-data H = Gluedata-cov ((fst o GlueT-Cofib o forget-composable) H)
                                        (snd (((GlueT-Cofib o forget-composable) H)))
                                        ((GlueT-T-Cov H))
                                        (GlueT-B-Cov H)
                                        (\ pα → (GlueT-f (forget-composable H) pα))
                                        ((\ pα → isEquiv-isEquivFill _ _ _
                                                   (GlueT-f-isEquiv (forget-composable H) pα)
                                                   (relCom-hasHCom _ (comEl' (HFiber-code {A =  ElCov (GlueT-T-Cov H pα)} {B = ElCov (GlueT-B-Cov H)} (GlueT-f H' pα)))))) where
      H' = forget-composable H
                             
    GlueComposable : ComposableUCov l → UCov l
    GlueComposable = \ C → GlueUCov (Composable-to-data C) 

    abstract
      hcom-UCov : hasHCom (UCov l)
      hcom-UCov r r' α {{cα}} T B = GlueComposable (HComCov r r' α cα T B) ,
                                  (\ pα → ! (GlueUCov-α (Composable-to-data (HComCov r r' α cα T B)) (inl pα)) ) ,
                                  (\ r=r' → ! (GlueUCov-α (Composable-to-data (HComCov r r' α cα T B)) (inr r=r'))) 

  UCovU : (l :{♭} Level) → U {lmax ℓ₂ (lsuc l)}
  UCovU l = code (Unit{lzero})
                 ( \ _ → UCov l )
                 (relCom-constant _ hcom-UCov)
                 <>
