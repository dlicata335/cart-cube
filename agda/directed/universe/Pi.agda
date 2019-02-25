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
open import universe.Universe
open import universe.Pi
open import directed.Segal
open import directed.Covariant
open import directed.SegalDepCovariant
open import directed.UCov

module directed.universe.Pi where

  open Layered


  ΠUKan : {l :{♭} Level} (A :{♭} U {l}) (B : El A → UCov l) → U
  ΠUKan A B = Πcode-universal (A , ElCov o B)

  Π-relCov : {l1 l2 l3 : Level} (Γ : Set l2) 
             (A : Set l1)
             (B : Γ × A → Set l3)
             (covB : relCov B)
             → relCov (λ z → ((x : A) → B (z , x)))
  Π-relCov Γ A B covB = relCov1-relCov (λ z → ((x : A) → B (z , x))) iscov where

    iscov : ∀ p α {{_}} t b → _
    iscov p α t b = (λ x → fst (f x)) , (λ pα → λ= (λ x → (fst (snd (f x))) pα)) where

      f : ∀ x → _
      f x = covB (λ i → (p i , x)) ``1 α (λ i pα → t i pα x) ((fst b) x , (λ pα → ap= ((snd b) pα)))

  ΠUCov : {l :{♭} Level} (A :{♭} U {l}) (B : El A → UCov l) → UCov _
  ΠUCov {l} A = code-cov (ΠUKan A , (Π-relCov (El A → UCov l)
                                              (El A)
                                              (λ x → ElC ((fst x) (snd x)))
                                              (dcomEl' (λ x → (fst x) (snd x))) ))
