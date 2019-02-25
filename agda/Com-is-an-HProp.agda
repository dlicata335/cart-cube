{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; Level; _⊔_)

open import Lib
open import Kan
open import Interval
open import Cofibs
open import Prop
open import Path

module Com-is-an-HProp where

  -- FIXME: better proof if you rephrase as SFiber (apply r) is contractible

  -- type of composition structures is an hprop

  -- \ x α t b → 
  -- com1 [α ↦ z.t, x=0 ↦ z.fill1^z [α ↦ z.t] b, x=1 ↦ z.fill2^z [α ↦ z.t] b] b

  com-hprop : ∀ {l : Level} {A : I → Set l} (com1 com2 : hasCom A) → Path (hasCom A) com1 com2
  com-hprop {l}{A} com1 com2 = ( (\ x r r' α t b → fst (f x r r' α t b) ,
                                                   (\ pα → fst (snd (f x r r' α t b)) (inl pα) ) ,
                                                   (\ r=r' → snd (snd (f x r r' α t b)) r=r')) ,
                                 (λ= \ r → λ= \ r' → λ= \ α → λ=inf \ cα → λ= \ t → λ= \ b →
                                     pair= ((! (fst (snd (f `0 r r' α {{ cα }} t b)) (inr (inl id))))) (pair= (λ= \ _ → uip) ((λ= \ _ → uip))))  ,
                                 (λ= \ r → λ= \ r' → λ= \ α → λ=inf \ cα → λ= \ t → λ= \ b →
                                     pair= ((! (fst (snd (f `1 r r' α {{ cα }} t b)) (inr (inr id))))) (pair= (λ= \ _ → uip) ((λ= \ _ → uip))))) where
   f : (x r r' : I) (α : Set) {{cα : Cofib α}} (t : (z : I) → α → A z) (b : _) → _
   f = (\ x r r' α t b → (com1 r r' (α ∨ ((x == `0) ∨ (x == `1)))
                                    (\ z → case (\ pα → t z pα)
                                                (case (\ x=0 → fst (com1 r z α t b))
                                                      (\ x=1 → fst (com2 r z α t b))
                                                      (\ p q → abort (iabort (q ∘ ! p))))
                                                (\ pα → (∨-elim _
                                                            (\ _ → fst (snd (com1 r z α t b)) pα)
                                                            (\ _ → fst (snd (com2 r z α t b)) pα)
                                                            (\ _ _ → uip)) ))
                                    (fst b , (∨-elim _
                                                     (\ pα → snd b pα)
                                                     (∨-elim _
                                                            (\ _ → ! (snd (snd (com1 r r α t b)) id))
                                                            (\ _ → ! (snd (snd (com2 r r α t b)) id))
                                                            (\ _ _ → uip))
                                                     (λ _ _ → uip)))))

