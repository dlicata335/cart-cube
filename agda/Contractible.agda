
{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Prop
open import Kan
open import Path

module Contractible where

  contr-extend-partial : {l : Level} {A : Set l} 
         → hasHCom A
         → Contractible A
         → ContractibleFill A
  contr-extend-partial hcomA cA α t = fst c , (\ pα → fst (snd c) pα ∘ ! (snd (snd (snd cA (t pα))))) where
    c = hcomA `0 `1 α (\ z pα → fst (snd cA (t pα)) z) (fst cA , (λ pα → fst (snd (snd cA (t pα)))))

  contr-implies-hprop : {l : Level} {A : Set l} 
                      → hasHCom A
                      → Contractible A
                      → (x y : A) → Path A x y
  contr-implies-hprop hcomA cA x y = (\ z → fst (p z) ) , (! ((snd (p `0)) (inl id))) , (! ((snd (p `1)) (inr id))) where
    p : ∀ z → _
    p z = contr-extend-partial hcomA cA ((z == `0) ∨ (z == `1)) (case01 (\ _ → x) (\ _ → y)) 

  contr-extend-partial-path : {l : Level} {A : Set l} 
                             → (hcomA : hasHCom A)
                             → (cA : Contractible A)
                             → (α : Set) {{cα : Cofib α}} (t : α → A)
                             → Path A (fst (contr-extend-partial hcomA cA α t)) (fst cA)
  contr-extend-partial-path hcomA cA α t = contr-implies-hprop hcomA cA _ _

  ContractibleFill-hprop : {l : Level} (A : Set l) → (c1 c2 : ContractibleFill A) → Path (ContractibleFill A) c1 c2
  ContractibleFill-hprop A c1 c2 = (\ z → λ α t → fst (c z α t) , (\ pα → snd (c z α t) (inl pα))) , (λ= \ α → λ=inf \ cα → λ= \ t → pair= (! (snd (c `0 α {{cα}} t) (inr (inl id))) ) (λ= \ _ → uip)) , (λ= \ α → λ=inf \ cα → λ= \ t → pair= (! (snd (c `1 α {{cα}} t) (inr (inr id))) ) (λ= \ _ → uip)) where
    c : ∀ z α {{cα : Cofib α}} t → _
    c z α t = c1 (α ∨ ((z == `0) ∨ (z == `1)))
              (case (\ pα → t pα)
                    (case01 (\ z=0 → fst (c1 α t)) (\ z=1 → fst (c2 α t)))
                    (\ pα → ∨-elim01 _
                            (\ z=0 → snd (c1 α t) pα)
                            ((\ z=1 → snd (c2 α t) pα))))

  inhabited-hprop-contractible : {l : Level} (A : Set l) 
                               → hasHCom A
                               → A
                               → ((x y : A) → Path A x y)
                               → ContractibleFill A
  inhabited-hprop-contractible A hcomA a p = contr-extend-partial hcomA (a , (\ b → p a b))


  hcomContractibleFill : {l : Level} (A : Set l) → hasHCom (ContractibleFill A)
  hcomContractibleFill A r r' α t b = (λ β s → fst (c β s) , (\ pβ → snd (c β s) (inl (inl pβ)))) , ((\ pα → λ= (\ β → λ=inf \ cβ → λ= \ s → pair= (snd (c β {{cβ}} s) (inl (inr pα))) (λ= \ _ → uip)))) , (\ r=r' → λ= (\ β → λ=inf \ cβ → λ= \ s → pair= (snd (c β {{cβ}} s) (inr r=r')) (λ= \ _ → uip))) where
    c : ∀ β {{cβ : Cofib β}} s → _
    c β s = (fst b ((β ∨ α) ∨ (r == r'))
                 (∨-elim _ (case s (\ pα → fst ((t r' pα) β s)) (\ pβ pα → snd ((t r' pα) β s) pβ))
                 (\ r=r' → fst (fst b β s))
                 (∨-elim _ (\ pβ r=r' → snd (fst b β s) pβ ∘ ap= (transport-constant trunc)) (\ pα r=r' → ((ap (\ h → fst (h β s))) (snd b pα) ∘ ap (\ h → fst (t h pα β s)) (! r=r')) ∘ ap= (transport-constant trunc) ) (\ _ _ → λ= \ _ → uip))))


