{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Path
open import Equiv
open import Cofibs
open import Kan
open import Glue
open import Glue-HCom

module Glue-Weak where

  private
    -- this stronger version is true, but doesn't get used for wcoe
    glue-weak-and-β : ∀ {l} {α : Set} {{_ : Cofib α}} {T : α → Set l} {B : Set l} {f : (u : α) → T u → B}
                      → hasHCom B
                      → (b : B) 
                      → (t : (pα : α) → HFiber (f pα) b)
                      → (HFiber {A = (Glue α T B f)} {B} unglue b) [ α ↦ (\ pα → HFiber-unglue-α _ pα (t pα)) ]
    glue-weak-and-β {α = α} {{ cα }}{T} hcomB b t = 
                          (glue _ _ _ _ 
                               (\ pα → fst (t pα))
                               (fst (fill `0) , (\ pα → fst (snd (fill `0)) pα ∘ ! (fst (snd (snd (t pα)))))),
                           (((\ z → fst (fill z)) , id , ! (snd (snd (fill `1)) id)) 
                            ∘= Glueβ _ _)) , 
                          (λ pα → =HFiber 
                                  (glue-cong _ _ _ _ _ _ (λ= \ pα' → apd (\ x → fst (t x)) (Cofib.eq cα pα pα')  ) (fst (snd (fill `0)) pα ∘ ! (fst (snd (snd (t pα))))) ∘ Glue-α-! _ _)
                                  (λ= (\ x → fst (snd (hcomB `1 x α (λ x₁ pα₁ → fst (snd (t pα₁)) x₁) (b , (λ pα₁ → snd (snd (snd (t pα₁))))))) pα))) where
       fill : (z : _) → _
       fill z = hcomB `1 z α (\ x pα → fst (snd (t pα)) x) 
                             (b , (λ pα → snd (snd (snd (t pα))) ))

  glue-weak : ∀ {l} {α : Set} {{_ : Cofib α}} {T : α → Set l} {B : Set l} {f : (u : α) → T u → B}
            → hasHCom B
            → (b : B) 
            → (t : (pα : α) → HFiber (f pα) b)
            → (Glue α T B f)
  glue-weak {α = α} {{ cα }}{T} hcomB b t = glue _ _ _ _ 
                               (\ pα → fst (t pα))
                               (fst (fill `0) , (\ pα → fst (snd (fill `0)) pα ∘ ! (fst (snd (snd (t pα)))))) where
       fill : (z : _) → _
       fill z = hcomB `1 z α (\ x pα → fst (snd (t pα)) x) 
                             (b , (λ pα → snd (snd (snd (t pα))) ))

  Glue-to-fiber : ∀ {l} {α : Set} {{cα : Cofib α}} {T : α → Set l} {B : Set l} {f : (u : α) → T u → B}
                    → (g : Glue α T B f)
                    → ((pα : α) → HFiber (f pα) (unglue g))
  Glue-to-fiber g = (\ pα → (coe (Glue-α _ _ _ _ pα) g ) , (\ _ → unglue g) , ! (unglue-α g pα) , id ) 

  -- could also show that the weak β is path-equal to refl, but don't need that below?
  glue-weak-η : ∀ {l} {α : Set} {{cα : Cofib α}} {T : α → Set l} {B : Set l} {f : (u : α) → T u → B}
              → (hb : hasHCom B)
              → (g : Glue α T B f)
              → Path (Glue α T B f)
                      (glue-weak {α = α} {{cα}}{T}{B}{f} hb (unglue g) (Glue-to-fiber g))
                      g 
  glue-weak-η {α = α} hcomB g = 
    (! (Glueη _) =∘ ((\ x → glue _ _ _ _ (\ pα → fst (Glue-to-fiber g pα)) 
                                         (fst (fillB x) , 
                                          (\ pα → fst (snd (fillB x)) pα ∘ unglue-α g pα))) , 
                    (ap (glue _ _ _ _ _) (pair= id (λ= \ _ → uip))) , 
                    (ap (glue _ _ _ _ _) (pair= (! (snd (snd (fillB `1)) id)) (λ= \ _ → uip))))) where
    fillB : (x : _) → _
    fillB x = (hcomB `1 x α (λ x pα → unglue g) (unglue g , (λ pα → id)))

  glue-weak= : ∀ {l} {α : Set} {{_ : Cofib α}} {T : α → Set l} {B : Set l} {f : (u : α) → T u → B}
              → (hcomB : hasHCom B)
              → (b b' : B) 
              → (t : (pα : α) → HFiber (f pα) b)
              → (t' : (pα : α) → HFiber (f pα) b')
              → b == b'
              → ((pα : α) → t pα =h t' pα)
              → glue-weak hcomB b t == glue-weak hcomB b' t'
  glue-weak= hcomB b b' t t' id h = ap {M = t} {N = t'} (glue-weak hcomB b) (λ= \ pα → het-to-hom (h pα))
