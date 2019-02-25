{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Equiv
open import Path
open import Equiv
open import universe.Universe

module universe.Case where

  El-case : {l' l :{♭} Level} {α : Set} {β : Set}
          → (A : α → U {l'})
          → (B : β → U {l'})
          → (AB :  (pα : α) → (pβ : β) → A pα == B pβ)
          → (pab : α ∨ β)
          → El (case A B AB pab) == case (El o A) (El o B) (\ a b → ap El (AB a b)) pab
  El-case A B AB = ∨-elim _ (\ _ → id) (\ _ → id) (\ _ _ → uip)

  comCase : {l' l :{♭} Level} {Γ : Set l} {α : Γ → Set} {β : Γ → Set}
          → (pab : (x : Γ) → α x ∨ β x)
          → (A : (x : Γ) → α x → U {l'})
          → (B : (x : Γ) → β x → U {l'})
          → (AB : (x : Γ) → (pα : α x) → (pβ : β x) → A x pα == B x pβ)
          → relCom {Γ = Γ} (\ x → El (case (A x) (B x) (AB x) (pab x) ))
  comCase pab A B AB = comPre (\ x → case (A x) (B x) (AB x) (pab x) ) El comEl
