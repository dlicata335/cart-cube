{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (_⊔_;Level;lsuc)
open import Lib 

module Prop where

  -- "HProp" without the H
  Prop : ∀ {l : Level} → Set (lsuc l)
  Prop {l} = Σ \ (A : Set l) → (x y : A) → x == y

  postulate
      _∨_ : {l : Level} (α : Set l) (β : Set l) → Set l

  module Or {l : Level} {α : Set l } {β : Set l} where
    postulate
      inl : α → α ∨ β
      inr : β → α ∨ β
      trunc : {x y : α ∨ β} → x == y
      case : ∀ {l} {A : Set l} → (f : α → A) → (g : β → A) → ((x : α) (y : β) → f x == g y) → (α ∨ β → A)
      case-inl : ∀ {l} {A : Set l} → {f : α → A} → {g : β → A} → {e : (x : α) (y : β) → f x == g y} {x : α}
               → case f g e (inl x) == f x
      case-inr : ∀ {l} {A : Set l} → {f : α → A} → {g : β → A} → {e : (x : α) (y : β) → f x == g y} {y : β}
               → case f g e (inr y) == g y
      {-# REWRITE case-inl #-}
      {-# REWRITE case-inr #-}
      case-η : ∀ {A : Set} → {a : α ∨ β → A} → a == case (\ x → a (inl x)) (\ y → a (inr y)) (\ _ _ → ap a (trunc)) 
      -- should be provable from above
      ∨-elim : ∀ {l} (A : α ∨ β → Set l) → (f : (x : α) → A (inl x)) → (g : (y : β) → A (inr y)) → ((x : α) (y : β) → transport A (trunc) (f x) == g y) → ((x : α ∨ β) → A x)
      ∨-elim-inl : ∀ {l} (A : α ∨ β → Set l) → (f : (x : α) → A (inl x)) → (g : (y : β) → A (inr y)) → (h : (x : α) (y : β) → transport A (trunc) (f x) == g y) 
                 → (x : α) → ∨-elim A f g h (inl x) == f x
      ∨-elim-inr : ∀ {l} (A : α ∨ β → Set l) → (f : (x : α) → A (inl x)) → (g : (y : β) → A (inr y)) → (h : (x : α) (y : β) → transport A (trunc) (f x) == g y) 
                 → (x : β) → ∨-elim A f g h (inr x) == g x 
      -- trunc-same : {x : α ∨ β} → trunc {x} {x} == id
      {-# REWRITE ∨-elim-inl #-}
      {-# REWRITE ∨-elim-inr #-}
      -- {-# REWRITE trunc-same #-}
 
  open Or public

  
