{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (_⊔_;Level)
open import Lib 
open import Interval 
open import Prop public

module Cofibs where

  ⊤ = Unit
  _∧_ = _×_
  ∀i : (I → Set) → Set
  ∀i α = (x : I) → α x

  -- this way we can't do cofib-induction... 
  postulate 
    isCofib : Set → Set 
    isCofib⊥ : isCofib ⊥
    isCofib∨ : ∀ {α β} → isCofib α → isCofib β → isCofib (α ∨ β)
    isCofib= : ∀ {r r' : I} → isCofib (r == r')
    isCofib∀ : ∀ {α : I → Set} → ((x : I) → isCofib (α x)) → isCofib (∀i α)

  record Cofib (α : Set) : Set where
    constructor cofib
    field 
      is : isCofib α
      eq : (x y : α) → x == y

  Cofibs : Set1
  Cofibs = Σ \ α → Cofib α

  instance
    Cofib⊥ : Cofib ⊥
    Cofib⊥ = cofib isCofib⊥ (\ ())

    Cofib∨ : ∀ {α β} → Cofib α → Cofib β → Cofib (α ∨ β)
    Cofib∨ (cofib cα eqα) (cofib cβ eqβ) = cofib (isCofib∨ cα cβ) (\ _ _ → trunc)

    Cofib= : ∀ {r r' : I} → Cofib (r == r')
    Cofib= = cofib (isCofib=) (\ _ _ → uip)
  
    Cofib∀ : ∀ {α : I → Set} → ((x : I) → Cofib (α x)) → Cofib ((x : I) → α x)
    Cofib∀ cα = cofib (isCofib∀ (\ x → Cofib.is (cα x))) (\ x y → λ= \ a → Cofib.eq (cα a) _ _ ) 

  extends : ∀ {l} {α : Set} {A : Set l} → {{_ : Cofib α}} → (t : α → A) (b : A) → Set l
  extends {_} {α} t b = (x : α) → t x == b

  _[_↦_] : ∀ {l} (A : Set l) (α : Set) → {{cα : Cofib α}} → (t : α → A) → Set l
  A [ α ↦ t ] = Σ \ b → extends t b

  _[_↦_]e : ∀ {l} (A : Set l) (α : Cofibs) → (t : fst α → A) → Set l
  A [ α ↦ t ]e = Σ \ b → extends {{snd α}} t b

  -- less annoying than using an or?  or maybe just saving the pain for later
  -- no compat necessary because they're both subobjects of the same thing
  _[_↦_,_↦_] : ∀ {l : Level} (A : Set l) (α : Set) {{_ : Cofib α}} (t : α → A) (β : Set) {{_ : Cofib β}} (s : β → A) → Set l
  A [ α ↦ t , β ↦ s ] = Σ \ b → (extends t b) × (extends s b)
  
  
