{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Glue
open import Equiv
open import Bool
open import universe.Universe

module universe.Bool where

  comBool : ∀ {l1 : Level} → relCom {Γ = Unit{lzero}} (\ _ → Bool{l1})
  comBool = relCom-constant Bool (hcomDec decBool)

  Bool-code-universal : ∀ {l1 :{♭} Level} → (Unit{lzero} → U {l1})
  Bool-code-universal = code _ (\ _ → Bool) comBool

  Bool-code : ∀ {l1 l2 :{♭} Level} {Γ : Set l2} → (Γ → U {l1})
  Bool-code{l1}{l2} _ = Bool-code-universal{l1} <>

  Bool-code-El : ∀ {l1 l2 :{♭} Level} {Γ : Set l2} → (θ : Γ) → El (Bool-code{l1}{l2}{Γ = Γ} θ) == Bool
  Bool-code-El θ = id

  Bool-code-stable : ∀ {l1 l2 l3 :{♭} Level} {Γ : Set l1} {Δ : Set l3} 
                     {θ : Δ → Γ}
                   → ((Bool-code{l2}{l1}) o θ) == Bool-code{l2}{l3}
  Bool-code-stable = id
