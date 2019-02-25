{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Equiv
open import Nat
open import universe.Universe

module universe.Nat where

  comNat : ∀ {l1 : Level} → relCom {Γ = Unit{lzero}} (\ _ → Nat{l1})
  comNat = relCom-constant Nat (hcomDec decNat)

  Nat-code-universal : ∀ {l1 :{♭} Level} → (Unit{lzero} → U {l1})
  Nat-code-universal = code _ (\ _ → Nat) comNat

  Nat-code : ∀ {l1 l2 :{♭} Level} {Γ : Set l2} → (Γ → U {l1})
  Nat-code{l1}{l2} _ = Nat-code-universal{l1} <>

  Nat-code-stable : ∀ {l1 l2 l3 :{♭} Level} {Γ : Set l1} {Δ : Set l3} 
                     {θ : Δ → Γ}
                   → ((Nat-code{l2}{l1}) o θ) == Nat-code{l2}{l3}
  Nat-code-stable = id

  Nat-code-El : ∀ {l1 l2 :{♭} Level} {Γ : Set l2} → (θ : Γ) → El (Nat-code{l1}{l2}{Γ = Γ} θ) == Nat
  Nat-code-El θ = id
