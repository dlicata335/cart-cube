{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Path
open import Prop

module Strictify where 

  postulate
      -- Orton-Pitts Axiom 9
      strictify : {l : Level}
                  {α : Set} {{ cα : Cofib α }}
                  (A : α → Set l)
                  (B : Set l)
                → (i : (pα : α) → Iso B (A pα))
                → Σ \ (B' : Set l [ α ↦ A ])
                  → Iso B (fst B') [ α ↦ (\ pα → eqIso (snd B' pα) ∘iso i pα  ) ]
