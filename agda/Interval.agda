open import Agda.Primitive using (lzero; Level; _⊔_)

open import Lib
open import Prop

module Interval where

  postulate
    I : Set
    `0 : I 
    `1 : I 
    -- Orton-Pitts Axiom 2
    iabort : `0 == `1 → ⊥{lzero}
    -- Orton-Pitts Axiom 1
    iconnected : {l : Level} (P : I → Prop{l})
               → ((i : I) → (fst (P i) ∨ (fst (P i) → ⊥{l})))
               → (((i : I) → fst (P i)) ∨ ((i : I) → (fst (P i)) → ⊥{l})) 
     


  Path : {l : Level} (A : Set l) (a0 a1 : A) → Set l
  Path A a0 a1 = Σ (\ (p : I → A) → (p `0 == a0) × (p `1 == a1))

