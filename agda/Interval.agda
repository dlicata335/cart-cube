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

  not0∨1 : ((x : I) → (x == `0) ∨ (x == `1))
         → ⊥{lzero}
  not0∨1 =01 = case (\ h → iabort (! (h `1))) (\ h → h `0 id) (\ x _ → abort (iabort (! (x `1)))) c where
    c = iconnected (\ x → x == `0 , (\ _ _ → uip))
                   (\ x → case inl
                               (\ =1 → inr (\ =0 → iabort (=1 ∘ ! =0)))
                               (\ p q → abort (iabort (q ∘ ! p)))
                               (=01 x))

  case01 : ∀ {l} {z : I} {A : Set l}
              → (f : (x : z == `0) → A)
              → (g : (y : z == `1) → A)
              → ((x : (z == `0) ∨ (z == `1) ) → A)
  case01 f g = case f g (\ p q → abort (iabort (q ∘ ! p)))

  ∨-elim01 : ∀ {l} {z : I} (A : (z == `0) ∨ (z == `1) → Set l)
              → (f : (x : z == `0) → A (inl x))
              → (g : (y : z == `1) → A (inr y))
              → ((x : (z == `0) ∨ (z == `1) ) → A x)
  ∨-elim01 A f g = ∨-elim A f g (\ p q → abort (iabort (q ∘ ! p)))

