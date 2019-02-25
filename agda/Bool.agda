{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Kan
open import Prop

module Bool where

  data Bool {l : Level} : Set l where
    true : Bool
    false : Bool

  decBool : {l : Level} (x y : Bool{l}) → (x == y) ∨ ((x == y) → ⊥{l})
  decBool true true = inl id
  decBool true false = inr (\ ())
  decBool false true = inr (\ ())
  decBool false false = inl id

  BoolF : ∀ {l1 l} {Γ : Set l1} → (Γ → Set l)
  BoolF _ = Bool

  -- not used anywhere, but I was wondering if this was internally refutable
  not-decide : (dec : (x : I) → (x == `0) ∨ (x == `1)) → true{lzero} == false
  not-decide dec =  
    case (\ f → ! ((f `1) ∘ ∨-elim (λ h → false == case (λ _ → true) (λ _ → false) (λ p q → abort (iabort (q ∘ ! p))) h) (\ x → abort (iabort (! x))) (\ _ → id) (\ x → abort (iabort (! x))) (dec `1)) )
         (\ f → abort ((f `0) ((∨-elim (λ h → case (λ _ → true) (λ _ → false) (λ p q → abort (iabort (q ∘ ! p))) h == true) (\ _ → id) (\ y → abort (iabort y)) (\ _ _ → uip) (dec `0)))))
         (\ q p → uip) use    where
    to-bool : (x : I) → Bool{lzero}
    to-bool x = case (\ _ → true) (\ _ → false) (\ p q → abort (iabort (q ∘ ! p))) (dec x)
  
    use : ((i : I) → to-bool i == true) ∨ ((i : I) → to-bool i == true → ⊥)
    use = iconnected (\ x → to-bool x == true , (\ _ _ → uip)) (\ i → decBool _ _)
