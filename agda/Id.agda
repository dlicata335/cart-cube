{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level; _⊔_)

open import Lib
open import Kan
open import Interval
open import Cofibs
open import Prop
open import Path

module Id where
  
  postulate
    isCofib⊤ : isCofib ⊤
    isCofib∧ : ∀ {α} {β : α → Set} → isCofib α → ((x : α) → isCofib (β x)) → isCofib (Σ β)
    Cofib-propositional-univalence : ∀ {α β} {{ cα : Cofib α }} {{ cβ : Cofib β }}
                                   → (α → β) → (β → α) → α == β

  instance
    Cofib⊤ : Cofib ⊤
    Cofib⊤ = cofib isCofib⊤ (\ _ _ → id)

    Cofib∧ : ∀ {α} {β : α → Set} → Cofib α → ((x : α) → Cofib (β x)) → Cofib (Σ β)
    Cofib∧ (cofib cα eqα) cβ = cofib (isCofib∧ cα (\ x → Cofib.is (cβ x))) (\ p q → pair= (eqα _ _) (Cofib.eq (cβ (fst q)) _ _))

  -- equal to the refl path, but more convenient without the type checking
  IsRefl : {l : Level} (A : Set l) {a0 a1 : A} → Path A a0 a1 → Set l
  IsRefl A {a0} p = fst p == (\ _ → a0)

  Id : {l : Level} (A : Set l) (a0 a1 : A) → Set (lsuc lzero ⊔ l)
  Id A a0 a1 = Σ \(φ : Cofibs) → (Σ \(p : Path A a0 a1) → fst φ → IsRefl A p)

  Id= : {l : Level} {A : Set l} {a0 a1 : A} → (p q : Id A a0 a1) 
        → fst p == fst q 
        → ((x : I) → fst (fst (snd p)) x == fst (fst (snd q)) x)
        → p == q
  Id= p q id eq2 = pair= id (pair= (pair= (λ= eq2) (pair= uip uip)) (λ= \ _ → uip))

  abstract
    Id=-transport1 : {l : Level} {A : Set l} {a0 a0' a1 : A} → (p : Id A a0 a1) (q : Id A a0' a1) 
          → (eq : a0 == a0')
          → fst p == fst q 
          → ((x : I) → fst (fst (snd p)) x == fst (fst (snd q)) x)
          → (transport (\ x → Id A x a1) eq p) == q
    Id=-transport1 p q id eq1 eq2 = Id= p q eq1 eq2

    Id=-transport2 : {l : Level} {A : Set l} {a0 a1 a1' : A} → (p : Id A a0 a1) (q : Id A a0 a1') 
          → (eq : a1 == a1')
          → fst p == fst q 
          → ((x : I) → fst (fst (snd p)) x == fst (fst (snd q)) x)
          → (transport (\ x → Id A a0 x) eq p) == q
    Id=-transport2 p q id eq1 eq2 = Id= p q eq1 eq2
  
  refl : {l : Level} (A : Set l) (a0 : A) → Id A a0 a0
  refl A a0 = (⊤{lzero} , Cofib⊤) , ((\ _ → a0) , id , id) , (\ _ → id)

  ContractibleId : {l : Level} (A : Set l) → Set (lsuc lzero ⊔ l)
  ContractibleId A = Σ \ (a : A) → (b : A) → Id A a b

