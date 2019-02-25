{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; Level; _⊔_)

open import Lib
open import Kan
open import Interval
open import Prop
open import Cofibs
open import Path
open import Equiv
open import Contractible

module com-glue-dagstuhl.IsEquiv-FillRefl where

  -- optimized definition that's used in coe_Glue:
  -- any partial element of the form (a,refl_f(a)) can be extended

  isEquiv'FillRefl : ∀ {l1 l2 :{♭} Level} {A : Set l1} {B : Set l2}
                      (f : A → B)
                      → Set (ℓ₁ ⊔ (l2 ⊔ l1))
  isEquiv'FillRefl {A = A} {B} f =
    {α : Set} {{_ : Cofib α}}
    (a : α → A)
    (b : B [ α ↦ (\ pα → f (a pα)) ])
    → HFiber' f (fst b) [ α ↦ (\ pα → (a pα) , (\ _ → (fst b)) , id , ! (snd b pα)) ]

  isEquiv'FillRefl-Equiv : ∀ {l1 l2 :{♭} Level} {A : Set l1} {B : Set l2}
                             (hcomB : hasHCom B)
                             (f : A → B)
                           → isEquiv'FillRefl f
                           → isEquiv' _ _ f
  isEquiv'FillRefl-Equiv {B = B} hcomB f eq b = h1 , (\ h2 → pth h2 )  where
    h1-boundary = (eq {⊥} (\ x → abort x) (b , (\ x → abort x)))
    h1 = fst h1-boundary

    pth : ∀ h2 → _
    pth h2 = (\ x → (fst (fst (use x))) ,
                    (\ y → fst (square x y)) ,
                            ! (snd (snd (q-fill x `0)) id) ∘ ! (fst (snd (square x `0)) (inr (inl id)))  ,
                            snd (snd (snd (fst (use x)))) ∘ ! (fst (snd (square x `1)) (inr (inr id))) ) ,
             (pair= (! (ap fst (snd (use `0) (inl id))))
                    ( (pair= (λ= \ y → ! (fst (snd (square `0 y)) (inl (inl id))) ∘ ap= (fst-transport-Path-right {a1 = f} (! (ap fst (snd (use `0) (inl id)))) _)) (pair= uip uip)) )) ,
             (pair= ((! (ap fst (snd (use `1) (inr id)))))
                    ( (pair= (λ= \ y → ! (fst (snd (square `1 y)) (inl (inr id))) ∘ ap= (fst-transport-Path-right {a1 = f} (! (ap fst (snd (use `1) (inr id)))) _)) ( (pair= uip uip) )) )) where
      p1 = snd h1
      p2 = snd h2

      abstract
        q-fill : (x y : I) → B [ _ ↦ _ , _ ↦ _ ]
        q-fill x y = hcomB `0 y ((x == `0) ∨ (x == `1))
                           (\ y → case01 (\ x=0 → fst p1 y ) ((\ x=1 → fst p2 y )))
                           (b , ∨-elim01 _ (\ x=0 → fst (snd p1)) (\ x=1 → fst (snd (p2))))

        use : (x : I) → _
        use x = eq {((x == `0) ∨ (x == `1))}
                 (case01 (\ x=0 → (fst h1)) (\ x=1 → (fst h2)))
                 (fst (q-fill x `1) , ∨-elim01 _ (\ x=0 → fst (snd (q-fill x `1)) (inl x=0) ∘ ! (snd (snd p1)) )
                                                 (\ x=1 → fst (snd (q-fill x `1)) (inr x=1) ∘ ! (snd (snd p2))))

        square : (x : I) (y : I) → _
        square x y = hcomB `0 `1
                           (((x == `0) ∨ (x == `1)) ∨ ((y == `0) ∨ (y == `1)))
                           (\ z → case (case01 (\ x=0 → fst p1 y)
                                               (\ x=1 → fst p2 y))
                                       (case01 (\ y=0 → fst (q-fill x `0))
                                               (\ y=1 → fst (snd (fst (use x))) z))
                                       (∨-elim01 _
                                                 (\ x=0 → ∨-elim01 _
                                                                   (\ y=0 → fst (snd (q-fill x `0)) (inl x=0) ∘ ap (fst p1) y=0 )
                                                                   (\ y=1 →  (apd (\ h → fst (snd h) z) (snd (use x) (inl x=0)) ∘ ap= (! (transport-constant (snd (use x) (inl x=0)))) ∘ fst (snd (q-fill x `1)) (inl x=0)) ∘ ap (fst p1) y=1 ))
                                                 (\ x=1 → ∨-elim01 _
                                                                   (\ y=0 → snd (snd (q-fill x `0)) id ∘ fst (snd (snd h2)) ∘ ap (fst (snd h2)) y=0 )
                                                                   (\ y=1 → apd (\ h → fst (snd h) z) (snd (use x) (inr x=1)) ∘ ap= (! (transport-constant (snd (use x) (inr x=1)))) ∘ fst (snd (q-fill x `1)) (inr x=1) ∘ ap (fst (snd h2)) y=1 ))))
                           (fst (q-fill x y) ,
                                ∨-elim _
                                       (∨-elim01 _ (\ x=0 → fst (snd (q-fill x y)) (inl x=0))
                                                   (\ x=1 → fst (snd (q-fill x y)) (inr x=1)))
                                       (∨-elim01 _ ( (\ y=0 → ap (\ h → fst (q-fill x h)) (! y=0)) )
                                                   (\ y=1 → ap (\ h → fst (q-fill x h)) (! y=1) ∘ fst (snd (snd (fst (use x))))))
                                       (\ _ _ → uip))
  
  
  isEquiv'FillRefl-HProp : ∀ {l1 l2 :{♭} Level} {A : Set l1} {B : Set l2}
                             (hcomB : hasHCom B)
                             (f : A → B)
                           → (hcomFiber : (b : B) → hasHCom (HFiber' f b)) -- STS hcomA and lemma
                           → (e1 e2 : isEquiv'FillRefl f) → Path (isEquiv'FillRefl f) e1 e2
  isEquiv'FillRefl-HProp hcomB f hcomFiber e1 e2 =
    (\ x {α} {{cα}} a b →  fst (c x {α} {{cα}} a b) , (\ pα → snd (c x {α} {{cα}} a b) (inr pα))) ,
    (λ=i \ α → λ=inf \ cα → λ= \ a → λ= \ b → pair= (! (snd (c `0 {{cα = cα}} a b) (inl (inl id)))) (λ= \ _ → uip)) ,
    (λ=i \ α → λ=inf \ cα → λ= \ a → λ= \ b → pair= (! (snd (c `1 {{cα = cα}} a b) (inl (inr id)))) (λ= \ _ → uip)) where

    abstract
      c : ∀ x {α} {{cα}} a b → _
      c x {α} a b = contr-extend-partial (hcomFiber _)
                                       (isEquiv'FillRefl-Equiv hcomB _ e1 (fst b))
                                       (((x == `0) ∨ (x == `1)) ∨ α)
                                       (case (case01 (\ _ → (fst (e1 a b)))
                                                     (\ _ →  (fst (e2 a b))))
                                             (\ pα → (a pα) , (\ _ → (fst b)) , id , ! (snd b pα))
                                             (∨-elim01 _
                                                       (\ x=0 pα → ! (snd (e1 a b) pα))
                                                       (\ x=1 pα → ! (snd (e2 a b) pα)))) 

{-
  test : {l :{♭} Level} (A : I → Set l) (r : I) → isEquiv'FillRefl {A  = (x : I) → A x} {(A r)} (\ f → f r)
  test = {!!}
-}
