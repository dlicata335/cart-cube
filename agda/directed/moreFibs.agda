{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Prop
open import Cofibs
open import directed.DirInterval
open import directed.Covariant
open import directed.Segal
open import directed.SegalDepCovariant

module directed.moreFibs where

  -- Fun generic definition of filler
  hasFiller : (Box : Set)
              (pBox : Box → Set)
              {{cof : (x : Box) → Cofib (pBox x)}}
              → ∀ {l} → (Box → Set l) → Set _
  hasFiller Box pBox {{cof}} A =
             (s : Box) (α : Set) {{_ : Cofib α}}
             (t : (s : Box) → α → A s)
             (b : (s : Box) → pBox s → A s [ α ↦ t s ])
             → _[_↦_,_↦_] (A s) α (t s) (pBox s) {{cof s}} (λ p → fst (b s p))

  relFiller : (Box : Set)
              (pBox : Box → Set)
              {{cof : (x : Box) → Cofib (pBox x)}}
              → ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → Set _
  relFiller Box pBox {{cof}} {Γ = Γ} A = (p : Box → Γ) → hasFiller Box pBox {{cof}} (A o p)

  -- defining inner fibrations
  hasInner = hasFiller Δ₂ Λ₂
  {-
  hasInner : ∀ {l} → (Δ₂ → Set l) → Set _
  hasInner A = (s : Δ₂) (α : Set) {{_ : Cofib α}}
               (t : (s : Δ₂) → α → A s)
               (b : (s : Δ₂) → Λ₂ s → A s [ α ↦ t s ])
               → A s [ α ↦ t s , Λ₂ s ↦ (λ p → fst (b s p)) ]
  -}
  
  relInner = relFiller Δ₂ Λ₂
  {-
  relInner : ∀ {l1 l2} → {Γ : Set l1} → (A : Γ → Set l2) → Set _
  relInner {Γ = Γ} A = (p : Δ₂ → Γ) → hasInner (A o p)
  -}



  Δ01 : Δ₂ → Set
  Δ01 (_ , y , _) = y == ``0

  Δ12 : Δ₂ → Set
  Δ12 (x , _ , _) = x == ``1
  
  Δ02 : Δ₂ → Set
  Δ02 (x , y , _) = x == y

  Λ₂₂ : Δ₂ → Set
  Λ₂₂ (x , y , _) = (x == ``1) ∨ (x == y) 

  Λ₂₀ : Δ₂ → Set
  Λ₂₀ (x , y , _) = (x == y) ∨ (y == ``0) 




  hasCartMor : ∀{l} (A : Δ₂ → Set l) (f : (x : Δ₂) → Δ12 x → A x) → Set _
  hasCartMor A f = (s : Δ₂)
                   (α : Set) {{_ : Cofib α}}
                   (t : (s : Δ₂) → α → (A s) [ Δ12 s ↦ f s ])
                   (b : (s : Δ₂) → Λ₂₂ s → (A s) [ α ↦ (λ p → fst (t s p)), Δ12 s ↦ f s ])
                   →
                   A s [ α ↦ (λ p → fst (t s p)) , Λ₂₂ s ↦ (λ p → fst (b s p)) ] 

  relCartMor' : ∀{l1 l2} {Γ : Set l1} (A : Γ → Set l2) (f : (s : Δ₂) → Δ12 s → Γ) (f' : (s : Δ₂) → (b : Δ12 s) → A (f s b)) → Set _
  relCartMor' {Γ = Γ} A f f' = (p : (s : Δ₂) → Γ [ Δ12 s ↦ f s ]) → hasCartMor (λ s → A (fst (p s))) (λ s b → transport A (snd (p s) b) (f' s b))

  relCartMor : ∀{l1 l2} {Γ : Set l1} (A : Γ → Set l2) (f : 𝟚 → Γ) (f' : (i : 𝟚) → A (f i)) → Set _
  relCartMor A f f' = relCartMor' A (λ {(_ , y , _) → λ _ → f y}) (λ {(_ , y , _) → λ _ → f' y})




  hasCoCartMor : ∀{l} (A : Δ₂ → Set l) (f : (x : Δ₂) → Δ01 x → A x) → Set _
  hasCoCartMor A f = (s : Δ₂)
                     (α : Set) {{_ : Cofib α}}
                     (t : (s : Δ₂) → α → (A s) [ Δ01 s ↦ f s ])
                     (b : (s : Δ₂) → Λ₂₀ s → (A s) [ α ↦ (λ p → fst (t s p)), Δ01 s ↦ f s ])
                     →
                     A s [ α ↦ (λ p → fst (t s p)) , Λ₂₀ s ↦ (λ p → fst (b s p)) ] 

  relCoCartMor' : ∀{l1 l2} {Γ : Set l1} (A : Γ → Set l2) (f : (s : Δ₂) → Δ01 s → Γ) (f' : (s : Δ₂) → (b : Δ01 s) → A (f s b)) → Set _
  relCoCartMor' {Γ = Γ} A f f' = (p : (s : Δ₂) → Γ [ Δ01 s ↦ f s ]) → hasCoCartMor (λ s → A (fst (p s))) (λ s b → transport A (snd (p s) b) (f' s b))

  relCoCartMor : ∀{l1 l2} {Γ : Set l1} (A : Γ → Set l2) (f : 𝟚 → Γ) (f' : (i : 𝟚) → A (f i)) → Set _
  relCoCartMor A f f' = relCoCartMor' A (λ {(x , _ , _) → λ _ → f x}) (λ {(x , _ , _) → λ _ → f' x})




  -- defining cartesian fibrations   (i.e. contravariant up to a commutative triangle)
  relCartFibMor : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → Set _
  relCartFibMor {Γ = Γ} A = (f : 𝟚 → Γ)
                            (a1 : A (f ``1))
                            → Σ (λ (f' : (i : 𝟚) → A (f i) [ i == ``1 ↦ (λ eq → transport (A o f) (! eq) a1) ]) → relCartMor A f (λ i → fst (f' i)))

  relCart : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → Set _
  relCart {Γ = Γ} A = relInner A × relCartFibMor A




  -- defining cocartesian fibrations   (i.e. covariant up to a commutative triangle)
  relCoCartFibMor : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → Set _
  relCoCartFibMor {Γ = Γ} A = (f : 𝟚 → Γ)
                              (a0 : A (f ``0))
                              → Σ (λ (f' : (i : 𝟚) → A (f i) [ i == ``0 ↦ (λ eq → transport (A o f) (! eq) a0) ]) → relCoCartMor A f (λ i → fst (f' i)))
                            
  relCoCart : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → Set _
  relCoCart {Γ = Γ} A = relInner A × relCoCartFibMor A





  relCov-to-relInner : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → relCov A → relInner A
  relCov-to-relInner {Γ = Γ} A covA p s α t b = fst a , snd (snd a) , fst (snd a) where

    a : _
    a = decompose-relDCom₂ A covA p s (λ s h → fst (b s h)) α (λ s pα → t s pα , (λ h → ! (snd (b s h) pα)))

  relCov-to-relCoCartFibMor : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → relCov A → relCoCartFibMor A
  relCov-to-relCoCartFibMor {Γ = Γ} A covA f a0 = (λ i → fst (f' i) , (λ {id → snd (snd (f' i)) id})) , coCartMorf where

    f' : ∀ i → _
    f' i = covA f i ⊥ (λ _ → abort) (a0 , λ x → abort x)

    fill : ∀ p x y α {{cα}} t b → _
    fill p x y α {{cα}} t b = covA (λ x → fst (p (lower-triangle x y))) x (α ∨ ((y == ``0) ∨ (y == ``1)))
                                   (λ z → case (λ pα → fst (t (lower-triangle z y) pα))
                                               (cased01 (λ y=0 → transport (λ y → A (fst (p (lower-triangle z y)))) (! y=0)
                                                                 (fst (b (z , ``0 , id) (inr id))))
                                                        (λ y=1 → transport (λ y → A (fst (p (lower-triangle z y)))) (! y=1)
                                                                 (fst (b (z , z , id) (inl id)))))
                                               (λ pα → ∨-elimd01 _ (λ y=0 → ap (λ b → transport (λ y → A (fst (p (lower-triangle z y)))) (! y=0) (transport (λ s → A (fst (p s))) (!(lower-trianglex0 z)) b)) (snd (snd (b (z , ``0 , id) (inr id))) id)
                                                                            ∘ ap (λ b → transport (λ y → A (fst (p (lower-triangle z y)))) (! y=0) b) (! (snd (t (lower-triangle z ``0) pα) id)) ∘ ! (apd (λ y → fst (t (lower-triangle z y) pα)) (! y=0)))
                                                                   (λ y=1 → ap (λ b → transport (λ y → A (fst (p (lower-triangle z y)))) (! y=1) (transport (λ s → A (fst (p s))) (!(lower-trianglex1 z)) b)) (fst (snd (b (z , z , id) (inl id))) pα)
                                                                            ∘ ! (apd (λ y → fst (t (lower-triangle z y) pα)) (! y=1)))))
                                   (transport (λ f → (A f)) (snd (p (lower-triangle ``0 y)) id) (fst (f' ``0))
                                   , ∨-elim _ (λ pα → ! (snd (t (lower-triangle ``0 y) pα) id))
                                              (∨-elimd01 _ (λ y=0 → ap (λ f → f (transport A (snd (p (``0 , ``0 , id)) id) (fst (f' ``0)))) (transport-constant (! y=0))
                                                                  ∘ ap (λ b → transport (λ y → A (fst (p (lower-triangle ``0 y)))) (! y=0) b) (! (snd (snd (b (``0 , ``0 , id) (inr id))) id)))
                                                           (λ y=1 → ap (λ f → f (transport A (snd (p (``0 , ``0 , id)) id) (fst (f' ``0)))) (transport-constant (! y=1))
                                                                  ∘ ap (λ b → transport (λ y → A (fst (p (lower-triangle ``0 y)))) (! y=1) b) (! (snd (snd (b (``0 , ``0 , id) (inl id))) id))))
                                              (λ _ _ → uip)) 
    
    my-triangle-from-square-boundary' : ∀ {l2} (A : Δ₂ → Set l2)
                                  → (f : (x : 𝟚) (y : 𝟚) → A (lower-triangle x y))
                                  → (x : 𝟚)
                                  → (a : A (lower-triangle x ``1))
                                  → a == f x ``1
                                  → triangle-from-square A f (x , x , id) == transport A (lower-trianglex1 x) a
    my-triangle-from-square-boundary' A sq x a id = het-to-hom (_∘h_ {!!} (transport-=h A (lower-triangle-ret (x , x , id)))) -- het-to-hom (_∘h_ (!h (transport-=h A (lower-trianglex1 x))) (transport-=h A (lower-triangle-ret (x , x , id))))

    my-triangle-from-square-boundary : ∀ {l2} (A : Δ₂ → Set l2)
                                  → (f : (x : 𝟚) (y : 𝟚) → A (lower-triangle x y))
                                  → (t : Δ₂)
                                  → (eq : fst t == fst (snd t))
                                  → (a : A (lower-triangle (fst t) ``1))
                                  → a == f (fst t) ``1
                                  → triangle-from-square A f t == transport A (ap (λ x → (fst t , fst x , snd x)) (pair= eq uip)) (transport A (lower-trianglex1 (fst t)) a)
    my-triangle-from-square-boundary A sq (x , .x , id) id a id = my-triangle-from-square-boundary' A sq x a id

    my-triangle-from-square-boundary'' : ∀ {l2} (A : Δ₂ → Set l2)
                                  → (f : (x : 𝟚) (y : 𝟚) → A (lower-triangle x y))
                                  → (t : Δ₂)
                                  → (eq : fst t == fst (snd t))
                                  → (a : A (lower-triangle (fst t) ``1))
                                  → a == f (fst t) (fst t)
                                  → triangle-from-square A f t == {!triangle-from-square A (λ x _ → A (lower-triangle x ``1))!}
    my-triangle-from-square-boundary'' A sq (x , .x , id) id a id = {!!}
                                  

    coCartMorf : relCoCartMor A f (λ i → fst (f' i))
    coCartMorf p s α {{cα}} t b =  triangle-from-square (λ s → A (fst (p s))) (λ x y → fst (fill p x y α {{cα}} t b)) s
                                , (λ pα → ! (triangle-from-square-boundary (λ s → A (fst (p s)))
                                                                           (λ x y → fst (fill p x y α {{cα}} t b))
                                                                           s _
                                                                           (fst (snd (fill p (fst s) (fst (snd s)) α t b)) (inl pα)))
                                          ∘ ! (apd (λ x → fst (t x pα)) (lower-triangle-ret s)))
                                , ∨-elim _ (λ x=y → ! (my-triangle-from-square-boundary (λ s → A (fst (p s))) (λ x y → fst (fill p x y α {{cα}} t b)) s x=y (fst (fill p (fst s) ``1 α t b)) {!(fst (snd (fill p (fst s) ``1 α t b))) (inr (inr id))!}) ∘ {!snd (b (fst s , fst s , id) (inl id))!})
                                -- my-triangle-from-square-boundary (λ s → A (fst (p s))) (λ x y → fst (fill p x y α {{cα}} t b)) (fst s) (fst (fill p (fst s) ``1 α t b))
 -- ! (triangle-from-square-boundary (λ s → A (fst (p s))) (λ x y → fst (fill p x y α {{cα}} t b)) s _ (fst (snd (fill p (fst s) (fst (snd s)) α t b)) (inr (inr {!x=y!})))) ∘ {!!})
                                -- snd (fill p (fst s) (fst (snd s)) α t b)
                                           (λ y=0 → ! (triangle-from-square-boundary (λ s → A (fst (p s))) (λ x y → fst (fill p x y α {{cα}} t b)) s _
                                                      (fst (snd (fill p (fst s) (fst (snd s)) α t b)) (inr (inl y=0))))
                                                    ∘ het-to-hom (_∘h_ (!h (transport-=h (λ s₁ → A (fst (p s₁))) (lower-triangle-ret s)))
                                                                 (_∘h_ (!h (transport-=h (λ y → A (fst (p (fst s , (fst s ⊓ y) , id)))) (! y=0)))
                                                                       (transport-=h (λ z → A (fst (p (fst z)))) (pair= (pair= id (pair= (! y=0) uip)) uip))))
                                                    ∘ ! (apd {b₁ = (fst s , ``0 , id) , id} {s , y=0}
                                                             (λ x → fst (b (fst x) (inr (snd x))))
                                                             (pair= (pair= id (pair= (! y=0) uip)) uip)))
                                           (λ _ _ → uip)

  relCov-to-relCoCart : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → relCov A → relCoCart A
  relCov-to-relCoCart {Γ = Γ} A covA = relCov-to-relInner A covA , relCov-to-relCoCartFibMor A covA
