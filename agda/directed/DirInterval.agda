{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; Level) renaming (_⊔_ to lmax)
open import Lib
open import Prop
open import Lib
open import Cofibs
open import Kan
open import Path
open import Interval

module directed.DirInterval where

  -- ----------------------------------------------------------------------
  -- postulates about the interval

  postulate
    𝟚  : Set
    ``0 : 𝟚 
    ``1 : 𝟚
    diabort : ``0 == ``1 → ⊥{lzero}

    diconnected : {l : Level} (P : 𝟚 → Prop{l})
               → ((i : 𝟚) → (fst (P i) ∨ (fst (P i) → ⊥{l})))
               → (((i : 𝟚) → fst (P i)) ∨ ((i : 𝟚) → (fst (P i)) → ⊥{l})) 

  postulate
    -- postulating consequences instead to see exactly what gets used
    -- ditotal : (x : 𝟚) (y : 𝟚) → (x ≤ y) ∨ (y ≤ x)

    -- can define connections from totality 
    _⊓_ : 𝟚 → 𝟚 → 𝟚
    0⊓ : (x : 𝟚) → (``0 ⊓ x) == ``0
    ⊓0 : (x : 𝟚) → (x ⊓ ``0) == ``0
    1⊓ : (x : 𝟚) → (``1 ⊓ x) == x
    ⊓1 : (x : 𝟚) → (x ⊓ ``1) == x
    {-# REWRITE 0⊓ #-}
    {-# REWRITE ⊓0 #-}
    {-# REWRITE 1⊓ #-}
    {-# REWRITE ⊓1 #-}
    ⊓comm : (x y : 𝟚) → (x ⊓ y) == (y ⊓ x)
    ⊓idem : (x : 𝟚) → (x ⊓ x) == x
    ⊓assoc' : (x y : 𝟚) → ((x ⊓ y) ⊓ x) == (x ⊓ y) -- associative too, but haven't needed it yet
    {-# REWRITE ⊓idem #-}
    {-# REWRITE ⊓assoc' #-}

    _⊔_ : 𝟚 → 𝟚 → 𝟚
    1⊔ : (x : 𝟚) → (``1 ⊔ x) == ``1
    ⊔1 : (x : 𝟚) → (x ⊔ ``1) == ``1
    0⊔ : (x : 𝟚) → (``0 ⊔ x) == x
    ⊔0 : (x : 𝟚) → (x ⊔ ``0) == x
    {-# REWRITE 1⊔ #-}
    {-# REWRITE ⊔1 #-}
    {-# REWRITE 0⊔ #-}
    {-# REWRITE ⊔0 #-}
    ⊔idem : (x : 𝟚) → (x ⊔ x) == x
    {-# REWRITE ⊔idem #-}
    ⊔comm : (x y : 𝟚) → (x ⊔ y) == (y ⊔ x)

    absorb1 : (x y : 𝟚) → (x ⊓ (x ⊔ y)) == x
    absorb2 : (x y : 𝟚) → (x ⊔ (y ⊓ x)) == x
    {-# REWRITE absorb1 #-}
    {-# REWRITE absorb2 #-}

  postulate
    -- FIXME: is this OK?
    dimonotonicity≤ : (p : 𝟚 → 𝟚) (x y : 𝟚) →
                       x == (x ⊓ y) → p x == (p x ⊓ p y)

    -- FIXME: is it OK that this is exact equality?
    𝟚-Inull' : (f : I → 𝟚) (x : I) → f x == f `0

    -- Q: also only constant maps 𝟚 → I ?

  𝟚-Inull : (f : I → 𝟚) → Σ \ (x : 𝟚) → f == (\ _ → x)
  𝟚-Inull f = f `0 , λ= \ y → 𝟚-Inull' f y

  postulate
    -- isCofib=𝟚0 : ∀ {x : 𝟚} → isCofib (``0 == x)
    -- isCofib=𝟚1 : ∀ {x : 𝟚} → isCofib (``1 == x)
    -- isCofib=𝟚0' : ∀ {x : 𝟚} → isCofib (x == ``0)
    -- isCofib=𝟚1' : ∀ {x : 𝟚} → isCofib (x == ``1)
    isCofib=𝟚diag : ∀ {x y : 𝟚} → isCofib (x == y) 
    isCofib∀𝟚 : ∀ {α : 𝟚 → Set} → ((x : 𝟚) → isCofib (α x)) → isCofib ((x : 𝟚) → α x)


  instance
    -- Cofib=𝟚0 : ∀ {x : 𝟚} → Cofib (``0 == x)
    -- Cofib=𝟚0 = cofib (isCofib=𝟚0) (\ _ _ → uip)

    -- Cofib=𝟚1 : ∀ {x : 𝟚} → Cofib (``1 == x)
    -- Cofib=𝟚1 = cofib (isCofib=𝟚1) (\ _ _ → uip)

    -- Cofib=𝟚0' : ∀ {x : 𝟚} → Cofib (x == ``0)
    -- Cofib=𝟚0' = cofib (isCofib=𝟚0') (\ _ _ → uip)

    -- Cofib=𝟚1' : ∀ {x : 𝟚} → Cofib (x == ``1)
    -- Cofib=𝟚1' = cofib (isCofib=𝟚1') (\ _ _ → uip)

    -- seems necessary to show that triangles are fibrant over the composite side
    Cofib=𝟚diag : ∀ {x y : 𝟚} → Cofib (x == y)
    Cofib=𝟚diag = cofib (isCofib=𝟚diag) (\ _ _ → uip) 

    Cofib∀𝟚 : ∀ {α : 𝟚 → Set} → ((x : 𝟚) → Cofib (α x)) → Cofib ((x : 𝟚) → α x)
    Cofib∀𝟚 cα = cofib (isCofib∀𝟚 (\ x → Cofib.is (cα x))) (\ x y → λ= \ a → Cofib.eq (cα a) _ _ ) 


  -- ----------------------------------------------------------------------
  -- useful abbreviations 

  _≤_ : 𝟚 → 𝟚 → Set
  x ≤ y = x == (x ⊓ y)

  diantisym : {x y : 𝟚} → x ≤ y → y ≤ x → x == y
  diantisym {x} {y} p q = (! q ∘ ⊓comm x y) ∘ p 

  cased01 : ∀ {l} {z : 𝟚} {A : Set l}
              → (f : (x : z == ``0) → A)
              → (g : (y : z == ``1) → A)
              → ((x : (z == ``0) ∨ (z == ``1) ) → A)
  cased01 f g = case f g (\ p q → abort (diabort (q ∘ ! p)))

  ∨-elimd01 : ∀ {l} {z : 𝟚} (A : (z == ``0) ∨ (z == ``1) → Set l)
              → (f : (x : z == ``0) → A (inl x))
              → (g : (y : z == ``1) → A (inr y))
              → ((x : (z == ``0) ∨ (z == ``1) ) → A x)
  ∨-elimd01 A f g = ∨-elim A f g (\ p q → abort (diabort (q ∘ ! p)))

  -- ----------------------------------------------------------------------
  -- Hom types 

  Hom : {l : Level} (A : Set l) (a0 a1 : A) → Set l
  Hom A a0 a1 = Σ (\ (p : 𝟚 → A) → (p ``0 == a0) × (p ``1 == a1))

  Hom= : {l : Level} {A : Set l} {a0 a1 : A}
         → (p q : Hom A a0 a1) 
         → ((x : 𝟚) → fst p x == fst q x) → p == q
  Hom= p q h = pair= (λ= h) (pair= uip uip)

  HomO : {l : Level} (A : 𝟚 → Set l) (a0 : A ``0) (a1 : A ``1) → Set l
  HomO A a0 a1 = Σ (\ (p : (x : 𝟚) → A x) → (p ``0 == a0) × (p ``1 == a1))

  HomO= : {l : Level} {A : 𝟚 → Set l} {a0 : A ``0} {a1 : A ``1}
         → (p q : HomO A a0 a1) 
         → ((x : 𝟚) → fst p x == fst q x) → p == q
  HomO= p q h = pair= (λ= h) (pair= uip uip)

  ⇒fstd : {l : Level} {A : I → 𝟚 → Set l} {a0 : (y : I) → A y ``0} {a1 : (y : I) → A y ``1} {r r' : I} (eq : r == r')
         → (p : HomO (A r) (a0 r) (a1 r))
         → (x : 𝟚) → fst (⇒ { A = \ r → HomO (A r) (a0 r) (a1 r)} p eq) x == ⇒ (fst p x) eq
  ⇒fstd id _ _ = id

  -- ENH: copy and paste of comPath, do extension types in general
  comHom : ∀ {l1 l : Level} {Γ : Set l1} {A : Γ × 𝟚 → Set l} (a0 : (γ : Γ) → A (γ , ``0)) (a1 : (γ : Γ) → A (γ , ``1)) 
          → relCom A 
          → relCom (\γ → HomO (\ z → A (γ , z)) (a0 γ) (a1 γ))
  comHom {A = A} a0 a1 comA p r r' α t b = 
          ((\ x → fst (coma x)) ,  (! (fst (snd (coma ``0)) (inr (inl id))) )  ,  (! (fst (snd (coma ``1)) (inr (inr id))) ) ) , 
          (\ pα →  HomO= _ _ (\ x → fst (snd (coma x)) (inl pα) ) ) , 
          (\ r=r' →  HomO= _ _ (\ x → snd (snd (coma x)) r=r' ∘ ⇒fstd {A = λ z z' → A (p z , z')} {a0 = λ z → a0 (p z)} {a1 = λ z → a1 (p z)} r=r' (fst b) _) ) where 
    coma : (x : 𝟚) → _
    coma x = comA (\ z → p z , x) r r' 
                  (α ∨ ((x == ``0) ∨ (x == ``1))) 
                  (\ z → case (\ pα → fst (t z pα) x ) 
                         (case (\ x=0 → transport ((\ x → A( p z , x))) (! x=0) (a0 (p z)) )
                               (\ x=1 → transport (((\ x → A( p z , x)))) (! x=1) (a1 (p z)) ) 
                               (\ p q → abort (diabort (q ∘ ! p))))
                         (\ pα → ∨-elim _ ( (\ x=0 → ap (transport _ (! x=0)) (fst (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=0))) ) ( ((\ x=1 → ap (transport _ (! x=1)) (snd (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=1)))) ) (\ _ _ → uip))) 
                  (fst (fst b) x , 
                   ∨-elim _ (\ pα →  ap (\ h → fst h x) (snd b pα) ) (∨-elim _ (\ x=0 →  ! (apd! (fst (fst b)) x=0) ∘ ap (transport _ (! x=0)) (! (fst (snd (fst b)))) ) ((\ x=1 →  ! (apd! (fst (fst b)) x=1) ∘ ap (transport _ (! x=1)) (! (snd (snd (fst b)))) )) ((\ _ _ → uip))) (((\ _ _ → uip))))

  fst-transport-Hom : {l1 l2 : Level} {Γ : Set l1} {A : Γ → Set l2} {a0 : (γ : Γ) → A γ} {a1 : (γ : Γ) → A γ}
                     {x y : Γ} (p : x == y)
                     → (q : Hom (A x) (a0 x) (a1 x))
                     → fst (transport (\ x → Hom (A x) (a0 x) (a1 x)) p q) == (\ x → transport A p (fst q x))
  fst-transport-Hom id q = id

  fst-transport-Hom-nd : {l1 l2 : Level} {Γ : Set l1} {A : Set l2} {a0 : Γ → A} {a1 : Γ → A}
                     {x y  : Γ} (p : x == y)
                     → (q : Hom A (a0 x) (a1 x))
                     → fst (transport (\ x → Hom A (a0 x) (a1 x)) p q) == (fst q)
  fst-transport-Hom-nd id q = id

  fst-transport-HomO-nd : {l1 l2 : Level} {Γ : Set l1} {A : 𝟚 → Set l2} {a0 : Γ → A ``0} {a1 : Γ → A ``1}
                     {x y  : Γ} (p : x == y)
                     → (q : HomO A (a0 x) (a1 x))
                     → fst (transport (\ x → HomO A (a0 x) (a1 x)) p q) == (fst q)
  fst-transport-HomO-nd id q = id

  -- ----------------------------------------------------------------------
  -- triangles

  ∂ : 𝟚 → Set
  ∂ i = (i == ``0) ∨ (i == ``1)

  Δ₂ = Σ \ (x : 𝟚) → Σ \ (y : 𝟚) → y ≤ x

  Δ₂= : {xy xy' : Δ₂} → fst xy == fst xy' → fst (snd xy) == fst (snd xy') → xy == xy'
  Δ₂= {xy} p q = pair= p (pair= (q ∘ fst-transport-Σ p (snd xy)) uip)

  Λ₂ : Δ₂ → Set
  Λ₂ (x , y , p) = (y == ``0) ∨ (x == ``1)

  lower-triangle : (x : 𝟚) (y : 𝟚) → Δ₂
  lower-triangle x y = (x , (x ⊓ y) , id)

  lower-trianglex0 : (x : 𝟚) → lower-triangle x ``0 ==  (x , ``0 , id)
  lower-trianglex0 x = id

  lower-triangle0y : (y : 𝟚) → lower-triangle ``0 y ==  (``0 , ``0 , id)
  lower-triangle0y y = id

  lower-trianglex1 : (x : 𝟚) → lower-triangle x ``1 ==  (x , x , id)
  lower-trianglex1 x = id

  lower-triangle1y : (y : 𝟚) → lower-triangle ``1 y ==  (``1 , y , id)
  lower-triangle1y y = id

  lower-triangle-diag : (x : 𝟚) → lower-triangle x x == ((x , x , id))
  lower-triangle-diag x = id

  lower-triangle-ret : (t : Δ₂) → lower-triangle (fst t) (fst (snd t)) == t
  lower-triangle-ret (x , y , y≤x) = pair= id (pair= (! y≤x ∘ ⊓comm x y ) uip)

  -- to construct a triangle, it suffices to construct a square
  -- with that as its lower triangle
  triangle-from-square : ∀ {l2} (A : Δ₂ → Set l2)
                       → ((x : 𝟚) (y : 𝟚) → A (lower-triangle x y))
                       → (xy : Δ₂) → A xy
  triangle-from-square A sq xy = transport A (lower-triangle-ret xy) (sq (fst xy) (fst (snd xy)))

  -- comes up often in this way
  triangle-from-square-boundary : ∀ {l2} (A : Δ₂ → Set l2)
                                  → (f : (x : 𝟚) (y : 𝟚) → A (lower-triangle x y))
                                  → (t : Δ₂)
                                  → (a : A (lower-triangle (fst t) (fst (snd t))))
                                  → a == f (fst t) (fst (snd t))
                                  → triangle-from-square A f t == transport A (lower-triangle-ret t) a
  triangle-from-square-boundary A sq xy a id = id

  -- uses diagonal cofib in 𝟚
  change-triangle-composite : ∀ {l} {A : Set l} → hasHCom A
                            → (t : Δ₂ → A)
                            → (r : (Hom A (t (``0 , ``0 , id)) (t (``1 , ``1 , id))))
                            → (Path (Hom A (t (``0 , ``0 , id)) (t (``1 , ``1 , id)))
                                    ((\ x → (t (x , x , id))) , id , id)
                                    r)
                            → (xy : Δ₂) → A [ Λ₂ xy ↦ k (t xy) , (fst xy) == (fst (snd xy)) ↦ k (fst r (fst xy)) ]
  change-triangle-composite hcomA t r p (x , y , y≤x) =
    fst c , (\ l → fst (snd c) (inl l)) , (\ x=y → fst (snd c) (inr x=y) ∘ ! (ap= (ap fst (snd (snd p))))) where
    c = hcomA `0 `1 ((Λ₂ (x , y , y≤x)) ∨ (x == y))
                    (\ z → case (\ _ → t (x , y , y≤x) )
                                (\ x=y →  fst (fst p z) x  )
                                (∨-elim _ (\ y=0 x=y → coh1 z x y y=0 x=y y≤x )
                                          (\ x=1 x=y → coh2 z x y x=1 x=y y≤x)
                                          (λ _ _ → λ= \ _ → uip)))
                    (t (x , y , y≤x) , ∨-elim _ (\ _ → id) (\ q → ! (coh3 x y q y≤x)) (λ _ _ → uip)) where

      coh1 : (z : _) (x y : _) (x₁ : y == ``0) (y₁ : x == y)  (y≤x : _) → t (x , y , y≤x) == fst (fst p z) x
      coh1 z _ _ id id id = ! (fst (snd (fst p z)))  

      coh2 : (z : _) (x y : _) (x₁ : x == ``1) (y₁ : x == y)  (y≤x : _) → t (x , y , y≤x) == fst (fst p z) x
      coh2 z _ _ id id id = ! (snd (snd (fst p z)))  

      coh3 : (x y : _) (y₁ : x == y)  (y≤x : _) → t (x , y , y≤x) == fst (fst p `0) x
      coh3 _ _ id id =  ! (ap= (ap fst (fst (snd p)))) 

  -- FIXME: abstract copy and paste
  change-triangle-composite-backwards : ∀ {l} {A : Set l} → hasHCom A
                            → (t : Δ₂ → A)
                            → (r : (Hom A (t (``0 , ``0 , id)) (t (``1 , ``1 , id))))
                            → (Path (Hom A (t (``0 , ``0 , id)) (t (``1 , ``1 , id)))
                                    r
                                    ((\ x → (t (x , x , id))) , id , id))
                            → (xy : Δ₂) → A [ Λ₂ xy ↦ k (t xy) , (fst xy) == (fst (snd xy)) ↦ k (fst r (fst xy)) ]
  change-triangle-composite-backwards hcomA t r p (x , y , y≤x) =
    fst c , (\ l → fst (snd c) (inl l)) , (\ x=y → fst (snd c) (inr x=y) ∘  ! (ap= (ap fst (fst (snd p)))) ) where
    c = hcomA `1 `0 ((Λ₂ (x , y , y≤x)) ∨ (x == y))
                    (\ z → case (\ _ → t (x , y , y≤x) )
                                (\ x=y →  fst (fst p z) x  )
                                (∨-elim _ (\ y=0 x=y → coh1 z x y y=0 x=y y≤x )
                                          (\ x=1 x=y → coh2 z x y x=1 x=y y≤x)
                                          (λ _ _ → λ= \ _ → uip)))
                    (t (x , y , y≤x) , ∨-elim _ (\ _ → id) (\ q →  ! (coh3 x y q y≤x) ) (λ _ _ → uip)) where

      coh1 : (z : _) (x y : _) (x₁ : y == ``0) (y₁ : x == y)  (y≤x : _) → t (x , y , y≤x) == fst (fst p z) x
      coh1 z _ _ id id id = ! (fst (snd (fst p z)))  

      coh2 : (z : _) (x y : _) (x₁ : x == ``1) (y₁ : x == y)  (y≤x : _) → t (x , y , y≤x) == fst (fst p z) x
      coh2 z _ _ id id id = ! (snd (snd (fst p z)))  

      coh3 : (x y : _) (y₁ : x == y)  (y≤x : _) → t (x , y , y≤x) == fst (fst p `1) x
      coh3 _ _ id id =  ! (ap= (ap fst (snd (snd p)))) 


  pathHomExchange : ∀ {l : Level} {A : Set l} {a0 a1 : A} → (f g : Hom A a0 a1)
          → (HomO (\ x → Path A (fst f x) (fst g x)) ((λ _ → a0) , ! (fst (snd f))  , ! (fst (snd g))) ((λ _ → a1) , ! (snd (snd f)) ,  ! (snd (snd g))))
          → Path (Hom A a0 a1) f g
  pathHomExchange f g h = (λ x → (\ z → fst (fst h z) x) , ap (\ Z → fst Z x) (fst (snd h))  , ap (\ Z → fst Z x) (snd (snd h))) , pair= (λ= \ x → fst (snd (fst h x))) (pair= uip uip) , pair= ((λ= \ x → snd (snd (fst h x)))) (pair= uip uip)
 

  -- ----------------------------------------------------------------------
  -- some currently unused things

  private

    ≤-to-hom : ∀ {x y} → x ≤ y → Hom 𝟚 x y
    ≤-to-hom {x} {y} p = (\ z → ((z ⊔ x) ⊓ y)) , (! p , id)

    upper-triangle : (x : 𝟚) (y : 𝟚) → Δ₂
    upper-triangle x y = (x ⊔ y , x , id)

    -- note the swap: Δ₂ is a lower triangle, so it's the identity on the swap of that, which is an upper triangle
    upper-triangle-ret : (t : Δ₂) → upper-triangle (fst (snd t)) (fst t) == t
    upper-triangle-ret (x , y , y≤x) = pair= ((ap (\ h → x ⊔ h) y≤x) ∘ ⊔comm y x) (pair= ((fst-transport-Σ ((ap (\ h → x ⊔ h) y≤x) ∘ ⊔comm y x) (y , id))) uip)
