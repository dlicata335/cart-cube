{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Prop
open import directed.DirInterval
open import universe.LibFlat
open import Equiv
open import Cofibs
open import Kan
open import Path
open import Interval
open import universe.Sigma
open import universe.Pi
open import directed.Covariant
open import directed.UCov

module directed.Discrete where

  DiscreteFn : {l : Level} (A : Set l) → Set l
  DiscreteFn A = (a b : A) → Hom A a b → Path A a b 
  
  relCov-constant-discrete : ∀ {l1 l2} (A : Set l2)
                             → CovFill.relCov {Γ = Unit{l1}} (\ _ → A)
                             → DiscreteFn A
  relCov-constant-discrete {_}{_} A dcomA a b p = 
      (\ x → fst (c x)) , ! (fst (snd (c `0)) (inl id)) , snd (snd p) ∘ ! (fst (snd (c `1)) (inr id)) where
      c : (x : I) → _
      c x = dcomA (\ x → <>)
                  ``1
                  ((x == `0) ∨ (x == `1))
                  (\ z → case ((\ _ → a))
                              ((\ _ → fst p z))
                              (\ p q → abort (iabort (q ∘ ! p))))
                  ((a , ∨-elim _ (\ _ → id)
                                 (\ _ → fst (snd p) )
                                 (λ p₁ q → abort (iabort (q ∘ ! p₁))))) 

  -- TODO: prove implies equiv
  hasHCom𝟚 : {l : Level} → Set l → Set (lmax (lsuc lzero) l)
  hasHCom𝟚 A = (r r' : 𝟚) (α : Set) {{_ : Cofib α}} 
                → (t : (z : 𝟚) → α → A) 
                → (b : A [ α ↦ t r ]) 
                → A [ α ↦ t r' , (r == r') ↦ (λ eq → fst b) ]

  ∘Hom' : ∀ {l} {A : Set l} {a b c : A} → hasHCom𝟚 A → Hom A b c → Hom A a b → Hom A a c
  ∘Hom' {a = a} hA q p = (\ x → fst (c x)) , 
                ! (fst (snd (c ``0)) (inl id))  ,  snd (snd q) ∘ ! (fst (snd (c ``1)) (inr id))  where
    c : (x : 𝟚) → _
    c x = (hA ``0 ``1 ((x == ``0) ∨ (x == ``1)) (\ z → case (\ x=0 → a) ((\ x=1 → fst q z)) (\ p q → abort (diabort (q ∘ ! p)))) (fst p x , ∨-elim _ ( (\ x=0 →  ap (fst p) (! (x=0)) ∘ ! (fst (snd p)) ) ) ( ((λ x=1 → ap (fst p) (! x=1) ∘ ! (snd (snd p)) ∘ fst (snd q))) ) (\ _ _ → uip))) 

  !Hom : ∀ {l} {A : Set l} {a b : A} → hasHCom𝟚 A → Hom A a b → Hom A b a
  !Hom {a = a}{b} hA p = 
                (\ x → fst (c x)) , 
                 snd (snd p) ∘ ! (fst (snd (c ``0)) (inl id))  , id ∘ ! (fst (snd (c ``1)) (inr id))  where
    c : (x : 𝟚) → _
    c x = (hA ``0 ``1 ((x == ``0) ∨ (x == ``1)) 
              (\ z → case (\ x=0 → fst p z) ((\ x=1 → a)) (\ p q → abort (diabort (q ∘ ! p))))
              (a , ∨-elim _ ( (\ x=0 → ((fst (snd p))) )) ( ((λ x=1 → id)) ) (\ _ _ → uip)))

  hasHCom𝟚-hprop : ∀{l}{A : Set l} → (com1 com2 : hasHCom𝟚 A) → Path _ com1 com2
  hasHCom𝟚-hprop {A = A} com1 com2 = (λ x r r' α {{c}} t b → fst (f x r r' α {{c}} t b) , (λ u → fst (snd (f x r r' α {{c}} t b)) (inl u)) , snd (snd (f x r r' α {{c}} t b)))
                                     , (λ= λ r → λ= λ r' → λ= λ α → λ=inf λ c → λ= λ t → λ= λ b → pair= (!(fst (snd (f `0 r r' α {{c}} t b)) (inr (inl id)))) (pair= (λ= λ _ → uip) (λ= λ _ → uip)))
                                     , (λ= λ r → λ= λ r' → λ= λ α → λ=inf λ c → λ= λ t → λ= λ b → pair= (!(fst (snd (f `1 r r' α {{c}} t b)) (inr (inr id)))) (pair= (λ= λ _ → uip) (λ= λ _ → uip))) where

    f : (x : I)(r r' : 𝟚)(α : Set){{c : Cofib α}}(t : (z : 𝟚) → α → A)(b : A [ α ↦ t r ]) → _
    f x r r' α {{c}} t b = com1 r r' (α ∨ ((x == `0) ∨ (x == `1)))
                                (λ i → case (λ u → t i u)
                                            (case01 (λ _ → fst (com1 r i α t b))
                                                    (λ _ → fst (com2 r i α t b)))
                                            (λ u → ∨-elim01 _ (λ _ → fst (snd (com1 r i α t b)) u)
                                                              (λ _ → fst (snd (com2 r i α t b)) u)))
                                (fst b , ∨-elim _ (snd b)
                                                  (∨-elim01 _ (λ _ → ! (snd (snd (com1 r r α t b)) id))
                                                              (λ _ → ! (snd (snd (com2 r r α t b)) id)))
                                                  (λ _ _ → uip))

  hcom𝟚-regular :  ∀ {l2} (A : Set l2) 
                → (hcom𝟚A : hasHCom𝟚 A) 
                → ∀ r r' α {{ cα : Cofib α }} (t : α → A) b →
                        (Path A (fst (hcom𝟚A r r' α (\ _ pα → t pα) b)) (fst b))
  hcom𝟚-regular A hcom𝟚A r r' α {{ cα }} t b =
     (\ x → fst (h x)) , ! (fst (snd (h `0)) (inr (inl id))) ,  ! (fst (snd (h `1)) (inr (inr id))) where
    h = \ x → hcom𝟚A r r' (α ∨ ((x == `0) ∨ (x == `1)))
                         (\ z → case t
                                     (case ((\ _ → fst (hcom𝟚A r z α (\ _ pα → t pα) b)))
                                           (\ _ → fst b)
                                           (\ p q → abort (iabort (q ∘ ! p))))
                                     (\ pα →  ∨-elim _
                                                     ( \ _ → fst (snd (hcom𝟚A r z α (\ _ pα → t pα) b)) pα )
                                                     (\ _ → snd b pα)
                                                     (\ p q → abort (iabort (q ∘ ! p)))))
                         (fst b , ∨-elim _
                                         (snd b)
                                         (∨-elim _ (\ _ → ! ((snd (snd (hcom𝟚A r r α (λ _ → t) b))) id))
                                                   (\ _ → id)
                                                   (\ _ _ → uip))
                                         (\ _ _ → uip))

  hasHCom𝟚01 : {l : Level} → Set l → Set (lmax (lsuc lzero) l)
  hasHCom𝟚01 A =  (α : Set) {{_ : Cofib α}} 
                → (t : (z : 𝟚) → α → A) 
                → (b : A [ α ↦ t ``0 ]) 
                → A [ α ↦ t ``1 ]
              
  !Hom01 : ∀ {l} {A : Set l} {a b : A} → hasHCom𝟚01 A → Hom A a b → Hom A b a
  !Hom01 {a = a}{b} hA p = 
                  (\ x → fst (c x)) , 
                   snd (snd p) ∘ !  (snd (c ``0) (inl id))  , id ∘ ! (snd (c ``1) (inr id))  where
    c : (x : 𝟚) → _
    c x = (hA ((x == ``0) ∨ (x == ``1)) 
              (\ z → case (\ x=0 → fst p z) ((\ x=1 → a)) (\ p q → abort (diabort (q ∘ ! p))))
              (a , ∨-elim _ ( (\ x=0 → ((fst (snd p))) )) ( ((λ x=1 → id)) ) (\ _ _ → uip)))

  hasHCom𝟚0 : {l : Level} → Set l → Set (lmax (lsuc lzero) l)
  hasHCom𝟚0 A = (r : 𝟚) (α : Set) {{_ : Cofib α}} 
                → (t : (z : 𝟚) → α → A) 
                → (b : A [ α ↦ t ``0 ]) 
                → A [ α ↦ t r , (``0 == r) ↦ k (fst b) ]

  hasHCom𝟚-to-hasHCom𝟚01 : ∀{l}{A : Set l} → hasHCom𝟚 A → hasHCom𝟚01 A
  hasHCom𝟚-to-hasHCom𝟚01 discA α t b = fst (discA ``0 ``1 α t b) , fst (snd (discA ``0 ``1 α t b))

  hasHCom𝟚-to-hasHCom𝟚0 : ∀{l}{A : Set l} → hasHCom𝟚 A → hasHCom𝟚0 A
  hasHCom𝟚-to-hasHCom𝟚0 discA r α t b = fst (discA ``0 r α t b) , fst (snd (discA ``0 r α t b)) , snd (snd (discA ``0 r α t b))

  hasHCom𝟚01-to-hasHCom𝟚0 : ∀{l}{A : Set l} → hasHCom𝟚01 A → hasHCom𝟚0 A
  hasHCom𝟚01-to-hasHCom𝟚0 discA r α t b = fst fill , (λ u → snd fill (inl u)) , (λ eq → snd fill (inr (! eq))) where

    fill : _
    fill = discA (α ∨ (r == ``0))
                 (λ i → case (t (i ⊓ r)) (λ _ → fst b)
                             (λ u r=0 → (snd b) u ∘ ap (λ r → (t (i ⊓ r) u)) r=0))
                 (fst b , ∨-elim _ (snd b) (λ r=0 → id) (λ _ _ → uip))

{-
  hasHCom𝟚0-to-hasHCom𝟚 : ∀{l}{A : Set l} → hasHCom𝟚0 A → hasHCom𝟚 A
  hasHCom𝟚0-to-hasHCom𝟚 discA r r' α t b = fst fill , {!λ u → fst (snd fill) (inl u)!} , (λ eq → {!snd (snd fill)!}) where

    fill : _
    fill = discA r' (α ∨ (r == r')) -- what if we do r ≤ r' and r' ≤ r ? 
                    (λ i → ∨-elim _ {!t ?!} (λ _ → fst b)
                                    (λ u r'=r → (snd b) u ∘ {!!}))
                    (fst b , ∨-elim _ {!snd b!} {!!} (λ _ _ → uip))

-}

{-
  hasHCom𝟚eq' : {l : Level}(A : Set l)
                (discA : hasHCom𝟚01 A)
                (α : Set) {{_ : Cofib α}} 
                (t : α → A)
                (b : _)
                → fst (discA α (λ _ → t) b) == fst b
  hasHCom𝟚eq' A discA α {{c}} t b = {!!} where
-}

{- TODO: 
  hasHCom𝟚01-to-hasHCom𝟚0 : ∀{l}{A : Set l} → hasHCom𝟚01 A →
                (r : 𝟚) (α : Set) {{_ : Cofib α}} 
                → (t : (z : 𝟚) → α → A) 
                → (b : A [ α ↦ t ``0 ]) 
                → A [ α ↦ t r , (``0 == r) ↦ (λ eq → transport _  eq (fst b)) ]
  hasHCom𝟚01-to-hasHCom𝟚0 discA r α {{c}} t b = fst (filla r) , (snd (filla r)) , (λ eq → {!!}) where

    filla : ∀ r → _
    filla r = discA (α ∨ (``0 == r)) {{c}} (λ i → t (i ⊓ r)) b
-}

  hasHCom𝟚-to-DiscreteFn' :
    ∀{l} (A : Set l)
    (discA : hasHCom𝟚01 A)
    →
    DiscreteFn A
  hasHCom𝟚-to-DiscreteFn' A discA x y p = (λ i → fst (pA i)) ,  fst (snd p) ∘ ! (snd (pA `0) (inl id)) , snd (snd p) ∘ ! (snd (pA `1) (inr id)) where

    t : (i : I) → (z : 𝟚) → ((i == `0) ∨ (i == `1)) → A
    t i z = ∨-elim _ (λ _ → fst p ``0)
                     (λ _ → fst p z)
                     (λ i=0 i=1 → abort (iabort (i=1 ∘ ! i=0)))

    b : (i : I) → A [ _ ↦ t i ``0 ]
    b i = fst p ``0 , ∨-elim _ (λ _ → id) (λ _ → id) (λ i=0 i=1 → abort (iabort (i=1 ∘ ! i=0)))

    pA : (i : I) → A [ _ ↦ t i ``1 ]
    pA i = discA ((i == `0) ∨ (i == `1)) (t i) (b i)

  hasHCom𝟚-to-DiscreteFn :
    ∀{l} (A : Set l)
    (discA : hasHCom𝟚 A)
    →
    DiscreteFn A
  hasHCom𝟚-to-DiscreteFn A discA x y p = (λ i → fst (pA i)) ,  fst (snd p) ∘ ! (fst (snd (pA `0)) (inl id)) , snd (snd p) ∘ ! (fst (snd (pA `1)) (inr id)) where

    t : (i : I) → (z : 𝟚) → ((i == `0) ∨ (i == `1)) → A
    t i z = ∨-elim _ (λ _ → fst p ``0)
                     (λ _ → fst p z)
                     (λ i=0 i=1 → abort (iabort (i=1 ∘ ! i=0)))

    b : (i : I) → A [ _ ↦ t i ``0 ]
    b i = fst p ``0 , ∨-elim _ (λ _ → id) (λ _ → id) (λ i=0 i=1 → abort (iabort (i=1 ∘ ! i=0)))

    pA : (i : I) → _
    pA i = discA ``0 ``1 ((i == `0) ∨ (i == `1)) (t i) (b i)
{-   
  DiscreteFn-to-hasHCom𝟚 :
    ∀{l} (A : Set l)
    (hcomA : hasHCom A)
    (discfA : DiscreteFn A)
    →
    hasHCom𝟚 A
  DiscreteFn-to-hasHCom𝟚 A hcomA discfA r r' α t b = a , αext , {!!} where
    thom0r : (u : α) → Hom A _ _
    thom0r u = (λ z → t (z ⊓ r) u) , id , id

    thom0r' : (u : α) → Hom A _ _
    thom0r' u = (λ z → t (z ⊓ r') u) , id , id

    tpath0r : (u : α) → Path A (t ``0 u) (t r u)
    tpath0r u = discfA _ _(thom0r u)

    tpath0r! : (u : α) → Path A (t r u) (t ``0 u)
    tpath0r! u = !Path hcomA (tpath0r u)

    tpath0r' : (u : α) → Path A (t ``0 u) (t r' u)
    tpath0r' u = discfA _ _(thom0r' u)

    tpath : (u : α) → Path A (t r u) (t r' u)
    tpath u = ∘Path hcomA (tpath0r' u) (tpath0r! u) 

    t' : (i : I) → α → A
    t' i u = fst (tpath u) i

    b' : A [ α ↦ t' `0 ]
    b' = fst b , (λ u → snd b u ∘ fst (snd (tpath u)))

    aext : _
    aext = hcomA `0 `1 _ t' b' 

    a : A
    a = fst aext

    αext : extends α (t r') a
    αext u = fst (snd (hcomA `0 `1 _ t' b')) u ∘ ! (snd (snd (tpath u)))

    idext : extends (r == r') (λ eq → transport (λ v → A) eq (fst b)) a
    idext eq = {!!}
-}

  hasHCom𝟚-to-relCov : ∀{l}
    (A : Set l)
    (discA : hasHCom𝟚 A)
    → -------------------------------------
    CovFill.relCov {Γ = Unit{l}} (\ _ → A)
  hasHCom𝟚-to-relCov A discA p r α t b = fst a , fst (snd a) , (λ eq →  (snd (snd a)) eq ∘ ap= (transport-constant eq)) where
    a = discA ``0 r α t b

  open Layered

  -- hasHCom𝟚-ElUCov : ∀{l :{♭} Level}
  --   (A : UCov l)
  --   →
  --   hasHCom𝟚 (ElC A)
  -- hasHCom𝟚-ElUCov A r r' α t b = {!!}

  hasHCom𝟚-Π : ∀ {l1 l2}
    {A : Set l1}
    {B : A → Set l2}
    (discB : (x : A) → hasHCom𝟚 (B x))
    →
    hasHCom𝟚 ((x :  A) → B x)
  hasHCom𝟚-Π {A = A} {B} discB r r' α t b = (λ x → fst (f x)) , (λ u → λ= λ x → fst (snd (f x)) u)
                                          , (λ eq → λ= λ x → snd (snd (f x)) eq) where

    f : (x : A) → _
    f x = discB x r r' α (λ i u → t i u x) ((fst b) x , (λ u → ap (λ f → f x) (snd b u)))
 
  hasHCom𝟚-Π' : ∀ {l1 l2}
    {A : Set l1}
    {B : A → Set l2}
    (discB : (x : A) → hasHCom𝟚01 (B x))
    →
    hasHCom𝟚01 ((x :  A) → B x)
  hasHCom𝟚-Π' {A = A} {B} discB α t b = (λ x → fst (f x)) , (λ u → λ= λ x → snd (f x) u) where

    f : (x : A) → _
    f x = discB x α (λ i u → t i u x) ((fst b) x , (λ u → ap (λ f → f x) (snd b u)))
 
  hasHCom𝟚-Π0 : ∀ {l1 l2}
    {A : Set l1}
    {B : A → Set l2}
    (discB : (x : A) → hasHCom𝟚0 (B x))
    →
    hasHCom𝟚0 ((x :  A) → B x)
  hasHCom𝟚-Π0 {A = A} {B} discB r α t b = (λ x → fst (f x)) , (λ u → λ= λ x → fst (snd (f x)) u)
                                        , (λ eq → λ= λ x → snd (snd (f x)) eq) where

    f : (x : A) → _
    f x = discB x r α (λ i u → t i u x) ((fst b) x , (λ u → ap (λ f → f x) (snd b u)))

  hasHCom𝟚-× : ∀ {l1 l2}
    {A : Set l1}
    {B : Set l2}
    (discA : hasHCom𝟚 A)
    (discB : hasHCom𝟚 B)
    →
    hasHCom𝟚 (A × B)
  hasHCom𝟚-× discA discB r r' α t b = (fst da , fst db) , (λ u → ×= (fst (snd da) u) (fst (snd db) u)) , (λ eq → ×= (snd (snd da) eq) (snd (snd db) eq)) where

    da : _
    da = discA r r' α (λ j u → fst (t j u)) (fst (fst b) , (λ u → ap fst (snd b u)))

    db : _
    db = discB r r' α (λ j u → snd (t j u)) (snd (fst b) , (λ u → ap snd (snd b u)))

  hasHCom𝟚-×0 : ∀ {l1 l2}
    {A : Set l1}
    {B : Set l2}
    (discA : hasHCom𝟚0 A)
    (discB : hasHCom𝟚0 B)
    →
    hasHCom𝟚0 (A × B)
  hasHCom𝟚-×0 discA discB r α t b = (fst da , fst db) , (λ u → ×= (fst (snd da) u) (fst (snd db) u)) , (λ eq → ×= (snd (snd da) eq) (snd (snd db) eq)) where

    da : _
    da = discA r α (λ j u → fst (t j u)) (fst (fst b) , (λ u → ap fst (snd b u)))

    db : _
    db = discB r α (λ j u → snd (t j u)) (snd (fst b) , (λ u → ap snd (snd b u)))
    
  hasHCom𝟚-×' : ∀ {l1 l2}
    {A : Set l1}
    {B : Set l2}
    (discA : hasHCom𝟚 A)
    (discB : hasHCom𝟚 B)
    →
    hasHCom𝟚01 (A × B)
  hasHCom𝟚-×' discA discB α t b = (fst da , fst db) , (λ u → ×= (fst (snd da) u) (fst (snd db) u)) where

    da : _
    da = discA ``0 ``1 α (λ j u → fst (t j u)) (fst (fst b) , (λ u → ap fst (snd b u)))

    db : _
    db = discB ``0 ``1 α (λ j u → snd (t j u)) (snd (fst b) , (λ u → ap snd (snd b u)))

{-
  com-hasHCom𝟚 : {l1 l2 : Level}
                {Γ : Set l1}
                (A : Γ → Set l2)
                (comA : relCom (λ x → A x))
                →
                (relCom (λ x → hasHCom𝟚 (A x)))
  com-hasHCom𝟚 {Γ = Γ} A comA p r r' α {{c}} t b = hcomA , {!!} , {!!} where

    tpath : ∀ u i → Path A (fst (t i u)) (fst (t ``1 u))
    tpath u i = hasHCom𝟚-to-DiscreteFn' A discA _ _ (thom u i)

    bhom : Hom A (fst (fst b)) (fst (p1 ``1))
    bhom = (λ i → fst (p1 i)) , ! (snd (p1 ``0) (inr id)) , id

    bpath = hasHCom𝟚-to-DiscreteFn' A discA _ _ bhom

    b2 : _
    b2 = comB (fst bpath) `0 `1 α (λ i u → {!!}) (transport B (!(fst (snd bpath))) (snd (fst b)) , (λ u → {!!}))

    p2 : _ 
    p2 = discB (fst (p1 ``1)) α
               (λ i u → transport B (snd (p1 ``1) (inl u)) (snd (t ``1 u)))
               (transport B (snd (snd bpath)) (fst b2) , (λ u → {!apd snd ((snd b) u)!}))
               {- (transport B (snd (snd bpath)) (fst b2)
               , λ u → {!snd (fst b)!}) -}
-}
{- move-transport-right! B (snd (snd bpath))
                                              ({!!}
                                              ∘ ap (λ f → f (fst (t2 u ``0))) (! (transport-∘ B (!(snd (snd bpath))) (snd (p1 ``1) (inl u) ∘ snd (snd (tpath u ``0))))))) -}

--  ap (λ eq → transport B eq (fst (t2 u ``0))) (uip {p = id} {(! (snd (snd bpath)) ∘ snd (p1 ``1) (inl u) ∘ snd (snd (tpath u ``0)))})

  hasHCom𝟚-DiscreteFn-𝟚→  : {l : Level} {A : Set l} → hasHCom𝟚 A
                   → (p : 𝟚 → A)
                   → Path A (p ``0) (p ``1)
  hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p = (\ x → fst (newp x)) , ! (fst (snd (newp `0)) (inl id)) ,  ! (fst (snd (newp `1)) (inr id)) where
    newp : (x : I) → _
    newp x = hcom𝟚A ``0 ``1
                    ((x == `0) ∨ (x == `1)) (\ z → case01 (\ _ → p ``0) (\ _ → p z))
                    (p ``0 , ∨-elim01 _ (\ _ → id) (\ _ → id))

  -- it feels like both of these should be an instance of some
  -- "induction-along-an-equivalence" for the I → A is 𝟚 → A equivalence,
  -- though that can probably be β-reduced to something more direct.
  --
  -- though I don't exactly see it
  --
  -- where induction-along-equivalence is that if f : A ≃ A' and B : A → Set
  -- then to get (a : A) → B(a) it suffices to give (a' : A') → B(f a')

  hasHCom𝟚-discrete-induction0 : {l l2 : Level} {A : Set l}
                                 (hcom𝟚A : hasHCom𝟚 A)
                               → (B : A → Set l2)
                               → (p : 𝟚 → A)
                               → (B (p ``0))
                               → (B (fst (hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p) `0))
  hasHCom𝟚-discrete-induction0 hcom𝟚A B p b = transport B (!(fst (snd (hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p)))) b

  hasHCom𝟚-discrete-induction1 : {l l2 : Level} {A : Set l}
                                 (hcom𝟚A : hasHCom𝟚 A)
                               → (B : A → Set l2)
                               → (p : 𝟚 → A)
                               → (B (p ``1))
                               → (B (fst (hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p) `1))
  hasHCom𝟚-discrete-induction1 hcom𝟚A B p b = transport B (!(snd (snd (hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p)))) b
{-
  hasHCom𝟚-discrete-induction  : {l l2 : Level} {A : Set l}
                                 (hcom𝟚A : hasHCom𝟚 A)
                               → (B : A → Set l2)
                               → relCom B
                               → (p : 𝟚 → A)
                               → ((x : 𝟚) → B (p x))
                               → ((x : I) → B (fst (hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p) x))
  hasHCom𝟚-discrete-induction hcom𝟚A B comB p b x = fst (fillb x) where

    fillb : ∀ i → _
    fillb i = (relCom-relCoe B comB) (fst (hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p)) `0 i (hasHCom𝟚-discrete-induction0 hcom𝟚A B p (b ``0))
-}

{- HERE-0

  hasHCom𝟚-discrete-PathO : {l l2 : Level} {A : Set l}
                                 (hcom𝟚A : hasHCom𝟚 A)
                               → (B : A → Set l2)
                               → (discB : (x : A) → hasHCom𝟚01 (B x))
                               → relCom B
                               → (p : 𝟚 → A)
                               → (b : (x : 𝟚) → B (p x))
                               → PathO (B o (fst (hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p)))
                                       (hasHCom𝟚-discrete-induction0 hcom𝟚A B p (b ``0))
                                       (hasHCom𝟚-discrete-induction1 hcom𝟚A B p (b ``1))
  hasHCom𝟚-discrete-PathO {A = A} hcom𝟚A B discB comB p b =
                          (\ z → fst (fix' z)) ,
                          ! (snd (fillb0 `0) id) ∘ ! ((snd (fix' `0)) (inl id)) ,
                          snd (snd fixhom) ∘ ! ((snd (fix' `1)) (inr id)) where

    -- from I 
    newp = hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p

    fillb0 : ∀ i → _
    fillb0 i = relCom-relCoe B comB (fst newp) `0 i (hasHCom𝟚-discrete-induction0 hcom𝟚A B p (b ``0))

    -- fillb1 : ∀ i → _
    -- fillb1 i = (relCom-relCoe B comB) (fst newp) `1 i (hasHCom𝟚-discrete-induction1 hcom𝟚A B p (b ``1))

    -- fix : ∀ (i : I) → _
    -- fix i =  relCom-hasHCom B comB (fst newp i) `0 `1
    --                        ((i == `0) ∨ (i == `1))
    --                        (\ z → case01 (\ _ → fst (fillb0 i) )
    --                                      (\ i=1 → {!    !} ) )
    --                        ((fst (fillb0 i) ,
    --                         ∨-elim01 _ (\ _ → id)
    --                                    {!!} ))

    -- at 0 equals newp
    a'' : ∀ z → Path A (p z) (p ``1)
    a'' z = hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A (\ x → (p (z ⊔ x)))

    apath'' : ∀ x → Path _ (fst (a'' ``1) x) (p ``1)
    apath'' x = hcom𝟚-regular _ hcom𝟚A _ _ _ _ _

    b' : ∀ i z → _
    b' i z = relCom-relCoe B comB (fst (a'' z)) `0 i (transport B (! (fst (snd (a'' z)))) (b z))

    b'0eq : b' `1 ``0 == fillb0 `1
    b'0eq = pair= id (λ= λ _ → uip)

    b'' : ∀ i → _
    b'' i = comB (fst (apath'' i)) `0 `1 (i == `0) (λ z i=0 → transport B (! (ap (λ i → fst (apath'' i) z) i=0) ∘ {! ap (λ x → fst x z) (fst (snd (apath'' )))!}) (fst (b' z ``1))) (transport B (! (fst (snd (apath'' i)))) (fst (b' i ``1)) , {!!}) -- this is very wrong (maybe wrong nesting order?)

    -- do as pathovers, then compose(?) to get het. path (or do lots of transports...if even possible)
    -- or can I always turn a pathover into a homover 
    bpathO : PathO _ (transport B (! (fst (snd (a'' ``1)))) (b ``1)) (fst (b' `1 ``1))
    bpathO = (λ i → fst (b' i ``1)) , ! (snd (b' `0 ``1) id) , id

    bpath : Path (B (p ``1)) (b ``1) (transport B (snd (snd (a'' ``1))) (fst (b' `1 ``1)))
    bpath = (λ i → transport B (snd (snd (apath'' i))) (fst (b'' i))) , {!snd (b'' `0)!} , {!!} 


    -- is this now circular? (hopefully not, as I can do all of this with just a reg. hom)
    bhomO : HomO _ (fst (fillb0 `1)) (fst (b' `1 ``1))
    bhomO = (λ i → fst (b' `1 i)) , id , id

    fixhomhelp : 𝟚 → _
    fixhomhelp i = {! blah!}

    fixhom' : Hom _ (hasHCom𝟚-discrete-induction1 hcom𝟚A B p (b ``1)) (fst (fillb0 `1))
    fixhom' = fixhomhelp
            , {!!}
            , {!!} 

    fixhom : Hom _ (fst (fillb0 `1)) (hasHCom𝟚-discrete-induction1 hcom𝟚A B p (b ``1))
    fixhom = !Hom01  (discB _) fixhom'
    {- (λ z → transport B (! (snd (snd newp)) ∘ snd (snd (a'' z))) (fst (b' z)))
           , {!!} -- true, but annoying
           , {!!} -}


    fixpath : Path _ (fst (fillb0 `1)) (hasHCom𝟚-discrete-induction1 hcom𝟚A B p (b ``1))
    fixpath = !Path (relCom-hasHCom B comB _) ({! (fillb0 i)!} , {!!} , {!!})

    fix'' : ∀ (i : I) → _
    fix'' i = relCom-hasHCom B comB (fst newp i) `0 `1
                                    ((i == `0) ∨ (i == `1))
                                    (\ z → case01 (\ _ → fst (fillb0 i))
                                                  (\ i=1 → transport B (ap (fst newp) (! i=1)) (fst fixpath z)))
                                    ((fst (fillb0 i) ,
                                      ∨-elim01 _ (\ _ → id)
                                                 (λ i=1 → apd (λ i → fst (fillb0 i)) (! i=1)
                                                        ∘ ap (transport (λ z → B (fst newp z)) (! i=1)) (fst (snd fixpath))
                                                        ∘ ! (ap (λ f → f (fst fixpath `0)) (transport-ap-assoc' B (fst newp) (! i=1))))))

    fix' : ∀ (i : I) → _
    fix' i =  discB (fst newp i) 
                    ((i == `0) ∨ (i == `1))
                    (\ z → case01 (\ _ → fst (fillb0 i))
                                  (\ i=1 → transport B (ap (fst newp) (! i=1)) (fst fixhom z)))
                    ((fst (fillb0 i) ,
                      ∨-elim01 _ (\ _ → id)
                                 (λ i=1 → apd (λ i → fst (fillb0 i)) (! i=1)
                                        ∘ ap (transport (λ z → B (fst newp z)) (! i=1)) (fst (snd fixhom))
                                        ∘ ! (ap (λ f → f (fst fixhom ``0)) (transport-ap-assoc' B (fst newp) (! i=1))))))

{-
    fix' : ∀ (i : I) → _
    fix' i =  discB (fst newp i) 
                    ((i == `0) ∨ (i == `1))
                    (\ z → case01 (\ _ → fst (fillb0 i) )
                                  (\ i=1 →  transport B ((ap (fst newp) (! i=1) ∘ ! (snd (snd newp))) ∘ snd (snd (a'' z)))
                                      (fst (relCom-relCoe B comB (fst (a'' z)) `0 `1
                                                          (transport B (! (fst (snd (a'' z))))
                                                           (b z))))))
                    ((fst (fillb0 i) ,
                      ∨-elim01 _ (\ _ → id)
                                 (λ i=1 → {!!}))) -- transport B ((ap (fst newp) id ∘ ! (snd (snd newp))) ∘ snd (snd (a'' ``1))) (fst (relCom-relCoe B comB (fst (a'' ``1)) `0 `1 (transport B (! (fst (snd (a'' ``1)))) (b ``1)))) == fst (fillb0 i)
-}
        -- want path in B(fst newp 1) from coe 0->1 (b ``0) to b ``1
        --    \ x → coe (x->1) b(x)

        -- suffices to give path in B(p ``1)
        --   coe_A[newp] 0 -> 1 (b ``0)   to  b ``1

        -- transport B {!!}
        --   (fst ((relCom-relCoe B comB) (fst newp) z `1
        --        (transport B {!!} (b {!!}))))


  relCov-over-discrete : ∀ {l1 l2}
                         {A : Set l1}
                         {B : A → Set l2}
                         (discA : hasHCom𝟚 A)
                         (discB : (x : A) → hasHCom𝟚01 (B x))
                         (comB  : relCom B)
                         → relCov1 B
  relCov-over-discrete {B = B} hcom𝟚A hcom𝟚B comB p α t b = transport B (snd (snd (newp))) (fst use) ,
                                                            (λ pα → move-transport-right! B (snd (snd (newp))) (fst (snd use) pα
                                                                    ∘ ! (ap (λ f → f pα) (snd (snd pathO)))
                                                                    ∘ ! (transport-→-post' α B (! (snd (snd (hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p)))) (t ``1) pα))) where
    newp = hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p

    pathO : _
    pathO = hasHCom𝟚-discrete-PathO hcom𝟚A (\ z → α → B z) (λ x → hasHCom𝟚-Π' (λ _ → hcom𝟚B x)) (com→ B comB) p t

    use = comB (\ x → fst newp x) `0 `1
          α
          (fst pathO)
          (hasHCom𝟚-discrete-induction0 hcom𝟚A B p (fst b) ,
             (λ pα → ap (λ x → transport B (! (fst (snd (hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p)))) x) (snd b pα)
                     ∘ transport-→-post' α B (! (fst (snd (hasHCom𝟚-DiscreteFn-𝟚→ hcom𝟚A p)))) (t ``0) pα
                     ∘ ap (λ f → f pα) (fst (snd pathO))))
{-    
  relCov-over-discrete0 : ∀ {l1 l2}
                         {A : Set l1}
                         {B : A → Set l2}
                         (discA : hasHCom𝟚0 A)
                         (discB : (x : A) → hasHCom𝟚0 (B x))
                         (comB  : relCom B)
                         → relCov B
  relCov-over-discrete0 {B = B} hcom𝟚A hcom𝟚B comB p α t b = {!!}
 -} 
  hasHCom𝟚-Σ-discrete-covariant : ∀ {l1 l2}
    {A : Set l1}
    {B : A → Set l2}
    (hcom𝟚A : hasHCom𝟚 A)
    (covB : relCov1 B)
    → hasHCom𝟚01 (Σ B)
  hasHCom𝟚-Σ-discrete-covariant {B = B} hcom𝟚A dcomB α u v = (fst (a'-fill ``1) , fst b') , (λ u → pair= (fst (snd (a'-fill ``1)) u) (snd b' u)) where
    a'-fill : (z : 𝟚) → _
    a'-fill z = hcom𝟚A ``0 z α (\ z pα → fst (u z pα)) (fst (fst v) , ( \ pα → ap fst (snd v pα) ))
    b' = dcomB (\ z → fst (a'-fill z))
                α
               (\ z pα → transport B (fst (snd (a'-fill z)) pα) (snd (u z pα)))
               (transport B (snd (snd (a'-fill ``0)) id) (snd (fst v)) , (λ pα → ap (λ x → transport B (snd (snd (a'-fill ``0)) id) x) (apd snd (snd v pα))
               ∘ ! (ap (λ f → transport B (snd (snd (a'-fill ``0)) id) (f (snd (u ``0 pα)))) (transport-ap-assoc' B fst (snd v pα)))
               ∘ ap (λ f → f (snd (u ``0 pα))) (transport-∘ B (snd (snd (a'-fill ``0)) id) (ap fst (snd v pα)))
               ∘ ap (λ eq → transport B eq (snd (u ``0 pα))) (uip {p = fst (snd (a'-fill ``0)) pα} {snd (snd (a'-fill ``0)) id ∘ ap fst (snd v pα)})))
    
  hasHCom𝟚-Σ-discrete-covariant0 : ∀ {l1 l2}
    {A : Set l1}
    {B : A → Set l2}
    (hcom𝟚A : hasHCom𝟚0 A)
    (covB : relCov B)
    → hasHCom𝟚0 (Σ B)
  hasHCom𝟚-Σ-discrete-covariant0 {B = B} hcom𝟚A dcomB r α u v = (fst (a'-fill r) , fst b')
                                                , (λ u → pair= (fst (snd (a'-fill r)) u) (fst (snd b') u))
                                                , (λ {id → pair= (snd (snd (a'-fill r)) id) (snd (snd b') id)}) where
    a'-fill : (z : 𝟚) → _
    a'-fill z = hcom𝟚A z α (\ z pα → fst (u z pα)) (fst (fst v) , ( \ pα → ap fst (snd v pα) ))
    b' = dcomB (\ z → fst (a'-fill z)) r
                α
               (\ z pα → transport B (fst (snd (a'-fill z)) pα) (snd (u z pα)))
               (transport B (snd (snd (a'-fill ``0)) id) (snd (fst v)) , (λ pα → ap (λ x → transport B (snd (snd (a'-fill ``0)) id) x) (apd snd (snd v pα))
               ∘ ! (ap (λ f → transport B (snd (snd (a'-fill ``0)) id) (f (snd (u ``0 pα)))) (transport-ap-assoc' B fst (snd v pα)))
               ∘ ap (λ f → f (snd (u ``0 pα))) (transport-∘ B (snd (snd (a'-fill ``0)) id) (ap fst (snd v pα)))
               ∘ ap (λ eq → transport B eq (snd (u ``0 pα))) (uip {p = fst (snd (a'-fill ``0)) pα} {snd (snd (a'-fill ``0)) id ∘ ap fst (snd v pα)})))

  hasHCom𝟚-Σ : ∀ {l1 l2}
    {A : Set l1}
    {B : A → Set l2}
    (discA : hasHCom𝟚 A)
    (discB : (x : A) → hasHCom𝟚01 (B x))
    (comB  : relCom B)
    → hasHCom𝟚01 (Σ B)
  hasHCom𝟚-Σ {B = B} hcom𝟚A hcom𝟚B comB =
    hasHCom𝟚-Σ-discrete-covariant hcom𝟚A (relCov-over-discrete hcom𝟚A hcom𝟚B comB)

{-
  hasHCom𝟚-Σ0 : ∀ {l1 l2}
    {A : Set l1}
    {B : A → Set l2}
    (discA : hasHCom𝟚0 A)
    (discB : (x : A) → hasHCom𝟚0 (B x))
    (comB  : relCom B)
    → hasHCom𝟚0 (Σ B)
  hasHCom𝟚-Σ0 {B = B} hcom𝟚A hcom𝟚B comB =
    hasHCom𝟚-Σ-discrete-covariant0 hcom𝟚A (relCov-over-discrete0 hcom𝟚A hcom𝟚B comB)
-}
{-
  hasHCom𝟚-Σ : ∀ {l1 l2}
    {A : Set l1}
    {B : A → Set l2}
    (discA : hasHCom𝟚 A)
    (discB : (x : A) → hasHCom𝟚 (B x))
    (comB  : relCom B)
    →
    hasHCom𝟚 (Σ B)
  hasHCom𝟚-Σ {A = A} {B} discA discB comB r r' α t b = (fst (p1 r') , fst p2)
                                                     , (λ u → pair= (fst (snd (p1 r')) u) (fst (snd p2) u))
                                                     , (λ u → pair= (snd (snd (p1 r')) u ∘ fst-transport-Σ' u (fst b))
                                                                    ((snd (snd p2) u) ∘ p2eq u)) where

    p1' : ∀ i → _
    p1' i = discA r (i ⊔ r) α (λ j u → fst (t j u)) (fst (fst b) , (λ u → ap fst (snd b u)))

    p1'' : ∀ i j → _
    p1'' i j = discA r (i ⊔ j) α (λ j u → fst (t j u)) (fst (fst b) , (λ u → ap fst (snd b u)))

    p1 : ∀ i → _
    p1 i = discA r i α (λ j u → fst (t j u)) (fst (fst b) , (λ u → ap fst (snd b u)))

    thom1 : Hom A (fst (fst b)) (fst (p1' ``1))
    thom1 = (λ i → (fst (p1' i))) , ! (snd (snd (p1' ``0)) id) , id

    thom2 : ∀ j → Hom A (fst (p1 j)) (fst (p1' ``1))
    thom2 j = (λ i → (fst (p1'' i j))) , id  , id

    bhom : ∀ j → Hom A (fst (fst b)) (fst (p1 j))
    bhom j = ∘Hom' discA (!Hom discA (thom2 j)) thom1

    bpath : ∀ j → Path A (fst (fst b)) (fst (p1 j))
    bpath j = hasHCom𝟚-to-DiscreteFn A discA _ _ (bhom j)


    p1hom : ∀ i j → Hom A (fst (p1 i)) (fst (p1 j))
    p1hom i j = ∘Hom' discA (bhom j) (!Hom discA (bhom i))

    p1path : ∀ i j → Path A (fst (p1 i)) (fst (p1 j))
    p1path i j = hasHCom𝟚-to-DiscreteFn A discA _ _ (p1hom i j)


    t2 : ∀ u i → _
    t2 u i = comB (fst (tpath u i)) `0 `1 ⊥ (λ _ → abort) (transport B (!(fst (snd (tpath u i)))) (snd (t i u)) , (λ x → abort x))

    p1' : ∀ i → _
    p1' i = discA ``0 ``1 (α ∨ (i == ``0)) (λ j → ∨-elim _ (λ u → fst (t ((i ⊓ j) ⊔ r)  u))
                                                  (λ _ → fst (fst b))
                                                  (λ u i=0 → (ap fst ((snd b) u) ∘ ap (λ z → fst (t ((z ⊓ j) ⊔ r) u)) i=0 ∘ ap (λ f → f (fst (t ((i ⊓ j) ⊔ r) u))) (transport-constant trunc))))
                                  (fst (fst b) , ∨-elim _ (λ u → ap fst ((snd b) u)) (λ _ → id) (λ _ _ → uip))

    b2 : _
    b2 = comB (fst bpath) `0 `1 α (λ i u → {! !}) (transport B (!(fst (snd bpath))) (snd (fst b)) , (λ u → {!!}))

    tB : ∀ i u → B (fst (p1 r'))
    tB i u = transport B (fst (snd (p1 r')) u) (snd (t r' u))

    tB' : ∀ i u → B (fst (p1 i))
    tB' i u = transport B (fst (snd (p1 i)) u) (snd (t i u)) 

    bB' : B (fst (fst b)) [ α ↦ (λ u → transport (λ z → B (fst z)) (snd b u) (snd (t r u))) ]
    bB' = snd (fst b) , λ u → apd snd (snd b u)

    bB1 : ∀ i j → _
    bB1 i j = comB (fst (bpath j)) `0 i ⊥ (λ _ → abort) (transport B (! (fst (snd (bpath j)))) (snd (fst b)) , (λ x → abort x))

    tbB1' : α → (z : 𝟚) → (B (fst (p1hom r r') z))
    tbB1' u z = {!B (fst (p1hom r r') z)!}

    bB1' : _
    bB1' = comB (fst (p1path r r')) `0 `1 α {!!} {!!}

    bB''' : ∀ i → B (fst (p1 i)) [ α ↦ tB' i ]
    bB''' i = {!!}

    bB : B (fst (p1 r')) [ α ↦ tB r ]
    bB = {!!} , {!!} -- (transport B (snd (snd bpath)) (fst b2) , (λ u → {!fst (snd b2) u!})) -- (transport B (snd (snd bpath)) (fst b2) , λ u → {!!})
    
    p2 : _ 
    p2 = discB (fst (p1 r')) r r' α tB bB


    p2eq : ∀ u → transport (λ v → B v) (snd (snd (p1 r')) u ∘ fst-transport-Σ' u (fst b)) (snd (transport (λ _ → Σ B) u (fst b))) == transport (λ _ → B (fst (p1 r'))) u (fst bB)
    p2eq id = {!!} -- transport B (snd (snd (p1 r)) id) (snd (fst b)) == fst bB
-}
{-
  hasHCom𝟚-Σ : ∀ {l1 l2}
    {A : Set l1}
    {B : A → Set l2}
    (discA : hasHCom𝟚 A)
    (discB : (x : A) → hasHCom𝟚 (B x))
    (covB  : relCov B)
    →
    hasHCom𝟚 (Σ B)
  hasHCom𝟚-Σ {A = A} {B} discA discB covB r r' α t b = (fst (filla r') , {!!}) 
                                                     , (λ u → pair= (fst (snd (filla r')) u) {!!})
                                                     , (λ u → pair= (snd (snd (filla r')) u ∘ fst-transport-Σ' u (fst b)) {!!}) where

    filla : ∀ i → _
    filla i = discA r i α (λ j u → fst (t j u)) (fst (fst b) , (λ u → ap fst (snd b u)))

    p1' : ∀ i → _
    p1' i = discA r (i ⊔ r) α (λ j u → fst (t j u)) (fst (fst b) , (λ u → ap fst (snd b u)))

    p1'' : ∀ i j → _
    p1'' i j = discA r (i ⊔ j) α (λ j u → fst (t j u)) (fst (fst b) , (λ u → ap fst (snd b u)))

    thom1 : Hom A (fst (fst b)) (fst (p1' ``1))
    thom1 = (λ i → (fst (p1' i))) , ! (snd (snd (p1' ``0)) id) , id

    thom2 : ∀ j → Hom A (fst (filla j)) (fst (p1' ``1))
    thom2 j = (λ i → (fst (p1'' i j))) , id  , id

    bhom : ∀ j → Hom A (fst (fst b)) (fst (filla j))
    bhom j = ∘Hom' discA (!Hom discA (thom2 j)) thom1

    p1hom : ∀ i j → Hom A (fst (filla i)) (fst (filla j))
    p1hom i j = ∘Hom' discA (bhom j) (!Hom discA (bhom i))

    b0 : ∀ i → _
    b0 i = discB (fst (filla r)) r i α (λ z u → transport B (fst (snd (filla r)) u) (snd (t r u)))
                 (transport B ((snd (snd (filla r)) id)) (snd (fst b))
                  , (λ u → {!snd b u!}))

    comb : _
    comb = covB (λ i → fst (filla i)) r' α (λ z u → transport B (fst (snd (filla z)) u) (snd (t z u))) ({!b0!} , {!!})

-}
{-
  comΣ' : ∀ {l1 l2 l3 : Level} {Γ : Set l1} {A : Γ → Set l2} {B : Σ A → Set l3} → relCom A → relCom B → relCom (\ γ → Σ \ (x : A γ) → B (γ , x))
  comΣ' {B = B} comA comB γ r r' α t b = ((fst (filla b r')) , fst (comb b)) , 
                                        (\ pα → pair= (fst (snd (filla b r')) pα) (fst (snd (comb b)) pα)) ,
                                        ((\ {id → pair= (snd (snd (filla b r')) id) (snd (snd (comb b)) id)})) where

    filla : (b : _) (z : I) → _
    filla b z = (comA γ r z α (\ pα z → fst (t pα z)) (fst (fst b) , (\ pα → ap fst (snd b pα))))

    comb : (b : _) → _
    comb b = 
      (comB (\ z → γ z , (fst (filla b z)))
            r r' 
            α (\ z pα →  transport (B o \ h → (γ z , h)) (fst (snd (filla b z)) pα) (snd (t z pα)) )
            (transport (B o \ h → (γ r , h)) ((snd (snd (filla b r)) id)) (snd (fst b)) , 
             (\ pα → ap (transport (B o (λ h → γ r , h)) (snd (snd (filla b r)) id)) (apd snd (snd b pα) ∘ ! (ap= (transport-ap-assoc' (λ z → B (γ r , z)) fst (snd b pα))) ) ∘ ap= (transport-∘ (B o (λ h → γ r , h)) (snd (snd (filla b r)) id) (ap fst (snd b pα))) ∘ ap {M = (fst (snd (filla b r)) pα)} {N = (snd (snd (filla b r)) id ∘ ap fst (snd b pα))} (\ h → transport (B o (λ h → γ r , h)) h (snd (t r pα))) uip)))
-}
{-

  hasHCom𝟚-Id : ∀{l}
    {A : Set l}
    (x y : A)
    →
    hasHCom𝟚 (x == y)
  hasHCom𝟚-Id {A = A} x y r r' α t b = fst b , (λ _ → uip) , (λ _ → uip)
  
  hasHCom𝟚-Id0 : ∀{l}
    {A : Set l}
    (x y : A)
    →
    hasHCom𝟚0 (x == y)
  hasHCom𝟚-Id0 {A = A} x y r α t b = fst b , (λ _ → uip) , (λ _ → uip)

{-
  relCom-Id : ∀{l1 l2}
    {Γ : Set l1}
    {A : Set l2}
    (comA : hasHCom A)
    (x y : Γ → A)
    → relCom (λ z → x z == y z)
  relCom-Id comA x y p r r' α {{c}} t b = {!fst b!} , (λ _ → uip) , (λ _ → uip) where

    x' : ∀ z → _
    x' z = comA r r' α {{c}} {!x (p r)!} {!!}
-}
{-
  hasHCom𝟚-Path : ∀ {l}
    {A : Set l}
    (discA : hasHCom𝟚 A)
    (x y : A)
    →
    hasHCom𝟚01 (Path A x y)
  hasHCom𝟚-Path {A = A} discA x y = hasHCom𝟚-Σ (hasHCom𝟚-Π (λ _ → discA)) (λ p → hasHCom𝟚-×' (hasHCom𝟚-Id _ _) (hasHCom𝟚-Id _ _)) {!!}
-}
{-
  relCom-Eq-lem :  ∀ {l}
    {A : Set l}
    (discA : hasHCom𝟚0 A)
    (x : A)
    (r : I)
    →
    relCom (λ z → z r == x)
  relCom-Eq-lem discA x r p i i' α = {!!}
-}
  hasHCom𝟚-Path0 : ∀ {l}
    {A : Set l}
    (discA : hasHCom𝟚0 A)
    (x y : A)
    →
    hasHCom𝟚0 (Path A x y)
  hasHCom𝟚-Path0 {A = A} discA x y = hasHCom𝟚-Σ0 (hasHCom𝟚-Π0 (λ _ → discA)) (λ p → hasHCom𝟚-×0 (hasHCom𝟚-Id0 _ _) (hasHCom𝟚-Id0 _ _)) {!!}
{-
  hasHCom𝟚-HFiber : ∀ {l1 l2}
    {A : Set l1}
    (discA : hasHCom𝟚 A)
    {B : Set l2}
    (discB : hasHCom𝟚 B)
    (comB : hasHCom B)
    (f : A → B)
    (b : B)
    →
    hasHCom𝟚01 (HFiber f b)
  hasHCom𝟚-HFiber discA discB comB f b = hasHCom𝟚-Σ discA (λ x → hasHCom𝟚-Path discB _ _) (comPath-endpoints (λ z → f z) (λ _ → b) comB)
-}
  hasHCom𝟚-HFiber0 : ∀ {l1 l2}
    {A : Set l1}
    (discA : hasHCom𝟚0 A)
    {B : Set l2}
    (discB : hasHCom𝟚0 B)
    (comB : hasHCom B)
    (f : A → B)
    (b : B)
    →
    hasHCom𝟚0 (HFiber f b)
  hasHCom𝟚-HFiber0 discA discB comB f b = hasHCom𝟚-Σ0 discA (λ x → hasHCom𝟚-Path0 discB _ _) (comPath-endpoints (λ z → f z) (λ _ → b) comB)
{-
  hasHCom𝟚-isEquiv : ∀ {l1 l2}
    {A : Set l1}
    (discA : hasHCom𝟚 A)
    {B : Set l2}
    (discB : hasHCom𝟚 B)
    (f : A → B)
    →
    hasHCom𝟚01 (isEquiv A B f)
  hasHCom𝟚-isEquiv discA discB f = hasHCom𝟚-Π' (λ b → hasHCom𝟚-Σ {!!} (λ f → hasHCom𝟚-Π' (λ f' → hasHCom𝟚-Path {!!} _ _)) {!!})
-}
  hasHCom𝟚-isEquiv0 : ∀ {l1 l2}
    {A : Set l1}
    (discA : hasHCom𝟚0 A)
    {B : Set l2}
    (discB : hasHCom𝟚0 B)
    (comB  : hasHCom B)
    (f : A → B)
    →
    hasHCom𝟚0 (isEquiv A B f)
  hasHCom𝟚-isEquiv0 discA discB comB f = hasHCom𝟚-Π0 (λ b → hasHCom𝟚-Σ0 (discHFib f b) (λ _ → hasHCom𝟚-Π0 (λ _ → hasHCom𝟚-Path0 (discHFib f b) _ _)) {!!}) where

    discHFib : ∀ f b → _
    discHFib f b = hasHCom𝟚-HFiber0 discA discB comB f b

-}



HERE-0 -}
