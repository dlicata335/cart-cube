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
import ComInternal
open import Contractible

module directed.Covariant where

  module CovFill where

    -- composite and filler definition

    hasCov : ∀ {l} → (𝟚 → Set l) → Set (lmax (lsuc lzero) l)
    hasCov A = (r' : 𝟚) (α : Set) {{_ : Cofib α}} 
           → (t : (z : 𝟚) → α → A z) 
           → (b : A ``0 [ α ↦ t ``0 ]) 
           → A r' [ α ↦ t r' , (``0 == r') ↦ (\ p → transport A p (fst b)) ]

    relCov : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set (lmax (lsuc lzero) (lmax l1 l2))
    relCov {_}{_} {Γ} A = (p : 𝟚 → Γ) → hasCov (A o p)

    hasDCoe : ∀ {l} → (𝟚 → Set l) → Set (l)
    hasDCoe A = (r' : 𝟚) (b : A ``0) → A r' [ (``0 == r') ↦ (\ p → transport A p b) ]

    relDCoe : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set ((lmax l1 l2))
    relDCoe {Γ = Γ} A = (p : 𝟚 → Γ) → hasDCoe (A o p)

    relCov-relDCoe : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
                  -> relCov A → relDCoe A
    relCov-relDCoe A dcomA p r' b = fst c , snd (snd c) where
      c = dcomA p r' ⊥ (\ _ → abort) (b , \ x → abort x)

    relCov-transport : {l1 l2 : Level} {A : Set l1} (B : A → Set l2) → relCov B
                   → {a0 a1 : A} → (p : Hom A a0 a1) → B a0 → B a1
    relCov-transport B dcomB p b = 
                   transport B (snd (snd p))
                     (fst (dcomB (\ z → fst p z)
                          ``1
                           ⊥ (\ _ x → abort x)
                           (transport B (! (fst (snd p))) b , (\ x → abort x))))

    relCov-internal : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set (lmax l1 l2)
    relCov-internal {Γ = Γ} A =
        (p : 𝟚 → Γ) (a : A (p ``0))
      → Contractible (Σ \ (b : A (p ``1)) → HomO (\ x → A (p x)) a b)
  
    to-internal : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
              → relCov A
              → relCov-internal A 
    to-internal A dcomA p a = ((fst (dcoe ``1)) ,
                             (\ x → fst (dcoe x)) ,
                             ! (snd (snd (dcoe ``0)) id) ,
                             id) ,
                            (\ bp →
                               -- path
                               (\ y → fst (unique bp ``1 y) ,
                                -- hom
                                (\ x → fst (unique bp x y)) ,
                                -- hom boundary
                                ! (snd (snd (unique bp ``0 y)) id) , id) ,
                               -- path boundary
                               pair= ( ! (fst (snd (unique bp ``1 `0)) (inl id)))
                                     (HomO= _ _ (\ x → ! (fst (snd (unique bp x `0)) (inl id)) ∘ ap (\ f → f x) (fst-transport-HomO-nd {A = A o p} (! (fst (snd (unique bp ``1 `0)) (inl id))) _))) ,
                               pair= (snd (snd (snd bp)) ∘ ( ! (fst (snd (unique bp ``1 `1)) (inr id))))
                                     (HomO= _ _ (\ x → ! (fst (snd (unique bp x `1)) (inr id)) ∘ ap (\ f → f x) (fst-transport-HomO-nd (snd (snd (snd bp)) ∘ ! (fst (snd (unique bp ``1 `1)) (inr id))) _)) )) where
      dcoe : (x : 𝟚) → _
      dcoe x = dcomA p x ⊥ (\ _ → abort) (a , \ x → abort x)
      
      unique : (bp : Σ (HomO (λ x → A (p x)) a)) (x : 𝟚) (y : I) → _
      unique (b , ab) x y = dcomA p x
                                  ((y == `0) ∨ (y == `1))
                                  (\ z → case (\ y=0 → fst (dcoe z))
                                              (\ y=1 → fst ab z)
                                              (λ p₁ q → abort (iabort (q ∘ ! p₁))))
                                  ((a , ∨-elim _
                                               (\ _ → ! (snd (snd (dcoe ``0)) id))
                                               (\ _ → fst (snd ab))
                                               (λ p₁ q → abort (iabort (q ∘ ! p₁))) )) 

    from-internal : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
                  → relCom A
                  → relCov-internal A
                  → relCov A
    from-internal A comA icovA p r' α t b =
      fst (snd (fst compose)) r' ,
      (\ pα → ap= (ap fst (apd snd (snd compose pα))) {r'} ∘ ! (ap (\ f → f r') (fst-transport-HomO-nd {A = A o p} (snd compose pα) ((λ x → t x pα) , snd b pα , id))) ) ,
      (\ {id → ! (fst (snd (snd (fst compose))))}) where
  
        -- FIXME: should be a nicer way to do this? it would be more internal not to plug in p ``1 first
        -- also, only need transport in right endpoint, so shouldn't need A to be Kan, just hcom, like in suspensions
        hcomT : hasHCom (Σ \ (b' : A (p ``1)) → HomO (A o p) (fst b) b')
        hcomT = relCom-hasHCom {Γ = Unit{lzero}} (\ _ → (Σ \ (b' : A (p ``1)) → HomO (A o p) (fst b) b'))
                               (ComInternal.comΣ {A = \ _ → A (p ``1)}
                                     {B = \ x → HomO (A o p) (fst b) (snd x)}
                                     (comPre (\ _ → (p ``1)) A comA)
                                     (comHom {A = \ (q : (Unit × A (p ``1)) × 𝟚) → A (p (snd q))} (\ _ → fst b) (\ x → snd x) ( (comPre (\ q → p (snd q)) A comA) )))
                               <> 
        
        compose = contr-extend-partial hcomT (icovA p (fst b)) α (\ pα → t ``1 pα , (\ x → t x pα) , snd b pα , id)

    erase-false-cov : ∀ {l : Level} {A : 𝟚 → Set l}
                → (dcomA : hasCov A)
                → (r' : 𝟚) (α β : Set) {{cα : Cofib α}} {{cβ : Cofib β}}
                → (t : (z : 𝟚) → α → A z)
                → (s : (z : 𝟚) → β → A z)
                → (ts : (z : 𝟚) (pα : α) (pβ : β) → t z pα == s z pβ )
                → (b : (A ``0) [ (α ∨ β) ↦ case (t ``0) (s ``0) (ts ``0) ])
                → (β → ⊥{lzero})
                → Path _
                  (fst (dcomA r' (α ∨ β) (\ z → case (t z) (s z) (ts z)) b))
                  (fst (dcomA r' α t (fst b , (\ pα → snd b (inl pα) ))))
    erase-false-cov dcomA r' α β t s ts b notβ =
                (\ z → fst (use z)) ,
                ! (fst (snd (use `0)) (inl id)) ,
                ! (fst (snd (use `1)) (inr id)) where
      use : (z : I) → _
      use z = dcomA r' ((z == `0) ∨ (z == `1))
                   (\ z → case01 (\ _ → (fst (dcomA z (α ∨ β) (\ z → case (t z) (s z) (ts z)) b)))
                                 ((\ _ → (fst (dcomA z α t (fst b , (\ pα → snd b (inl pα) )))))) )
                   (fst b , ∨-elim01 _ (\ _ → ! (snd (snd (dcomA ``0 (α ∨ β) (\ z → case (t z) (s z) (ts z)) b)) id))
                                       (\ _ → ! (snd (snd (dcomA ``0 α t (fst b , (\ pα → snd b (inl pα) )))) id)))

    -- FIXME rephrase as contr-extend-partial
    adjust-hasCov : {l : Level} (A : 𝟚 → Set l)
          → (com : hasCov A)
          → (β : Set) {{_ : Cofib β}}
          → (dcomApartial : β → hasCov A)
          → hasCov A [ β ↦ dcomApartial ]
    adjust-hasCov A dcomA β {{cβ}} comApartial = (λ r' α {{cα}} t b → fst (use r' α t b) ,
                                                               (\ pα → fst (snd (use r' α t b)) (inl pα)) ,
                                                               (\ r=r' → (snd (snd (use r' α t b))) r=r' ) ) ,
                                        (\ pβ → λ= \ r' → λ= \ α → λ=inf \ cα → λ= \ t → λ= \ b →
                                          pair= (fst (snd (use r' α {{cα}} t b)) (inr pβ)) (pair= (λ= \ _ → uip) ((λ= \ _ → uip)))) where
      use : ∀ r' α {{cα : Cofib α}} t b → _
      use r' α {{cα}} t b = dcomA r'
                                   (α ∨ β)
                                   (\ z → case (\ pα → t z pα)
                                               (\ pβ → fst (comApartial pβ z α t b))
                                               (\ pα pβ → fst (snd (comApartial pβ z α t b)) pα) )
                                   (fst b ,
                                    ∨-elim _
                                           (\ pα → snd b pα)
                                           (\ pβ → ! (snd (snd (comApartial pβ ``0 α t b)) id))
                                           (\ _ _ → uip))

    adjust-hasCov-not : {l : Level} (A : 𝟚 → Set l)
          → (com : hasCov A)
          → (β : Set) {{_ : Cofib β}}
          → (covApartial : β → hasCov A)
          → (β → ⊥{lzero})
          → ∀ r' α {{cα : Cofib α}} t b
          → Path _ (fst (fst (adjust-hasCov A com β covApartial) r' α t b)) (fst (com r' α t b)) 
    adjust-hasCov-not A com β comApartial notβ r' α t b =
      erase-false-cov com r' α β t (\ z pβ → fst (comApartial pβ z α t b)) (\ z pα pβ → fst (snd (comApartial pβ z α t b)) pα) (fst b , ∨-elim _ (\ pα → snd b pα) (\ pβ → ! (snd (snd (comApartial pβ ``0 α t b)) id)) (\ _ _ → uip)) notβ 



  open CovFill public

  module CovComp where

    -- we have connections, so composite suffices
    
    hasCov1 : ∀ {l} → (𝟚 → Set l) → Set (lmax (lsuc lzero) l)
    hasCov1 A = (α : Set) {{_ : Cofib α}} 
             → (t : (z : 𝟚) → α → A z) 
             → (b : A ``0 [ α ↦ t ``0 ]) 
             → A ``1 [ α ↦ t ``1 ]
    
    relCov1 : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set (lmax (lsuc lzero) (lmax l1 l2))
    relCov1 {_}{_} {Γ} A = (p : 𝟚 → Γ) → hasCov1 (A o p)
    
    relCov1-relCov : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
                   → relCov1 A
                   → CovFill.relCov A
    relCov1-relCov A dcom1 p r' α t b =
      (fst d) ,
      (\ pα →  snd d (inl pα) ) ,
      (\ r'=0 →  snd d (inr (! r'=0)) ∘ ap (\ h → transport (A o p) h (fst b)) (uip {p = r'=0} {q = (ap (_⊓_ ``1) (! (! r'=0)))}) ) where
        d = dcom1
                (\ z → p (z ⊓ r'))
                (α ∨ (r' == ``0))
                (\ z → case (\ pα → t (z ⊓ r') pα)
                            (\ r'=0 → transport (A o p) (ap (\ h → z ⊓ h) (! r'=0)) (fst b))
                            (\ pα r'=0 → ((ap= (transport-ap-assoc' (A o p) (\ h → z ⊓ h) (! r'=0))) ∘ ap (transport (λ z₁ → A (p (z ⊓ z₁))) (! r'=0)) (snd b pα)) ∘ (! (apd (\ h → (t (z ⊓ h) pα)) (! r'=0))) ))
                ((fst b) ,
                 (∨-elim _
                         (\ pα → snd b pα)
                         (\ r'=0 →  ap (\ h → transport (A o p) h (fst b)) (uip {p = (ap (_⊓_ ``0) (! r'=0))} {q = id}) )
                         (\ _ _ → uip)))

    hasDCoe1 : ∀ {l} → (𝟚 → Set l) → Set (l)
    hasDCoe1 A = A ``0 → A ``1 

    relDCoe1 : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set ((lmax l1 l2))
    relDCoe1 {Γ = Γ} A = (p : 𝟚 → Γ) → hasDCoe1 (A o p)

    relCov1-relDCoe1 : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
                  -> relCov1 A → relDCoe1 A
    relCov1-relDCoe1 A dcomA p b = fst c where
      c = dcomA p ⊥ (\ _ → abort) (b , \ x → abort x)

    hasHomog : ∀ {l} → (A : 𝟚 → Set l) → hasCov1 A → Set (lmax (lsuc lzero) l)
    hasHomog A dcomA =
             (r : 𝟚) (α : Set) {{_ : Cofib α}} 
           → (t : (z : 𝟚) → α → A z) 
           → (b : A r [ α ↦ t r ]) 
           → A ``1 [ α ↦ t ``1 , r == ``0 ↦ (\ r=0 → fst (dcomA α t (transport (\ x → A x [ α ↦ t x ]) r=0 b))) ]

    hasHomog' : ∀ {l} → (A : 𝟚 → Set l) → hasCov A → Set (lmax (lsuc lzero) l)
    hasHomog' A dcomA =
             (r : 𝟚) (α : Set) {{_ : Cofib α}} 
           → (t : (z : 𝟚) → α → A z) 
           → (b : A r [ α ↦ t r ]) 
           → A ``1 [ α ↦ t ``1 , r == ``0 ↦ (\ r=0 → fst (dcomA ``1 α t (transport (\ x → A x [ α ↦ t x ]) r=0 b))) , r == ``1 ↦ (λ r=1 → transport (λ x → A x) r=1 (fst b)) ]

    relHomog : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
             → relCov1 A
             -> Set (lmax (lsuc lzero) (lmax l1 l2))
    relHomog {_}{_} {Γ} A dcomA = (p : 𝟚 → Γ) → hasHomog (A o p) (dcomA p)
    
    relHomog' : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
             → relCov A
             -> Set (lmax (lsuc lzero) (lmax l1 l2))
    relHomog' {_}{_} {Γ} A dcomA = (p : 𝟚 → Γ) → hasHomog' (A o p) (dcomA p)

    relCov-relHomog : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
                    → (dcomA : relCov1 A)
                    → relHomog A dcomA
    relCov-relHomog A dcomA p r α t b =
      fst d , (\ pα → (snd d) pα) , (\ {id → id}) where
      d = dcomA (\ x → p (r ⊔ x))
                α
                (\ z pα → t ((r ⊔ z)) pα)
                (fst b , snd b)

    relCov-relHomog' : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
                    → (dcomA : relCov A)
                    → relHomog' A dcomA
    relCov-relHomog' A dcomA p r α t b =
      fst d , (\ pα → fst (snd d) (inl pα)) , (\ r=0 → fst (snd d) (inr (inl r=0)) ∘ ap= (! (transport-constant (! r=0))) ) , (\ r=1 → fst (snd d) (inr (inr r=1)) ∘ ! (ap= (transport-constant (! r=1)))) where 
      d = dcomA (\ x → p (r ⊔ x))
                ``1 (α ∨ ((r == ``0) ∨ (r == ``1)))
                (\ z → ∨-elim _ (λ pα → t ((r ⊔ z)) pα)
                                (cased01 (\ r=0 → transport (\ r → A (p (r ⊔ z))) (! r=0) (fst (dcomA p z α t (transport (λ x → (A o p) x [ α ↦ t x ]) r=0 b))))
                                         (\ r=1 → transport (\ r → A (p (r ⊔ z))) (! (r=1)) (transport (A o p) r=1 (fst b))))
                                         (\ pα → ∨-elimd01 _ (\ r=0 → (ap (transport (λ r₁ → A (p (r₁ ⊔ z))) (! r=0)) (fst (snd (dcomA p z α t (transport (λ x → (A o p) x [ α ↦ t x ]) r=0 b))) pα) ∘ ! (apd (\ x → t (x ⊔ z) pα) (! r=0)) ) ∘ ap= (transport-constant trunc))
                                                             (\ r=1 → ((ap (\ H → transport (λ r₁ → A (p (r₁ ⊔ z))) (! r=1) (transport (λ x → A (p x)) r=1 H)) (snd b pα)) ∘ ap (transport (λ z₁ → A (p (z₁ ⊔ z))) (! r=1)) (! (apd (\ z → t z pα) r=1)) ∘ ! (apd (\ r → t (r ⊔ z) pα) (! r=1))) ∘ ap= (transport-constant trunc)) )) 
                (fst b , ∨-elim _ (\ pα → snd b pα)
                                  (∨-elimd01 _
                                             (\r=0 → (ap= (transport-inv (A o p) r=0) ∘ ap (transport (λ r₁ → A (p r₁)) (! r=0)) (fst-transport-Σ' {C = 𝟚} {A = (\ x → (A o p) x)} {B = _} r=0 b)) ∘ ! (ap (transport (λ r₁ → A (p r₁)) (! r=0)) (snd (snd (dcomA p ``0 α t (transport (λ x → (A o p) x [ α ↦ t x ]) r=0 b))) id)))
                                             (\ r=1 → ap= (transport-inv (A o p) r=1)))
                                  (\ _ _ → uip))

    hasDCoeFrom : ∀ {l} → (A : 𝟚 → Set l) → hasDCoe1 A → Set (l)
    hasDCoeFrom A dcoeA =
                (r : 𝟚) (b : A r) 
              → A ``1 [ r == ``0 ↦ (\ r=0 → (dcoeA (transport A r=0 b))) ]

    relDCoeFrom : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> relDCoe1 A → Set ((lmax l1 l2))
    relDCoeFrom {Γ = Γ} A dcoeA = (p : 𝟚 → Γ) → hasDCoeFrom (A o p) (dcoeA p)

    relCov-relDCoeFrom : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
                       → (dcomA : relCov1 A)
                       → relDCoeFrom A (relCov1-relDCoe1 A dcomA)
    relCov-relDCoeFrom A dcomA p r b = fst h , (λ { id → snd (snd h) id }) where
      h = relCov-relHomog A dcomA p r ⊥ (\ _ → abort) (b , \ x → abort x)
           

  ∘Hom : ∀ {l} {A : Set l} {a b c : A} → relCov {l} (λ (_ : ⊤) → A) → Hom A b c → Hom A a b → Hom A a c
  ∘Hom {a = a} hA q p = (\ x → fst (c x)) , 
                ! (fst (snd (c ``0)) (inl id))  ,  snd (snd q) ∘ ! (fst (snd (c ``1)) (inr id))  where
    c : (x : 𝟚) → _
    c x = (hA (λ _ → <>) ``1 ((x == ``0) ∨ (x == ``1)) (\ z → case (\ x=0 → a) ((\ x=1 → fst q z)) (\ p q → abort (diabort (q ∘ ! p)))) (fst p x , ∨-elim _ ( (\ x=0 →  ap (fst p) (! (x=0)) ∘ ! (fst (snd p)) ) ) ( ((λ x=1 → ap (fst p) (! x=1) ∘ ! (snd (snd p)) ∘ fst (snd q))) ) (\ _ _ → uip))) 

  open CovComp public

  rcov-hprop : ∀ {l1 l2} {Γ : Set l1}(A : Γ → Set l2) → (x y : relCov A) → Path _ x y
  rcov-hprop {Γ = Γ} A cov1 cov2 = (λ x p i α {{c}} t b → (fst (f x p i α {{c}} t b) , (λ u → (fst (snd (f x p i α {{c}} t b)) (inl u))) , snd (snd (f x p i α {{c}} t b))))
                                   , (λ= λ p → λ= λ i → λ= λ α → λ=inf λ c → λ= λ t → λ= λ b → pair= (! (fst (snd (f `0 p i α {{c}} t b)) (inr (inl id)))) (pair= (λ= λ _ → uip) (λ= λ _ → uip)))
                                   , (λ= λ p → λ= λ i → λ= λ α → λ=inf λ c → λ= λ t → λ= λ b → pair= (! (fst (snd (f `1 p i α {{c}} t b)) (inr (inr id)))) (pair= (λ= λ _ → uip) (λ= λ _ → uip))) where

    f : (x : I)(p : 𝟚 → Γ)(i : 𝟚)(α : Set){{cα : Cofib α}}(t : (z : 𝟚) → α → A (p z)) (b : A (p ``0) [ α ↦ t ``0 ]) → _
    f x p i α {{c}} t b = cov1 p i (α ∨ ((x == `0) ∨ (x == `1)))
                           (λ j → case (t j)
                                       (case01 (λ _ → fst (cov1 p j α t b))
                                               (λ _ → fst (cov2 p j α t b)))
                                       (λ u → ∨-elim01 _
                                                       (λ _ → fst (snd (cov1 p j α t b)) u)
                                                       (λ _ → fst (snd (cov2 p j α t b)) u)))
                           (fst b , ∨-elim _ (snd b)
                                             (∨-elim01 _
                                                       (λ _ → ! (snd (snd (cov1 p ``0 α t b)) id))
                                                       (λ _ → ! (snd (snd (cov2 p ``0 α t b)) id)))
                                             (λ _ _ → uip))

  relCov= : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) 
              (r1 r2 : relCov A) → 
              ((p : 𝟚 → Γ) (i : 𝟚) (α : Set) {{_ : Cofib α}} (t : _) (b : _) → fst (r1 p i α t b) == fst (r2 p i α t b))
              → r1 == r2
  relCov= A r1 r2 eq = λ= λ p → λ= λ i → λ= λ α → λ=inf λ c → λ= λ t → λ= λ b → pair= (eq p i α {{c}} t b) (pair= (λ= λ _ → uip) (λ= λ _ → uip))

  relCov1= : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) 
               (r1 r2 : relCov1 A) → 
               ((p : 𝟚 → Γ) (α : Set) {{_ : Cofib α}} (t : _) (b : _) → fst (r1 p α t b) == fst (r2 p α t b))
               → r1 == r2
  relCov1= A r1 r2 eq = λ= λ p → λ= λ α → λ=inf λ c → λ= λ t → λ= λ b → pair= (eq p α {{c}} t b) (λ= λ _ → uip)


  dcom= : {l1 l2 : Level}
          {Γ : Set l1}
          (A : Γ → Set l2)
          (dcomA : relCov A)
          (p : 𝟚 → Γ)
          {i : 𝟚}
          {α : Set} {{_ : Cofib α}}
          {t t' : (z : 𝟚) → α → A (p z)}
          {b : A (p ``0) [ α ↦ t ``0 ]}
          {b' : A (p ``0) [ α ↦ t' ``0 ]}
          (teq : t == t')
          (beq : fst b == fst b')
          → (fst (dcomA p i α t b)) == (fst (dcomA p i α t' b'))
  dcom= A dcomA p {i = i} {α} {b = b} {b' = b'} id beq =
         ap (λ x → fst (dcomA p i α (fst x) (snd x)))
                       (pair= (λ= λ _ → λ= λ x → id)
                              (pair= (beq ∘ (fst-transport-Σ (λ= λ _ → λ= λ x → id) b)  ) 
                                     (λ= λ x → uip)))

  dcom1= : {l1 l2 : Level}
          {Γ : Set l1}
          {A : Γ → Set l2}
          {dcomA : relCov1 A}
          {p : 𝟚 → Γ}
          {α : Set} {{_ : Cofib α}}
          {t t' : (z : 𝟚) → α → A (p z)}
          {b : A (p ``0) [ α ↦ t ``0 ]}
          {b' : A (p ``0) [ α ↦ t' ``0 ]}
          (teq : t == t')
          (beq : fst b == fst b')
          → (fst (dcomA p α t b)) == (fst (dcomA p α t' b'))
  dcom1= {dcomA = dcomA} {p = p} {α} {b = b} {b' = b'} id beq =
         ap (λ x → fst (dcomA p α (fst x) (snd x)))
                       (pair= (λ= λ _ → λ= λ x → id)
                              (pair= (beq ∘ (fst-transport-Σ (λ= λ _ → λ= λ x → id) b)  ) 
                                     (λ= λ x → uip)))

  relCov⊥= : {l1 l2 : Level}
              {Γ : Set l1}
              (A : Γ → Set l2)
              (dcomA : relCov A)
              (p : 𝟚 → Γ)
              (i : 𝟚) (α : Set)
              {{_ : Cofib α}}
              (α⊥ : α → ⊥{lzero})
              (t t' : (z : 𝟚) → α → A (p z))
              (b : A (p ``0) [ α ↦ t ``0 ])
              (b' : A (p ``0) [ α ↦ t' ``0 ])
              (beq : fst b == fst b')
              → (fst (dcomA p i α t b)) == (fst (dcomA p i α t' b'))
  relCov⊥= A dcomA p i α α⊥ t t' b b' beq = ap (λ x → fst (dcomA p i α (fst x) (snd x)))
                                                (pair= (λ= λ _ → λ= λ x → abort (α⊥ x))
                                                       (pair= (beq ∘ fst-transport-Σ (λ= λ _ → λ= λ x → abort (α⊥ x)) b)
                                                              (λ= λ x → abort (α⊥ x))))
                                                              
{-
  -- FIXME: should work if A Segal to get dependent yoneda
  encode-decode-covariant :
        {l : Level} {A : Set l} (a : A) (Code : A → Set l) (dcomCode : relCov Code)
      → (codea : Code a)
      → (decode : (a' : A) → Code a' → Hom A a a')
      → ((a' : A) (codea' : Code a')
          -- FIXME define a lemma for tranpsport instance
          → Path _
                 (relCov-transport Code dcomCode (decode a' codea') codea)
                 codea')
      → Path (Hom A a a) (decode a codea) ((\ x → a) , id , id)
      → (a' : A) → QEquiv (Hom A a a') (Code a')
  encode-decode-covariant a Code dcomCode codea decode encode-after-decode decode-after-encode-base a' =
    (\ a → (relCov-transport Code dcomCode a codea)) ,
    (decode a') ,
    {!!} , -- dependent yoneda 
    encode-after-decode a'
-}

{-

  are these fibrant?

  com-relCov : ∀ {l1 l2} → relCom (\ (p : Σ \ (Γ : Set l1) → (Γ → Set l2)) → relCov (snd p))
  com-relCov ΓA r r' α t b =
    (λ q y β s u → {!!} , {!!}) , {!!}
-}


{-
  module Both where

    -- couldn't figure out how to get this from relCov1 in one step

    hasCov : ∀ {l} → (𝟚 → Set l) → Set (lmax (lsuc lzero) l)
    hasCov A = (r r' : 𝟚) (l : r ≤ r')
               (α : Set) {{_ : Cofib α}} 
             → (t : (z : 𝟚) → α → A z) 
             → (b : A r [ α ↦ t r ]) 
             → A r' [ α ↦ t r' ]

    relCov : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set (lmax (lsuc lzero) (lmax l1 l2))
    relCov {_}{_} {Γ} A = (p : 𝟚 → Γ) → hasCov (A o p)
-}
      


