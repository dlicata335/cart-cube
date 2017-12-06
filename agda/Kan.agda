{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Prop

-- the lsuc lzero is avoidable, because we could define codes for cofibs in universe 0

module Kan where 

  ⇐ : ∀ {l} (A : I → Set l) {r r' : I} → A r' → (p : r == r') → A r
  ⇐ A x id = x

  ⇒ : ∀ {l} {A : I → Set l} {r r' : I} → A r → (p : r == r') → A r'
  ⇒ {A = A} x p = transport A p x

  k : ∀ {l1 l2} {A : Set l1} {B : Set l2} → A → B → A
  k x y = x

  hasCom : ∀ {l} → (I → Set l) → Set (lsuc lzero ⊔ l)
  hasCom A = (r r' : I) (α : Set) {{_ : Cofib α}} 
           → (t : (z : I) → α → A z) 
           → (b : A r [ α ↦ t r ]) 
           → A r' [ α ↦ t r' , (r == r') ↦ ⇒ (fst b) ]

  relCom : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set (lsuc lzero ⊔ l1 ⊔ l2)
  relCom {_}{_} {Γ} A = (p : I → Γ) → hasCom (A o p)

  comPre : ∀ {l1 l2 l3} {Δ : Set l1} {Γ : Set l2} (θ : Δ → Γ) (A : Γ → Set l3) → relCom A → relCom (A o θ)
  comPre θ _ comA p = comA (θ o p)

  comPre-o : {l1 l2 l3 l4 : Level} {Γ1 : Set l1} {Γ2 : Set l2} {Γ3 : Set l3} {A : Γ3 → Set l4}
           → (g : Γ2 → Γ3) (f : Γ1 → Γ2) (comA : relCom A)
           → comPre f (A o g) (comPre g A comA) == comPre (g o f) A comA
  comPre-o g f comA = id

  Fib : ∀ {l} (Γ : Set l) → Set (lsuc l)
  Fib {l} Γ = Σ \ (A : Γ → Set l) → relCom A

  -- ----------------------------------------------------------------------
  -- specialized notions and interderivabilities

  hasHCom : {l : Level} → Set l → Set (lsuc lzero ⊔ l)
  hasHCom A = (r r' : I) (α : Set) {{_ : Cofib α}} 
            → (t : (z : I) → α → A) 
            → (b : A [ α ↦ t r ]) 
            → A [ α ↦ t r' , (r == r') ↦ k (fst b) ]

  hasCoe : {l : Level} → (I → Set l) → Set l
  hasCoe A = (r r' : I) 
           → (b : A r) 
           → A r' [ (r == r') ↦ ⇒ b ]

  hasWCoe : {l : Level} → (I → Set l) → Set l
  hasWCoe A = (r r' : I) →  
    Σ \ (f : A r → A r') → 
        ((e : r == r') → (b : A r) → Σ \ (p : (x : I) → A r') → (p `0 == f b) × (p `1 == ⇒ b e))

  relCoe : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set (l1 ⊔ l2)
  relCoe {_} {_} {Γ} A = (p : I → Γ) → hasCoe (A o p)

  coePre : ∀ {l1 l2 l3} {Δ : Set l1} {Γ : Set l2} (θ : Δ → Γ) (A : Γ → Set l3) → relCoe A → relCoe (A o θ)
  coePre θ _ r p = r (θ o p)

  relWCoe : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> Set (l1 ⊔ l2)
  relWCoe {_} {_} {Γ} A = (p : I → Γ) → hasWCoe (A o p)

  decompose-com : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → 
                  ((x : Γ) → hasHCom (A x)) 
                  → relCoe A 
                  → relCom A
  decompose-com A hcomA coeA p r r' α t b = 
    (fst h) , 
    (\ u → fst (snd h) u ∘ snd (coeA p r' r' (t r' u)) id) , 
           (\ { id → snd (snd h) id ∘ snd (coeA p r r (fst b)) id}) where
    h = ((hcomA (p r')) r r' 
                α (\ z u → fst (coeA p z r' (t z u)))
                (fst (coeA p r r' (fst b)) , (\ u → ap (\ h → fst (coeA p r r' h)) (snd b u))))

  -- decompose-com-stable : ∀ {l1 l2 l3} {Γ : Set l1} (A : Γ → Set l2) {Δ : Set l3} → 
  --                      (hcomA : (x : Γ) → hasHCom (A x))
  --                      (coeA : relCoe A)
  --                      (θ : Δ → Γ)
  --                      → comPre θ A (decompose-com A hcomA coeA) == decompose-com (A o θ) (\ z → hcomA (θ z)) (coePre θ A coeA)
  -- decompose-com-stable A hcomA coeA θ = relCom= (A o θ) _ _ (λ p r r' α t b → id) 

  relCom-hasHCom : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> 
                   relCom A 
                 → (x : Γ) → hasHCom (A x)
  relCom-hasHCom A rA x r r' α t b = fst user , fst (snd user) , (\ r=r' → snd (snd user) r=r' ∘ ! (ap= (transport-constant r=r'))) where
    user = rA (\ _ → x) r r' α t b

  relCom-relCoe : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) -> 
                   relCom A 
                 → relCoe A
  relCom-relCoe A comA p r r' b = fst com , (\ r=r' → snd (snd com) r=r') where
    com = comA p r r' ⊥ (\ x → abort) (b , \ x → abort x)

  coe-from-wcoe : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) 
                 → ((x : Γ) → hasHCom (A x))
                 → relWCoe A
                 → relCoe A
  coe-from-wcoe A hcomA wcoeA p s s' b = fst fix , (\ s=s' → fst (snd fix) s=s' ∘ ! (snd (snd (snd (wcoeA p s s') s=s' b)))) where
    fix = hcomA (p s') `0 `1 (s == s') 
                             (\ x → \ s=s' → fst ((snd (wcoeA p s s') s=s') b) x)
                             ((fst (wcoeA p s s') b) , 
                              (\ s=s' →  fst (snd ((snd (wcoeA p s s') s=s' b))) ))

  relCom-constant : ∀ {l1 l2} {Γ : Set l1} (A : Set l2) -> 
                  hasHCom A
                  → relCom {Γ = Γ} (\ _ → A )
  relCom-constant A hcomA p r r' α t b = 
    (fst (hcomA r r' α t b)) , ((\ pα → fst (snd (hcomA r r' α t b)) pα) , (\ {id → snd (snd (hcomA r r' α t b)) id}))

  hcomDec : ∀ {l : Level} {A : Set l} 
          → ((x y : A) → (x == y) ∨ ((x == y) → ⊥{l}))
          → hasHCom A
  hcomDec {A = A} dec r r' α t (b , p) = 
    b , (\ pα → p pα ∘ ! (constant (\ x → t x pα) r r')) , (λ { id → id }) where

    constant : ∀ (t : I → A) (r r' : I) → t r == t r'
    constant t r r' = 
      case (\ f → f r')
           (\ f → abort (f r id))
           (\ _ _ → uip)
           (iconnected (\ i → (t r == t i , (\ _ _ → uip))) (\ i →  dec (t r) (t i) ))

  Strictly-Preserves-HCom : {l1 l2 : Level} (A : Set l1) (C : A → Set l2)
                          → (hcomA : hasHCom A)
                          → (comC : relCom C)
                          → (f : (x : A) → C x) → Set _
  Strictly-Preserves-HCom A C hcomA comC f = 
    (r r' : I) (α : Set) {{_ : Cofib α}} 
           → (t : (z : I) → α → A) 
           → (b : A [ α ↦ t r ]) 
           → f (fst (hcomA r r' α t b)) == 
             (fst (comC (\ x → (fst (hcomA r x α t b))) r r' α 
                        (\z pα → transport C (fst (snd (hcomA r z α t b)) pα) (f (t z pα)))
                        (transport C (snd (snd (hcomA r r α t b)) id) (f (fst b)) , 
                         (\ pα → (! (apd f (snd (snd (hcomA r r α t b)) id))) 
                                   ∘ apd f (fst (snd (hcomA r r α t b)) pα)))))

  f-natural : ∀ {l} {A B : I → Set l} (f : (x : I) → A x → B x)
            → (coeA : hasCoe A)
            → (comB : relCom B)
            → (r r' : I) (a : A r) 
            → Path (B r') (f r' (fst (coeA r r' a))) (fst (relCom-relCoe B comB (\ x → x) r r' (f r a))) 
               [ r == r' ↦ (\ r=r' → (\ _ → ⇒ (f r a) r=r') , 
                                      (ap (f r') (snd (coeA r r' a) r=r')) ∘ ! (transport-natural-trans {B = A} {C = B} f r=r' a) , 
                                      snd (relCom-relCoe B comB (λ x → x) r r' (f r a)) r=r' ) ]
  f-natural f coeA comB r r' a = 
    (((\ x → fst (usecom x)) , 
     (! (fst (snd (usecom `0)) (inl id))) , 
     ! (fst (snd (usecom `1)) (inr id))) , 
     (\ r=r' → pair= (λ= \ x → snd (snd (usecom x)) r=r') (pair= uip uip))) where
   usecom : (x : I) → _
   usecom x = comB (\ z → z) r r'
                   ((x == `0) ∨ (x == `1)) 
                     (\ z → case (\ x=0 → f z (fst (coeA r z a)))
                                  (\ x=1 → fst (relCom-relCoe _ comB (\ x → x) r z (f r a)))
                                  (\ p q → abort (iabort (q ∘ ! p)))) 
                     (f r a , ∨-elim _ (\ x=0 →  ap (f r) (! ((snd (coeA r r a)) id)))
                                       (\ x=1 → ! (snd (relCom-relCoe _ comB (\ x → x) r r (f r a)) id)) (\ _ _ → uip))

  -- ----------------------------------------------------------------------
  -- equality lemmas

  relCom= : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) 
           (r1 r2 : relCom A) → 
           ((p : I → Γ) (r r' : I) (α : Set) {{_ : Cofib α}} (t : _) (b : _) → fst (r1 p r r' α t b) == fst (r2 p r r' α t b))
           → r1 == r2
  relCom= A r1 r2 h = λ= \ p → λ= \ s → λ= \ s' → λ= \ α → λ=inf \ cα → λ= \ t → λ= \ b → pair= (h p s s' α {{ cα }} t b) (pair= (λ= \ _ → uip) ((λ= \ _ → uip)))   

  hCom= : ∀ {l2} {A : Set l2}
           (hcom1 hcom2 : hasHCom A) → 
           ((r r' : I) (α : Set) {{_ : Cofib α}} (t : _) (b : _) → fst (hcom1 r r' α t b) == fst (hcom2 r r' α t b))
           → hcom1 == hcom2
  hCom= r1 r2 h = λ= \ s → λ= \ s' → λ= \ α → λ=inf \ cα → λ= \ t → λ= \ b → pair= (h s s' α {{ cα }} t b) (pair= (λ= \ _ → uip) ((λ= \ _ → uip)))   

  hCom=h : ∀ {l2} {A A' : Set l2}
           → (p : A == A')
           (hcom1 : hasHCom A) (hcom2 : hasHCom A') → 
           ((r r' : I) (α : Set) {{_ : Cofib α}} {t : _} {t' : _} → (t =h t') → {b : _} {b' : _} → b =h b' → fst (hcom1 r r' α t b) =h (fst (hcom2 r r' α t' b')))
           → hcom1 =h  hcom2
  hCom=h id hcom1 hcom2 h = hom-to-het (hCom= hcom1 hcom2 ((\ r r' α {{ cα }} t b → het-to-hom (h r r' α {{ cα }} {t} {t} hid {b} {b} hid)))) 
                            
