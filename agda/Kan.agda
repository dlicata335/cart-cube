{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Prop

-- the lsuc lzero is avoidable, because we could define codes for cofibs in universe 0

module Kan where 

  ⇐ : ∀ {l} {I : Set} (A : I → Set l) {r r' : I} → A r' → (p : r == r') → A r
  ⇐ A x id = x

  ⇒ : ∀ {l} {I : Set} {A : I → Set l} {r r' : I} → A r → (p : r == r') → A r'
  ⇒ {A = A} x p = transport A p x

  k : ∀ {l1 l2} {A : Set l1} {B : Set l2} → A → B → A
  k x y = x

  hasCom : ∀ {l} → (I → Set l) → Set (lsuc lzero ⊔ l)
  hasCom A = (r r' : I) (α : Set) {{_ : Cofib α}} 
           → (t : (z : I) → α → A z) 
           → (b : A r [ α ↦ t r ]) 
           → A r' [ α ↦ t r' , (r == r') ↦ ⇒ (fst b) ]

  relCom : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2)
         -> Set (lsuc lzero ⊔ l1 ⊔ l2)
  relCom {Γ = Γ} A = (p : I → Γ) → hasCom (A o p)

  comPre : ∀ {l1 l2 l3} {Δ : Set l1} {Γ : Set l2} (θ : Δ → Γ) (A : Γ → Set l3) → relCom A → relCom (A o θ)
  comPre θ _ comA p = comA (θ o p)

  comPre-o : {l1 l2 l3 l4 : Level} {Γ1 : Set l1} {Γ2 : Set l2} {Γ3 : Set l3} {A : Γ3 → Set l4}
           → (g : Γ2 → Γ3) (f : Γ1 → Γ2) (comA : relCom A)
           → comPre f (A o g) (comPre g A comA) == comPre (g o f) A comA
  comPre-o g f comA = id

  Fib : ∀ (l : Level) {l1 : Level} (Γ : Set l1) → Set (l1 ⊔ lsuc l)
  Fib l Γ = Σ \ (A : Γ → Set l) → relCom A

  reindex-Fib : {l : Level} {l1 l2 : Level} {Γ : Set l1} {Δ : Set l2} (θ : Γ → Δ) → Fib l Δ → Fib l Γ
  reindex-Fib θ (A , comA) = (A o θ) , comPre θ A comA

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

  wcoePre : ∀ {l1 l2 l3} {Δ : Set l1} {Γ : Set l2} (θ : Δ → Γ) (A : Γ → Set l3) → relWCoe A → relWCoe (A o θ)
  wcoePre θ _ r p = r (θ o p)

  decompose-hasCom : ∀ {l2} (A : I → Set l2) → 
                  ((x : I) → hasHCom (A x)) 
                  → hasCoe A 
                  → hasCom A
  decompose-hasCom A hcomA coeA r r' α t b = 
    (fst h) , 
    (\ u → fst (snd h) u ∘ snd (coeA r' r' (t r' u)) id) , 
           (\ { id → snd (snd h) id ∘ snd (coeA r r (fst b)) id}) where
    h = ((hcomA r') r r' 
                α (\ z u → fst (coeA z r' (t z u)))
                (fst (coeA r r' (fst b)) , (\ u → ap (\ h → fst (coeA r r' h)) (snd b u))))

  decompose-com : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → 
                  ((x : Γ) → hasHCom (A x)) 
                  → relCoe A 
                  → relCom A
  decompose-com A hcomA coeA p = decompose-hasCom (A o p) (\ x → hcomA (p x)) (coeA p) 

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

  hasCoe-from-hasWCoe : ∀ {l2} (A : I → Set l2) 
                 → ((x : I) → hasHCom (A x))
                 → hasWCoe A
                 → hasCoe A
  hasCoe-from-hasWCoe A hcomA wcoeA s s' b = fst fix , (\ s=s' → fst (snd fix) s=s' ∘ ! (snd (snd (snd (wcoeA s s') s=s' b)))) where
    fix = hcomA (s') `0 `1 (s == s') 
                             (\ x → \ s=s' → fst ((snd (wcoeA s s') s=s') b) x)
                             ((fst (wcoeA s s') b) , 
                              (\ s=s' →  fst (snd ((snd (wcoeA s s') s=s' b))) ))

  coe-from-wcoe : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) 
                 → ((x : Γ) → hasHCom (A x))
                 → relWCoe A
                 → relCoe A
  coe-from-wcoe A hcomA wcoeA p = hasCoe-from-hasWCoe (A o p) (\ x → hcomA (p x)) (wcoeA p) 

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

  -- useful macro
  hasCom-hasCom2 : ∀ {l} → (A : I → Set l) → hasCom A
               → (r r' : I) (α : Set) {{_ : Cofib α}} 
               → (t : (z : I) → α → A z)
               → (α' : Set)  {{_ : Cofib α'}} 
               → (t' : (z : I) → α' → A z)
               → (compat : (x : I) (p : α) (q : α') → t x p == t' x q)
               → (b : A r [ (α ∨ α') ↦ case (t r) (t' r) (compat r) ]) 
               → A r' [ (α ∨ α') ↦ case (t r') (t' r') (compat r') , (r == r') ↦ ⇒ (fst b) ]
  hasCom-hasCom2 A hcomA r r' α t α' t' compat b =
    hcomA r r' (α ∨ α') (\ x → case (t x) (t' x) (compat x)) b 


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

  -- only used for contradicting fiberwise internal universe
  hcom= : {l : Level} {A : Set l} {a b : A} → hasHCom (a == b)
  hcom= r r' α t b = fst b , (\ _ → uip) , (\ _ → uip)

  fiberwise-com-=I : {l : Level} → (x : I) → relCom {Γ = Unit{lzero}} (\ _ → `0 == x)
  fiberwise-com-=I x = relCom-constant _ (hcom=)

  ContractibleFill : {l : Level} (A : Set l) → Set (ℓ₁ ⊔ l)
  ContractibleFill A = (α : Set) {{cα : Cofib α}} → (t : α → A) → A [ α ↦ t ]

  -- ----------------------------------------------------------------------
  -- equality lemmas

  relCom= : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) 
           (r1 r2 : relCom A) → 
           ((p : I → Γ) (r r' : I) (α : Set) {{_ : Cofib α}} (t : _) (b : _) → fst (r1 p r r' α t b) == fst (r2 p r r' α t b))
           → r1 == r2
  relCom= A r1 r2 h = λ= \ p → λ= \ s → λ= \ s' → λ= \ α → λ=inf \ cα → λ= \ t → λ= \ b → pair= (h p s s' α {{ cα }} t b) (pair= (λ= \ _ → uip) ((λ= \ _ → uip)))   

  com=tb : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) 
           (comA : relCom A) →
           (p : I → Γ)
           (r r' : I) (α : Set) {{_ : Cofib α}}
           (t t' : _) → t == t' → 
           (b : _) (b' : _) → fst b == fst b'
           → fst (comA p r r' α t b) == fst (comA p r r' α t' b')
  com=tb A comA p r r' α t t' id b b' id = ap (\ h → fst (comA p r r' α t (fst b' , h))) (λ= \ _ → uip) 

  -- hasCom=hαtb : ∀ {l2} (A : I → Set l2) (A' : I → Set l2) → 
  --          (comA : hasCom A) (comA' : hasCom A')
  --          (r r' : I) (α α' : Set) {{_ : Cofib α}} {{_ : Cofib α'}}
  --          (t : _) (t' : _) → t =h t' → 
  --          (b : _) (b' : _) → fst b == fst b'
  --          → fst (comA r r' α t b) == fst (comA p r r' α t' b')
  -- hasCom=hαtb A comA p r r' α t t' id b b' id = ap (\ h → fst (comA p r r' α t (fst b' , h))) (λ= \ _ → uip) 

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
                            

  -- doesn't work
  -- hasCom-pre : ∀ {l} → (f : I → I) (A : I → Set l) → hasCom A → hasCom (A o f)
  -- hasCom-pre f A comA r r' α t b = fst (comA (f r) (f r') α {!!} {!!}) , {!!}

  -- ----------------------------------------------------------------------
  -- some facts about interderivabilities

  hcom-fill-rescaled : ∀ {l2} (A : Set l2) 
                      → (hcomA : hasHCom A) 
                      → ∀ r r' α {{ cα : Cofib α }} t b →
                        (Path A (fst (hcomA r r' α t b)) (fst b))
                        -- and it's constant on r=r'
                         [ -- ENH shouldn't there be something to say about it on α?
                           -- α ↦ (λ pα → (\ x → fst b) , fst (snd (hcomA r r' α t b)) pα ∘ {!! (snd b pα)!} , {!!}) ,
                           r == r' ↦ (\ r=r' → (\ _ → fst b) , snd (snd (hcomA r r' α t b)) r=r'  , id ) ]
  hcom-fill-rescaled A hcomA r r' α t b =
    ((\ x → fst (rescale x) ) , (! (fst (snd (rescale `0)) (inl id)) , ! (fst (snd (rescale `1)) (inr id)))) ,
    (\ r=r' → pair= (λ= \ x → snd (snd (rescale x)) r=r' ) (pair= uip uip)) where
    fill = \ x → (hcomA r x α t b)
    rescale = \x → hcomA r r' ((x == `0) ∨ (x == `1))
                               (\ z → case (\ _ → fst (fill z))
                                           (\ _ → fst b)
                                           (\ p q → abort (iabort (q ∘ ! p))))
                               (fst b , ∨-elim _ (\ _ → ! (snd (snd (fill r)) id)) (\ _ → id) (\ _ _ → uip))

  hcom-regular : ∀ {l2} (A : Set l2) 
               → (hcomA : hasHCom A) 
               → ∀ r r' α {{ cα : Cofib α }} (t : α → A) b →
                        (Path A (fst (hcomA r r' α (\ _ pα → t pα) b)) (fst b))
  hcom-regular A hcomA r r' α {{ cα }} t b =
     (\ x → fst (h x)) , ! (fst (snd (h `0)) (inr (inl id))) ,  ! (fst (snd (h `1)) (inr (inr id))) where
    h = \ x → hcomA r r' (α ∨ ((x == `0) ∨ (x == `1)))
                         (\ z → case t
                                     (case ((\ _ → fst (hcomA r z α (\ _ pα → t pα) b)))
                                           (\ _ → fst b)
                                           (\ p q → abort (iabort (q ∘ ! p))))
                                     (\ pα →  ∨-elim _
                                                     ( \ _ → fst (snd (hcomA r z α (\ _ pα → t pα) b)) pα )
                                                     (\ _ → snd b pα)
                                                     (\ p q → abort (iabort (q ∘ ! p)))))
                         (fst b , ∨-elim _
                                         (snd b)
                                         (∨-elim _ (\ _ → ! ((snd (snd (hcomA r r α (λ _ → t) b))) id))
                                                   (\ _ → id)
                                                   (\ _ _ → uip))
                                         (\ _ _ → uip))

  coe-regular-path : {l1 l : Level} {Γ : Set l1} (A : Set l) (comA : relCom {_}{_}{Γ} (\ _ → A))
                (p : I → Γ) (r r' : I) (b : A)
              → Path A (fst (relCom-relCoe (\ _ → A) comA p r r' b)) b 
  coe-regular-path A comA p r r' b = (\ x → fst (rescale x)) , ! (fst (snd (rescale `0)) (inl id)) ,  ! (fst (snd (rescale `1)) (inr id)) where
    rescale = \ x → comA p r r' ((x == `0) ∨ (x == `1))
                                (\ z → case (\ _ → fst (relCom-relCoe (\ _ → A) comA p r z b)) (\ _ → b) (\ p q → abort (iabort (q ∘ ! p))))
                                (b , ∨-elim _ (\ _ → ! ((snd (relCom-relCoe (λ _ → A) comA p r r b)) id)) (\ _ → id) (\ p q → abort (iabort (q ∘ ! p))) )

  decompose-com-stable : ∀ {l1 l2 l3} {Γ : Set l1} (A : Γ → Set l2) {Δ : Set l3} → 
                       (hcomA : (x : Γ) → hasHCom (A x))
                       (coeA : relCoe A)
                       (θ : Δ → Γ)
                       → comPre θ A (decompose-com A hcomA coeA) == decompose-com (A o θ) (\ z → hcomA (θ z)) (coePre θ A coeA)
  decompose-com-stable A hcomA coeA θ = relCom= (A o θ) _ _ (λ p r r' α t b → id) 

  -- is this version more useful?
  -- coe-in-decomposeCom : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → 
  --                         (hcomA : (x : Γ) → hasHCom (A x))
  --                         (coeA : relCoe A)
  --                         → Path (relCoe A) (relCom-relCoe A (decompose-com A hcomA coeA)) coeA
  -- coe-in-decomposeCom A hcomA coeA = 
  --                     (λ x p r r' b →
  --                         fst (fst (use-hcom-empty-system x p r r' b)) x ,
  --                                  (\ {id → ap (\ f → f x) (ap fst (snd (use-hcom-empty-system x p r r' b) id)) ∘ snd (coeA p r r b) id})) ,
  --                         (λ= \ p → λ= \ r → λ= \ r' → λ= \ b → pair= ( fst (snd (fst (use-hcom-empty-system `0 p r r' b)))) (λ= \ _ → uip)) ,
  --                         (λ= \ p → λ= \ r → λ= \ r' → λ= \ b → pair= ( snd (snd (fst (use-hcom-empty-system `1 p r r' b)))) (λ= \ _ → uip)) where
  --    -- arguments are read off from decompose-com
  --    use-hcom-empty-system = \ x p r r' b → (hcom-fill-rescaled (A (p r')) (hcomA (p r')) r r' ⊥ (λ z u → fst (coeA p z r' (abort u))) (fst (coeA p r r' b) , (λ u → ap (λ h → fst (coeA p r r' h)) (abort u))))

  coe-in-decomposeCom-pointwise : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → 
                          (hcomA : (x : Γ) → hasHCom (A x))
                          (coeA : relCoe A)
                          → ∀ p r r' b →
                              Path (A (p r'))
                                   (fst (relCom-relCoe A (decompose-com A hcomA coeA) p r r' b))
                                   (fst (coeA p r r' b))
  coe-in-decomposeCom-pointwise A hcomA coeA p r r' b =
    fst (hcom-fill-rescaled (A (p r')) (hcomA (p r')) r r' ⊥ (λ z u → fst (coeA p z r' (abort u))) (fst (coeA p r r' b) , (λ u → ap (λ h → fst (coeA p r r' h)) (abort u)))) 

  coe-from-wcoe-0-1 : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) 
                 → (hcomA : (x : Γ) → hasHCom (A x))
                 → (wcoeA : relWCoe A)
                 → ∀ p (b : A (p `0))
                 → Path (A (p `1))
                        (fst (coe-from-wcoe A hcomA wcoeA p `0 `1 b))
                        (fst (wcoeA p `0 `1) b) 
  coe-from-wcoe-0-1 A hcomA wcoeA p b = fst (hcom-fill-rescaled (A (p `1)) (hcomA (p `1)) `0 `1 (`0 == `1) (λ x s=s' → fst (snd (wcoeA p `0 `1) s=s' b) x) (fst (wcoeA p `0 `1) b , (λ s=s' → fst (snd (snd (wcoeA p `0 `1) s=s' b)))) )

  -- if the second part is already compatible with the first fill,
  -- then we get a path
  hasCom-hasCom2-path : ∀ {l} → (A : I → Set l) → (comA : hasCom A)
               → (r r' : I) (α : Set) {{_ : Cofib α}} 
               → (t : (z : I) → α → A z) 
               → (α' : Set) {{_ : Cofib α'}}  (t' : (z : I) → α' → A z)
               → (compat : (x : I) (p : α) (q : α') → t x p == t' x q)
               → (b : A r [ (α ∨ α') ↦ case (t r) (t' r) (compat r) ])
               → (compat' : (x : I) → (pα' : α') → fst (comA r x α t (fst b , (\ pα → snd b (inl pα)))) == t' x pα')
               → Path (A r')
                      (fst (hasCom-hasCom2 A comA r r' α t α' t' compat b))
                      (fst (comA r r' α t (fst b , (\ pα → snd b (inl pα)))))
  hasCom-hasCom2-path A comA r r' α t α' t' compat b compat' =
        (\ y → fst (c y)) , ! (fst (snd (c `0)) (inr (inl id))) , ! (fst (snd (c `1)) (inr (inr id)))  where
    c = \ y → comA r r' ((α ∨ α') ∨ ((y == `0) ∨ (y == `1)))
                   (\ x → case
                             (case (t x) (t' x) (compat x))
                             (case (\ _ → (fst (hasCom-hasCom2 A comA r x α t α' t' compat b)))
                                   (\ _ → (fst (comA r x α t (fst b , (\ pα → snd b (inl pα))))))
                                   (\ p q → abort (iabort (q ∘ ! p))))
                             (∨-elim _
                                     (\ pα → ∨-elim _ (\ _ → fst (snd (hasCom-hasCom2 A comA r x α t α' t' compat b)) (inl pα) )
                                                      (\ _ → fst (snd (comA r x α t (fst b , (λ pα₁ → snd b (inl pα₁))))) pα)
                                                      (\ _ _ → uip))
                                     (\ pα' → ∨-elim _ 
                                                     (\ _ → fst (snd (hasCom-hasCom2 A comA r x α t α' t' compat b)) (inr pα'))
                                                     (\ _ → ! (compat' x pα') )
                                                     (\ _ _ → uip) )
                                     (\ _ _ → (λ= \ _ → uip))))
                   (fst b , ∨-elim _
                            (∨-elim _
                                    (λ pα → snd b (inl pα))
                                    ((λ pα' → snd b (inr pα')))
                                    (\ _ _ → uip))
                            (∨-elim _
                                    (\ _ → ! (snd (snd  (hasCom-hasCom2 A comA r r α t α' t' compat b)) id))
                                    (\ _ → ! (snd (snd (comA r r α t (fst b , (λ pα → snd b (inl pα))))) id))
                                    (\ _ _ → uip))
                            (\ _ _ → uip))
