{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; Level; _⊔_)

open import Lib
open import Kan
open import Interval
open import Cofibs
open import Prop

module Path where

  funext : ∀{l1 l2}{A : Set l1}{B : A → Set l2}{a0 a1 : (x : A) → B x} → ((x : A) → Path _ (a0 x) (a1 x)) → Path ((x : A) → B x) a0 a1
  funext p = (λ i x → fst (p x) i) , (λ= λ x → fst (snd (p x))) , (λ= λ x → snd (snd (p x)))

  PathO : {l : Level} (A : I → Set l) (a0 : A `0) (a1 : A `1) → Set l
  PathO A a0 a1 = Σ (\ (p : (x : I) → A x) → (p `0 == a0) × (p `1 == a1))

  PathO= : {l : Level} {A : I → Set l} {a0 : A `0} {a1 : A `1}
         → (p q : PathO A a0 a1) 
         → ((x : I) → fst p x == fst q x) → p == q
  PathO= p q h = pair= (λ= h) (pair= uip uip)

  ⇒fst : {l : Level} {A : I → I → Set l} {a0 : (y : I) → A y `0} {a1 : (y : I) → A y `1} {r r' : I} (eq : r == r')
         → (p : PathO (A r) (a0 r) (a1 r))
         → (x : I) → fst (⇒ { A = \ r → PathO (A r) (a0 r) (a1 r)} p eq) x == ⇒ (fst p x) eq
  ⇒fst id _ _ = id

  Contractible : {l : Level} (A : Set l) → Set l
  Contractible A = Σ \ (a : A) → (b : A) → Path A a b

  HFiber : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B) → Set (l1 ⊔ l2)
  HFiber f b = Σ \a → Path _ (f a) b

  =HFiber : {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} {b : B}
            {v1 v2 : HFiber f b}
          → (p : fst v1 == fst v2)
          → fst (snd v1) == (fst (snd v2))
          → v1 == v2
  =HFiber {v2 = v2} id id = ap (\ x → (fst v2 , fst (snd v2) , x)) (ap2 _,_ uip uip)

  HFiber' : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B) → Set (l1 ⊔ l2)
  HFiber' f b = Σ \a → Path _ b (f a)

  =HFiber' : {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} {b : B}
            {v1 v2 : HFiber' f b}
          → (p : fst v1 == fst v2)
          → fst (snd v1) == (fst (snd v2))
          → v1 == v2
  =HFiber' {v2 = v2} id id = ap (\ x → (fst v2 , fst (snd v2) , x)) (ap2 _,_ uip uip)

  scontr : ∀ {l} {A : Set l} → hasHCom A → (a : A) → Contractible (Σ \ b → Path A b a)
  scontr hcomA a = (a , ((\ _ → a) , id , id)) , ((λ s → (\ x → fst (square s x `0) , (\ y → fst (square s x y)) , id , ! (snd (snd (square s x `1)) id)) , 
                                                          =HFiber (! (fst (snd (square s `0 `0)) (inl id))) (λ= \ y → ! (fst (snd (square s `0 y)) (inl id))) , 
                                                          =HFiber (fst (snd (snd s)) ∘ (! (fst (snd (square s `1 `0)) (inr id)))) 
                                                                  (λ= \ y → ! (fst (snd (square s `1 y)) (inr id))))) where
    square : (s : _) (x : _) (y : _) → _
    square s x y = hcomA `1 y ((x == `0) ∨ (x == `1))
                               (\ y → case (\ _ → a) 
                                           (\ _ → fst (snd s) y) 
                                           (\ p q → abort (iabort (q ∘ ! p)) )) 
                               (a  , ∨-elim _ (\ x=0 → snd (snd (snd s)) ∘ ! (snd (snd (snd s)))) 
                                              (\ x=1 → snd (snd (snd s))) (\ _ _ → uip))

  eq-to-Path : ∀{l}{A : Set l} → (a a' : A) → a == a' → Path A a a'
  eq-to-Path a a' eq = (λ _ → a) , id , eq

  _∘=_  : ∀ {l} {A : Set l} {M N P : A} → Path A N P → M == N → Path A M P
  p ∘= q = (\ x → fst p x) , (! q ∘ fst (snd p)) , (snd (snd p))

  _=∘_  : ∀ {l} {A : Set l} {M N P : A} → N == P → Path A M N → Path A M P
  p =∘ q = (\ x → fst q x) , (fst (snd q)), (p ∘ snd (snd q))

  ∘Path : ∀ {l} {A : Set l} {a b c : A} → hasHCom A → Path A b c → Path A a b → Path A a c
  ∘Path {a = a} hA q p = (\ x → fst (c x)) , 
                ! (fst (snd (c `0)) (inl id))  ,  snd (snd q) ∘ ! (fst (snd (c `1)) (inr id))  where
    c : (x : I) → _
    c x = (hA `0 `1 ((x == `0) ∨ (x == `1)) (\ z → case (\ x=0 → a) ((\ x=1 → fst q z)) (\ p q → abort (iabort (q ∘ ! p)))) (fst p x , ∨-elim _ ( (\ x=0 →  ap (fst p) (! (x=0)) ∘ ! (fst (snd p)) ) ) ( ((λ x=1 → ap (fst p) (! x=1) ∘ ! (snd (snd p)) ∘ fst (snd q))) ) (\ _ _ → uip))) 

  !Path : ∀ {l} {A : Set l} {a b : A} → hasHCom A → Path A a b → Path A b a
  !Path {a = a}{b} hA p = 
                (\ x → fst (c x)) , 
                 snd (snd p) ∘ ! (fst (snd (c `0)) (inl id))  , id ∘ ! (fst (snd (c `1)) (inr id))  where
    c : (x : I) → _
    c x = (hA `0 `1 ((x == `0) ∨ (x == `1)) 
              (\ z → case (\ x=0 → fst p z) ((\ x=1 → a)) (\ p q → abort (iabort (q ∘ ! p))))
              (a , ∨-elim _ ( (\ x=0 → ((fst (snd p))) )) ( ((λ x=1 → id)) ) (\ _ _ → uip))) 

  ⇒fst-nd : {l : Level} {A : Set l} {a0 : (y : I) → A} {a1 : (y : I) → A} {r r' : I} (eq : r == r')
         → (p : Path A (a0 r) (a1 r))
         → (x : I) → fst (⇒ { A = \ r → Path A (a0 r) (a1 r)} p eq) x == (fst p x)
  ⇒fst-nd id _ _ = id

  fst-transport-Path : {l : Level} {A : I → Set l} {a0 : (γ : I) → A γ} {a1 : (γ : I) → A γ}
                     {r r' : I} (p : r == r')
                     → (q : Path (A r) (a0 r) (a1 r))
                     → fst (transport (\ x → Path (A x) (a0 x) (a1 x)) p q) == (\ x → transport A p (fst q x))
  fst-transport-Path id q = id

  fst-transport-Path' : {l l2 : Level} {Γ : Set l2} {A : Γ → Set l} {a0 : (γ : Γ) → A γ} {a1 : (γ : Γ) → A γ}
                     {r r' : Γ} (p : r == r')
                     → (q : Path (A r) (a0 r) (a1 r))
                     → fst (transport (\ x → Path (A x) (a0 x) (a1 x)) p q) == (\ x → transport A p (fst q x))
  fst-transport-Path' id q = id

  fst-transport-Path-left : {l l2 : Level} {Γ : Set l2} {A : Set l} {a0 : (γ : Γ) → A} {a1 : A}
                     {r r' : Γ} (p : r == r')
                     → (q : Path (A) (a0 r) (a1))
                     → fst (transport (\ x → Path (A) (a0 x) (a1)) p q) == (\ x → (fst q x))
  fst-transport-Path-left id q = id

  fst-transport-Path-right : {l1 l2 : Level} {A : Set l1} {B : Set l2} {a0 : A} {a1 : B → A}
                     {b b' : B} (p : b == b')
                     → (q : Path A a0 (a1 b))
                     → fst (transport (\ x → Path A a0 (a1 x)) p q) == (fst q)
  fst-transport-Path-right id q = id

  fst-transport-HFiber-base : {l l' : Level} {A : Set l} {B : Set l'} (f : A → B)
                            {b0 b1 : B} (p : b0 == b1)
                            → (q : HFiber f b0)
                            → fst (transport (HFiber f) p q) == (fst q)
  fst-transport-HFiber-base f id q = id

  fst-snd-transport-HFiber-base : {l l' : Level} {A : Set l} {B : Set l'} (f : A → B)
                            {b0 b1 : B} (p : b0 == b1)
                            → (q : HFiber f b0)
                            → fst (snd (transport (HFiber f) p q)) == (fst (snd q))
  fst-snd-transport-HFiber-base f id q = id

  fst-transport-HFiber'-base : {l l' : Level} {A : Set l} {B : Set l'} (f : A → B)
                            {b0 b1 : B} (p : b0 == b1)
                            → (q : HFiber' f b0)
                            → fst (transport (HFiber' f) p q) == (fst q)
  fst-transport-HFiber'-base f id q = id

  fst-snd-transport-HFiber'-base : {l l' : Level} {A : Set l} {B : Set l'} (f : A → B)
                            {b0 b1 : B} (p : b0 == b1)
                            → (q : HFiber' f b0)
                            → fst (snd (transport (HFiber' f) p q)) == (fst (snd q))
  fst-snd-transport-HFiber'-base f id q = id

  -- seem to need this for HITs, assumes only an hcom structure
  comPath-endpoints : ∀ {l1 l : Level} {Γ : Set l1} {A : Set l} (a0 : (γ : Γ) → A) (a1 : (γ : Γ) → A) 
          → hasHCom A 
          → relCom (\γ → Path A (a0 γ) (a1 γ))
  comPath-endpoints {A = A} a0 a1 hcomA p r r' α t b = 
          ((\ x → fst (hcoma x)) , (! (fst (snd (hcoma `0)) (inr (inl id))) ) , (! (fst (snd (hcoma `1)) (inr (inr id))) )) , 
          (\ pα → PathO= _ _ (\ x → fst (snd (hcoma x)) (inl pα) )) , 
          (\ r=r' → PathO= _ _ (\ x → snd (snd (hcoma x)) r=r' ∘ ⇒fst-nd {A = A} {a0 = λ z → a0 (p z)} {a1 = λ z → a1 (p z)} r=r' (fst b) x)) where 
    hcoma : (x : I) → _
    hcoma x = hcomA r r' 
                  (α ∨ ((x == `0) ∨ (x == `1))) 
                  (\ z → case (\ pα → fst (t z pα) x ) 
                         (case (\ x=0 → transport _ (! x=0) (a0 (p z)) )
                               (\ x=1 → transport _ (! x=1) (a1 (p z)) ) 
                               (\ p q → abort (iabort (q ∘ ! p))))
                         (\ pα → ∨-elim _ (\ x=0 → ap (transport _ (! x=0)) (fst (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=0))) ((\ x=1 → ap (transport _ (! x=1)) (snd (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=1)))) (\ _ _ → uip))) 
                  (fst (fst b) x , 
                   ∨-elim _ (\ pα → ap (\ h → fst h x) (snd b pα)) (∨-elim _ (\ x=0 → ! (apd! (fst (fst b)) x=0) ∘ ap (transport _ (! x=0)) (! (fst (snd (fst b))))) ((\ x=1 → ! (apd! (fst (fst b)) x=1) ∘ ap (transport _ (! x=1)) (! (snd (snd (fst b)))))) ((\ _ _ → uip))) (((\ _ _ → uip))))


  -- would be in Kan.agda, but easiest to state with a Path type, so it's here
  erase-false : ∀ {l : Level} {A : I → Set l}
              → (comA : hasCom A)
              → (r r' : I) (α β : Set) {{cα : Cofib α}} {{cβ : Cofib β}}
              → (t : (z : I) → α → A z)
              → (s : (z : I) → β → A z)
              → (ts : (z : I) (pα : α) (pβ : β) → t z pα == s z pβ )
              → (b : (A r) [ (α ∨ β) ↦ case (t r) (s r) (ts r) ])
              → (β → ⊥{lzero})
              → Path _
                (fst (comA r r' (α ∨ β) (\ z → case (t z) (s z) (ts z)) b))
                (fst (comA r r' α t (fst b , (\ pα → snd b (inl pα) ))))
  erase-false comA r r' α β t s ts b notβ =
              (\ z → fst (use z)) ,
              ! (fst (snd (use `0)) (inl id)) ,
              ! (fst (snd (use `1)) (inr id)) where
    use : (z : I) → _
    use z = comA r r' ((z == `0) ∨ (z == `1))
                 (\ z → case01 (\ _ → (fst (comA r z (α ∨ β) (\ z → case (t z) (s z) (ts z)) b)))
                               ((\ _ → (fst (comA r z α t (fst b , (\ pα → snd b (inl pα) )))))) )
                 (fst b , ∨-elim01 _ (\ _ → ! (snd (snd (comA r r (α ∨ β) (\ z → case (t z) (s z) (ts z)) b)) id))
                                     (\ _ → ! (snd (snd (comA r r α t (fst b , (\ pα → snd b (inl pα) )))) id)))


  -- FIXME: if you rephrase hasCom as Contractible (SFiber (apply r)),
  -- this is just contr-extend-partial
  abstract
    adjust-hasCom : {l : Level} (A : I → Set l)
          → (com : hasCom A)
          → (β : Set) {{_ : Cofib β}}
          → (comApartial : β → hasCom A)
          → hasCom A [ β ↦ comApartial ]
    adjust-hasCom A comA β {{cβ}} comApartial = (λ r r' α {{cα}} t b → fst (use r r' α t b) ,
                                                               (\ pα → fst (snd (use r r' α t b)) (inl pα)) ,
                                                               (\ r=r' → (snd (snd (use r r' α t b))) r=r' ) ) ,
                                        (\ pβ → λ= \ r → λ= \ r' → λ= \ α → λ=inf \ cα → λ= \ t → λ= \ b →
                                          pair= (fst (snd (use r r' α {{cα}} t b)) (inr pβ)) (pair= (λ= \ _ → uip) ((λ= \ _ → uip)))) where
      use : ∀ r r' α {{cα : Cofib α}} t b → _
      use r r' α {{cα}} t b = comA r r'
                                   (α ∨ β)
                                   (\ z → case (\ pα → t z pα)
                                               (\ pβ → fst (comApartial pβ r z α t b))
                                               (\ pα pβ → fst (snd (comApartial pβ r z α t b)) pα) )
                                   (fst b ,
                                    ∨-elim _
                                           (\ pα → snd b pα)
                                           (\ pβ → ! (snd (snd (comApartial pβ r r α t b)) id))
                                           (\ _ _ → uip))

    adjust-hasCom-not : {l : Level} (A : I → Set l)
          → (com : hasCom A)
          → (β : Set) {{_ : Cofib β}}
          → (comApartial : β → hasCom A)
          → (β → ⊥{lzero})
          → ∀ r r' α {{cα : Cofib α}} t b
          → Path _ (fst (fst (adjust-hasCom A com β comApartial) r r' α t b)) (fst (com r r' α t b)) 
    adjust-hasCom-not A com β comApartial notβ r r' α t b =
      erase-false com r r' α β t (\ z pβ → fst (comApartial pβ r z α t b)) (\ z pα pβ → fst (snd (comApartial pβ r z α t b)) pα) (fst b , ∨-elim _ (\ pα → snd b pα) (\ pβ → ! (snd (snd (comApartial pβ r r α t b)) id)) (\ _ _ → uip)) notβ 
   
