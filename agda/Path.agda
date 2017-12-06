{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; Level; _⊔_)

open import Lib
open import Kan
open import Interval
open import Cofibs
open import Pi
open import Sigma
open import Prop

module Path where

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

  comPath : ∀ {l1 l : Level} {Γ : Set l1} {A : Γ × I → Set l} (a0 : (γ : Γ) → A (γ , `0)) (a1 : (γ : Γ) → A (γ , `1)) 
          → relCom A 
          → relCom (\γ → PathO (\ z → A (γ , z)) (a0 γ) (a1 γ))
  comPath {A = A} a0 a1 comA p r r' α t b = 
          ((\ x → fst (coma x)) , (! (fst (snd (coma `0)) (inr (inl id))) ) , (! (fst (snd (coma `1)) (inr (inr id))) )) , 
          (\ pα → PathO= _ _ (\ x → fst (snd (coma x)) (inl pα) )) , 
          (\ r=r' → PathO= _ _ (\ x → snd (snd (coma x)) r=r' ∘ ⇒fst {A = λ z z' → A (p z , z')} {a0 = λ z → a0 (p z)} {a1 = λ z → a1 (p z)} r=r' (fst b) _)) where 
    coma : (x : I) → _
    coma x = comA (\ z → p z , x) r r' 
                  (α ∨ ((x == `0) ∨ (x == `1))) 
                  (\ z → case (\ pα → fst (t z pα) x ) 
                         (case (\ x=0 → transport _ (! x=0) (a0 (p z)) )
                               (\ x=1 → transport _ (! x=1) (a1 (p z)) ) 
                               (\ p q → abort (iabort (q ∘ ! p))))
                         (\ pα → ∨-elim _ (\ x=0 → ap (transport _ (! x=0)) (fst (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=0))) ((\ x=1 → ap (transport _ (! x=1)) (snd (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=1)))) (\ _ _ → uip))) 
                  (fst (fst b) x , 
                   ∨-elim _ (\ pα → ap (\ h → fst h x) (snd b pα)) (∨-elim _ (\ x=0 → ! (apd! (fst (fst b)) x=0) ∘ ap (transport _ (! x=0)) (! (fst (snd (fst b))))) ((\ x=1 → ! (apd! (fst (fst b)) x=1) ∘ ap (transport _ (! x=1)) (! (snd (snd (fst b)))))) ((\ _ _ → uip))) (((\ _ _ → uip))))

  comPathcoherent : ∀ {l1 l2 l : Level} {Δ : Set l2} {Γ : Set l1} {A : Γ × I → Set l} {θ : Δ → Γ} (a0 : (γ : Γ) → A (γ , `0)) (a1 : (γ : Γ) → A (γ , `1)) 
               → (comA : relCom A) 
               → comPre θ (\γ → PathO (\ z → A (γ , z)) (a0 γ) (a1 γ)) (comPath {A = A} a0 a1 comA) == 
                  comPath {A = \ p → A (θ (fst p) , snd p)} (\ x → a0 (θ x)) ((\ x → a1 (θ x))) (comPre (\ a → (θ (fst a), snd a)) A comA) 
  comPathcoherent {A = A} {θ = θ} a0 a1 comA = 
    relCom= ((\γ → PathO (\ z → A (γ , z)) (a0 γ) (a1 γ)) o θ) _ _ 
              (\ p r r' α {{ cα }} t b → id)

  Contractible : {l : Level} (A : Set l) → Set l
  Contractible A = Σ \ (a : A) → (b : A) → Path A a b

  -- write the type again in de bruijn form, sigh
  comContractible : {l1 l3 : Level} {Γ : Set l3} (A : Γ → Set l1)  
                  → relCom A
                  → relCom (Contractible o A)
  comContractible A comA = comΣ {A = A} {B = \ p → ( x : A (fst p) ) → Path (A (fst p)) (snd p) x} comA 
                                (comΠ {A = A o fst} {B = \ q → Path (A (fst (fst q))) (snd (fst q)) (snd q)} 
                                      (comPre fst A comA) 
                                      (comPath {Γ = Σ (A o fst)} {A = A o fst o fst o fst} (\ q → (snd (fst q))) (\ q → snd q) 
                                               (comPre (fst o fst o fst) A comA)))


  HFiber : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (b : B) → Set (l1 ⊔ l2)
  HFiber f b = Σ \a → Path _ (f a) b

  =HFiber : {l1 l2 : Level} {A : Set l1} {B : Set l2} {f : A → B} {b : B}
            {v1 v2 : HFiber f b}
          → (p : fst v1 == fst v2)
          → fst (snd v1) == (fst (snd v2))
          → v1 == v2
  =HFiber {v2 = v2} id id = ap (\ x → (fst v2 , fst (snd v2) , x)) (ap2 _,_ uip uip)

  comHFiber : {l1 l2 l3 : Level} {Γ : Set l3} (A : Γ → Set l1) (B : Γ → Set l2) (f : (γ : Γ) → A γ → B γ) 
            → relCom A
            → relCom B
            → relCom (\(p : Σ B) → (HFiber (f (fst p)) (snd p)))
  comHFiber A B f comA comB = comΣ {A = A o fst} {B = \ (p : Σ (A o fst)) → Path (B (fst (fst p))) (f (fst (fst p)) (snd p)) (snd (fst p)) } 
                                   (comPre fst A comA) 
                                   (comPath {Γ = Σ (λ (p : Σ B) → A (fst p))}
                                      {A = λ p → B (fst (fst (fst p)))} (λ p → f (fst (fst p)) (snd p))
                                      (λ p → snd (fst p)) (comPre (fst o fst o fst) B comB )) 

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

  -- seem to need this for suspensions, assumes only an hcom structure
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


