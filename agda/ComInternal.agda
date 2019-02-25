-- these versions are not currently used anywhere, but we include them
-- because they are slightly stronger than the universe-ified ones,
-- because they work for types with other free variables that they are not
-- Kan relative to

{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Kan
open import Prop
open import Bool
open import Nat
open import Path
open import Id
open import Susp

module ComInternal where

  comNat : ∀ {l1 l : Level} {Γ : Set l1} → relCom {Γ = Γ} (\ _ → Nat{l})
  comNat = relCom-constant Nat (hcomDec decNat)

  comBool : ∀ {l1 l : Level} {Γ : Set l1} → relCom {Γ = Γ} (\ _ → Bool{l})
  comBool = relCom-constant Bool (hcomDec decBool)

  comΣ : ∀ {l1 l2 l3 : Level} {Γ : Set l1} {A : Γ → Set l2} {B : Σ A → Set l3} → relCom A → relCom B → relCom (\ γ → Σ \ (x : A γ) → B (γ , x))
  comΣ {B = B} comA comB γ r r' α t b = ((fst (filla b r')) , fst (comb b)) , 
                                       (\ pα → pair= (fst (snd (filla b r')) pα) (fst (snd (comb b)) pα)) ,
                                       ((\ {id → pair= (snd (snd (filla b r')) id) (snd (snd (comb b)) id)})) where

   filla : (b : _) (z : I) → _
   filla b z = (comA γ r z α (\ pα z → fst (t pα z)) (fst (fst b) , (\ pα → ap fst (snd b pα))))

   comb : (b : _) → _
   comb b = 
     (comB (\ z → γ z , (fst (filla b z)))
           r r' 
           α (\ z pα →  transport (B o \ h → (γ z , h)) (fst (snd (filla b z)) pα) (snd (t z pα)) )
           (transport (B o \ h → (γ r , h)) (snd (snd (filla b r)) id) (snd (fst b)) , 
            (\ pα → ap (transport (B o (λ h → γ r , h)) (snd (snd (filla b r)) id)) (apd snd (snd b pα) ∘ ! (ap= (transport-ap-assoc' (λ z → B (γ r , z)) fst (snd b pα))) ) ∘ ap= (transport-∘ (B o (λ h → γ r , h)) (snd (snd (filla b r)) id) (ap fst (snd b pα))) ∘ ap {M = (fst (snd (filla b r)) pα)} {N = (snd (snd (filla b r)) id ∘ ap fst (snd b pα))} (\ h → transport (B o (λ h → γ r , h)) h (snd (t r pα))) uip)))

  comΣcoherent : ∀ {l1 l2 l3} {Δ : Set l1} {Γ : Set l2} {θ : Δ → Γ} {A : Γ → Set l3} {B : Σ A → Set l3}
               → (comA : relCom A) (comB : relCom B)
               → comPre θ (\ γ → Σ \ (x : A γ) → B (γ , x)) (comΣ {_}{_}{_} {_} {A} {B} comA comB) == 
                  comΣ {_} {_}{_}{_} {A o θ} {\ γ → B (θ (fst γ) , snd γ)} 
                      (comPre θ A comA) (comPre ( \ p → θ (fst p) , snd p) B comB) 
  comΣcoherent {θ = θ} {A = A} {B = B} comA comB = 
    relCom= ((\ γ → Σ \ (x : A γ) → B (γ , x)) o θ) _ _ 
              (\ p r r' α {{ cα }} t b → id)



  comΠ : ∀ {l1 l2 l3 : Level} {Γ : Set l1} {A : Γ → Set l2} {B : Σ A → Set l3} → relCom A → relCom B → relCom (\ γ → (x : A γ) → B (γ , x))
  comΠ {A = A} {B = B} comA comB γ r r' α t b = 
    (\ a' →  transport (\ h → B (γ r' , h)) (! (snd (fillback a' r') id))
             (fst (forward a'))  ) , 
    (λ pα → λ= \ a' →  ! (ap= (transport-ap-assoc' B (λ h → γ r' , h) (! (snd (fillback a' r') id)))) ∘ ap (transport B (ap (\ h → γ r' , h) (! (snd (fillback a' r') id)))) (fst (snd (forward a')) pα) ∘ ap= (transport-ap-assoc' B (λ h → γ r' , h) (! (snd (fillback a' r') id))) ∘ apd! (t r' pα) (snd (fillback a' r') id)) , 
    (λ {id → λ= \ a' → ! (ap= (transport-ap-assoc' B (λ h → γ r' , h) (! (snd (fillback a' r') id)))) ∘ ( ap (transport B (ap (λ h → γ r' , h) (! (snd (fillback a' r') id)))) (snd (snd (forward a')) id) ∘ ap= (transport-ap-assoc' B (λ h → γ r' , h) (! (snd (fillback a' r') id)))) ∘ apd! (fst b) (snd (fillback a' r) id)}) where
    
    fillback : (a' : _) (z : I) → _
    fillback a' z = relCom-relCoe A comA γ r' z a'
    
    forward : (a' : _) → _
    forward a' = 
      (comB (\ z → γ z , (fst (fillback a' z)))
            r r' 
            α (\ z pα → t z pα (fst (fillback a' z)))
            (fst b (fst (fillback a' r)) , 
             (\ pα → ap (\ f → f _) (snd b pα))))

  comΠcoherent : ∀ {l1 l2 l3} {Δ : Set l1} {Γ : Set l2} {θ : Δ → Γ} {A : Γ → Set l3} {B : Σ A → Set l3}
               → (comA : relCom A) (comB : relCom B)
               → comPre θ (\ γ → (x : A γ) → B (γ , x)) (comΠ {_}{_}{_} {_} {A} {B} comA comB) == 
                  comΠ {_} {_}{_}{_} {A o θ} {\ γ → B (θ (fst γ) , snd γ)} 
                      (comPre θ A comA) (comPre ( \ p → θ (fst p) , snd p) B comB) 
  comΠcoherent {θ = θ} {A = A} {B = B} comA comB = 
    relCom= ((\ γ → (x : A γ) → B (γ , x)) o θ) _ _ 
              (\ p r r' α {{ cα }} t b → λ= \ a' → id)


  com→ :  ∀ {l1 l2 l3 : Level} {Γ : Set l1} {A : Set l2} (B : Γ → Set l3) → relCom B → relCom (λ γ → A → B γ)
  com→ B comB γ r r' α t b = (λ a → fst (fillb a)) , (λ pα → λ= λ a → fst (snd (fillb a)) pα) , (λ {id → λ= (λ a → snd (snd (fillb a)) id)}) where
  
    fillb : ∀ a → _
    fillb a = comB γ r r' α (λ z pα → (t z pα) a) ((fst b) a , (λ pα → ap (λ f → f a) (snd b pα)))

  hcomΠ : ∀ {l1 l2 : Level} (A : Set l1) (B : A → Set l2)
           → ((x : A) → hasHCom (B x) )
           → hasHCom ( (x : A) → B x)
  hcomΠ A B comB r r' α t b = (λ a → fst (fillb a)) , (λ pα → λ= λ a → fst (snd (fillb a)) pα) , (λ {id → λ= (λ a → snd (snd (fillb a)) id)}) where
  
    fillb : ∀ a → _
    fillb a = comB a r r' α (λ z pα → (t z pα) a) ((fst b) a , (λ pα → ap (λ f → f a) (snd b pα)))

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

  -- sealed version, because comEl'-Path-code in universe/path is too slow if this reduces
  abstract
    comPath' : ∀ {l1 l : Level} {Γ : Set l1} {A : Γ × I → Set l} (a0 : (γ : Γ) → A (γ , `0)) (a1 : (γ : Γ) → A (γ , `1)) 
          → relCom A 
          → relCom (\γ → PathO (\ z → A (γ , z)) (a0 γ) (a1 γ))
    comPath'{l1}{l} {Γ}{A} a0 a1 = comPath{l1}{l}{Γ}{A}a0 a1

    comPath-is-comPath' : ∀ {l1 l : Level} {Γ : Set l1} {A : Γ × I → Set l} (a0 : (γ : Γ) → A (γ , `0)) (a1 : (γ : Γ) → A (γ , `1)) (comA : relCom A)
                        → comPath {A = A} a0 a1 comA == comPath' {A = A} a0 a1 comA
    comPath-is-comPath' a0 a1 comA = id

    comPath'coherent : ∀ {l1 l2 l : Level} {Δ : Set l2} {Γ : Set l1} {A : Γ × I → Set l} {θ : Δ → Γ} (a0 : (γ : Γ) → A (γ , `0)) (a1 : (γ : Γ) → A (γ , `1)) 
                  → (comA : relCom A) 
                  → comPre θ (\γ → PathO (\ z → A (γ , z)) (a0 γ) (a1 γ)) (comPath' {A = A} a0 a1 comA) == 
                          comPath' {A = \ p → A (θ (fst p) , snd p)} (\ x → a0 (θ x)) ((\ x → a1 (θ x))) (comPre (\ a → (θ (fst a), snd a)) A comA) 
    comPath'coherent {A = A} {θ = θ} a0 a1 comA = comPathcoherent {A = A} {θ = θ} a0 a1 comA


  -- write the type again in de bruijn form, sigh
  comContractible : {l1 l3 : Level} {Γ : Set l3} (A : Γ → Set l1)  
                  → relCom A
                  → relCom (Contractible o A)
  comContractible A comA = comΣ {A = A} {B = \ p → ( x : A (fst p) ) → Path (A (fst p)) (snd p) x} comA 
                                (comΠ {A = A o fst} {B = \ q → Path (A (fst (fst q))) (snd (fst q)) (snd q)} 
                                      (comPre fst A comA) 
                                      (comPath {Γ = Σ (A o fst)} {A = A o fst o fst o fst} (\ q → (snd (fst q))) (\ q → snd q) 
                                               (comPre (fst o fst o fst) A comA)))

  comHFiber : {l1 l2 l3 : Level} {Γ : Set l3} (A : Γ → Set l1) (B : Γ → Set l2) (f : (γ : Γ) → A γ → B γ) 
            → relCom A
            → relCom B
            → relCom (\(p : Σ B) → (HFiber (f (fst p)) (snd p)))
  comHFiber A B f comA comB = comΣ {A = A o fst} {B = \ (p : Σ (A o fst)) → Path (B (fst (fst p))) (f (fst (fst p)) (snd p)) (snd (fst p)) } 
                                   (comPre fst A comA) 
                                   (comPath {Γ = Σ (λ (p : Σ B) → A (fst p))}
                                      {A = λ p → B (fst (fst (fst p)))} (λ p → f (fst (fst p)) (snd p))
                                      (λ p → snd (fst p)) (comPre (fst o fst o fst) B comB )) 

  scontrId : ∀ {l} {A : Set l} → hasHCom A → (a : A) → 
           (s : (Σ \ b → Id A b a)) → Id (Σ \ b → Id A b a) (a , refl A a) s
  scontrId {A = A} hcomA a (b , (α , p , isrefl)) = 
         -- where the path in S(a) is constant
         α , 
         ((\ x → -- path in A
                 fst (square b p α isrefl x `0) , 
                 -- path in Id
                   -- where it's constant
                   ((x == `0) ∨ (fst α) , Cofib∨ Cofib= ((snd α))) , 
                   -- path in Path, with endpoints proofs
                   (((\ y → fst (square _ p α (isrefl) x y))) , 
                      id , ! (snd (snd (square _ p α (isrefl) x `1)) id)) , 
                   -- proof of constancy, because both are constant on the α from s
                   (case (\ x=0 → λ= \ y → fst (snd (square b p α isrefl x `0)) (inl (inl x=0)) ∘ ! (fst (snd (square b p α isrefl x y)) (inl (inl x=0))) ) 
                         (\ pα → λ= \ z → fst (snd (square b p α isrefl x `0)) (inr pα) ∘ 
                                  ! (fst (snd (square b p α isrefl x z)) (inr pα)))
                         (\ _ _ → uip))) , 
          -- correct boundary 1: x=0 from tube, and propositional univalence for cofibs
          pair= (! (fst (snd (square b p α isrefl `0 `0)) (inl (inl id))) ) 
                                      -- copy and paste sigh
                ( (Id=-transport1 _ _ (! (fst (snd (square b p α isrefl `0 `0)) (inl (inl id))) )
                  ( (pair= (Cofib-propositional-univalence {{ cα = Cofib∨ Cofib= (snd α) }} {{ cβ = Cofib⊤ }} (\ _ → <>) 
                         (\ _ → inl id))
                         Cofib-prop) ) 
                  (\ x → (! (fst (snd (square b p α isrefl `0 x)) (inl (inl id))) ) )) ) , 
          -- correct boundary 2:
          pair= (fst (snd p) ∘ (! (fst (snd (square b p α isrefl `1 `0)) (inl (inr id))) ))
                ((Id=-transport1 _ _  (fst (snd p) ∘ (! (fst (snd (square b p α isrefl `1 `0)) (inl (inr id))) ))
                                      (pair= (Cofib-propositional-univalence {{cα = Cofib∨ Cofib= (snd α)}} {{cβ = snd α}} 
                                                (case (\q → abort (iabort (! q))) (\ p → p) (\ _ → \ pα → Cofib.eq (snd α) _ _))
                                                inr) 
                                             Cofib-prop ) 
                                      (\ x → ! (fst (snd (square b p α isrefl `1 x)) (inl (inr id)))) ))
          ) , 
          -- path in S(a) is constant
          (\ pα → λ= \ x → pair= (! (fst (snd (square b p α isrefl x `0)) (inr pα))) 
                                  ( (Id=-transport1 _ _ (! (fst (snd (square b p α isrefl x `0)) (inr pα)))
                                     (pair= ( (Cofib-propositional-univalence {{cα = Cofib∨ Cofib= (snd α)}} {{cβ = Cofib⊤}} 
                                                                            (\ _ → <>) (\ _ → inr (pα))) )
                                            Cofib-prop) 
                                     (\ y → ! (fst (snd (square b p α isrefl x y)) (inr pα)))) ))
    where
    square : (b : _) (s : Path A b a) (α : Cofibs) (isrefl : fst α → IsRefl A s) (x : _) (y : _) → _
    square b s α isrefl x y = hcomA `1 y (((x == `0) ∨ (x == `1)) ∨ fst α)
                               {{ Cofib∨ (Cofib∨ Cofib= Cofib=) (snd α) }}
                               (\ y → case (case (\ _ → a) 
                                                  (\ _ → fst s y) 
                                                  (\ p q → abort (iabort (q ∘ ! p)) ))
                                            (\ _ → a)
                                            (∨-elim _ (\ _ _ → id) 
                                                      (\ _ pα →  (snd (snd s)) ∘ ! (ap= (isrefl pα)) ∘ ap= (isrefl pα) )
                                                      (\ _ _ → (λ= \ _ → uip))))
                               (a  , ∨-elim _ 
                                            (∨-elim _ (\ x=0 → snd (snd s) ∘ ! (snd (snd s)))
                                                        (\ x=1 → snd (snd s)) (\ _ _ → uip))
                                            (\ _ → id) 
                                            (\ _ _ → uip))

  scontrId-refl : ∀ {l} {A : Set l} → (hcomA : hasHCom A) → (a : A) → 
             scontrId hcomA a (a , refl A a) == refl (Σ \ b → Id A b a) (a , refl A a)
  scontrId-refl {A = A} hcomA a = Id= _ _ id (\ x →  ap= (snd (snd (scontrId hcomA a (a , refl A a))) <>) {x})

  transportId : {l1 l2 : Level} (A : Set l1) (a0 : A) (C : A → Set l2) 
    → relCom C
    → (c : C a0)
    → Σ \ (f : (a1 : A) (p : Id A a0 a1) → C (a1)) → f a0 (refl A a0) == c
  transportId A a0 C comC c = 
    (\ a1 p → transport C (snd (snd (fst (snd p)))) (fst (com a1 p))) , 
     ! (fst (snd (com a0 (refl A a0))) <>)
    where
    com : (a1 : _) (p : _) → _
    com a1 p = (comC (\ x → fst (fst (snd p)) x)
                        `0 `1 (fst (fst p)) {{ snd (fst p) }} 
                        (\ z pp →  transport C (! (ap= (snd (snd p) pp){z})) c )
                        (transport C (! (fst (snd (fst (snd p))))) c , 
                         (\ pp → ap (\ h → transport C h c) (uip {p = (! (ap= (snd (snd p) pp)))} {q = (! (fst (snd (fst (snd p)))))}))))

  J : {l1 l2 : Level} (A : Set l1) → hasHCom A → (a0 : A)     
    → (C : (Σ \ (a : A) → Id A a a0) → Set l2) 
    → relCom C
    → (c : C (a0 , refl A a0))
    → Σ \ (f : (a1 : A) (p : Id A a1 a0) → C (a1 , p)) → f a0 (refl A a0) == c
  J A hcomA a0 C comC c = (\ a1 p → (fst tr (a1 , p) (scontrId hcomA a0  (a1 , p) ))) , 
                          snd tr ∘  ap (fst tr (a0 , refl A a0)) (scontrId-refl hcomA a0)  where 
    tr = transportId (Σ \ b → Id A b a0) (a0 , refl A a0) C comC c

  comId : ∀ {l1 l : Level} {Γ : Set l1} {A : Γ → Set l} (a0 : (γ : Γ) → A γ) (a1 : (γ : Γ) → A γ) 
          → relCom A 
          → relCom (\γ → Id (A γ) (a0 γ) (a1 γ))
  comId {A = A} a0 a1 comA p r r' α {{ cα }} t b = 
    ( (newα , newα-cofib), 
     fst c , 
     -- c is constant on newα
     case (\ l → λ= \ x → ap= (snd (snd (t r' (fst l))) (snd l)) ∘ ap (\ h → fst h x) (! (fst (snd c) (fst l))) )
          (\ ri → λ= \ x → (apd (\ h → a0 (p h)) (fst ri) ∘ ap (transport (λ z → A (p z)) (fst ri)) (ap= (snd (snd (fst b)) (snd ri)){x}) ∘ 
                            ap= (fst-transport-Path (fst ri) (fst (snd (fst b)))) )
                  ∘ ap (\ h → fst h x) (! (snd (snd c) (fst ri)))) 
          (\ _ _ → uip)) , 
    -- important that for the coherences that  α, r=r' ⊢ φ_{t r'} == φ_{b}
    (\ pα → Id= _ _ (pair= (Cofib-propositional-univalence {{ cα = (snd (fst (t r' pα))) }} {{ cβ = newα-cofib }} 
                               (\ pt → inl (pα , pt)) 
                               (case (\ p → transport (\ h → fst (fst (t r' h))) (Cofib.eq cα _ _) (snd p))
                                     (\ q → coe (ap (\ h → fst (fst (t h pα))) (fst q) ∘ ! (ap fst (ap fst (snd b pα)))) (snd q)) 
                                     (\ _ _ → Cofib.eq (snd (fst (t r' pα))) _ _))) 
                           Cofib-prop) 
                     (\ x → ap (\ h → fst h x) (fst (snd c) pα))) , 
    (\ {id → Id= _ _ (pair= ( (Cofib-propositional-univalence {{ cα = (snd (fst (fst b))) }} {{ cβ = newα-cofib }} 
                               (\ pb → inr (id , pb)) 
                               (case (\ p → coe (ap fst (ap fst ((snd b (fst p))))) (snd p)) 
                                     (\ q → snd q) 
                                     (\ _ _ → Cofib.eq (snd (fst (fst b))) _ _)
                               )) ) 
                           Cofib-prop) 
                     (\ x →  ap (\ h → fst h x) (snd (snd c) id) )}) where
  
      c =  comPath {A = (\ p → A (fst p))} a0 a1 (comPre fst A comA) p r r' 
                   α (\ z pα → (fst (snd (t z pα))))
                   (fst (snd (fst b)) , 
                     (λ x → ap (\ x → fst (snd x)) (snd b x) )) 

      newα = (Σ \ (pα : α) → (fst (fst (t r' pα)))) ∨ ((r == r') × fst (fst (fst b))) 
      newα-cofib = Cofib∨ (Cofib∧ cα (\ pα → snd (fst (t r' pα)))) (Cofib∧ Cofib= (\_ → snd (fst (fst b))))


  suspη : ∀ {l'} {A : Set l'} (x : Susp A) 
          → Path (Susp A) 
            (Susp-elim (\ _ → Susp A) (relCom-constant _ (fcomSusp)) north south (\ a → (\ x → merid a x) , id , id ) x)
            x
  suspη {A = A} = Susp-elim _ 
                   (comPath-endpoints (\ z → (Susp-elim (λ _ → Susp A) (relCom-constant (Susp A) fcomSusp) north south (λ a → merid a , id , id) z)) (\ z → z)
                                      fcomSusp ) -- Note be careful when syntacticfying, this isn't necessarily hcom_(Path_(Susp A)) !
                   ((\ _ → north) , id , id) 
                   (((\ _ → south) , id , id)) 
                   (\ a → ((\ x →  (\ _ → merid a x), id , id ) , id , id) )

  wcoeSusp : ∀ {l l'} {Γ : Set l} {A : Γ → Set l'} 
          → relCoe A
          → relWCoe (\ x → Susp (A x))
  wcoeSusp {A = A} coeA p r r' = 
    (s (\ x → fst(movea x)) , (\ {id b → fst (suspη b) ,  ap= (ap s (λ= \ x → snd (movea x) id  )) {b}  ∘ fst (snd (suspη b))  , snd (snd (suspη b))}))  where

    movea : (a : _) → _
    movea a = coeA p r r' a

    s : (movea1 : _) (b : _) → _
    s movea1 = Susp-elim (\ _ → Susp (A (p r')))
                  ((relCom-constant _ fcomSusp)) 
                  (north) 
                  (south) 
                  (\ a → (\ x → merid (movea1 a) x) , id , id) 
                  
