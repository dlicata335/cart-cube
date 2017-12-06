{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level; _⊔_)

open import Lib
open import Kan
open import Interval
open import Cofibs
open import Pi
open import Sigma
open import Prop
open import Path

module Id where
  
  postulate
    isCofib-prop : ∀ {A : Set} → (p q : Cofib A) → p == q
    isCofib⊤ : isCofib ⊤
    isCofib∧ : ∀ {α} {β : α → Set} → isCofib α → ((x : α) → isCofib (β x)) → isCofib (Σ β)
    Cofib-propositional-univalence : ∀ {α β} {{ cα : Cofib α }} {{ cβ : Cofib β }}
                                   → (α → β) → (β → α) → α == β

  instance
    Cofib⊤ : Cofib ⊤
    Cofib⊤ = cofib isCofib⊤ (\ _ _ → id)

    Cofib∧ : ∀ {α} {β : α → Set} → Cofib α → ((x : α) → Cofib (β x)) → Cofib (Σ β)
    Cofib∧ (cofib cα eqα) cβ = cofib (isCofib∧ cα (\ x → Cofib.is (cβ x))) (\ p q → pair= (eqα _ _) (Cofib.eq (cβ (fst q)) _ _))

  -- equal to the refl path, but more convenient without the type checking
  IsRefl : {l : Level} (A : Set l) {a0 a1 : A} → Path A a0 a1 → Set l
  IsRefl A {a0} p = fst p == (\ _ → a0)

  Id : {l : Level} (A : Set l) (a0 a1 : A) → Set (lsuc lzero ⊔ l)
  Id A a0 a1 = Σ \(φ : Cofibs) → (Σ \(p : Path A a0 a1) → fst φ → IsRefl A p)

  Id= : {l : Level} {A : Set l} {a0 a1 : A} → (p q : Id A a0 a1) 
        → fst p == fst q 
        → ((x : I) → fst (fst (snd p)) x == fst (fst (snd q)) x)
        → p == q
  Id= p q id eq2 = pair= id (pair= (pair= (λ= eq2) (pair= uip uip)) (λ= \ _ → uip))

  abstract
    Id=-transport1 : {l : Level} {A : Set l} {a0 a0' a1 : A} → (p : Id A a0 a1) (q : Id A a0' a1) 
          → (eq : a0 == a0')
          → fst p == fst q 
          → ((x : I) → fst (fst (snd p)) x == fst (fst (snd q)) x)
          → (transport (\ x → Id A x a1) eq p) == q
    Id=-transport1 p q id eq1 eq2 = Id= p q eq1 eq2

    Id=-transport2 : {l : Level} {A : Set l} {a0 a1 a1' : A} → (p : Id A a0 a1) (q : Id A a0 a1') 
          → (eq : a1 == a1')
          → fst p == fst q 
          → ((x : I) → fst (fst (snd p)) x == fst (fst (snd q)) x)
          → (transport (\ x → Id A a0 x) eq p) == q
    Id=-transport2 p q id eq1 eq2 = Id= p q eq1 eq2
  
  refl : {l : Level} (A : Set l) (a0 : A) → Id A a0 a0
  refl A a0 = (⊤{lzero} , Cofib⊤) , ((\ _ → a0) , id , id) , (\ _ → id)

  ContractibleId : {l : Level} (A : Set l) → Set (lsuc lzero ⊔ l)
  ContractibleId A = Σ \ (a : A) → (b : A) → Id A a b

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
                         (isCofib-prop _ _)) ) 
                  (\ x → (! (fst (snd (square b p α isrefl `0 x)) (inl (inl id))) ) )) ) , 
          -- correct boundary 2:
          pair= (fst (snd p) ∘ (! (fst (snd (square b p α isrefl `1 `0)) (inl (inr id))) ))
                ((Id=-transport1 _ _  (fst (snd p) ∘ (! (fst (snd (square b p α isrefl `1 `0)) (inl (inr id))) ))
                                      (pair= (Cofib-propositional-univalence {{cα = Cofib∨ Cofib= (snd α)}} {{cβ = snd α}} 
                                                (case (\q → abort (iabort (! q))) (\ p → p) (\ _ → \ pα → Cofib.eq (snd α) _ _))
                                                inr) 
                                             (isCofib-prop _ _) ) 
                                      (\ x → ! (fst (snd (square b p α isrefl `1 x)) (inl (inr id)))) ))
          ) , 
          -- path in S(a) is constant
          (\ pα → λ= \ x → pair= (! (fst (snd (square b p α isrefl x `0)) (inr pα))) 
                                  ( (Id=-transport1 _ _ (! (fst (snd (square b p α isrefl x `0)) (inr pα)))
                                     (pair= ( (Cofib-propositional-univalence {{cα = Cofib∨ Cofib= (snd α)}} {{cβ = Cofib⊤}} 
                                                                            (\ _ → <>) (\ _ → inr (pα))) )
                                            (isCofib-prop _ _)) 
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
                           (isCofib-prop _ _)) 
                     (\ x → ap (\ h → fst h x) (fst (snd c) pα))) , 
    (\ {id → Id= _ _ (pair= ( (Cofib-propositional-univalence {{ cα = (snd (fst (fst b))) }} {{ cβ = newα-cofib }} 
                               (\ pb → inr (id , pb)) 
                               (case (\ p → coe (ap fst (ap fst ((snd b (fst p))))) (snd p)) 
                                     (\ q → snd q) 
                                     (\ _ _ → Cofib.eq (snd (fst (fst b))) _ _)
                               )) ) 
                           (isCofib-prop _ _)) 
                     (\ x →  ap (\ h → fst h x) (snd (snd c) id) )}) where
  
      c =  comPath {A = (\ p → A (fst p))} a0 a1 (comPre fst A comA) p r r' 
                   α (\ z pα → (fst (snd (t z pα))))
                   (fst (snd (fst b)) , 
                     (λ x → ap (\ x → fst (snd x)) (snd b x) )) 

      newα = (Σ \ (pα : α) → (fst (fst (t r' pα)))) ∨ ((r == r') × fst (fst (fst b))) 
      newα-cofib = Cofib∨ (Cofib∧ cα (\ pα → snd (fst (t r' pα)))) (Cofib∧ Cofib= (\_ → snd (fst (fst b))))


{-
  comPathcoherent : ∀ {l1 l2 l : Level} {Δ : Set l2} {Γ : Set l1} {A : Γ × I → Set l} {θ : Δ → Γ} (a0 : (γ : Γ) → A (γ , `0)) (a1 : (γ : Γ) → A (γ , `1)) 
               → (comA : relCom A) 
               → comPre θ (\γ → PathO (\ z → A (γ , z)) (a0 γ) (a1 γ)) (comPath {A = A} a0 a1 comA) == 
                  comPath {A = \ p → A (θ (fst p) , snd p)} (\ x → a0 (θ x)) ((\ x → a1 (θ x))) (comPre (\ a → (θ (fst a), snd a)) A comA) 
  comPathcoherent {A = A} {θ = θ} a0 a1 comA = 
    relCom= ((\γ → PathO (\ z → A (γ , z)) (a0 γ) (a1 γ)) o θ) _ _ 
              (\ p r r' α {{ cα }} t b → id)
-}



