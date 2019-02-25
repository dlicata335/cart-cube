{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Equiv
open import Path
open import Equiv
open import universe.LibFlat

module universe.Universe where

  module U{l :{♭} Level} where
    postulate
      U : Set (ℓ₂ ⊔ lsuc l)
      El : U → Set l
      comEl : relCom El 
      code : {l1 :{♭} Level} (Γ :{♭} Set l1) (A :{♭} Γ → Set l) (comA :{♭} relCom A) 
           → Γ → U

    postulate
      code-El : {l1 :{♭} Level} {Γ :{♭} Set l1} {A :{♭} Γ → Set l} {comA :{♭} relCom A}
                → (x : Γ) → El ((code Γ A comA) x) == A x
  
    {-# REWRITE code-El #-}

    El' : {l' : Level} {Γ : Set l'} → (Γ → U) → Γ → Set l
    El' A = El o A

    comEl' : {l1 : Level} {Γ : Set l1} (A : Γ → U)
           → relCom (El o A)
    comEl' A = comPre A El comEl

    postulate
      comEl-β : {l1 :{♭} Level} {Γ :{♭} Set l1} {A :{♭} Γ → Set l} {comA :{♭} relCom A}
                → (comEl' (code Γ A comA))  == comA

      code-η : {l1 :{♭} Level} {Γ :{♭} Set l1} (A :{♭} Γ → U) 
             → A == code Γ (El' A) (comEl' A)


  open U public


  -- some general lemmas

  -- expand definition of equality for code to isolate interesting parts
  code= :{♭} {l1 l :{♭} Level} (Γ :{♭} Set l1) (A A' :{♭} Γ → Set l) (comA :{♭} relCom A) (comA' :{♭} relCom A') 
        → (eq :{♭} (g : Γ) → A g == A' g)
           ( _ :{♭} ∀ p r r' α cα t b → 
              fst (comA p r r' α {{ cα }} t b) == 
              coe (! (eq _)) (fst (comA' p r r' α {{ cα }} 
                                  (\ z pα → coe (eq _) (t z pα)) 
                                  ((coe (eq _) (fst b), (\ pα → ap (coe (eq _)) (snd b pα)))))) )
        → code Γ A comA == code Γ A' comA'
  code= Γ A A' comA comA' Aeq h = 
    code=' A' comA' (λ= Aeq) 
    (\ p r r' α cα t b → 
      ap {M = Aeq} {N = \ x → ap= (λ= Aeq) {x} }
         (\ (H : (x : _) → A x == A' x) →  coe (! (H _))
         (fst (comA' p r r' α {{ cα }} (λ z pα → coe (H _) (t z pα))
              (coe (H _) (fst b) , (λ pα → ap (coe (H _)) (snd b pα)))))) (λ= \ _ → uip) ∘ 
         h p r r' α cα t b)  where
      code=' : (A' :{♭} _) (comA' :{♭} relCom A')
           (eq :{♭} A == A')
        → ( h :{♭} ∀ p r r' α cα t b → 
              fst (comA p r r' α {{ cα }} t b) == 
              coe (! (ap= eq)) (fst (comA' p r r' α {{ cα }} (\ z pα → coe (ap= eq) (t z pα)) ((coe (ap= eq) (fst b), (\ pα → ap (coe (ap= eq)) (snd b pα)))))) )
        → code Γ A comA == code Γ A' comA'
      code=' .A comA2 id h = ap♭ (code Γ A) (relCom= A _ _ (\ p r r' α {{ cα }} t b → ap (\ h → fst (comA2 p r r' α t (fst b , h))) (λ= \ _ → uip) ∘ h p r r' α cα t b)) 

  universal-code-η : ∀ {l :{♭} Level} → (A : U{l}) → A == (code U El comEl) A
  universal-code-η A = ap {M = (\ x → x)}{_} (\ h → h A) (code-η (\ X → X))

  comEl-code-subst : ∀ {l1 l2 l :{♭} Level} {Δ : Set l2} {Γ :{♭} Set l1} 
                     {A :{♭} Γ → Set l} {comA :{♭} relCom A} (f : Δ → Γ)
                   → comEl' ((code _ A comA) o f)  == comPre f A comA 
  comEl-code-subst {A = A}{comA} f = ap (comPre f (El o code _ A comA)) (comEl-β {A = A} {comA = comA}) ∘ ! (comPre-o {A = El} (code _ A comA) f comEl)

  ap-code-com : {l l1 :{♭} Level} {Γ :{♭} Set l1} {A :{♭} Γ → Set l} {comA com'A :{♭} relCom A} {x : Γ}
              → (p :{♭} comA == com'A)
              → (code Γ A comA) x == (code Γ A com'A) x
  ap-code-com {Γ = Γ}{A} {x = x} p = ap♭ (\ h → code Γ A h x) p

  code-flat-assoc : ∀ {l1 l2 l :{♭} Level} {Δ :{♭} Set l2} {Γ :{♭} Set l1} 
                  {A :{♭} Γ → Set l} {comA :{♭} relCom A} (f :{♭} Δ → Γ)
                → (x : Δ) → (code Γ A comA) (f x) == (code Δ (\ x → A (f x)) (comPre f A comA)) x
  code-flat-assoc {Δ = Δ} {A = A} {comA = comA} f x =  
    ap-code-com (comEl-code-subst {A = A} f) ∘ 
    ap (\ h → h x) (code-η (\ x → (code _ A comA) (f x)))


  Uext-♭ : ∀ {l1 l2 :{♭} Level} {Γ :{♭} Set l1}
            (A B :{♭} Γ → U{l2})
            (eq :{♭} (g : Γ) → El (A g) == El (B g))
            ( _ :{♭} ∀ p r r' α cα t b → 
              fst (comEl' A p r r' α {{ cα }} t b) == 
              coe (! (eq _)) (fst (comEl' B p r r' α {{ cα }} 
                                  (\ z pα → coe (eq _) (t z pα)) 
                                  ((coe (eq _) (fst b), (\ pα → ap (coe (eq _)) (snd b pα)))))) )
            → A == B
  Uext-♭ A B eq1 eq2 =
    ! (code-η B) ∘
    code= _ (El o A) (El o B) (comEl' A) (comEl' B) eq1 eq2 ∘
    code-η A

  coeU : ∀ {l :{♭} Level} (A : I → U {l}) → hasCoe (El o A)
  coeU A = relCom-relCoe (El o A) (comEl' A) (\ x → x)

  ElFib : {l :{♭} Level} → Fib l (U{l})
  ElFib = (El , comEl)

  Fib-to-fn : {l l1 :{♭} Level} {Γ :{♭} Set l1} (_ :{♭} Fib l Γ) → Γ → U{l}
  Fib-to-fn {Γ = Γ} (A , comA) = code Γ A comA

  fn-to-Fib : {l1 l2 :{♭} Level} {Γ : Set l1} → (Γ → U{l2}) → Fib l2 Γ
  fn-to-Fib A = reindex-Fib A ElFib

  hcomEl : {l :{♭} Level} → (A : U{l}) → hasHCom (El A)
  hcomEl A = relCom-hasHCom (\ (_ : Unit{lzero}) → El A) (comEl' (\ _ → A)) <>

  comEl=h : {l :{♭} Level} {A A' : I → U{l}} → A == A'
          → (r r' : I) (α : Set) {{cα : Cofib α}}
          → {t : (z : I) → α → El (A z)} {t' : (z : I) → α → El (A' z)} → t =h t'
          → {b : El (A r) [ α ↦ t r ]} {b' : El(A' r) [ α ↦ t' r ]} → fst b =h fst b'
          → fst (comEl A r r' α t b) =h fst (comEl A' r r' α t' b')
  comEl=h {A = A} id r r' α {t} hid {(b1 , _)} hid = hom-to-het (ap (\ z → fst (comEl A r r' α t (b1 , z))) (λ= \ _ → uip))

  module NoNonFlatUExt (Uext : ∀ {l1 l2 :{♭} Level} {Γ : Set l1}
                               (A B : Γ → U{l2})
                               (eq : (g : Γ) → El (A g) == El (B g))
                               ( _ : ∀ p r r' α cα t b → 
                                     fst (comEl' A p r r' α {{ cα }} t b) == 
                                          coe (! (eq _))
                                          (fst (comEl' B p r r' α {{ cα }} 
                                                      (\ z pα → coe (eq _) (t z pα)) 
                                                      ((coe (eq _) (fst b), (\ pα → ap (coe (eq _)) (snd b pα)))))) )
                               → A == B) where
     suppose : ∀ {l :{♭} Level} {Γ :{♭} Set l}
               (A B : Γ → U {l})
               (eq : (x : Γ) → El (A x) == El (B x))
               (eqhcoms : ∀ x r r' α cα t b → 
                               fst (comEl' (\ (_ : Unit{lzero}) → A x) (\ _ → <>) r r' α {{ cα }} t b) == 
                               coe (! (eq _))
                                  (fst (comEl' (\ (_ : Unit{lzero}) → B x) (\ _ → <>)
                                       r r' α {{ cα }} 
                                       (\ z pα → coe (eq _) (t z pα)) 
                                       ((coe (eq _) (fst b), (\ pα → ap (coe (eq _)) (snd b pα))))))
                               )
               (x : Γ) → A x == B x
     suppose A B eqelts eqhcoms x = ap= (Uext (\ (_ : Unit{lzero}) → A x) (\ _ → B x)
                                        (\ _ → eqelts x)
                                        (\ _ → eqhcoms x))   
         


  -- test : ∀ {l :{♭} Level} → code (U{l} × U{l}) (\ x → El (fst x)) (comPre fst El comEl ) == (\ p → (code U El comEl) (fst p))
  -- test {l} = λ= (\ p → ! ((code-flat-assoc {A = El} {comA = comEl} fst) p)) 

