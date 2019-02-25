{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Glue
open import Equiv
open import Equiv
open import Path
open import universe.Universe
open import universe.Sigma
open import universe.Pi

module universe.Path where

  PathData : ∀ {l :{♭} Level} → Set (lsuc (lsuc lzero) ⊔ lsuc l)
  PathData {l} = (Σ \ (A : I → U {l}) → El(A `0) × El(A `1))

  Path-from-data : ∀ {l :{♭} Level} → PathData{l} → Set _
  Path-from-data Aab = PathO (\ x → El (fst Aab x)) (fst (snd (Aab))) (snd (snd (Aab)))

  com-Path-universal : ∀ {l :{♭} Level} → relCom {Γ = (PathData {l})} Path-from-data
  com-Path-universal{l} Aa0a1 r r' α t b =
    ((\ x → fst (coma x)) , (! (fst (snd (coma `0)) (inr (inl id))) ) , (! (fst (snd (coma `1)) (inr (inr id))) )) , 
    (\ pα → PathO= _ _ (\ x → fst (snd (coma x)) (inl pα) )) , 
    (\ r=r' → PathO= _ _ (\ x → snd (snd (coma x)) r=r' ∘ ⇒fst {A = λ z z' → El (A z z')} {a0 = λ z → a0 z} {a1 = λ z → a1 z} r=r' (fst b) _)) where 
    A = \ x → fst (Aa0a1 x)
    a0 = \ x → fst (snd (Aa0a1 x)) 
    a1 = \ x → snd (snd (Aa0a1 x)) 
    coma : (x : I) → _
    coma x = comEl (\ z → A z x) r r' 
                   (α ∨ ((x == `0) ∨ (x == `1))) 
                   (\ z → case (\ pα → fst (t z pα) x ) 
                         (case (\ x=0 →  transport _ (! x=0) (a0 z)  )
                               (\ x=1 →  transport _ (! x=1) (a1 z)  ) 
                               (\ p q → abort (iabort (q ∘ ! p))))
                         (\ pα → ∨-elim _ (\ x=0 → ap (transport _ (! x=0)) (fst (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=0))) ((\ x=1 → ap (transport _ (! x=1)) (snd (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=1)))) (\ _ _ → uip))) 
                   (fst (fst b) x , 
                    ∨-elim _ (\ pα → ap (\ h → fst h x) (snd b pα)) (∨-elim _ (\ x=0 → ! (apd! (fst (fst b)) x=0) ∘ ap (transport _ (! x=0)) (! (fst (snd (fst b))))) ((\ x=1 → ! (apd! (fst (fst b)) x=1) ∘ ap (transport _ (! x=1)) (! (snd (snd (fst b)))))) ((\ _ _ → uip))) (((\ _ _ → uip))))

  Path-code-universal : ∀ {l :{♭} Level} → PathData{l} → U{l}
  Path-code-universal {l} = code (PathData{l})
                                 (Path-from-data{l})
                                 com-Path-universal
                                 
  Path-code : ∀ {l1 l2 :{♭} Level} {Γ : Set l1}
              (A : Γ × I → U{l2})
              (a0 : (θ : Γ) → El (A (θ , `0)))
              (a1 : (θ : Γ) → El (A (θ , `1)))
              → Γ → U{l2}
  Path-code A a0 a1 = Path-code-universal o (\ θ → ((\ y → A (θ , y)) , a0 θ , a1 θ))

  El-Path-code : ∀ {l1 l2 :{♭} Level} {Γ : Set l1}
                   (A : Γ × I → U{l2})
                   (a0 : (x : Γ) → El (A (x , `0)))
                   (a1 : (x : Γ) → El (A (x , `1)))
                 → (θ : Γ) → El (Path-code A a0 a1 θ) == PathO (\ x → El (A (θ , x))) (a0 θ) (a1 θ) 
  El-Path-code A a0 a1 θ = id


  private
    -- tried using this for HITs but it didn't work; see Susp.agda
    com-Path-endpoints : ∀ {l :{♭} Level} (A : U {l})→ relCom {Γ = El A × El A} (\ p → Path (El A) (fst p) (snd p))
    com-Path-endpoints A a0a1 r r' α t b = 
           ((\ x → fst (hcoma x)) , (! (fst (snd (hcoma `0)) (inr (inl id))) ) , (! (fst (snd (hcoma `1)) (inr (inr id))) )) , 
           (\ pα → PathO= _ _ (\ x → fst (snd (hcoma x)) (inl pα) )) , 
           (\ r=r' → PathO= _ _ (\ x → snd (snd (hcoma x)) r=r' ∘ ⇒fst-nd {A = El A} {a0 = λ z → a0 z} {a1 = λ z → a1 z} r=r' (fst b) x)) where
      a0 = \ z → fst (a0a1 z)
      a1 = \ z → snd (a0a1 z)
      hcoma : (x : I) → _
      hcoma x = hcomEl A r r' 
                   (α ∨ ((x == `0) ∨ (x == `1))) 
                   (\ z → case (\ pα → fst (t z pα) x ) 
                          (case (\ x=0 → transport _ (! x=0) (a0 z) )
                                (\ x=1 → transport _ (! x=1) (a1 z) ) 
                                (\ p q → abort (iabort (q ∘ ! p))))
                          (\ pα → ∨-elim _ (\ x=0 → ap (transport _ (! x=0)) (fst (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=0))) ((\ x=1 → ap (transport _ (! x=1)) (snd (snd (t z pα))) ∘ ! (apd (fst (t z pα)) (! x=1)))) (\ _ _ → uip))) 
                   (fst (fst b) x , 
                    ∨-elim _ (\ pα → ap (\ h → fst h x) (snd b pα)) (∨-elim _ (\ x=0 → ! (apd! (fst (fst b)) x=0) ∘ ap (transport _ (! x=0)) (! (fst (snd (fst b))))) ((\ x=1 → ! (apd! (fst (fst b)) x=1) ∘ ap (transport _ (! x=1)) (! (snd (snd (fst b)))))) ((\ _ _ → uip))) (((\ _ _ → uip))))

    Path-code-endpoints-universal : ∀ {l :{♭} Level} (A :{♭} U {l}) → El A × El A → U{l}
    Path-code-endpoints-universal A = code (El A × El A) ((\ p → Path (El A) (fst p) (snd p))) (com-Path-endpoints A)


  HFiber-code : ∀ {l :{♭} Level} {A B : U {l}} (f : El A → El B) → El B → U {l}
  HFiber-code {A = A}{B} f b = Σcode-universal (A , (\ a → Path-code-universal ((\ _ → B) , (f a , b)))) 

  Contractible-code : {l1 :{♭} Level} (A : U{l1}) → U{l1}
  Contractible-code A = Σcode-universal (A , (\ x → Πcode-universal (A , (\ y → Path-code-universal ((\ _ → A) , ((x , y)))))))

  isEquiv-code : {l1 :{♭} Level} (A : U {l1}) (B : U {l1}) (f : El A → El B) → U {l1}
  isEquiv-code A B f = Πcode-universal (B  , (\ x → Contractible-code ((HFiber-code {A = A} {B} f x))))

  coePathU : {l :{♭} Level} {A B : U{l}} → Path U A B → El A → El B
  coePathU p a =
    coe (ap El ((snd (snd p)))) (fst (coeU (fst p) `0 `1 (coe (ap El (! (fst (snd p)))) a)))
