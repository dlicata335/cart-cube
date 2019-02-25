{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Glue
open import Equiv
open import Bool
open import universe.Universe

module universe.Pi where

  ΠData : (l :{♭} Level) → Set _
  ΠData l = Σ \ (A : U {l}) → (El A → U {l})

  Π-from-data : ∀ {l :{♭} Level} → ΠData l → Set _
  Π-from-data (A , B) = (x : El A) → El (B x)

  comΠ : ∀ {l :{♭} Level} → relCom {Γ = (ΠData l)} Π-from-data
  comΠ AB r r' α t b = (\ a' →  transport (\ h → El (B (r' , h))) (! (snd (fillback a' r') id))
             (fst (forward a'))  ) , 
             (λ pα → λ= \ a' →  ! (ap= (transport-ap-assoc' (El o B) (λ h → r' , h) (! (snd (fillback a' r') id)))) ∘ ap (transport (El o B) (ap (\ h → r' , h) (! (snd (fillback a' r') id)))) (fst (snd (forward a')) pα) ∘ ap= (transport-ap-assoc' (El o B) (λ h → r' , h) (! (snd (fillback a' r') id))) ∘ apd! (t r' pα) (snd (fillback a' r') id)) , 
             (λ {id → λ= \ a' → ! (ap= (transport-ap-assoc' (El o B) (λ h → r' , h) (! (snd (fillback a' r') id)))) ∘ ( ap (transport (El o B) (ap (λ h → r' , h) (! (snd (fillback a' r') id)))) (snd (snd (forward a')) id) ∘ ap= (transport-ap-assoc' (El o B) (λ h → r' , h) (! (snd (fillback a' r') id)))) ∘ apd! (fst b) (snd (fillback a' r) id)}) where
    A = \ x → fst (AB x)
    B = \ xa → snd (AB (fst xa)) (snd xa)

    fillback : (a' : _) (z : I) → _
    fillback a' z = coeU A r' z a' 

    forward : (a' : _) → _
    forward a' = comEl (\ z → B (z , (fst (fillback a' z))))
                       r r'
                       α (\ z pα → t z pα (fst (fillback a' z)))
                       (fst b (fst (fillback a' r)) , 
                         (\ pα → ap (\ f → f _) (snd b pα)))

  Πcode-universal : ∀ {l :{♭} Level} 
                  → (Σ \ (A : U {l}) → El(A) → U{l}) → U{l}
  Πcode-universal {l} = code (Σ \ (A : U {l}) → El(A) → U{l}) 
                             (\ AB → (x : El (fst AB)) → El (snd AB x))
                             (comΠ) 

  Πcode : ∀ {l1 l2 :{♭} Level} {Γ : Set l1} (A : Γ → U{l2}) (B : Σ (El o A) → U{l2}) → (Γ → U{l2})
  Πcode A B = Πcode-universal o (\ x → (A x , \ y → B (x , y)))

  Πcode-stable : ∀ {l1 l2 l3 :{♭} Level} {Γ : Set l1} {Δ : Set l3} (A : Γ → U{l2}) (B : Σ (El o A) → U{l2})
                   {θ : Δ → Γ}
               → ((Πcode A B) o θ) == Πcode (A o θ) (B o (\ p → (θ (fst p) , snd p)))
  Πcode-stable A B = id

  El-Πcode : ∀ {l1 l2 :{♭} Level} {Γ : Set l1} (A : Γ → U{l2}) (B : Σ (El o A) → U{l2})
           → (g : Γ) → El (Πcode A B g) == ((x : El (A g)) → El (B (g , x)))
  El-Πcode A B g = id

  comEl'-Πcode : ∀ {l1 l2 :{♭} Level} {Γ :{♭} Set l1} 
                   (A : Γ → U{l2}) (B : Σ (El o A) → U{l2}) → (Γ → U{l2})
                 → comEl' (Πcode A B) ==  comPre (\ γ → (A γ , \ a → B (γ , a))) Π-from-data comΠ  
  comEl'-Πcode {l2 = l2} {Γ} A B p = 
    comEl-code-subst {Γ = (Σ \ (A : U {l2}) → El(A) → U{l2})} {A = (\ AB → (x : El (fst AB)) → El (snd AB x))} (\ x → (A x , \ y → B (x , y)))

  -- ΠFib : {l :{♭} Level} {Γ :{♭} Set l}
  --        (A :{♭} Fib l Γ) (B :{♭} Fib l (Σ \ (x : Γ) → fst A x))
  --        → Fib l Γ
  -- ΠFib A B =  fn-to-Fib (Πcode (Fib-to-fn A) (Fib-to-fn B)) 

