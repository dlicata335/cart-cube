{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Glue
open import Equiv
open import Path
open import Equiv
open import universe.Universe

module universe.Sigma where

  ΣData : (l :{♭} Level) → Set _
  ΣData l = Σ \ (A : U {l}) → (El A → U {l})

  Σ-from-data : ∀ {l :{♭} Level} → ΣData l → Set _
  Σ-from-data (A , B) = Σ \ (x : El A) → El (B x)

  comΣ : ∀ {l :{♭} Level} → relCom {Γ = (ΣData l)} Σ-from-data
  comΣ AB r r' α t b = ((fst (filla b r')) , fst (comb b)) , 
                        (\ pα → pair= (fst (snd (filla b r')) pα) (fst (snd (comb b)) pα)) ,
                        ((\ {id → pair= (snd (snd (filla b r')) id) (snd (snd (comb b)) id)})) where
    A = \ x → fst (AB x)
    B = \ xa → snd (AB (fst xa)) (snd xa)

    filla : (b : _) (z : I) → _
    filla b z = (comEl A r z α (\ pα z → fst (t pα z)) (fst (fst b) , (\ pα → ap fst (snd b pα))))

    comb : (b : _) → _
    comb b = 
      (comEl (\ z → B (z , (fst (filla b z))))
              r r' 
              α (\ z pα →  transport (El o (B o \ h → (z , h))) (fst (snd (filla b z)) pα) (snd (t z pα)) )
                (transport (El o B o \ h → (r , h)) (snd (snd (filla b r)) id) (snd (fst b)) , 
                (\ pα → ap (transport (El o B o (λ h → r , h)) (snd (snd (filla b r)) id)) (apd snd (snd b pα) ∘ ! (ap= (transport-ap-assoc' (λ z → El (B (r , z))) fst (snd b pα))) ) ∘ ap= (transport-∘ (El o B o (λ h → r , h)) (snd (snd (filla b r)) id) (ap fst (snd b pα))) ∘ ap {M = (fst (snd (filla b r)) pα)} {N = (snd (snd (filla b r)) id ∘ ap fst (snd b pα))} (\ h → transport (El o B o (λ h → r , h)) h (snd (t r pα))) uip)))

  Σcode-universal : ∀ {l :{♭} Level} 
                  → (Σ \ (A : U {l}) → El(A) → U{l}) → U{l}
  Σcode-universal {l} = code (ΣData l) 
                             (\ AB → Σ \ (x : El (fst AB)) → El (snd AB x))
                             comΣ

  Σcode : ∀ {l1 l2 :{♭} Level} {Γ : Set l1} (A : Γ → U{l2}) (B : Σ (El o A) → U{l2}) → (Γ → U{l2})
  Σcode A B = Σcode-universal o (\ x → (A x , \ y → B (x , y)))

  Σcode-stable : ∀ {l1 l2 l3 :{♭} Level} {Γ : Set l1} {Δ : Set l3} (A : Γ → U{l2}) (B : Σ (El o A) → U{l2})
                   {θ : Δ → Γ}
               → ((Σcode A B) o θ) == Σcode (A o θ) (B o (\ p → (θ (fst p) , snd p)))
  Σcode-stable A B = id

  El-Σcode : ∀ {l1 l2 :{♭} Level} {Γ : Set l1} (A : Γ → U{l2}) (B : Σ (El o A) → U{l2})
           → (g : Γ) → El (Σcode A B g) == (Σ \ (x : El (A g)) → El (B (g , x)))
  El-Σcode A B g = id

  -- comEl'-Σcode : ∀ {l1 l2 :{♭} Level} {Γ :{♭} Set l1} 
  --                  (A : Γ → U{l2}) (B : Σ (El o A) → U{l2}) → (Γ → U{l2})
  --                → comEl' (Σcode A B) == comΣ {A = (El o A) } {B = (El o B) } (comEl' A) (comEl' B) 
  -- comEl'-Σcode {l2 = l2} {Γ} A B p = 
  --     comΣcoherent  {Γ = (Σ \ (A : U {l2}) → El(A) → U{l2})} {θ = (\ x → (A x , \ y → B (x , y)))} {B = λ ABa → El (snd (fst ABa) (snd ABa)) } (comPre fst El comEl) (comPre (\ ABa → (snd (fst ABa) (snd ABa))) El comEl ) 
  --   ∘ comEl-code-subst {Γ = (Σ \ (A : U {l2}) → El(A) → U{l2})} {A = (\ AB → Σ \ (x : El (fst AB)) → El (snd AB x))} (\ x → (A x , \ y → B (x , y)))

