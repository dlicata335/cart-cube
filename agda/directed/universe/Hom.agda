{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Prop
open import directed.DirInterval
open import universe.LibFlat
open import Equiv
open import Cofibs
open import Kan
open import Path
open import Interval
open import universe.Universe
open import universe.Sigma
open import directed.Segal
open import directed.Covariant
open import directed.SegalDepCovariant
open import directed.UCov

module directed.universe.Hom where

  open Layered

  -- FIXME change this to dependent hom instead

  Hom-code-universal : {l :{♭} Level} → (Σ \ (A : U{l}) → El A × El A) → U
  Hom-code-universal {l} = code (Σ \ (A : U) → El A × El A)
                         (\ H → Hom (El (fst H)) (fst (snd H)) (snd (snd H)))
                         (comHom {Γ = (Σ \ (A : U) → El A × El A)} {A = \ H → (El (fst (fst H)))} (\ g → fst (snd g)) ((\ g → snd (snd g)))
                                 (comEl' (\ H → (fst (fst H)))))
  
  ∘Hom' : ∀ {l} {A : Set l} {a b c : A} → relCov {l} (λ (_ : ⊤) → A) → Hom A b c → Hom A a b → Hom A a c
  ∘Hom' {a = a} hA q p = (\ x → fst (c x)) , 
                ! (fst (snd (c ``0)) (inl id))  ,  snd (snd q) ∘ ! (fst (snd (c ``1)) (inr id))  where
    c : (x : 𝟚) → _
    c x = (hA (λ _ → <>) ``1 ((x == ``0) ∨ (x == ``1)) (\ z → case (\ x=0 → a) ((\ x=1 → fst q z)) (\ p q → abort (diabort (q ∘ ! p)))) (fst p x , ∨-elim _ ( (\ x=0 →  ap (fst p) (! (x=0)) ∘ ! (fst (snd p)) ) ) ( ((λ x=1 → ap (fst p) (! x=1) ∘ ! (snd (snd p)) ∘ fst (snd q))) ) (\ _ _ → uip)))

  HomData :  (l :{♭} Level) → Set _
  HomData l = Σ \ (A : UCov l) → ElC A × ElC A

  Hom-from-data : {l :{♭} Level} → HomData l → Set l
  Hom-from-data H = Hom (ElC (fst H)) (fst (snd H)) (snd (snd H))
            
  Hom-relCov : {l :{♭} Level} → relCov1 (Hom-from-data {l})
  Hom-relCov {l} Aa0a1 α t b = ((\ x → fst (c x)) , ! (fst (snd (c ``0)) (inr (inl id)))  , ! (fst (snd (c ``1)) (inr (inr id)))) , (\ pα → HomO= _ _ (\ x → fst (snd (c x)) (inl pα))) where 

    A = \ z → fst (Aa0a1 z)
    a0 = \ z → fst (snd (Aa0a1 z))
    a1 = \ z → snd (snd (Aa0a1 z))

    c : (x : 𝟚) → _ 
    c x = dcomEl {l} A
               ``1
               (α ∨ ((x == ``0) ∨ (x == ``1)))
               (\ z → case (λ pα → fst (t z pα) x)
                           (case (\ x=0 → a0 z)
                                 (\ x=1 → a1 z)
                                 (\ p q → abort (diabort (q ∘ ! p))))
               ( λ pα → ∨-elimd01 _ ( λ x=0 →  fst (snd (t z pα)) ∘  ap (fst (t z pα)) x=0 )
                                    (λ x=1 →   snd (snd (t z pα)) ∘   ap (fst (t z pα)) x=1 ) 
                                    ))
               (fst (fst b) x , ∨-elim _ (\ pα → ap (\ h → fst h x) (snd b pα))
                                         (∨-elimd01 _ ((\ x=0 → ap (fst (fst b)) (! x=0) ∘ ! (fst (snd (fst b))) )) (\ x=1 → ap (fst (fst b)) (! x=1) ∘ ! (snd (snd (fst b)))) )
                                         (\ _ _ → uip))

  Hom-code-cov-universal : {l :{♭} Level} → HomData l → UCov l
  Hom-code-cov-universal {l} = code-cov (( (\ H → Hom-code-universal{l = l} (ElCov (fst H) , fst (snd H) , snd (snd H))) ) ,
                                          relCov1-relCov (Hom-from-data {l}) Hom-relCov )


  
