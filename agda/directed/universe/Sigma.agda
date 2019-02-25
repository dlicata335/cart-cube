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

module directed.universe.Sigma where

  open Layered

  ΣDataCov : (l :{♭} Level) → Set (lmax ℓ₂ (lsuc l))
  ΣDataCov l = Σ \ (A : UCov l) → (ElC A → UCov l)

  Σ-from-data-cov : ∀ {l :{♭} Level} → ΣDataCov l → Set _
  Σ-from-data-cov (A , B) = Σ \ (x : ElC A) → ElC (B x)

  covΣ : ∀ {l :{♭} Level} → relCov1 {Γ = (ΣDataCov l)} Σ-from-data-cov
  covΣ{l} AB α t b = 
    ((fst (filla b ``1)) , fst (comb b)) , 
      (\ pα → pair= (fst (snd (filla b ``1)) pα) (fst (snd (comb b)) pα)) where
    A = \ x → fst (AB x)
    B = \ xa → snd (AB (fst xa)) (snd xa)

    filla : (b : _) (z : 𝟚) → _
    filla b z =  (dcomEl A z α (\ pα z → fst (t pα z)) (fst (fst b) , (\ pα → ap fst (snd b pα)))) 

    comb : (b : _) → _
    comb b = 
      (dcomEl (\ z → B (z , (fst (filla b z))))
              ``1 
              α (\ z pα →  transport (ElC o (B o \ h → (z , h))) (fst (snd (filla b z)) pα) (snd (t z pα)) )
                (transport (ElC o B o \ h → (``0 , h)) (snd (snd (filla b ``0)) id) (snd (fst b)) , 
                (\ pα → ap (transport (ElC o B o (λ h → ``0 , h)) (snd (snd (filla b ``0)) id)) (apd snd (snd b pα) ∘ ! (ap= (transport-ap-assoc' (λ z → ElC (B (``0 , z))) fst (snd b pα))) ) ∘ ap= (transport-∘ (ElC o B o (λ h → ``0 , h)) (snd (snd (filla b ``0)) id) (ap fst (snd b pα))) ∘ ap {M = (fst (snd (filla b ``0)) pα)} {N = (snd (snd (filla b ``0)) id ∘ ap fst (snd b pα))} (\ h → transport (ElC o B o (λ h → ``0 , h)) h (snd (t ``0 pα))) uip)))

  Σcode-cov-universal : ∀ {l :{♭} Level} 
                  → ΣDataCov l → UCov l
  Σcode-cov-universal {l} = code-cov ( (\ AB → Σcode-universal (ElCov (fst AB) , \ (x : _) → ElCov (snd AB x))) , 
                                       (relCov1-relCov Σ-from-data-cov covΣ) )

