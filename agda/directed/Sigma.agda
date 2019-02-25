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
open import directed.Segal
open import directed.Covariant
open import directed.SegalDepCovariant
open import directed.UCov
open import universe.Sigma

module directed.Sigma where

  dhcomSigma : ∀ {l1 l2 : Level} {A : Set l1} (B : A → Set l2)
             → hasDHCom A
             → relCov B
             → hasDHCom (Σ \ (x : A) → B x)
  dhcomSigma B dhcomA dcomB xy h α t =
    ((fst (cA xy) , fst cB )),
    (\ l → pair= (fst (snd (cA xy)) l) (fst (snd cB) l)) ,
    (\ pα → pair= (snd (snd (cA xy)) pα) (snd (snd cB) pα)) where

    cA : (xy : Δ₂) → _
    cA =  \ xy → dhcomA xy
                        (\ xy l → fst (h xy l))
                        α
                        (\ xy pα → fst (fst (t xy pα)) ,
                        (\ l →  ap fst ((snd (t xy pα)) l) ))

    cB = decompose-relDCom₂ B dcomB
          (\ xy → fst (cA xy))
          xy
          (\ xy l → transport B (fst (snd (cA xy)) l) (snd (h xy l)))
          α
          (\ xy pα →  transport B ((snd (snd (cA xy)) pα)) (snd (fst (t xy pα)))  ,
                      (λ l → ap (transport B (snd (snd (cA xy)) pα)) (apd snd (snd (t xy pα) l)) ∘
                      ! (ap (transport B (snd (snd (cA xy)) pα)) (ap= (transport-ap-assoc' B fst (snd (t xy pα) l))))
                      ∘ ap= (transport-∘ B (snd (snd (cA xy)) pα) (ap fst (snd (t xy pα) l)))
                      ∘ ap (\ x → transport B x (snd (h xy l))) (uip {p = (fst (snd (cA xy)) l)} {q = (snd (snd (cA xy)) pα ∘ ap fst (snd (t xy pα) l))})  ))
