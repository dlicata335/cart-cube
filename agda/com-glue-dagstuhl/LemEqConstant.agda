-- simplified lemma for coe_{hcom_U} from Dagsthul
-- show that coe is an equivalence in a simpler way, for a specific definition of equivalence

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
open import universe.Glue
open import universe.U
open import com-glue-dagstuhl.IsEquiv-FillRefl

module com-glue-dagstuhl.LemEqConstant where

  -- for CCHM take r=0, r'=1
  module Gen (r r' : I) where

    fillBackU : ∀ {l :{♭} Level} (z : I) (A : I → U {l}) → (b : El (A r')) → El (A z) [ _ ↦  _ ]
    fillBackU z A b = ((relCom-relCoe (El o A) (comEl' {Γ = I} A) (\ x → x) r' z) b)
    
    fillU : ∀ {l :{♭} Level} (z : I) (A : I → U {l}) → (b : El (A r)) → El (A z) [ _ ↦  _ ]
    fillU z A b = ((relCom-relCoe (El o A) (comEl' {Γ = I} A) (\ x → x) r z) b)
    
    coeBackU : ∀ {l :{♭} Level} (A : I → U {l}) → El (A r') → El (A r)
    coeBackU A b = fst (fillBackU r A b)
    
    
    lemeqConst : ∀ {l :{♭} Level} (A : I → U {l}) → isEquiv'FillRefl (coeBackU A)
    lemeqConst A {α} a b = (a~ ,
                            (((\ w → fst (final w)) ,
                                     ! (snd (snd (fill-b r)) id) ∘  ! (fst (snd (final `0)) (inl (inl id)))   ,
                                      ! (fst (snd (final `1)) (inl (inr id))) ))) ,
                           (\ pα → pair= ((fst (snd (fill-b r')) pα ∘  snd (fillBackU r' A (a pα)) id ))
                                         ( (pair= (λ= \ w →  (fst (snd (final w)) (inr pα)) ∘ ! (snd b pα) ∘
                                                           ap= (fst-transport-Path-right {a1 = coeBackU A} (fst (snd (fill-b r')) pα ∘  snd (fillBackU r' A (a pα)) id ) ((λ _ → fst b) , id , ! (snd b pα)))  )
                                                (pair= uip uip)) ) )
      where
      -- α "is" thA up-down direction in thA picturA (examplA was α = (x = 0) ∨ (x = 1)
      -- z is thA in-out-of-board direction in thA picture
      -- thA refls on f(a) arA thA left-right direction in thA picture
    
      -- back/front squares in picture
      fillBackα : (pα : α) (z : I) → El (A z) [ _ ↦ _ ] 
      fillBackα pα z = (fillBackU z A (a pα))
    
      -- left square in picture
      fill-b : (z : I) → El (A z) [ _ ↦ _ , _ ↦ _ ]
      fill-b z = comEl' A (\ x → x) r z
                        α (\ z pα → fst (fillBackα pα z))
                        (fst b , (\ pα → snd b pα)) 
    
      -- top of left squarA in picture
      a~ = (fst (fill-b r'))
    
      -- right squarA in picture
      fillBack-a~ : (z : I) → El (A z) [ _ ↦ _ ]
      fillBack-a~ z = fillBackU z A a~
    
      -- bottom squarA in picture, given as compositA of all "five" (two of thA fivA arA α)
      -- w is thA left-right direction in thA picture
      final : (w : I) → El (A r) [ _ ↦ _ , _ ↦ _ ]
      final w = comEl' A (\ x → x) r' r
                         (((w == `0) ∨ (w == `1)) ∨ α)
                         (\ z → case (case01 (\ w=0 → fst (fill-b z))
                                             (\ w=1 → fst (fillBack-a~ z)) )
                                     (\ pα → fst (fillBackα pα z))
                                     (∨-elim _ (\ w=0 pα → ! (fst (snd (fill-b z)) pα))
                                               (\ w=1 pα →  ap (\ h → fst (fillBackU z A h)) ( ! (snd (fillBackα pα r') id) ∘ ! (fst (snd (fill-b r')) pα) ) )
                                               (\ p q → abort (iabort (q ∘ ! p)))))
                         (a~ ,
                          ∨-elim _ (∨-elim _ (\ w=0 → id)
                                             (\ w=1 → ! (snd (fillBack-a~ r') id) )
                                             (\ _ _ → uip))
                                   (\ pα → fst (snd (fill-b r')) pα )
                                   (\ _ _ → uip) )


{-
  module IdEquiv (r : I) where

    module G = Gen r r

    idIsEquiv : {l :{♭} Level} {A : U {l} } → isEquiv'FillRefl (\ (x : El A) → x)
    idIsEquiv {A = A} a b = (transport (\ f → HFiber' f (fst b)) (λ= \ a → ! (snd (G.fillBackU r (\ _ → A) a) id)) (fst use) ) ,
                            (\ pα →  =HFiber' ({!OK!} ∘ ap fst (snd use pα)) {!!} ) where
      use = G.lemeqConst (\ _ → A) a (fst b , (\ pα → snd b pα ∘ ! (snd (G.fillBackU r (\ _ → A) (a pα)) id)))
-}
