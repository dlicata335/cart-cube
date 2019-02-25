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
open import directed.Covariant 

module directed.Chaotic where


chaotic : ∀{i} → Set i → Set i
chaotic A = (x y : A) → Contractible (Hom A x y)

-- needs better name
chBox : ∀{i} → Set i → Set _
chBox A = (i : 𝟚)
          (h : (i : 𝟚) → ∂ i → A)
          (α : Set) {{cα : Cofib α }}
          (t : (i : 𝟚) → α → A [ ∂ i ↦ h i ])
        → A [ ∂ i ↦ h i , α ↦ fst o t i ]

chBox-to-chaotic : ∀{i} → (A : Set i) → chBox A → chaotic A
chBox-to-chaotic A cboxA x y = ((λ i → fst (f i)) , ! (fst (snd (f ``0)) (inl id)) , ! (fst (snd (f ``1)) (inr id)))
                             , (λ p → (λ j → (λ i → fst (u p i j)) , !(fst (snd (u p ``0 j)) (inl id)) , !(fst (snd (u p ``1 j)) (inr id)))
                                      , pair= (λ= λ j → !(snd (snd (u p j `0)) (inl id))) (pair= uip uip)
                                      , pair= (λ= λ j → !(snd (snd (u p j `1)) (inr id))) (pair= uip uip)) where
  f : ∀ i → _
  f i = cboxA i (λ _ → cased01 (λ _ → x) (λ _ → y)) ⊥ (λ _ → abort)

  u : ∀(p : Hom _ x y) i j → _
  u p i j = cboxA i (λ _ → cased01 (λ _ → x) (λ _ → y)) ((j == `0) ∨ (j == `1))
                    (λ i → case01 (λ _ → fst (f i) , fst (snd (f i)))
                                  (λ _ → fst p i   , ∨-elimd01 _ (λ i=0 → ap (fst p) (! i=0) ∘ !(fst (snd p)))
                                                                 (λ i=1 → ap (fst p) (! i=1) ∘ !(snd (snd p)))))

chaotic-to-chBox : ∀{i} → (A : Set i) → hasHCom A → chaotic A → chBox A
chaotic-to-chBox A hcomA chA i h α t = fst (fix i)
                               , ∨-elimd01 _ (λ i=0 → (fst (snd (fix i))) (inr (inl i=0)))
                                             (λ i=1 → (fst (snd (fix i))) (inr (inr i=1)))
                               , (λ pα → (coe (ap (λ x → fst x i == fst (fix i)) (snd (snd (snd f (t' pα))))) (fst (snd (fix i)) (inl pα)))) where

  f : _
  f = chA (h ``0 (inl id)) (h ``1 (inr id))

  t' : ∀ pα → Hom A (h ``0 (inl id)) (h ``1 (inr id))
  t' pα = (λ i → fst (t i pα)) , ! (snd (t ``0 pα) (inl id)) , ! (snd (t ``1 pα) (inr id))

  fix : ∀ i → _
  fix i = hcomA `0 `1 (α ∨ ((i == ``0) ∨ (i == ``1)))
           (λ j → case (λ pα → fst (fst ((snd f) (t' pα)) j) i)
                       (cased01 (λ i=0 → h i (inl i=0))
                                (λ i=1 → h i (inr i=1)))
                       (λ pα → ∨-elimd01 _ (λ i=0 → transport (λ{(i , eq) → fst (fst (snd f (t' pα)) j) i ==  h i (inl eq)}) {``0 , id} {i , i=0} (pair= (! i=0) uip) (fst (snd (fst (snd f (t' pα)) j))))
                                           (λ i=1 → transport (λ{(i , eq) → fst (fst (snd f (t' pα)) j) i ==  h i (inr eq)}) {``1 , id} {i , i=1} (pair= (! i=1) uip) (snd (snd (fst (snd f (t' pα)) j))))))
            (fst (fst f) i , ∨-elim _ (λ pα → ap (λ f → fst f i) (fst (snd (snd f (t' pα)))))
                                      (∨-elimd01 _ (λ i=0 → transport (λ{(i , eq) → h i (inl eq) == fst (fst f) i}) {``0 , id} {i , i=0} (pair= (! i=0) uip) (! (fst (snd (fst f)))))
                                                   (λ i=1 → transport (λ{(i , eq) → h i (inr eq) == fst (fst f) i}) {``1 , id} {i , i=1} (pair= (! i=1) uip) (! (snd (snd (fst f))))))
                                      (λ _ _ → uip)) 

-- needs better name
hasChFill : ∀ {i} → (𝟚 → Set i) → Set _
hasChFill A = (chA : (x : 𝟚) → chBox (A x))
            (a0 : A ``0)
            (a1 : A ``1)
            → HomO A a0 a1


relChFill : ∀ {l1 l2} {Γ : Set l1} → (Γ → Set l2) → Set _
relChFill {Γ = Γ} A = (p : 𝟚 → Γ) → hasChFill (A o p)

          
chBox-Π : ∀{l1 l2}
  {A : Set l1}
  {B : A → Set l2}
  (_ : (x : A) → chBox (B x))
  →
  chBox ((x : A) → B x)
chBox-Π ch i h α t = (λ x → fst (f x)) , (λ e → λ= λ x → fst (snd (f x)) e) , (λ pα → λ= λ x → snd (snd (f x)) pα) where

  f : ∀ x → _
  f x = ch x i (λ i e → h i e x) α (λ i pα → fst (t i pα) x , (λ e → ap (λ f → f x) (snd (t i pα) e)))


chFill-Π : ∀{l1 l2 l3}
  {Γ : Set l1}
  {A : Γ → Set l2}
  {B : Σ A → Set l3}
  (chA : relChFill A)
  (chB : relChFill B)
  →
  relChFill (λ x → (a : A x) → B (x , a))
chFill-Π {A = A} {B} chA chB p = {!!}


module isEquivForall {l :{♭} Level} (A B : 𝟚 → Set l) (p : (x : 𝟚) → A x → B x )where

  fall : ((x : 𝟚) → A x) → ((x : 𝟚) → B x)
  fall f x = p x (f x)

  lemma1 : isEquiv _ _ fall
         → (x : 𝟚) (y : B x) → Contractible (HFiber (p x) y)
  lemma1 iseq x y = ({!iseq stuck !} , {!!}) , {!!}

  lemma2 : ((x : 𝟚) → isEquiv _ _ (p x))
         → isEquiv _ _ fall
  lemma2 input f = ((\ x → fst (fst (input x (f x)))) ,
                          (\ z → \ x → fst (snd (fst (input x (f x)))) z ) ,
                                       (λ= \ x → fst (snd (snd (fst (input x (f x)))))) , λ= \ x → snd (snd (snd (fst (input x (f x)))))) ,
                   (\ b → (\ z → (\ x → fst (fst (snd (input x (f x)) ((fst b x) , (\ y → fst (snd b) y x) ,  ap= (fst (snd (snd b))) {x} , ap= (snd (snd (snd b))) {x})) z)) ,
                                 (\ y → \ x → fst (snd (fst (snd (input x (f x)) ((fst b x) , (\ y → fst (snd b) y x) ,  ap= (fst (snd (snd b))) {x} , ap= (snd (snd (snd b))) {x})) z)) y ) ,
                                        (λ= \ x → fst (snd (snd (fst (snd (input x (f x)) (fst b x , (λ y → fst (snd b) y x) , ap= (fst (snd (snd b))) , ap= (snd (snd (snd b))))) z)))) ,
                                        (λ= \ x → snd (snd (snd (fst (snd (input x (f x)) (fst b x , (λ y → fst (snd b) y x) , ap= (fst (snd (snd b))) , ap= (snd (snd (snd b))))) z))))) ,
                      =HFiber (λ= \ x → ap fst (fst (snd (snd (input x (f x)) (fst b x , (λ y → fst (snd b) y x) , ap= (fst (snd (snd b))) , ap= (snd (snd (snd b))))))))
                              (λ= \ y → λ= \ x → ap= (ap (\ x → fst (snd x)) (fst (snd (snd (input x (f x)) (fst b x , (λ y → fst (snd b) y x) , ap= (fst (snd (snd b))) , ap= (snd (snd (snd b)))))))) {y}) ,
                      =HFiber (λ= \ x → ap fst (snd (snd (snd (input x (f x)) (fst b x , (λ y → fst (snd b) y x) , ap= (fst (snd (snd b))) , ap= (snd (snd (snd b))))))) )
                              (λ= \ y → λ= \ x →  ap= (ap (\ x → fst (snd x)) (snd (snd (snd (input x (f x)) (fst b x , (λ y → fst (snd b) y x) , ap= (fst (snd (snd b))) , ap= (snd (snd (snd b)))))))) {y} ))

  lemma3 : ((x : 𝟚) → isEquiv _ _ (p x))
         → ( (f : (x : 𝟚) → B x) (x : 𝟚) → Contractible (HFiber (p x) (f x)))
  lemma3 fiberwiseeq f x = fiberwiseeq x (f x)

  lemma4 : ( (f : (x : 𝟚) → B x) (x : 𝟚) → Contractible (HFiber (p x) (f x)))
         → ((x : 𝟚) → isEquiv _ _ (p x))
  lemma4 input x b = {! input {!stuck!} x !}

  lemma5 : isEquiv _ _ fall
         → ( (f : (x : 𝟚) → B x) (x : 𝟚) → Contractible (HFiber (p x) (f x)))
  lemma5 input f x = (fst (fst (input f)) x ,
                      (\ z → fst (snd (fst (input f))) z x) , {!!} , {!!}) ,
                      (\ b → (\ z → (fst (fst (snd (input f) {!STUCK?!}) z) x ) , {!!}) , {!!} , {!!})  

  lemma6 : ( (f : (x : 𝟚) → B x) (x : 𝟚) → Contractible (HFiber (p x) (f x)))
         → isEquiv _ _ fall
  lemma6 input f = ((\ x → fst (fst (input f x))) , (\ z → \ x → fst (snd (fst (input f x))) z) , {!!} , {!!}) ,
                   (\ b → (\ z → (\ x → fst (fst (snd (input f x) (fst b x , (\ y → fst (snd b) y x) , {!!} , {!!})) z)) ,
                                 (\ y → \ x → fst (snd (fst (snd (input f x) (fst b x , (\ y → fst (snd b) y x) , {!!} , {!!})) z)) y) , {!!} , {!!}) ,
                          {!!} , {!!})
