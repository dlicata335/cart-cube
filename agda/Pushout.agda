{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Kan
open import Path
open import Prop

module Pushout where


  postulate
    Pushout : {l : Level} (C : Set l) (A : Set l) (B : Set l) (f : C → A) (g : C → B) → Set l

  module PushoutRules {l : Level} {C : Set l} {A : Set l} {B : Set l} {f : C → A} {g : C → B} where
    P = Pushout C A B f g

    postulate 
      Inl : A → P
      Inr : B → P
      glue : (c : C) → I → P
      glue0 : (c : C) → glue c `0 == Inl (f c)
      glue1 : (c : C) → glue c `1 == Inr (g c)
    {-# REWRITE glue0 #-}
    {-# REWRITE glue1 #-}
    postulate
      fcomPush : hasHCom P

      Push-elim : {l' : Level} 
                (D : P → Set l')
              → (comD : relCom D)
              → (l : (a : A) → D (Inl a))
              → (r : (b : B) → D (Inr b))
              → ((c : C) → PathO (\ x → D(glue c x)) (l (f c)) (r (g c)))
              → (x : P) → D x
      Push-elim-l : {l' : Level} 
                (D : P → Set l')
              → (comD : relCom D)
              → (l : (a : A) → D (Inl a))
              → (r : (b : B) → D (Inr b))
              → (g : (c : C) → PathO (\ x → D(glue c x)) (l (f c)) (r (g c)))
              → (a : A) → Push-elim D comD l r g (Inl a) == l a
      Push-elim-r : {l' : Level} 
                (D : P → Set l')
              → (comD : relCom D)
              → (l : (a : A) → D (Inl a))
              → (r : (b : B) → D (Inr b))
              → (g : (c : C) → PathO (\ x → D(glue c x)) (l (f c)) (r (g c)))
              → (b : B) → Push-elim D comD l r g (Inr b) == r b
      Push-elim-g : {l' : Level} 
                (D : P → Set l')
              → (comD : relCom D)
              → (l : (a : A) → D (Inl a))
              → (r : (b : B) → D (Inr b))
              → (g : (c : C) → PathO (\ x → D(glue c x)) (l (f c)) (r (g c)))
              → (c : C) (x : I) → Push-elim D comD l r g (glue c x) == fst (g c) x
    {-# REWRITE Push-elim-l #-}
    {-# REWRITE Push-elim-r #-}
    {-# REWRITE Push-elim-g #-}
    postulate
      Push-elim-fcom : {l' : Level} 
                (D : P → Set l')
              → (comD : relCom D)
              → (l : (a : A) → D (Inl a))
              → (r : (b : B) → D (Inr b))
              → (g : (c : C) → PathO (\ x → D(glue c x)) (l (f c)) (r (g c)))
              → Strictly-Preserves-HCom P D fcomPush comD (Push-elim D comD l r g)

  open PushoutRules

  wcoePush : {l l' : Level} {Γ : Set l'} (C : Γ → Set l) (A : Γ → Set l) (B : Γ → Set l) (f : (x : Γ) → C x → A x) (g : (x : Γ) → C x → B x)
           → relCom A
           → relCom B
           → relCoe C
           → relWCoe (\ x → Pushout (C x) (A x) (B x) (f x) (g x))
  wcoePush C A B f g comA comB coeC p r r' = 
            (wcoe-f r') , 
            (\ {id → \ b → !Path fcomPush (wcoe-path b) }) where -- FIXME optimize the ! -- could combine with making the strict coe

    PF = (\ x → Pushout (C x) (A x) (B x) (f x) (g x))

    fixa : (r' : _) (c : _) → _
    fixa r' c = (f-natural (\ x → f (p x)) ((coePre p C coeC (\ x → x))) (comPre p A comA) r r' c) 

    fixb : (r' : _) (c : _) → _
    fixb r' c = (f-natural (\ x → g (p x)) (((coePre p C coeC (\ x → x)))) (comPre p B comB) r r' c) 

    fixglue-fill : (r' : _) (w : I) (c : _) (z : _) → _
    fixglue-fill r' w c z = 
        (fcomPush `0 w ((z == `0) ∨ (z == `1)) 
                       (\ x → case (\ z=0 → Inl (fst (fst (fixa r' c)) x ))
                                   (\ z=0 → Inr (fst (fst (fixb r' c)) x ))
                                   (\ p q → abort (iabort (q ∘ ! p)))) 
                       (glue (fst (coeC p r r' c)) z  , 
                         ∨-elim _ (\ z=0 → ap (glue (fst (coeC p r r' c))) (! z=0) ∘ ap Inl (fst (snd (fst (fixa r' c)))) )
                                  ((\ z=0 → ap (glue (fst (coeC p r r' c))) (! z=0) ∘ ap Inr (fst (snd (fst (fixb r' c)))) ))
                                  (\ _ _ → uip)))
                                                 
    wcoe-f : (r' : I) → _
    wcoe-f r' = 
         (Push-elim (\ _ → PF (p r'))
                     (relCom-constant _ fcomPush)
                     (\ a → Inl (fst (relCom-relCoe A comA p r r' a))) 
                     (\ b → Inr (fst (relCom-relCoe B comB p r r' b)))
                     (\ c → (\ z → fst (fixglue-fill r' `1 c z) ),
                                    ap Inl (snd (snd (fst (fixa r' c)))) ∘ ! (fst (snd (fixglue-fill r' `1 c `0)) (inl id)) , 
                                    ap Inr (snd (snd (fst (fixb r' c)))) ∘ ! (fst (snd (fixglue-fill r' `1 c `1)) (inr id)) ))

    wcoe-path : (b : PF (p r)) → Path (PF (p r)) b (wcoe-f r b)
    wcoe-path = Push-elim (\ b → Path (PF (p r)) b (wcoe-f r b)) 
                          (comPath-endpoints (\ x → x) (wcoe-f r) fcomPush) 
                          (\ a → (\ _ → Inl a) , id , ap Inl ((snd (relCom-relCoe A comA p r r a)) id)) 
                          (\ b → (\ _ → Inr b) , id , ap Inr ((snd (relCom-relCoe B comB p r r b)) id))
                          (\ c → (\ x → ( \ y → fst (fixglue-fill r y c x)) , 
                                         ap (\ h → glue h x) (! (snd (coeC p r r c) id))  ∘ ! (snd (snd (fixglue-fill r `0 c x)) id) , 
                                         id ) , 
                                  pair= (λ= \ x → ap Inl (ap= (! (ap fst (snd (fixa r c) id)))) ∘ ! (fst (snd (fixglue-fill r x c `0)) (inl id))) (pair= uip uip)  , 
                                  pair= (λ= \ x → ap Inr ((ap= (! (ap fst (snd (fixb r c) id))))) ∘ ! (fst (snd (fixglue-fill r x c `1)) (inr id))) (pair= uip uip) )

