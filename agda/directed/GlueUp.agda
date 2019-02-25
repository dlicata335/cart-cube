{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Kan
open import Path
open import Prop
open import Strictify

module directed.GlueUp where 

  private 

    postulate
      StrictPushout : {l1 l2 l3 : Level} (C : Set l1) (A : Set l2) (B : Set l3)
                      (f : C → A) (g : C → B) → Set (l1 ⊔ l2 ⊔ l3)

    module _ {l1 l2 l3 : Level} {C : Set l1} {A : Set l2} {B : Set l3}
              {f : C → A} {g : C → B} where
      P = StrictPushout C A B f g
      postulate 
        SPinl : A → P
        SPinr : B → P
        SPglue : (c : C) → SPinl (f c) == SPinr (g c)
        SPelim : {l : Level} (D : P → Set l)
                 (l : (a : A) → D (SPinl a))
                 (r : (b : B) → D (SPinr b))
                 (g : (c : C) → transport D (SPglue c) (l (f c)) == r (g c))
                 → (p : P) → D p
        SPβ1 : {l : Level} (D : P → Set l)
                 (l : (a : A) → D (SPinl a))
                 (r : (b : B) → D (SPinr b))
                 (g : (c : C) → transport D (SPglue c) (l (f c)) == r (g c))
                 → (a : A) → SPelim D l r g (SPinl a) == l a
        {-# REWRITE SPβ1 #-}
        SPβ2 : {l : Level} (D : P → Set l)
                 (l : (a : A) → D (SPinl a))
                 (r : (b : B) → D (SPinr b))
                 (g : (c : C) → transport D (SPglue c) (l (f c)) == r (g c))
                 → (b : B) → SPelim D l r g (SPinr b) == r b
        {-# REWRITE SPβ2 #-}

    NonStrictPushS :  ∀ {l} (α : Set)
            {{_ : Cofib α}}
            (T : α → Set l)
            (B : Set l)
            (f : (u : α) → B → T u) → Set l
    NonStrictPushS α T B f = StrictPushout (α × B) B (Σ \ (pα : α) → T pα) snd (\ pαb → fst pαb , f (fst pαb) (snd pαb))
    
    NonStrictPushSIso :  ∀ {l} (α : Set)
            {{_ : Cofib α}}
            (T : α → Set l)
            (B : Set l)
            (f : (u : α) → B → T u) 
         → (pα : α) → Iso (NonStrictPushS α T B f) (T pα)
    NonStrictPushSIso α {{ cα }} T B f pα = 
      iso (SPelim (\ _ → T pα) (\ b → f pα b )
                               (\ q → transport T (Cofib.eq cα _ _) (snd q))
                               (\ c  → ! (apd (\ H → f H (snd c)) (Cofib.eq cα (fst c) pα)) ∘ ap= (transport-constant  (SPglue c))))
          (\ q → SPinr (pα , q) )
          (SPelim _ (\ b → ! (SPglue (pα , b)))
                    (\ b → ap SPinr (pair= (Cofib.eq cα pα (fst b))
                                           (ap (\ H → transport T H (snd b)) (uip {p = (Cofib.eq cα pα (fst b) ∘ Cofib.eq cα (fst b) pα)} {q = id}) ∘ ! (ap= (transport-∘ T (Cofib.eq cα pα (fst b)) (Cofib.eq cα (fst b) pα))))))
                    ( \_ → uip))
          (λ x → ap (\ h → transport T h x) (uip {p = (Cofib.eq cα pα pα)} {id}))


  
    module MakePushS {l} (α : Set) {{cα : Cofib α}} (T : α → Set l) (B : Set l) (f : (u : α) → B → T u) where

      Strict : Σ (λ (B' : Set l [ α ↦ T ]) → Iso (NonStrictPushS α T B f) (fst B') [ α ↦ (λ pα → eqIso (snd B' pα) ∘iso NonStrictPushSIso α T B f pα) ])
      Strict = (strictify T (NonStrictPushS α T B f) (NonStrictPushSIso α T B f)) 
      
      -- for some reason if all of thisis in n abstract block then it doesn't expand PushS ?  seems like a bug
      
      PushS : Set l
      PushS = fst (fst Strict)
      
      PushS-α : (u : α) → PushS == T u
      PushS-α pα = ! ((snd (fst Strict) ) pα) 
      
      PushS-in : B → PushS
      PushS-in b = Iso.f (fst (snd Strict)) (SPinl b)
      
      PushS-in-α : (b : B) (pα : α) → (PushS-in b) ==  coe (! (PushS-α pα)) (f pα b)  
      PushS-in-α b pα = ((ap (\ H → coe H (f pα  b)) (uip {p = snd (fst Strict) pα} {q = (! (PushS-α pα))})) )
                         ∘ ! (ap (\ h → Iso.f h (SPinl b)) (snd (snd Strict) pα)) where
        eq : SPinl {C = (α × B)} {B} {(Σ \ (pα : α) → T pα)} {snd} {(\ pαb → fst pαb , f (fst pαb) (snd pαb))} b
          == SPinr (pα , f pα b) 
        eq = SPglue ((pα , b))

      adjust : (q : Σ T) → coe (! (PushS-α (fst q))) (snd q) == Iso.f (fst (snd Strict)) (SPinr q)
      adjust q = (ap (\ H → Iso.f H (SPinr q)) (snd (snd Strict) (fst q)) ∘
                  ap (coe (snd (fst Strict) (fst q))) (ap (\ h → transport T h (snd q)) (uip {p = id} {q = (Cofib.eq cα (fst q) (fst q))}))
                  ∘ ap (\ H → coe H  (snd q)) (uip {p = (! (PushS-α (fst q)))} {q = snd (fst Strict) (fst q)})  )

      PushS-elim' : ∀ {l2}
             → (D : PushS → Set l2)
             → (d : (b : B) → D (PushS-in b))
             → (dα : (pα : α) (t : T pα) → D (coe (! (PushS-α pα)) t))
             → ((pα : α) (b : B) → d b == transport D (! (PushS-in-α b pα)) (dα pα (f pα b)))
             → (g : (NonStrictPushS α T B f)) → D (Iso.f (fst (snd Strict)) g)
      PushS-elim' D d dα eq = SPelim _ d
                                     (\ q → transport D
                                            (adjust q)
                                            (dα (fst q) (snd q)))
                                     (\ q → (( ap (\ H → transport D H (dα (fst q) (f (fst q) (snd q))))
                                                 (uip {p = (ap (λ z → Iso.f (fst (snd Strict)) z) (SPglue q) ∘ ! (PushS-in-α (snd q) (fst q)))}
                                                      {q = (ap (λ H → Iso.f H (SPinr (fst q , f (fst q) (snd q)))) (snd (snd Strict) (fst q)) ∘ ap (coe (snd (fst Strict) (fst q))) (ap (λ h → transport T h (f (fst q) (snd q))) (uip {p = id} {q = (Cofib.eq cα (fst q) (fst q))})) ∘ ap (λ H → coe H (f (fst q) (snd q))) (uip {p = (! (PushS-α (fst q)))} {q = snd (fst Strict) (fst q)}))} )
                                             ∘ ! (ap= (transport-∘ D (ap (λ z → Iso.f (fst (snd Strict)) z) (SPglue q)) (! (PushS-in-α (snd q) (fst q)))) {(dα (fst q) (f (fst q) (snd q)))})) ∘
                                             (ap= (transport-ap-assoc' D (λ z → (Iso.f (fst (snd Strict)) z)) (SPglue q)) ))
                                             ∘ ap (transport (λ z → D (Iso.f (fst (snd Strict)) z)) (SPglue q)) (eq (fst q) (snd q)) )
      
      PushS-elim : ∀ {l2}
             → (D : PushS → Set l2)
             → (d : (b : B) → D (PushS-in b))
             → (dα : (pα : α) (t : T pα) → D (coe (! (PushS-α pα)) t))
             → ((pα : α) (b : B) → d b == transport D (! (PushS-in-α b pα)) (dα pα (f pα b)))
             → (g : PushS) → D g
      PushS-elim D d dα eq g = transport D (Iso.fg (fst (snd Strict)) g)
                                 (PushS-elim' D d dα eq (Iso.g (fst (snd Strict)) g))
      
      PushS-elim-α : ∀ {l2}
             → (D : PushS → Set l2)
             → (d : (b : B) → D (PushS-in b))
             → (dα : (pα : α) (t : T pα) → D (coe (! (PushS-α pα)) t))
             → (eq : (pα : α) (b : B) → d b == transport D (! (PushS-in-α b pα)) (dα pα (f pα b)))
             → (pα : α)
             → (t : T pα)
             → PushS-elim D d dα eq ((coe (! (PushS-α pα)) t)) == dα pα t
      PushS-elim-α D d dα eq pα t =
        ap= (transport-inv D (adjust (pα , t))) ∘
        ap (transport D (! (adjust (pα , t)))) (apd (\ h → (PushS-elim' D d dα eq h)) eq') ∘
        ! (((ap (\ H → transport D H (PushS-elim' D d dα eq (Iso.g (fst (snd Strict)) (coe (! (PushS-α pα)) t))))
               (uip {p = (! (adjust (pα , t)) ∘ ap (λ z → Iso.f (fst (snd Strict)) z) eq')} {q = (Iso.fg (fst (snd Strict)) (coe (! (PushS-α pα)) t))})
        ∘ ! (ap= (transport-∘ D (! (adjust (pα , t))) (ap (λ z → Iso.f (fst (snd Strict)) z) eq')))) ∘
        ap (transport D (! (adjust (pα , t)))) (ap= (transport-ap-assoc' D (λ z → (Iso.f (fst (snd Strict)) z)) eq')))) where
          eq' : Iso.g (fst (snd Strict)) (coe (! (PushS-α pα)) t) == SPinr (pα , t)
          eq' = ap (\ h → SPinr (pα , h)) (ap= (transport-inv-2 (\ X → X) (PushS-α pα))) ∘ ! (ap= (ap Iso.g (snd (snd Strict) pα)))
      
      PushS-elim-in : ∀ {l2}
             → (D : PushS → Set l2)
             → (d : (b : B) → D (PushS-in b))
             → (dα : (pα : α) (t : T pα) → D (coe (! (PushS-α pα)) t))
             → (eq : (pα : α) (b : B) → d b == transport D (! (PushS-in-α b pα)) (dα pα (f pα b)))
             → (b : B)
             → PushS-elim D d dα eq (PushS-in b) == d b
      PushS-elim-in D d dα eq b =
        (apd (PushS-elim' D d dα eq) (Iso.gf (fst (snd Strict)) (SPinl b))) ∘
        ! (ap= (transport-ap-assoc' D (λ z → (Iso.f (fst (snd Strict)) z)) (Iso.gf (fst (snd Strict)) (SPinl b))))
        ∘ ap (\ H → transport D H (PushS-elim' D d dα eq (Iso.g (fst (snd Strict)) (PushS-in b))))
              (uip {p = (Iso.fg (fst (snd Strict)) (PushS-in b)) } {q = (ap (λ z → Iso.f (fst (snd Strict)) z)
        (Iso.gf (fst (snd Strict)) (SPinl b)))}) 


  -- public interface: all abstract

  module _ {l} (α : Set) {{cα : Cofib α}} (T : α → Set l) (B : Set l) (f : (u : α) → B → T u) where

     private module M = MakePushS α T B f

     abstract
  
       PushS : Set l
       PushS = M.PushS

       PushS-α : (u : α) → PushS == T u
       PushS-α = M.PushS-α 
  
       PushS-in : B → PushS
       PushS-in = M.PushS-in
  
       PushS-in-α : (b : B) (pα : α) → (PushS-in b) ==  coe (! (PushS-α pα)) (f pα b)  
       PushS-in-α = M.PushS-in-α
  
       PushS-elim : ∀ {l2}
            → (D : PushS → Set l2)
            → (d : (b : B) → D (PushS-in b))
            → (dα : (pα : α) (t : T pα) → D (coe (! (PushS-α pα)) t))
            → ((pα : α) (b : B) → d b == transport D (! (PushS-in-α b pα)) (dα pα (f pα b)))
            → (g : PushS) → D g
       PushS-elim = M.PushS-elim

       PushS-elim-α : ∀ {l2}
            → (D : PushS → Set l2)
            → (d : (b : B) → D (PushS-in b))
            → (dα : (pα : α) (t : T pα) → D (coe (! (PushS-α pα)) t))
            → (eq : (pα : α) (b : B) → d b == transport D (! (PushS-in-α b pα)) (dα pα (f pα b)))
            → (pα : α)
            → (t : T pα)
            → PushS-elim D d dα eq ((coe (! (PushS-α pα)) t)) == dα pα t
       PushS-elim-α = M.PushS-elim-α

       PushS-elim-in : ∀ {l2}
            → (D : PushS → Set l2)
            → (d : (b : B) → D (PushS-in b))
            → (dα : (pα : α) (t : T pα) → D (coe (! (PushS-α pα)) t))
            → (eq : (pα : α) (b : B) → d b == transport D (! (PushS-in-α b pα)) (dα pα (f pα b)))
            → (b : B)
            → PushS-elim D d dα eq (PushS-in b) == d b
       PushS-elim-in = M.PushS-elim-in
       {-# REWRITE PushS-elim-in #-}

       
