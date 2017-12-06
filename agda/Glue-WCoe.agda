{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Path
open import Equiv
open import Cofibs
open import Kan
open import Glue
open import Glue-HCom
open import Glue-Weak

module Glue-WCoe where

  wcoe-isweq : {l1 l : Level} {Γ : Set l1}
        (α : Γ → Cofibs)
        (T : (x : Γ) → fst (α x) → Set l)
        (B : Γ → Set l)
        (f : (x : Γ) (u : fst (α x)) → T x u → B x) 
        (feq : (x : Γ) (u : fst (α x)) → isEquiv (T x u) (B x) (f x u))
        (comT : relCom (\ (p : Σ \ (x : Γ) → fst (α x)) → T (fst p) (snd p)))
        (comB : relCom B)
        → (relWCoe (GlueF α T B f)) 
  wcoe-isweq α T B f feq comT comB p r r' = 
    -- send b' over, invent something upstairs, and make a term out of it
    (\ g → glue-weak' (b' g) (\ pα → fst (feq (p r') pα (b' g)))) , 
    -- on r=r', make a path to g.  most of this is propositional reasoning
    (\ e g → ∘Path (hcom-Glue-fiberwise (p r')) -- FIXME: rewrite to avoid doing the composite in Glue? 
              (-- Path 1: η law
               glue-weak-η {α = (fst (α (p r')))} {{ (snd (α (p r'))) }} hcomB (⇒ g e) ∘= 
               -- propositional munging
               glue-weak= {α = (fst (α (p r')))} {{ (snd (α (p r'))) }} 
                            hcomB  _ _(λ x → g-in-fiber e g x) (Glue-to-fiber {{ cα = (snd (α (p r'))) }} (⇒ g e)) 
                            (b'-on-r=r' g e) (\ pα → g-in-fiber-eq e g pα))
              ( ( (-- Path 2:
               -- Path (HFiber (f (p r') pα) (b' g)) (fst (feq (p r') pα (b' g))) (g-in-fiber g pα e)
               -- from contractibility (plus some congruence)
                (\ x → glue-weak' (b' g) (\ pα →  fst ( (g-in-fiber-path g pα e) )  x)),
               ap (glue-weak' (b' g)) ((λ= \ pα →  fst (snd (g-in-fiber-path g pα e)) )) , 
               ap (glue-weak' (b' g)) ((λ= \ pα →  snd (snd (g-in-fiber-path g pα e)) )) )
              ) )) where

    -- unpacking things

    G = GlueF α T B f

    hcomB = relCom-hasHCom B comB (p r') 
    coeB = relCom-relCoe B comB

    hcom-Glue-fiberwise : (x : _) → _
    hcom-Glue-fiberwise x = hcomGlue _ {{ snd (α x) }} _ _ (f x)
                            ((\ u → relCom-hasHCom (\ (p : Σ \ (x : _) → fst (α x)) → T (fst p) (snd p)) comT (x , u)))
                            (relCom-hasHCom B comB x)
    
    glue-weak' : (b' : _) (t : (pα : _) → HFiber (f (p r') pα) b') → _ {- Glue r' -}
    glue-weak' b' q = glue-weak {{snd (α (p r'))}} hcomB b' q

    -- Step 1: make b'

    b' : (g : G (p r)) → _
    b' g = (fst (coeB p r r' (unglue g)))

    -- Step 2: on r=r' and α, the original g is in the fiber over b'(=unglue g) at r'(=r)
    g-in-fiber : (e : r == r') 
                 (g : G (p r))
                 (pα : fst (α (p r'))) → HFiber (f (p r') pα) (b' g)
    g-in-fiber id g pα = transport (HFiber _) (snd (coeB p r r' (unglue g)) id)
                         (Glue-to-fiber {{ cα = snd (α (p r')) }} {f = (f _)} g pα) 

    -- Step 3: on r=r' and α, path comparing sending (b' g) up using the equivalence and g itself
    -- that we get from contractibility
    g-in-fiber-path : (g : _) (pα : _) (r=r' : _) 
                    → Path (HFiber (f (p r') pα) (b' g)) (fst (feq (p r') pα (b' g))) (g-in-fiber r=r' g pα)
    g-in-fiber-path g pα r=r' = (snd (feq (p r') pα (b' g)) (g-in-fiber r=r' g pα))


    -- propositional equality junk

    b'-on-r=r' : (g : G (p r)) (r=r' : r == r') → b' g == unglue (transport (G o p) r=r' g)
    b'-on-r=r' g id = ! ((snd (coeB p r r' (unglue g))) id)
  
    g-in-fiber-eq : (e : r == r') 
                 (g : Glue _ {{ snd (α (p r)) }} _ _ _)
                 (pα : fst (α (p r'))) 
                 → (g-in-fiber e g pα) =h (Glue-to-fiber {{ cα = snd (α (p r')) }} {f = (f _)} (⇒ g e) pα) 
    g-in-fiber-eq id g pα = transport-=h _ (snd (coeB p r r (unglue g)) id)


{-
  -- FIXME: can we inline aligning?
  -- even if we make the wcoe correct on α, it seems like the coe-from-wcoe gets in the way

  -- only used for the aligning, which is currently unused

    t' : (g : _) (pα : (x : I) → fst (α (p x))) → HFiber (f (p r') (pα r')) (b' g)
    t' g pα = (fst (coeT (\ x → p x , pα x) r r' 
                        ((coe (Glue-α _ {{ snd (α (p r)) }} _ _ _ (pα r)) g)))) , 
              (( (ap (\ x → (fst (coeB p r r' x))) (unglue-α g (pα _))) ) =∘ 
               (f-natural {_} {\ x → T (p x) (pα x)} {B o p} (\x → f (p x) (pα x)) 
                                (coeT (\ w → (p w , pα w)))
                                (\ q → comB (p o q)) r r' 
                                ((coe (Glue-α (fst (α (p r))) {{ snd (α (p r)) }} (λ v → T (p r) v) (B (p r)) (λ v v₁ → f (p r) v v₁) (pα r)) g))))
-}




