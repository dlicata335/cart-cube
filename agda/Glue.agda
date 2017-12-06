{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Kan
open import Path
open import Prop

module Glue where 

  private 

    postulate
      -- Orton-Pitts Axiom 9
      strictify : {l : Level} {α : Set} {{ cα : Cofib α}} (A : α → Set l) (B : Set l)
                → (i : (pα : α) → Iso B (A pα))
                → Σ \ (B' : Set l [ α ↦ A ]) → Iso B (fst B') [ α ↦ (\ pα → eqIso (snd B' pα) ∘iso i pα  ) ]

    NonStrictGlue :  ∀ {l} (α : Set)
            {{_ : Cofib α}}
            (T : α → Set l)
            (B : Set l)
            (f : (u : α) → T u → B) → Set l
    NonStrictGlue α T B f = Σ \ (t : (pα : α) → T pα) → B [ α ↦ (\ pα → f pα (t pα)) ]

    NonStrictGlueIso :  ∀ {l} (α : Set)
            {{_ : Cofib α}}
            (T : α → Set l)
            (B : Set l)
            (f : (u : α) → T u → B) 
         → (pα : α) → Iso (NonStrictGlue α T B f) (T pα)
    NonStrictGlueIso α {{ cα }} T B f pα = 
      iso (\ g → fst g pα) 
       (\ t → (\ _ → transport T (Cofib.eq cα _ _) t) , 
              (f pα t , (\ pα' → ! (het-to-hom (apdo2 f (Cofib.eq cα pα pα') (!h (transport-=h T (Cofib.eq cα pα pα')))))))) 
       (\ g → pair= (λ= \ z → apd (fst g) (Cofib.eq cα pα z)) 
                    (pair= (snd (snd g) pα ∘ fst-transport-Σ {B = \ (h : _) (b : B) → (pα : α) → f pα (h pα) == b} (λ= (λ z → apd (fst g) (Cofib.eq cα pα z))) _ ) (λ= \ _ → uip))) 
       (\ t → ap= (ap {M = (Cofib.eq cα pα pα)} {N = id} (transport T) (uip)))

  -- the types in this abstract block
  -- are the public interface to Glue; the implementation is private
  abstract
    Glue : ∀ {l} (α : Set)
           {{_ : Cofib α}}
           (T : α → Set l)
           (B : Set l)
           (f : (u : α) → T u → B) → Set l
    Glue α T B f = fst (fst (strictify T (NonStrictGlue α T B f) (NonStrictGlueIso α T B f)))

    Glue-α : ∀ {l} (α : Set) {{_ : Cofib α}} (T : α → Set l) (B : Set l) (f : (u : α) → T u → B)
           → (u : α) → Glue α T B f == T u
    Glue-α α T B f pα = ! ((snd (fst (strictify T (NonStrictGlue α T B f) (NonStrictGlueIso α T B f))) ) pα) 

    glue : ∀ {l} (α : Set) {{_ : Cofib α}} (T : α → Set l) (B : Set l) (f : (u : α) → T u → B)
         → (top  : ((u : α) → T u)) 
         → B [ α ↦ (\ u → f u (top u) ) ]
         → Glue α T B f
    glue α T B f t u = Iso.f (fst (snd (strictify T (NonStrictGlue α T B f) (NonStrictGlueIso α T B f)) )) (t , u)

    glue-α : ∀ {l} {α : Set} {{_ : Cofib α}} {T : α → Set l} {B : Set l} {f : (u : α) → T u → B}
         → (top  : ((u : α) → T u)) 
         → (base : B [ α ↦ (\ u → f u (top u) ) ])
         → (u : α) → coe (Glue-α α T B f u) (glue α T B f top base) == top u
    glue-α {α = α} {T}{B}{f} top base pα = 
       (ap= (transport-inv (\ X → X) ((snd (fst (strictify T (NonStrictGlue α T B f) (NonStrictGlueIso α T B f))) ) pα))) 
        ∘ ! (ap (coe (Glue-α α T B f pα)) (ap (\ h → Iso.f h (top , base)) (snd (snd (strictify T (NonStrictGlue α T B f) (NonStrictGlueIso α T B f)) ) pα)))

    unglue : ∀ {l} {α : Set} {{cα : Cofib α}} {T : α → Set l} {B : Set l} {f : (u : α) → T u → B}
             → Glue α T B f → B
    unglue {_}{α}{{cα}}{T}{B}{f} g = fst (snd (Iso.g (fst (snd (strictify T (NonStrictGlue α T B f) (NonStrictGlueIso α T B f)) )) g))

    unglue-α : ∀ {l} {α : Set} {{_ : Cofib α}} {T : α → Set l} {B : Set l} {f : (u : α) → T u → B}
             → (g : Glue α T B f) → (u : α) → f u (coe (Glue-α _ _ _ _ u) g) == unglue g 
    unglue-α {_}{α}{{cα}}{T}{B}{f} g pα = ap (\ x → fst (snd x)) (ap (\ h → Iso.g h g) (snd (snd (strictify T (NonStrictGlue α T B f) (NonStrictGlueIso α T B f)) ) pα)) 

    Glueβ : ∀ {l} {α : Set}
          {{_ : Cofib α}}
          {T : α → Set l}
          {B : Set l}
          {f : (u : α) → T u → B} → 
          (top  : ((u : α) → T u))
          (base : B [ α ↦ (\ u → f u (top u) ) ])
          → unglue (glue α T B f top base) == fst base
    Glueβ {α = α} {T} {B} {f} t b = ap (\ x → fst(snd x)) (Iso.gf (fst (snd (strictify T (NonStrictGlue α T B f) (NonStrictGlueIso α T B f)))) (t , b)) 

    Glueη : ∀ {l} {α : Set}
          {{_ : Cofib α}}
          {T : α → Set l}
          {B : Set l}
          {f : (u : α) → T u → B} → 
          (g : Glue α T B f)
          → g == (glue α T B f (\ u → coe (Glue-α α T B f u) g) (unglue g , unglue-α g))
    Glueη {α = α}{{cα}} {T} {B} {f} g =  
      ap (Iso.f (fst (snd (strictify T (NonStrictGlue α T B f) (NonStrictGlueIso α T B f))))) 
      (pair= thing
             ( (pair= ( fst-transport-Σ {B = λ h (b : B) → (pα : α) → f pα (h pα) == b} thing _) (λ= \ _ → uip)) ))  
      ∘ ! (Iso.fg (fst (snd (strictify T (NonStrictGlue α T B f) (NonStrictGlueIso α T B f)))) g)  where
        thing = (λ= \ pα → ap= (ap {M = Cofib.eq cα pα pα} {N = id} (transport T) (uip)) ∘ ! (ap (\ h → (fst (Iso.g h g) pα)) ((snd (snd (strictify T (NonStrictGlue α T B f) (NonStrictGlueIso α T B f)))) pα)))

  glue-cong : ∀ {l} (α : Set) {{cα : Cofib α}} (T : α → Set l) (B : Set l) (f : (u : α) → T u → B)
         → {top1 top2  : ((u : α) → T u)}
         → (base1 : B [ α ↦ (\ u → f u (top1 u) ) ])
         → (base2 : B [ α ↦ (\ u → f u (top2 u) ) ])
         → top1 == top2
         → (fst base1 == fst base2)
         → glue α T B f top1 base1 == glue α T B f top2 base2
  glue-cong α T B f {top1} base1 _ id id = ap (\ h → glue α T B f top1 (fst base1 , h)) (λ= (\ _ → uip))

  GlueF : ∀ {l1 l} {Γ : Set l1}
        (α : Γ → Cofibs)
        (T : (x : Γ) → fst (α x) → Set l)
        (B : Γ → Set l)
        (f : (x : Γ) (u : fst (α x)) → T x u → B x)
        → Γ → Set l
  GlueF α T B f γ = Glue (fst (α γ)) {{ snd (α γ) }} (T γ) (B γ) (f γ) 

  ⇒GlueF-unglue : ∀ {l1 l} {Γ : Set l1}
        {α : Γ → Cofibs}
        {T : (x : Γ) → fst (α x) → Set l}
        {B : Γ → Set l}
        {f : (x : Γ) (u : fst (α x)) → T x u → B x}
        (p : I → Γ) {r r' : I} (eq : r == r')
        (g : (GlueF α T B f) (p r))
        → unglue (⇒{A = (GlueF α T B f) o p } g eq) == (⇒{A = B o p} (unglue g) eq)
  ⇒GlueF-unglue p id g = id

  Glue-α-! : ∀ {l} {α : Set} {{cc : Cofib α}} {T : α → Set l} {B : Set l} {f : (u : α) → T u → B}
           → (u : α) (t : T u)
           → (coe (! (Glue-α α T B f u)) t) == glue α _ _ _ (\ _ → transport T (Cofib.eq cc _ _) t) (f u t , (\ pα →  ap= (apd f (! (Cofib.eq cc u pα)) ∘ ! (transport-→-pre' T (! (Cofib.eq cc u pα)) (f pα))) ∘ ap {M = (Cofib.eq cc u pα)} {N = ! (! (Cofib.eq cc u pα))}(\ h → f pα (transport T h t)) uip   )) 
  Glue-α-! {α = α} {{cα}} {T} {B} {f} u t = glue-cong _ _ _ _ _ _ (λ= \ x → ap (\h → transport T (Cofib.eq cα u x) h) (ap= (transport-inv-2 (\ X → X) (Glue-α α T B f u))) ∘ ! (apd (\ h → coe (Glue-α α T B f h) (coe (! (Glue-α α T B f u)) t)) (Cofib.eq cα u x)) ) 
                                                                 (ap (f u) (ap= (transport-inv-2 (\ X → X) ((Glue-α α T B f u)))) ∘ ! (unglue-α (coe (! (Glue-α α T B f u)) t) u)) ∘ Glueη _ 

  -- in fact this is an equality, but this is more convenient to use 
  HFiber-unglue-α : ∀ {l} {α : Set} {{_ : Cofib α}} {T : α → Set l} {B : Set l} {f : (u : α) → T u → B} (b : B)
                    → (pα : α) 
                    → HFiber {A = T pα} {B} (f pα) b
                    → (HFiber {A = (Glue α T B f)} {B} unglue b)
  HFiber-unglue-α {α = α} {{cα}} {T} {B} {f = f} b pα t = 
    coe (! (Glue-α _ _ _ _ pα)) (fst t) , (\ z → fst (snd t)  z) , ((unglue-α _ pα ∘ ap (f pα) (! (ap= (transport-inv-2 (\ X → X) (Glue-α α T B f pα))))) ∘ fst (snd (snd t))) , (snd (snd (snd t))) 


