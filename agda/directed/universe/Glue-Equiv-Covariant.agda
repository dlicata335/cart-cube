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
open import directed.UCov
open import directed.Covariant
open import Glue
open import universe.Glue
open import Glue-Weak
open import universe.Universe

module directed.universe.Glue-Equiv-Covariant where

  open Layered

  GlueU : {l :{♭} Level}
          (α : Set)
          {{c : Cofib α}}
          (T : α → U{l})
          (B : U{l})
          (f : (pα : α) → EquivFill (El (T pα)) (El B))
          → U{l}
  GlueU α {{c}} T B f = Glue-code-universal (gluedata α c T B (\ pα → fst (f pα)) (\ pα → snd (f pα)))

  -- ----------------------------------------------------------------------
  -- "unaligned" covariance for glue with an equivalence

  dcom-glue-unaligned1 : {l1 l2 :{♭} Level}
             {Γ : Set l1}
             (α : Γ → Cofibs)
             (T : (x : Γ) → fst (α x) → UCov l2)
             (B : Γ → UCov l2)
             (f : (x : Γ) → (pα : fst (α x)) → EquivFill (ElC (T x pα)) (ElC (B x)))
           → relCov1 (\ x → El (GlueU (fst (α x)) {{snd (α x)}} (ElCov o (T x)) (ElCov (B x)) (f x)) )
  dcom-glue-unaligned1 {Γ = Γ} α T B f p β u v =
                      glue-weak-better {{ cα = (snd (α (p ``1))) }}
                                       (relCom-hasHCom (El o ElCov o B) (comEl' (ElCov o B)) (p ``1) )
                                       β
                                       (u ``1)
                                       (fst b' , (\ pβ → (fst (snd b') pβ)))
                                       (\ pα1 → (fiber pα1))  where
    b' = dcomEl' B p ``1 β
                 (\ z pβ → unglue (u z pβ))
                 (unglue (fst v) , (\ pβ → ap unglue (snd v pβ)))

    -- contr extend partial fixes the fiber on β
    fiber : ∀ pα1 → HFiber (fst (f (p ``1) pα1)) (fst b') [ _ ↦ _ ]
                -- FIXME try this with universe wrappers, should be nicer
    fiber pα1 = (snd (f (p ``1) pα1) (fst b')) β ( λ pβ → transport (HFiber (fst (f (p ``1) pα1))) (fst (snd b') pβ) (Glue-to-fiber (u ``1 pβ) pα1))
    
  dcom-glue-unaligned : {l1 l2 :{♭} Level}
             {Γ : Set l1}
             (α : Γ → Cofibs)
             (T : (x : Γ) → fst (α x) → UCov l2)
             (B : Γ → UCov l2)
             (f : (x : Γ) → (pα : fst (α x)) → EquivFill (ElC (T x pα)) (ElC (B x)))
           → relCov (\ x → El (GlueU (fst (α x)) {{snd (α x)}} (ElCov o (T x)) (ElCov (B x)) (f x)) )
  dcom-glue-unaligned α T B f =
    relCov1-relCov (\ x → El (GlueU (fst (α x)) {{snd (α x)}} (ElCov o (T x)) (ElCov (B x)) (f x)) )
                   (dcom-glue-unaligned1 α T B f)

  -- ----------------------------------------------------------------------
  -- aligning

  module DComGlue {l1 l2 :{♭} Level}
            {Γ : Set l1}
            (α : Γ → Cofibs)
            (T : (x : Γ) → fst (α x) → UCov l2)
            (B : Γ → UCov l2)
            (f : (x : Γ) → (pα : fst (α x)) → EquivFill (ElC (T x pα)) (ElC (B x))) where

         G = \ (x : Γ) → (GlueU (fst (α x)) {{snd (α x)}} (ElCov o (T x)) (ElCov (B x)) (f x))

         -- what we would do on the fiber
         fill-Glue-fiber : ∀ (p : 𝟚 → Γ) (p∀α : (x : _) → (fst o α o p) x) 
                           (w : 𝟚) (β : Set) {{ cβ : Cofib β }} 
                           (t : (z : 𝟚) → β → El ((G o p) z)) 
                           (b : (El ((G o p) ``0)) [ β ↦ (t ``0) ]) 
                         → ((ElC (T (p w) (p∀α w))) [ β ↦ _ , _ ↦ _ ])
         fill-Glue-fiber p p∀α w β {{cβ}} t b =
             (dcomEl' (\ p → T (fst p) (snd p)) (\ x → p x , p∀α x) w β
                      (\ w pβ → coe (Glue-α _ {{ (snd (α (p w))) }} _ _ _ ((p∀α w))) (t w pβ))
                      ((coe (Glue-α _ {{ (snd (α (p ``0))) }} _ _ _ ((p∀α ``0))) (fst b)) , 
                                  (\ pβ → ap (coe (Glue-α _ {{ (snd (α (p ``0))) }} _ _ _ (p∀α ``0))) ((snd b) pβ))))
                                  
         dcom-glue : Σ \ (c : relCov (El o G)) →
                         -- for any p for which α holds always, do what you would do on the fiber
                         (p : 𝟚 → Γ)
                         (p∀α : (x : 𝟚) → fst (α (p x)))
                       → ∀ r' β {{cβ}} t b →
                         fst (c p r' β  {{cβ}} t b) ==
                         coe (! (Glue-α _ {{snd (α (p r'))}} _ _ _ (p∀α r')))
                             (fst ( (fill-Glue-fiber p p∀α r' β {{cβ}} t b) ))
         dcom-glue = (\ p r' β {{cβ}} t b → fst (use p r' β {{cβ}} t b)  ,
                                            (\ pβ → (fst (snd (use p r' β {{cβ}} t b))) (inl pβ)) ,
                                            (\ 0=r' → snd (snd (use p r' β t b)) 0=r')) ,
                                            (\ p p∀α r' β {{cβ}} t b → ! (fst (snd (use p r' β {{cβ}} t b)) (inr p∀α)) ) where
           use : ∀ p r' β {{cβ}} t b → _
           use  p r' β {{cβ}} t b =
               dcom-glue-unaligned α T B f p r'
                           (β ∨ ((x : 𝟚) → fst (α (p x))))
                           {{ Cofib∨ cβ (Cofib∀𝟚 (\ x → snd (α (p x)))) }}
                           (\ z → case (t z)
                                       (\ p∀α → coe (! (Glue-α _ {{snd (α (p z))}} _ _ _ (p∀α z))) (fst ( (fill-Glue-fiber p p∀α z β {{cβ}} t b) )))
                                       ((λ pβ p∀α → move-transport-right (λ X → X) (Glue-α _ {{snd (α (p z))}} _ _ _ (p∀α z)) (fst (snd ( (fill-Glue-fiber p p∀α z β {{cβ}} t b) )) pβ))))
                           (fst b , ∨-elim _
                                           (\ pβ → (snd b pβ))
                                           (\ p∀α → move-transport-left! (\ X → X) (Glue-α _ {{ (snd (α (p ``0))) }} _ _ _ (p∀α ``0)) (! (snd (snd ( (fill-Glue-fiber p p∀α ``0 β {{cβ}} t b) )) id)))
                                           (\ _ _ → uip))


  -- ----------------------------------------------------------------------
  -- universe wrappers

  record GlueDataUCov (l :{♭} Level) : Set (lmax ℓ₂ (lsuc l)) where
    constructor Gluedata-cov
    field
      α : Set
      c : Cofib α
      T : α → UCov l
      B : UCov l
      f : (pα : α) → ElC (T pα) → ElC B
      feq : (pα : α) → isEquivFill _ _ (f pα)

  mkGlueDataUCov : {l :{♭} Level} → (α : Set) → {{c : Cofib α}}
                 → (T : α → UCov l) → (B : UCov l)
                 → (f : (pα : α) → ElC (T pα) → ElC B)
                 → (feq : (pα : α) → isEquivFill _ _ (f pα))
                 → GlueDataUCov l
  mkGlueDataUCov α {{c}} T B f feq = Gluedata-cov α c T B f feq

  forget : {l :{♭} Level} → GlueDataUCov l → GlueData l
  forget (Gluedata-cov α c T B f feq) = gluedata α c (\ pα → ElCov (T pα)) (ElCov B) f feq

  module DG {l1 :{♭} Level} =
    DComGlue {Γ = GlueDataUCov l1} (\ H → GlueDataUCov.α H , GlueDataUCov.c H) GlueDataUCov.T GlueDataUCov.B (\ H pα → GlueDataUCov.f H pα , GlueDataUCov.feq H pα)

  Glue-code-universal' : {l :{♭} Level} → GlueData l → U {l}
  Glue-code-universal' = Glue-code-universal

  abstract
    -- too slow if this reduces below
    dcom-Glue-code-universal-forget : {l :{♭} Level} → relCov (El{l} o Glue-code-universal' o forget)
    dcom-Glue-code-universal-forget = (fst DG.dcom-glue) 

    Glue-code-forget-α : {l :{♭} Level} (g : Σe (GlueDataUCov l) GlueDataUCov.α) →
                         Glue-code-universal' (forget (fst g))
                         == fst (ElCov'{l}) (GlueDataUCov.T (fst g) (snd g))
    Glue-code-forget-α g = Glue-code-universal-α (forget (fst g)) (snd g)

    Glue-dcom-restricts : ∀ {l :{♭} Level} (p   : 𝟚 → Σ GlueDataUCov.α)
            (r'  : 𝟚)
            (α   : Set)
            {{cα  : Cofib α}}
            (t   : (z : 𝟚) → α → (El o (λ x → (Glue-code-universal' o forget) (fst (p x)))) z)
            (b   : ((El o (λ x → (Glue-code-universal' o forget) (fst (p x)))) ``0) [ α ↦ (t ``0) ])
            → fst (dcom-Glue-code-universal-forget{l} (λ i → fst (p i)) r' α t b)
            == transport El (! (Glue-code-forget-α (p r')))
                            (fst (dcomEl' (λ x → GlueDataUCov.T (fst x) (snd x)) p r' α
                                     (λ z pα₁ → transport El (Glue-code-forget-α (p z)) (t z pα₁))
                                     (transport El (Glue-code-forget-α (p ``0)) (fst b) ,
                                              (λ pα₁ → ap (transport El (Glue-code-forget-α (p ``0))) (snd b pα₁)))))
    Glue-dcom-restricts {l} p r' α t b =
       het-to-hom ((!h (transport-=h El (! (Glue-code-forget-α (p r')))) ∘h
       hom-to-het ( ap (\P → fst (dcomEl' (λ x → GlueDataUCov.T (fst x) (snd x)) p r' α (fst P) (snd P))) 
                       (pair=o (λ= \ z → λ= \ pβ → ap= (Glue-code-forget-α-definition z p))
                               ( (pair=oo (ap=o id (extends α) (extends α) hid (hom-to-het (λ= \ pz → ap= (Glue-code-forget-α-definition ``0 p) {t ``0 pz}))) (hom-to-het (ap= (Glue-code-forget-α-definition ``0 p) {fst b}))
                                          (λ=o1 (\ pα → uipo {p = ap (coe (Glue-α (GlueDataUCov.α (fst (p ``0))) {{(GlueDataUCov.c (fst (p ``0)))}} (El o ElCov o GlueDataUCov.T (fst (p ``0))) (El (ElCov (GlueDataUCov.B (fst (p ``0))))) (GlueDataUCov.f (fst (p ``0))) (snd (p ``0)))) (snd b pα)}
                                                             {q = ap (transport El (Glue-code-forget-α (p ``0))) (snd b pα)}
                                                             {r = hom-to-het (ap= (Glue-code-forget-α-definition ``0 p))}))) )))) ∘h
       transport-=h (\ X → X) (! (Glue-α (GlueDataUCov.α (fst (p r'))) {{ (GlueDataUCov.c (fst (p r')))  }} (El o ElCov o GlueDataUCov.T (fst (p r'))) (El (ElCov (GlueDataUCov.B (fst (p r'))))) (λ pα → GlueDataUCov.f (fst (p r')) pα) (snd (p r')))))
       -- aligning 
       ∘ snd (DG.dcom-glue{l}) (λ i → fst (p i)) (λ i → snd (p i)) r' α t b where

             Glue-code-forget-α-definition : ∀ (z : 𝟚) (p :  𝟚 → Σ (GlueDataUCov.α{l})) → 
                 transport (\ X → X)
                   (Glue-α (GlueDataUCov.α (fst (p z))) {{ (GlueDataUCov.c (fst (p z))) }}
                           (El o ElCov o GlueDataUCov.T (fst (p z)))
                               (El (ElCov (GlueDataUCov.B (fst (p z)))))
                               (GlueDataUCov.f (fst (p z)))
                           (snd (p z)))
                 == transport El (Glue-code-forget-α (p z))
             Glue-code-forget-α-definition z p =
                (! (transport-ap-assoc' (\ X → X) El (Glue-code-forget-α (p z)))) ∘
                    ap (\ X → coe X) (uip {p = (Glue-α (GlueDataUCov.α (fst (p z))) {{(GlueDataUCov.c (fst (p z)))}} (El o ElCov o GlueDataUCov.T (fst (p z))) (El (ElCov (GlueDataUCov.B (fst (p z))))) (GlueDataUCov.f (fst (p z))) (snd (p z)))} {q = (ap El (Glue-code-forget-α (p z)))})


  GlueUCov : {l1 :{♭} Level} → GlueDataUCov l1 → UCov l1
  GlueUCov {l1} = code-cov ((Glue-code-universal' o forget) , dcom-Glue-code-universal-forget) 

  -- putting this in an abstract block takes too long because the above definitions reduce
  private
    GlueUCov-α' : {l :{♭} Level} → (H : GlueDataUCov l) 
                                → (pα : GlueDataUCov.α H) 
                                → GlueUCov H == GlueDataUCov.T H pα
    GlueUCov-α' {l} (Gluedata-cov α cα T B f feq) pα =
        GlueUCov{l} (Gluedata-cov{l} α cα T B f feq) =〈 code-cov-flat-assoc {Δ = (Σ \ (H : GlueDataUCov l) → GlueDataUCov.α H)} {Γ = GlueDataUCov l} {A = Glue-code-universal' o forget} {dcomA = dcom-Glue-code-universal-forget} fst (Gluedata-cov α cα T B f feq , pα)   〉
        step2  =〈 ap= (code-cov= (Σ (λ (H : GlueDataUCov l) → GlueDataUCov.α H)) (\ Z → ElCov (GlueUCov (fst Z))) (\ p → ElCov (GlueDataUCov.T (fst p) (snd p)))
                                 ( dcomEl' (\ Z → GlueUCov (fst Z))) (dcomEl' (\ p → GlueDataUCov.T (fst p) (snd p)))
                                 Glue-code-forget-α
                                 (\ p r' α cα t b → Glue-dcom-restricts p r' α {{cα}} t b))  〉
        step3  =〈 ! (universal-code-cov-η _) ∘
                    ! (code-cov-flat-assoc {Δ = (Σ \ (H : GlueDataUCov l) → GlueDataUCov.α H)} {Γ = UCov l} {A = ElCov} {dcomA = dcomEl' (\ X → X)} ( \ p → GlueDataUCov.T (fst p) (snd p)) ((Gluedata-cov α cα T B f feq) , pα))   〉
        (T pα ∎) where
    
        step2 : UCov l
        step2 = code-cov 
                  {Γ = Σ (λ (H : GlueDataUCov l) → GlueDataUCov.α H)}
                  ((\ Z → ElCov (GlueUCov (fst Z))) , dcomEl' (\ Z → GlueUCov (fst Z)) )
                  ((Gluedata-cov α cα T B f feq) , pα)
    
        step3 : UCov l
        step3 = code-cov 
                  {Γ = Σ (λ (H : GlueDataUCov l) → GlueDataUCov.α H)}
                  ((\ p → ElCov (GlueDataUCov.T (fst p) (snd p))),
                          dcomEl' (\ p → GlueDataUCov.T (fst p) (snd p)))
                  ((Gluedata-cov α cα T B f feq) , pα)       

  abstract
    GlueUCov-α : {l :{♭} Level} → (H : GlueDataUCov l) 
                                → (pα : GlueDataUCov.α H) 
                                → GlueUCov H == GlueDataUCov.T H pα
    GlueUCov-α = GlueUCov-α'

  
