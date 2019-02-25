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
open import universe.Sigma
open import Glue
open import directed.Covariant
open import Glue-Weak
import Glue-Com-NoCofib
open import universe.Universe
open import directed.UCov
import directed.universe.FunGlueKan
open import directed.universe.FunGlueKan hiding (FunGlueUKan; FunGlueUKan0; FunGlueUKan1; dua-α'; dua-α; dua-T; dua-f; dua-B; dua-α-constant; duafun)

module directed.universe.FunGlue where

  open Layered

  FunGlueUKan : {l1 :{♭} Level} → FunGlueDataKan {l1} → U{l1}
  FunGlueUKan = directed.universe.FunGlueKan.FunGlueUKan

  FunGlueUKan0 : {l1 :{♭} Level} (d : FunGlueDataKan {l1}) →
                     FunGlueDataKan.i d == ``0
                   → FunGlueUKan d == FunGlueDataKan.A d
  FunGlueUKan0 = directed.universe.FunGlueKan.FunGlueUKan0

  FunGlueUKan1 : {l1 :{♭} Level} (d : FunGlueDataKan {l1}) →
                   FunGlueDataKan.i d == ``1
                 → FunGlueUKan d == FunGlueDataKan.B d
  FunGlueUKan1 = directed.universe.FunGlueKan.FunGlueUKan1

  dua-α' : 𝟚 → Set
  dua-α' = (\ x → ((x == ``0) ∨ (x == ``1)))

  module _ {l1 : Level} (x : 𝟚) (A : Set l1) (B : Set l1) (f : A → B) where
    dua-α = dua-α' x

    dua-T  : dua-α → Set l1
    dua-T = (cased01 (\ _ → A) (\ _ → B))

    dua-B = B

    dua-f : (p : dua-α) → dua-T p → dua-B 
    dua-f = (∨-elimd01 _ (\ _ → f) (\ _ x → x) )

  dua-α-constant : {l : Level} {Γ : Set l}
                   (θ : Γ → 𝟚) (p : I → Γ)
                 → Σ \ (α' : Set) → (x : I) → (dua-α' (θ (p x))) == α'
  dua-α-constant θ p = dua-α' (fst pick) , ((\ x → ap dua-α' (ap= (snd pick)))) where
    pick = (𝟚-Inull (θ o p))

  preduafun : ∀ {l1 : Level} (x : 𝟚) (A : Set l1) (B : Set l1) (f : A → B) → Set l1
  preduafun x A B f = Glue (dua-α x A B f) (dua-T x A B f) (dua-B x A B f) (dua-f x A B f)

  duaF : ∀ {l1 l2 : Level} {Γ : Set l1}
           (x : Γ → 𝟚) (A : Γ → Set l2) (B : Γ → Set l2)
           (f : (θ : Γ) → A θ → B θ)
           → Γ → Set l2
  duaF {Γ = Γ} x A B f θ = preduafun (x θ) (A θ) (B θ) (f θ)

  -- this proof seems like it should generalize to
  -- x ⊢ Glue (α(x) ∨ β(x) ↦ f ∨ g) where
  --   (α ``1) → α y for all y
  --   g is an equivalence


  -- **********************************************************************
  -- main idea is here: covariance of function glueing
  
  relCov-duaF : ∀ {l1 l2 : Level} {Γ : Set l1}
               (x : Γ → 𝟚)
               (A B : Γ → Set l2)
               (f : (θ : Γ) → A θ → B θ)
               → relCov A
               → relCov B
               → relCov1 (duaF x A B f)
  relCov-duaF x A B f dcomA dcomB p α t b =
    glue _ _ _ _
             (∨-elimd01 _ (\ xp1=0  → fst (tleft xp1=0))
                          (\ xp1=1  → fst (tright-fill ``1)))
             (fst b' ,
              ∨-elimd01 _ (\ xp1=0 → fst (snd b') (inl (inr xp1=0)))
                          (\ xp1=1 → fst (snd b') (inr xp1=1))) ,
             (\ pα → glue-cong _ _ _ _ _ _
                          (λ= (∨-elimd01 _
                                 (\ xp1=0 → ! (tleft-α pα xp1=0))
                                 (\ xp1=1 →  fst (snd (tright-fill ``1)) pα ∘ unglue-α (t ``1 pα) (inr xp1=1)  )))
                          (fst (snd b') (inl (inl pα))) ∘ Glueη (t ``1 pα)) where
    
    back-in-time : ((x o p) ``1 == ``0) → (y : _) → (x o p) y == ``0
    back-in-time eq y = transport (\ h → (x o p) y ≤ h) eq (dimonotonicity≤ (x o p) y ``1 id) 

    -- when the result in is in A, compose in A 
    tleft-fill : (y : 𝟚) (xp1=0 : x (p ``1) == ``0) → _
    tleft-fill y xp1=0 =
      dcomA p y α
             (\ z pα → coe (Glue-α _ _ _ _ (inl (back-in-time xp1=0 z))) (t z pα))
             (coe (Glue-α _ _ _ _ (inl (back-in-time xp1=0 ``0 ))) (fst b) ,
                 (λ pα → ((ap (coe (Glue-α _ _ _ _ (inl _))) (snd b pα)) ∘ ap (\ h → (coe (Glue-α _ _ _ _ (inl h)) (t ``0 pα))) uip)))

    tleft = tleft-fill ``1

    -- on α, the composite in A is just t 1
    tleft-α : (pα : α) → (xp1=0 : x(p ``1) == ``0) →
           fst (tleft xp1=0) == coe (Glue-α _ _ _ _ (inl xp1=0)) (t ``1 pα)
    tleft-α pα xp1 = (ap (\ h → coe (Glue-α _ _ _ _ (inl h)) (t ``1 pα)) uip) ∘ ! (fst (snd (tleft xp1)) pα)

    tright-fill : ∀ y → _
    tright-fill y = dcomB p y
                        (α)
                        (\ z pα → unglue (t z pα))
                        (unglue (fst b) ,
                                (\ pα → ap unglue (snd b pα)))

    -- unglue everyone to B and compose there, agreeing with f (tleft-fill) on xp1 = 0
    b' : Σ \ (b' : B (p ``1)) → _
    b' = dcomB p ``1
               ((α ∨ (x (p ``1) == ``0)) ∨ (x (p ``1) == ``1))
               ((\ z → case (case (\ pα →  unglue (t z pα))
                               (\ xp1=0 → f (p z) (fst (tleft-fill z xp1=0)))
                               (\ pα xp1=0 → ap (f (p z)) (fst (snd (tleft-fill z xp1=0)) pα) ∘ ! (unglue-α (t z pα) (inl (back-in-time xp1=0 z)))  ))
                            (\ xp1=1 → fst (tright-fill z))
                            (∨-elim _ (\ pα xp1=1 → fst (snd (tright-fill z)) pα )
                                      (\ p q → abort (diabort (q ∘ ! p)) )
                                      (λ _ _ → λ= \ _ → uip))))
               (unglue (fst b) ,
                 ∨-elim _ 
                 (∨-elim _ (\ pα → ap unglue (snd b pα))
                          (\ xp1=0 → unglue-α (fst b) (inl (back-in-time xp1=0 ``0 )) ∘ ! (ap (f (p ``0)) (snd (snd (tleft-fill ``0 xp1=0)) id)) )
                          (\ _ _ → uip) )
                 (\ xp1=1 → ! (snd (snd (tright-fill ``0)) id))
                 (\ _ _ → uip))
  
  -- **********************************************************************

  private
    -- FIXME: change UCov to relCov1 instead of relCov and then these will be enough
    -- not currently used
    dcom-dua-restricts-0 : ∀ {l1 l2 : Level} {Γ : Set l1}
                         (x : Γ → 𝟚)
                         (A B : Γ → Set l2)
                         (f : (θ : Γ) → A θ → B θ)
                         (dcomA : relCov A)
                         (dcomB : relCov B)
                         → (p : 𝟚 → Γ)
                         → (xpy=0 : (y : 𝟚) → x (p y) == ``0)
                         → ∀ α {{cα : Cofib α}} t b 
                         → coe (Glue-α _ _ _ _ (inl (xpy=0 ``1))) (fst (relCov-duaF x A B f dcomA dcomB p α t b)) ==
                               (fst (dcomA p ``1 α
                                           (\ z pα →  coe (Glue-α _ _ _ _ (inl (xpy=0 z))) (t z pα))
                                           (coe (Glue-α _ _ _ _ (inl (xpy=0 ``0))) (fst b) ,
                                            (\ pα → ap (\ x → coe (Glue-α _ _ _ _ (inl (xpy=0 ``0))) x) (snd b pα)))))    
    dcom-dua-restricts-0 x A B f dcomA dcomB p xpy=0 α t b =
      dcom= A dcomA p
            (λ= \ z → λ= \ pα → ap (\ H → (coe (Glue-α ((x (p z) == ``0) ∨ (x (p z) == ``1)) (dua-T (x (p z)) (A (p z)) (B (p z)) (f (p z))) (dua-B (x (p z)) (A (p z)) (B (p z)) (f (p z))) (dua-f (x (p z)) (A (p z)) (B (p z)) (f (p z))) (inl H)) (t z pα))) uip)
            (ap (\ H → coe (Glue-α (((x o p) ``0 == ``0) ∨ (x (p ``0) == ``1)) (dua-T (x (p ``0)) (A (p ``0)) (B (p ``0)) (f (p ``0))) (dua-B (x (p ``0)) (A (p ``0)) (B (p ``0)) (f (p ``0))) (dua-f (x (p ``0)) (A (p ``0)) (B (p ``0)) (f (p ``0))) (inl H)) (fst b)) uip) ∘
      (glue-α _ _ (inl (xpy=0 ``1)))
    
    dcom-dua-restricts-1 : ∀ {l1 l2 : Level} {Γ : Set l1}
                         (x : Γ → 𝟚)
                         (A B : Γ → Set l2)
                         (f : (θ : Γ) → A θ → B θ)
                         (dcomA : relCov A)
                         (dcomB : relCov B)
                         → (p : 𝟚 → Γ)
                         → (xpy=1 : (y : 𝟚) → x (p y) == ``1)
                         → ∀ α {{cα : Cofib α}} t b 
                         → coe (Glue-α _ _ _ _ (inr (xpy=1 ``1))) (fst (relCov-duaF x A B f dcomA dcomB p α t b)) ==
                               (fst (dcomB p ``1 α
                                          (\ z pα →  coe (Glue-α _ _ _ _ (inr (xpy=1 z))) (t z pα))
                                          (coe (Glue-α _ _ _ _ (inr (xpy=1 ``0))) (fst b) ,
                                               (\ pα → ap (\ x → coe (Glue-α _ _ _ _ (inr (xpy=1 ``0))) x) (snd b pα)))))    
    dcom-dua-restricts-1 x A B f dcomA dcomB p xpy=1 α t b =
      dcom= B dcomB p (λ= \ z → λ= \ pα → ! (unglue-α (t z pα) (inr (xpy=1 z))) )
                      (! (unglue-α (fst b) (inr (xpy=1 ``0))))
      ∘ (glue-α _ _ (inr (xpy=1 ``1)))


  record FunGlueData {l :{♭} Level} : Set (lmax ℓ₂ (lsuc l)) where
    constructor fungluedata
    field
      A : UCov l
      B : UCov l
      f : ElC A → ElC B
      i : 𝟚

  dua-α-cov : {l :{♭} Level} → FunGlueData {l} → Set
  dua-α-cov (fungluedata A B f i) = dua-α' i

  dua-T-cov : {l :{♭} Level} → (d : FunGlueData {l}) → dua-α-cov d → UCov l
  dua-T-cov (fungluedata A B f i) = (cased01 (\ _ → A) (\ _ → B))

  FunGlueDataKan-from-FunGlueData : {l :{♭} Level} → FunGlueData {l} → FunGlueDataKan {l}
  FunGlueDataKan-from-FunGlueData (fungluedata A B f i) = fungluedatakan (ElCov A) (ElCov B) f i

  duafun : {l :{♭} Level} → FunGlueData {l} → Set l
  duafun {l} = (El{l}) o (FunGlueUKan{l}) o (FunGlueDataKan-from-FunGlueData{l})

  ElCov-cased01 : ∀ {l :{♭} Level} {x : 𝟚}
            → {A : x == ``0 → UCov l} {B : x == ``1 → UCov l}
              (p : (x == ``0) ∨ (x == ``1))
              → ElCov (cased01 A B p) ==
                cased01 (\ x → ElCov (A x)) (\ y → ElCov (B y)) p
  ElCov-cased01 = ∨-elimd01 _ (\ _ → id) ((\ _ → id))
  -- add this commuting conversion as a definitional equality for convenience
  {-# REWRITE ElCov-cased01 #-}

  El-cased01 : ∀ {l :{♭} Level} {x : 𝟚}
            → {A : x == ``0 → U {l}} {B : x == ``1 → U {l}}
              (p : (x == ``0) ∨ (x == ``1))
              → El (cased01 A B p) ==
                cased01 (\ x → El (A x)) (\ y → El (B y)) p
  El-cased01 = ∨-elimd01 _ (\ _ → id) ((\ _ → id))
  -- add this commuting conversion as a definitional equality for convenience
  {-# REWRITE El-cased01 #-}

{- made this definitional since I was getting annoyed by it below
  abstract
    FunGlue-eq : {l :{♭} Level} → (d : FunGlueData {l}) → duaF (FunGlueData.i) (ElC o FunGlueData.A) (ElC o FunGlueData.B) FunGlueData.f d == duafun d
    FunGlue-eq {l} d = ap (λ X → Glue {l} ((FunGlueData.i d == ``0) ∨ (FunGlueData.i d == ``1)) (fst X) (El (fst (ElCov'{l}) (FunGlueData.B d))) (snd X)) (pair= (λ= eq1) (λ= eq2)) where
    
      eq1 : ∀ pα → dua-T (FunGlueData.i d) (ElC (FunGlueData.A d)) (ElC (FunGlueData.B d)) (FunGlueData.f d) pα == dua-TKan (FunGlueDataKan-from-FunGlueData d) pα
      eq1 pα = cased01 (λ i=0 → ap {M = inl (i=0)} {N = pα} (λ x → El (case (λ _ → fst (ElCov'{l}) (FunGlueData.A d)) (λ _ → fst (ElCov'{l}) (FunGlueData.B d)) (λ p q → abort (diabort (q ∘ ! p))) x)) trunc
                              ∘ ap {M = pα} {N = inl (i=0)} (λ x → dua-T (FunGlueData.i d) (ElC (FunGlueData.A d)) (ElC (FunGlueData.B d)) (FunGlueData.f d) x) trunc)
                       (λ i=1 → ap {M = inr (i=1)} {N = pα} (λ x → El (case (λ _ → fst (ElCov'{l}) (FunGlueData.A d)) (λ _ → fst (ElCov'{l}) (FunGlueData.B d)) (λ p q → abort (diabort (q ∘ ! p))) x)) trunc
                              ∘ ap {M = pα} {N = inr (i=1)} (λ x → dua-T (FunGlueData.i d) (ElC (FunGlueData.A d)) (ElC (FunGlueData.B d)) (FunGlueData.f d) x) trunc)
                       pα
    
      eq2 : ∀ pα → (transport (λ v → (u : (FunGlueData.i d == ``0) ∨ (FunGlueData.i d == ``1)) → v u → El (fst (ElCov'{l}) (FunGlueData.B d))) (λ= eq1)
                              (dua-f (FunGlueData.i d) (ElC{l} (FunGlueData.A d)) (ElC{l} (FunGlueData.B d)) (FunGlueData.f d))) pα == (dua-fKan (FunGlueDataKan-from-FunGlueData d)) pα
      eq2 pα = cased01 (λ i=0 → apd {b₁ = inl (i=0)} {b₂ = pα} (λ x → dua-fKan (FunGlueDataKan-from-FunGlueData d) x) trunc
                              ∘  het-to-hom (!h (transport-=h _ trunc)
                                            ∘h (ap=od1 (λ= λ pα → ap (λ X → (X → (ElC (FunGlueData.B d)))) (! (eq1 pα)))
                                                       (transport (λ v₁ → (u : (FunGlueData.i d == ``0) ∨ (FunGlueData.i d == ``1)) → v₁ u → El (fst (ElCov'{l}) (FunGlueData.B d)))
                                                                  (λ= eq1)
                                                                  (dua-f (FunGlueData.i d) (ElC (FunGlueData.A d)) (ElC (FunGlueData.B d)) (FunGlueData.f d)))
                                                       (dua-f (FunGlueData.i d) (ElC (FunGlueData.A d)) (ElC (FunGlueData.B d)) (FunGlueData.f d))
                                                       (transport-=h _ (λ= eq1))
                                            ∘h transport-=h _ (! trunc)))
                              ∘ apd! {b₁ = pα} {b₂ = inl (i=0)}
                                     (λ x → transport (λ v₁ → (u : (FunGlueData.i d == ``0) ∨ (FunGlueData.i d == ``1)) → v₁ u → El (fst (ElCov'{l}) (FunGlueData.B d)))
                                                      (λ= eq1)
                                                      (dua-f (FunGlueData.i d) (ElC (FunGlueData.A d)) (ElC (FunGlueData.B d)) (FunGlueData.f d)) x)
                                     trunc)
                                    
                       (λ i=1 → apd {b₁ = inr (i=1)} {b₂ = pα} (λ x → dua-fKan (FunGlueDataKan-from-FunGlueData d) x) trunc
                              ∘  het-to-hom (!h (transport-=h _ trunc)
                                            ∘h (ap=od1 (λ= λ pα → ap (λ X → (X → (ElC (FunGlueData.B d)))) (! (eq1 pα)))
                                                       (transport (λ v₁ → (u : (FunGlueData.i d == ``0) ∨ (FunGlueData.i d == ``1)) → v₁ u → El (fst (ElCov'{l}) (FunGlueData.B d)))
                                                                  (λ= eq1)
                                                                  (dua-f (FunGlueData.i d) (ElC (FunGlueData.A d)) (ElC (FunGlueData.B d)) (FunGlueData.f d)))
                                                       (dua-f (FunGlueData.i d) (ElC (FunGlueData.A d)) (ElC (FunGlueData.B d)) (FunGlueData.f d))
                                                       (transport-=h _ (λ= eq1))
                                            ∘h transport-=h _ (! trunc)))
                              ∘ apd! {b₁ = pα} {b₂ = inr (i=1)}
                                     (λ x → transport (λ v₁ → (u : (FunGlueData.i d == ``0) ∨ (FunGlueData.i d == ``1)) → v₁ u → El (fst (ElCov'{l}) (FunGlueData.B d)))
                                                      (λ= eq1)
                                                      (dua-f (FunGlueData.i d) (ElC (FunGlueData.A d)) (ElC (FunGlueData.B d)) (FunGlueData.f d)) x)
                                     trunc) pα
-}

  covFunGlue-unaligned : {l :{♭} Level} → relCov (duafun{l})
  covFunGlue-unaligned {l} = relCov1-relCov duafun
                                    (relCov-duaF (FunGlueData.i)
                                                 (ElC o FunGlueData.A)
                                                 (ElC o FunGlueData.B)
                                                 FunGlueData.f
                                                 (dcomPre FunGlueData.A ElCov (snd (ElCov'{l})))
                                                 (dcomPre FunGlueData.B ElCov (snd (ElCov'{l}))))

  abstract
  
    hasCov-FunGlue-fiber : {l :{♭} Level} (G : 𝟚 → FunGlueData {l})
                      (p∀α : (x : _) → dua-α' (FunGlueData.i (G x)))
                    → hasCov (duafun o G) 
    hasCov-FunGlue-fiber G p∀α s' β {{ cβ }} t b = 
      coe (! (Glue-α _ _ _ _ ((p∀α s')))) (fst comT) ,
      (\ pβ → ap (coe (! (Glue-α _ _ _ _ ((p∀α s'))))) (fst (snd comT) pβ) ∘ ! (ap= (transport-inv (\ X → X) (Glue-α _ _ _ _ ((p∀α s')))))) ,
      (\ {id → ap (coe (! (Glue-α _ _ _ _ ((p∀α s'))))) (snd (snd comT) id) ∘ ! (ap= (transport-inv (\ X → X) (Glue-α _ _ _ _ ((p∀α s')))))}) 
      where
      comT = dcomEl (\ x → dua-T-cov (G x) (p∀α x)) s' β
                    (\ w pβ → coe ( (Glue-α _ _ _ _ (p∀α w)) ) (t w pβ))
                    ((coe ( (Glue-α _ _ _ _ ((p∀α ``0))) ) (fst b)) ,
                      ((\ pβ → ap (coe ( (Glue-α _ _ _ _ (p∀α ``0)) )) ((snd b) pβ))))

    covFunGlue : {l :{♭} Level} → relCov (duafun {l})
    covFunGlue G = fst (adjust-hasCov (duafun o G) (covFunGlue-unaligned G) ((x : _) → (dua-α-cov (G x) )) (hasCov-FunGlue-fiber G)) 

    covFunGlue-∀α : {l :{♭} Level}(G : 𝟚 → FunGlueData {l})
               → (p∀α : (x₁ : 𝟚) → dua-α-cov (G x₁)) → hasCov-FunGlue-fiber G p∀α == covFunGlue G
    covFunGlue-∀α G =  snd (adjust-hasCov (duafun o G) (covFunGlue-unaligned G) ((x : _) → (dua-α-cov (G x) )) (hasCov-FunGlue-fiber G)) 

    covFunGlue-not∀α : {l :{♭} Level} (G : 𝟚 → FunGlueData {l})
               → (not∀α : ((x₁ : 𝟚) → dua-α-cov (G x₁)) → ⊥{lzero})
               → ∀ r' α {{cα : Cofib α}} t b
               → Path _ (fst (covFunGlue G r' α t b)) (fst (covFunGlue-unaligned G r' α t b)) 
    covFunGlue-not∀α G not∀α r' α {{cα}} t b = fst q ,
                                              fst (snd q)   ,
                                              snd (snd q) where
      q = adjust-hasCov-not (duafun o G) (covFunGlue-unaligned G) ((x : _) → (dua-α-cov (G x) )) (hasCov-FunGlue-fiber G)
                            not∀α r' α t b


  FunGlueUCov : {l :{♭} Level} → FunGlueData {l} → UCov l
  FunGlueUCov {l} = code-cov (FunGlueUKan o FunGlueDataKan-from-FunGlueData , covFunGlue {l}) 


  -- checking that sides of code are correct

  fix0 : {l :{♭} Level} (x : (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``0)))
        → ElCov{l} (FunGlueUCov (fst x)) == ElCov{l} (FunGlueData.A (fst x))
  fix0 (d , eq) = FunGlueUKan0 (FunGlueDataKan-from-FunGlueData d) eq

  fix1 : {l :{♭} Level} (x : (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``1)))
        → ElCov{l} (FunGlueUCov (fst x)) == ElCov{l} (FunGlueData.B (fst x))
  fix1 (d , eq) = FunGlueUKan1 (FunGlueDataKan-from-FunGlueData d) eq

  covFunGlue0 : {l :{♭} Level} →
                relCov {Γ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``0))}
                       (λ x → duafun{l} (fst x))
  covFunGlue0 {l} p r α t b =
    transport El (! ((fix0 (p r)))) (fst c)
    , ( (λ pα → ap (transport El (! (fix0 (p r)))) (fst (snd c) pα) ∘ ! (ap= (transport-inv El (fix0 (p r))))  ) )
    , ( (λ {id → ap (transport El (! (fix0 (p r)))) (snd (snd c) id) ∘ ! (ap= (transport-inv El (fix0 (p r))))  }) ) where
    
    c = (dcomEl'{l} (λ x → FunGlueData.A (fst x)) p r α
                (λ z pα → transport El (fix0 (p z)) (t z pα))
                          (transport El (fix0 (p ``0)) (fst b) ,
                          (λ pα → ap (transport El (fix0 (p ``0))) (snd b pα))))


  covFunGlue1 : {l :{♭} Level} →
                relCov {Γ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``1))}
                       (λ x → duafun{l} (fst x))
  covFunGlue1 {l} p r α t b = 
    transport El (! ((fix1 (p r)))) (fst c)
    , ( (λ pα → ap (transport El (! (fix1 (p r)))) (fst (snd c) pα) ∘ ! (ap= (transport-inv El (fix1 (p r))))  ) )
    , ( (λ {id → ap (transport El (! (fix1 (p r)))) (snd (snd c) id) ∘ ! (ap= (transport-inv El (fix1 (p r))))  }) ) where
    
    c = (dcomEl'{l} (λ x → FunGlueData.B (fst x)) p r α
                (λ z pα → transport El (fix1 (p z)) (t z pα))
                          (transport El (fix1 (p ``0)) (fst b) ,
                          (λ pα → ap (transport El (fix1 (p ``0))) (snd b pα))))

  abstract
    restricts0 : {l :{♭} Level}
                 (p : 𝟚 → Σ (λ d → FunGlueData.i d == ``0))
                 (r : 𝟚)
                 (α  : Set)
                 {{cα : Cofib α}}
                 (t : (z : 𝟚) → α → ((duafun{l}) o fst o p) z)
                 (b : ((duafun{l}) o fst o p) ``0 [ α ↦ t ``0 ])
               → _==_
                (fst (covFunGlue{l} (\ z → fst (p z)) r α t b))
                (fst (covFunGlue0{l} p r α t b))
    restricts0 {l} p r α t b =
      het-to-hom ((!h (transport-=h El (! ( (FunGlueUKan0 (fungluedatakan (ElCov (FunGlueData.A (fst (p r)))) (ElCov (FunGlueData.B (fst (p r)))) (FunGlueData.f (fst (p r))) (FunGlueData.i (fst (p r)))) (snd (p r)))))) ∘h  
                    dcomEl=h {A = (λ x → FunGlueData.A (fst (p x)))} {A' = (λ x → FunGlueData.A (fst (p x)))} id r α
                             (λ=o1 \ w → λ=o1 \ h → (!h (transport-=h El (fix0 (p w))) ∘h transport-=h (\ x → x) (Glue-α _ _ _ _ (inl (snd (p w))))))
                             ((!h (transport-=h El (fix0 (p ``0))) ∘h transport-=h (\ x → x) (Glue-α _ _ _ _ (inl (snd (p ``0)))))) ) ∘h
                             transport-=h (\ x → x) (! (Glue-α _ _ _ _ (inl (snd (p r))))) )
      -- aligning
      ∘ ! (ap (\ H → fst (H r α t b)) (covFunGlue-∀α (\ z → fst (p z)) (\ z → inl (snd (p z)))))
    
    restricts1 : {l :{♭} Level}
                 (p : 𝟚 → Σ (λ d → FunGlueData.i d == ``1))
                 (r : 𝟚)
                 (α  : Set)
                 {{cα : Cofib α}}
                 (t : (z : 𝟚) → α → ((duafun{l}) o fst o p) z)
                 (b : ((duafun{l}) o fst o p) ``0 [ α ↦ t ``0 ])
               → _==_
                (fst (covFunGlue{l} (\ z → fst (p z)) r α t b))
                (fst (covFunGlue1{l} p r α t b))
    restricts1 {l} p r α t b = 
      het-to-hom ((!h (transport-=h El (! ( (FunGlueUKan1 (fungluedatakan (ElCov (FunGlueData.A (fst (p r)))) (ElCov (FunGlueData.B (fst (p r)))) (FunGlueData.f (fst (p r))) (FunGlueData.i (fst (p r)))) (snd (p r)))))) ∘h  
                    dcomEl=h {A = (λ x → FunGlueData.B (fst (p x)))} {A' = (λ x → FunGlueData.B (fst (p x)))} id r α
                             (λ=o1 \ w → λ=o1 \ h → (!h (transport-=h El (fix1 (p w))) ∘h transport-=h (\ x → x) (Glue-α _ _ _ _ (inr (snd (p w))))))
                             ((!h (transport-=h El (fix1 (p ``0))) ∘h transport-=h (\ x → x) (Glue-α _ _ _ _ (inr (snd (p ``0)))))) ) ∘h
                             transport-=h (\ x → x) (! (Glue-α _ _ _ _ (inr (snd (p r))))) )
      -- aligning
      ∘ ! (ap (\ H → fst (H r α t b)) (covFunGlue-∀α (\ z → fst (p z)) (\ z → inr (snd (p z)))))


  private
    FunGlueUCov0' : {l :{♭} Level} (d : FunGlueData {l}) →
                   FunGlueData.i d == ``0
                 → FunGlueUCov d == FunGlueData.A d
    FunGlueUCov0' {l} (fungluedata A B f .``0) id =
      (FunGlueUCov (fungluedata A B f ``0))
                   =〈 (code-cov-flat-assoc {Δ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``0))} {Γ = FunGlueData {l}} {(ElCov{l}) o FunGlueUCov} {covFunGlue} fst ((fungluedata A B f ``0) , id)) 〉
      _
                   =〈 ap= (code-cov= (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``0)) (\ x → (ElCov{l}) (FunGlueUCov (fst x))) (\ x → (ElCov{l}) (FunGlueData.A (fst x))) (dcomPre fst ((ElCov{l}) o FunGlueUCov) covFunGlue) (dcomEl'{l} (\ x → (FunGlueData.A (fst x)))) fix0 (λ p r α cα t b → restricts0{l} p r α {{cα}} t b )) 〉
      code-cov ((λ x → ElCov (FunGlueData.A (fst x))) , dcomEl' (λ x → FunGlueData.A (fst x))) (fungluedata A B f ``0 , id)
                   =〈  ! (universal-code-cov-η _) ∘ ! (code-cov-flat-assoc {Δ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``0))} {Γ = UCov l} {A = ElCov} {dcomEl} (\ x → (FunGlueData.A (fst x))) ((fungluedata A B f ``0) , id)) 〉
      (A ∎)
    
    FunGlueUCov1' : {l :{♭} Level} (d : FunGlueData {l}) →
                   FunGlueData.i d == ``1
                 → FunGlueUCov d == FunGlueData.B d
    FunGlueUCov1' {l} (fungluedata A B f .``1) id =
      (FunGlueUCov (fungluedata A B f ``1))
                   =〈 (code-cov-flat-assoc {Δ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``1))} {Γ = FunGlueData {l}} {ElCov o FunGlueUCov} {covFunGlue} fst ((fungluedata A B f ``1) , id)) 〉
      _
                   =〈 ap= (code-cov= (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``1)) (\ x → ElCov (FunGlueUCov (fst x))) (\ x → ElCov (FunGlueData.B (fst x))) (dcomPre fst (ElCov o FunGlueUCov) covFunGlue) (dcomEl' (\ x → (FunGlueData.B (fst x)))) fix1 (λ p r α cα t b →  restricts1{l} p r α {{cα}} t b)) 〉 
      code-cov ((λ x → ElCov (FunGlueData.B (fst x))) , dcomEl' (λ x → FunGlueData.B (fst x))) (fungluedata A B f ``1 , id)
                   =〈  ! (universal-code-cov-η _) ∘ ! (code-cov-flat-assoc {Δ = (Σ (λ (d : FunGlueData {l}) → FunGlueData.i d == ``1))} {Γ = UCov l} {A = ElCov} {dcomEl} (\ x → (FunGlueData.B (fst x))) ((fungluedata A B f ``1) , id)) 〉
      (B ∎)

  abstract
    FunGlueUCov0 : {l :{♭} Level} (d : FunGlueData {l}) →
                   FunGlueData.i d == ``0
                 → FunGlueUCov d == FunGlueData.A d
    FunGlueUCov0 = FunGlueUCov0'
    
    FunGlueUCov1 : {l :{♭} Level} (d : FunGlueData {l}) →
                   FunGlueData.i d == ``1
                 → FunGlueUCov d == FunGlueData.B d
    FunGlueUCov1 = FunGlueUCov1'
    

  private
    -- ----------------------------------------------------------------------
    -- misc stuff, not really used
    dua-identity : ∀ {l : Level} {A : Set l} {x : 𝟚} → QEquiv (preduafun x A A (\ x → x)) A -- in fact this is an isomorphism
    dua-identity =
      unglue ,
      ((\ a → glue _ _ _ _ (∨-elimd01 _ (\ _ → a) (\ _ → a)) (a , (∨-elimd01 _ (\ _ → id) (\ _ → id)))) ,
       (\ g → (\ _ → g) , glue-cong _ _ _ _ _ _ (λ= (∨-elimd01 _ (\x → unglue-α g (inl x)) (\ y → unglue-α g (inr y)))) id ∘ Glueη g , id) ,
       (\ a → (\ _ → a) , ! (Glueβ _ _) , id))  
  
    -- argument for monotonicity being necessary:
    -- reversal + preduafun covariant is contradictory
    no-reverse : ({l1 : Level} (A : Set l1) (B : Set l1) (f : A → B)
           (p : 𝟚 → 𝟚) → (preduafun (p ``0) A B f) → preduafun (p ``1) A B f )
        → (1- : 𝟚 → 𝟚)
        → (1- ``0 == ``1)
        → (1- ``1 == ``0)
        → ⊥{lzero}
    no-reverse comdua 1- p q = coe (Glue-α _ _ _ _ (inl q)) (comdua' 1- (coe (! (Glue-α _ _ _ _ (inr p))) _))  where
      comdua' = comdua ⊥ (Unit) (\ _ → <>) 
      

