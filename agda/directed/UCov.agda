{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level) renaming (_⊔_ to lmax)
open import Lib
open import Prop
open import Cofibs
open import Kan
open import Path
open import Interval
open import directed.DirInterval
open import directed.Covariant
open import universe.Universe
open import directed.Covariant-is-Fibrant
open import universe.LibFlat

module directed.UCov where

  module Layered where
  
    hasCov-code : ∀ {l2 :{♭} Level}
                → (𝟚 → U {l2})
                → U {lmax (lsuc lzero) l2}
    hasCov-code = code _ (\ A → hasCov (El o A)) com where
      abstract
        com = (com-hasCov {Δ = 𝟚 → U} (\ p x → El (p x)) (comEl' (λ p → (fst p (snd p)))) )

    -- the reason for relCovU is that the easiest 
    -- relative universe construction gives a classifier for
    -- fibrancy predicates of this form,
    -- where the "has" is in the universe
    relCovU : {l l' :{♭} Level} {Γ : Set l'} (A : Γ → U{l})
            → Set (lmax ℓ₁ (lmax l' l))
    relCovU {Γ = Γ} A = (p : 𝟚 → Γ) → El (hasCov-code (A o p))

    relCovU-definition : {l l' :{♭} Level} {Γ : Set l'} (A : Γ → U{l})
                       → relCovU A == relCov (El o A)
    relCovU-definition A = id        
    
    dcomPre : {l l' l'' :{♭} Level} {Γ : Set l'} {Δ : Set l''}
                 (f : Δ → Γ)
                 (A : Γ → U{l})
               → relCovU A
               → relCovU (A o f)
    dcomPre f A dcomA = \ p → dcomA (f o p)

    CovFib : {l' : Level} (l :{♭} Level) (Γ : Set l')
           → Set (lmax ℓ₂ (lmax (lsuc l) l'))
    CovFib l Γ = Σ \ (A : (Γ → U {l})) → relCovU A

    {-
    -- TODO : Finish, should land in HProp not strict Prop
    isprop-relCovU : ∀ {l1 l2} {Γ : Set l1} → (A : Γ → U {l2}) → Prop
    isprop-relCovU A = relCovU A , (λ x y → λ= (λ p → λ= (λ α → λ=inf (λ c → λ= (λ t → λ= (λ b → pair= {!!} (λ= (λ _ → uip))))))))
    -}

    _[_] : {l l' l'' :{♭} Level} {Γ : Set l'} {Γ' : Set l''} (Φ : CovFib l Γ) (γ : Γ' → Γ)
         → CovFib l Γ'
    (A , dcomA) [ γ ] = (A o γ , (\ p → dcomA (\ x → γ (p x))))

    -- a generalized version of LOPS'18 constructs this from tininess of 𝟚
    postulate
      UCov  : ∀ (l :{♭} Level) → Set (lmax ℓ₂ (lsuc l))
    
      ElCov : {l :{♭} Level} → UCov l → U {l}
      dcomEl : {l1 :{♭} Level} → relCovU (ElCov{l1}) 

      code-cov : {l l1 :{♭} Level} {Γ :{♭} Set l1} (Φ :{♭} CovFib l Γ) → Γ → (UCov l)
    
    ElCov' : ∀ {l :{♭} Level} → CovFib l (UCov l)
    ElCov' = ElCov , dcomEl

    postulate
      Elcode : {l l1 :{♭} Level} {Γ :{♭} Set l1} (Φ :{♭} CovFib l Γ) → (ElCov' [ code-cov Φ ]) == Φ
    
      code-cov-η : {l l1 :{♭} Level} {Γ :{♭} Set l1} (γ :{♭} Γ → UCov l) → γ == code-cov (ElCov' [ γ ])



    ElC : {l :{♭} Level} → UCov l → Set l
    ElC = El o (fst ElCov')

    dcomEl' : {l1 :{♭} Level} {l2 : Level}
              {Γ : Set l2}
              (A : Γ → UCov l1)
              → relCovU (ElCov{l1} o A) 
    dcomEl' {l1} A = dcomPre A ElCov ( (snd (ElCov'{l1})) )

    ElCov-code-cov-β :
      {l :{♭} Level} {l1 :{♭} Level}  {Γ :{♭} Set l1}
      (φ :{♭} CovFib l Γ)
      (x : Γ)
      → -- expanding ElCov because rewrite doesn't like the redex
      ElCov (code-cov φ x) == fst φ x
    ElCov-code-cov-β φ x = ap (λ h → fst h x) (Elcode φ)
    {-# REWRITE ElCov-code-cov-β #-}

    dcomEl'-β : {l :{♭} Level}
      {l1 :{♭} Level} {Γ :{♭} Set l1}
      (φ :{♭} CovFib l Γ)
      →
      -- expand out 
      -- dcomEl' (code-cov φ) == snd φ
      -- so that it can be a rewrite
      (p : 𝟚 → Γ)
       → dcomEl (λ i → code-cov φ (p i)) == (snd φ) p 
    dcomEl'-β φ p =  apd (λ x → (snd x) p) (Elcode φ) ∘
                     ! (het-to-hom ((transport-=h (λ z → (r' : 𝟚) (α : Set) {{z₁ : Cofib α}} (t : (z₂ : 𝟚) → α → (El o (λ x → fst z (p x))) z₂) (b : (El o (λ x → fst z (p x))) ``0 [ α ↦ t ``0 ]) → (El o (λ x → fst z (p x))) r' [ α ↦ t r' , ``0 == r' ↦ (λ p₁ → transport (El o (λ x → fst z (p x))) p₁ (fst b)) ]) 
                                   (Elcode φ))))  
    {-# REWRITE dcomEl'-β #-}



    -- FIXME do these in general as much as possible

    -- expand definition of equality for code to isolate interesting parts
    code-cov= :{♭} {l1 l :{♭} Level} (Γ :{♭} Set l1) (A A' :{♭} Γ → U {l}) (dcomA :{♭} relCovU A) (dcomA' :{♭} relCovU A') 
          → (eq :{♭} (g : Γ) → A g == A' g)
            ( _ :{♭} ∀ p r' α cα t b → 
              fst (dcomA p r' α {{ cα }} t b) == 
              transport El (! (eq _)) (fst (dcomA' p r' α {{ cα }} 
                                       (\ z pα → transport El (eq _) (t z pα)) 
                                       ((transport El (eq _) (fst b), (\ pα → ap (transport El (eq _)) (snd b pα)))))) )
          → code-cov {Γ = Γ} (A , dcomA) == code-cov {Γ = Γ} (A' , dcomA')
    code-cov= {l1} {l} Γ A A' comA comA' Aeq h =
      code-cov=' A A' comA comA' (λ= Aeq)
              (\ p r' α cα t b → ap {M = Aeq} {N = \ x → ap= (λ= Aeq) {x} }
                                 (\ (H : (x : _) → A x == A' x) →  transport El(! (H _))
                                 (fst (comA' p r' α {{ cα }} (λ z pα → transport El (H _) (t z pα))
                                 (transport El (H _) (fst b) , (λ pα → ap (transport El (H _)) (snd b pα)))))) (λ= \ _ → uip)
                               ∘ h p r' α cα t b) where
      code-cov=' : (A A' :{♭} Γ → U{l}) (dcomA :{♭} relCovU A) (dcomA' :{♭} relCovU A') 
          → (eq :{♭} A == A')
            ( _ :{♭} ∀ p r' α cα t b → 
              fst (dcomA p r' α {{ cα }} t b) == 
              transport El (! (ap= eq)) (fst (dcomA' p r' α {{ cα }} 
                                       (\ z pα → transport El (ap= eq) (t z pα)) 
                                       ((transport El (ap= eq) (fst b), (\ pα → ap (transport El (ap= eq)) (snd b pα)))))) )
          → code-cov {Γ = Γ} (A , dcomA) == code-cov {Γ = Γ} (A' , dcomA')
      code-cov=' A .A dcomA dcomA' id h =
        ap♭ (\ H → code-cov (A , H))
          (relCov= (El o A) _ _
                   ((\ p r' α {{ cα }} t b →
                       (ap (\ H → fst (dcomA' p r' α (λ z pα → t z pα) (fst b , H))) (λ= \ _ → uip)) ∘ h p r' α cα t b)))

    universal-code-cov-η : ∀ {l :{♭} Level} → (A : UCov l) → A == (code-cov (ElCov , dcomEl' (\ x → x))) A
    universal-code-cov-η A = ap {M = (\ x → x)}{_} (\ h → h A) ( (code-cov-η (\ X → X)) )

    -- definitional
    dcomEl-code-subst : ∀ {l1 l2 l :{♭} Level} {Δ : Set l2} {Γ :{♭} Set l1} 
                     {A :{♭} Γ → U{l}} {dcomA :{♭} relCovU A} (f : Δ → Γ)
                   → dcomEl' ((code-cov (A , dcomA)) o f)  == dcomPre f A dcomA 
    dcomEl-code-subst {A = A}{comA} f = id

    ap-code-cov-dcom : {l l1 :{♭} Level} {Γ :{♭} Set l1} {A :{♭} Γ → U{l}} {dcomA dcom'A :{♭} relCovU A} {x : Γ}
              → (p :{♭} dcomA == dcom'A)
              → (code-cov (A , dcomA)) x == (code-cov (A , dcom'A)) x
    ap-code-cov-dcom {Γ = Γ}{A} {x = x} p = ap♭ (\ h → code-cov (A , h) x) p

    code-cov-flat-assoc : ∀ {l1 l2 l :{♭} Level} {Δ :{♭} Set l2} {Γ :{♭} Set l1} 
                  {A :{♭} Γ → U{l}} {dcomA :{♭} relCovU A} (f :{♭} Δ → Γ)
                → (x : Δ) → (code-cov (A , dcomA)) (f x) == (code-cov ((\ x → A (f x)) , (dcomPre f A dcomA)) x)
    code-cov-flat-assoc {Δ = Δ} {A = A} {dcomA = dcomA} f x =  
       ap= (code-cov-η (\ x → (code-cov (A , dcomA)) (f x))) {x}


    dcomEl=h : {l :{♭} Level} {A A' : 𝟚 → UCov l} → A == A'
          → (r' : 𝟚) (α : Set) {{cα : Cofib α}}
          → {t : (z : 𝟚) → α → ElC (A z)} {t' : (z : 𝟚) → α → ElC (A' z)} → t =h t'
          → {b : ElC (A ``0) [ α ↦ t ``0 ]} {b' : ElC(A' ``0) [ α ↦ t' ``0 ]} → fst b =h fst b'
          → fst (dcomEl A r' α t b) =h fst (dcomEl A' r' α t' b')
    dcomEl=h {A = A} id r' α {t} hid {(b1 , _)} hid = hom-to-het (ap (\ z → fst (dcomEl A r' α t (b1 , z))) (λ= \ _ → uip))


    dcoe : {l :{♭} Level} (A B : UCov l) → (p : Hom _ A B) → ElC A → ElC B
    dcoe A B p a = coe (ap ElC (snd (snd p)))  (fst (dcomEl' (fst p) (λ x → x) ``1 ⊥ (λ _ → abort) (coe (ap ElC (! (fst (snd p)))) a , (λ x → abort x))))

    dcoetoi : {l :{♭} Level} (p : 𝟚 → UCov l) → (i : 𝟚) → (x : ElC (p ``0)) → _
    dcoetoi p i x =  dcomEl' p (λ x → x) i ⊥ (λ _ → abort) ( x , (λ x → abort x))

    dcoe𝟚U : {l :{♭} Level} → (A : 𝟚 → UCov l) → ElC (A ``0) → ElC (A ``1)
    dcoe𝟚U A a = (fst (dcomEl' (A) (λ x → x) ``1 ⊥ (λ _ → abort) (a , (λ x → abort x))))


  -- make a flattened version that doesn't mention U
  module Flattened where

    open Layered
  
    relComCov : ∀ {l1 l2} {Γ : Set l1} (A : Γ → Set l2) → Set (lmax ℓ₁ (lmax l1 l2))
    relComCov A = relCom A × relCov A

    CovFib' : ∀{l'} → (l : Level) → Set l' → Set (lmax l' (lsuc l))
    CovFib' {l'} l Γ = Σ (\ (A : Γ → Set l) → relComCov A)

    CovFib-to-CovFib' : ∀{l'} {l :{♭} Level} {Γ : Set l'} → CovFib l Γ → CovFib' l Γ
    CovFib-to-CovFib' (A , dcomA) = El o A , (comEl' A , dcomA)

    Cov-to-CovFib : ∀{l' :{♭} Level} {l :{♭} Level} {Γ :{♭} Set l'} (f :{♭} CovFib' l Γ) → CovFib l Γ 
    Cov-to-CovFib (A , comA , dcomA) = (code _ A comA) , dcomA

    Cov-to-CovFib-to-CovFib' : ∀{l' :{♭} Level} {l :{♭} Level} {Γ :{♭} Set l'}
                         (f :{♭} CovFib' l Γ)
                         → CovFib-to-CovFib' (Cov-to-CovFib f) == f
    Cov-to-CovFib-to-CovFib' f = pair= id (pair= (λ= \ p → ap= (comEl-β {A = (fst f)} {comA = fst (snd f)}) {p})
                                         (ap= (transport-constant (λ= (λ p → ap= (comEl-β {A = (fst f)} {comA = fst (snd f)}))))  ))

    CovFib-to-Cov-to-CovFib : ∀{l' :{♭} Level} {l :{♭} Level} {Γ :{♭} Set l'}
                          (f :{♭} CovFib l Γ)
                        → Cov-to-CovFib (CovFib-to-CovFib' f) == f
    CovFib-to-Cov-to-CovFib (A , dcomA) = pair= ((! (code-η A))) ((het-to-hom (transport-=h relCovU (! (code-η A)) {dcomA} )))

  

  -- TODO: if it seems convenient, we could define these by combining the layered
  -- version with the isomorphism
  {-

    infixl 25 _[_]
    _[_] : ∀{l l' l''}{Γ : Set l'} {Γ' : Set l''} → (Cov l Γ) → (Γ' → Γ) → Cov l Γ'
    (A , (d , α)) [ γ ] = (A o γ) , comPre γ A d , ( λ p → α (γ o p))

    UCov : (l :{♭} Level) → Set (lmax ℓ₂ (lsuc l))

    El   : Cov l (UCov l)

    code : 
      {l1 :{♭} Level} (Γ :{♭} Set l1)
      (φ :{♭} Cov l Γ)
      → ---------------------------
      Γ → (UCov l)

    Elcode :
      {l1 :{♭} Level} {Γ :{♭} Set l1}
      (φ :{♭} Cov l Γ)
      → ---------------------------
      El [ code Γ φ ] == φ

    codeEl :
      {l1 :{♭} Level} {Γ :{♭} Set l1}
      (γ :{♭} Γ → (UCov l))
      → ---------------------------
      code Γ (El [ γ ]) == γ

    El₀ = fst El
    dcomEl = fst (snd El)
    comEl = snd (snd El)
   
    β₁ :
     {l1 :{♭} Level}  {Γ :{♭} Set l1}
       (φ :{♭} Cov l Γ)
       (x : Γ)
       → ------------------------
       fst El (code Γ φ x) == fst φ x
    β₁ φ x = ap (λ h → fst h x) (Elcode φ)
    {-# REWRITE β₁ #-}
   
    β₂ : 
      {l1 :{♭} Level} {Γ :{♭} Set l1}
      (φ :{♭} Cov l Γ)
      →
      ∀ p → fst (snd El) (λ i → code Γ φ (p i)) == fst (snd φ) p
    β₂ φ p = apd (λ x → fst (snd x) p) (Elcode φ)
            ∘ ap (λ h → h (fst (snd (El [ code _ φ ])) p)) (!(transport-ap-assoc' (λ z → hasCom (z o p)) fst (Elcode φ)))
            ∘ ap (λ h → transport (λ z → hasCom (z o p)) h (fst (snd (El [ code _ φ ])) p)) (uip {p = id} {(ap fst (Elcode φ))})
    {-# REWRITE β₂ #-}
   
    β₃ : 
      {l1 :{♭} Level} {Γ :{♭} Set l1}
      (φ :{♭} Cov l Γ)
      →
      ∀ p → snd (snd El) (λ i → code _ φ (p i)) == snd (snd φ) p
    β₃ φ p = apd (λ x → snd (snd x) p) (Elcode φ)
            ∘ ap (λ h → h (snd (snd (El [ code _ φ ])) p)) (!(transport-ap-assoc' (λ z → hasCov1 (z o p)) fst (Elcode φ)))
            ∘ ap (λ h → transport (λ z → hasCov1 (z o p)) h (snd (snd (El [ code _ φ ])) p)) (uip {p = id} {(ap fst (Elcode φ))})
    {-# REWRITE β₃ #-}
  -}


