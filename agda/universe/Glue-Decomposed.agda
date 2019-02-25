{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Glue
open import com-glue-decomposed.Glue-Com
open import com-glue-decomposed.Glue-WCoe
open import Equiv
open import Path
open import universe.Universe

module universe.Glue-Decomposed where

  -- ----------------------------------------------------------------------
  -- code for the universe itself in the next universe

  record GlueData (l :{♭} Level) : Set (ℓ₂ ⊔ lsuc l) where
    constructor gluedata
    field
      α : Set
      c : Cofib α
      T : α → U{l}
      B : U{l}
      f : (pα : α) → El (T pα) → El B
      feq : (pα : α) → isEquiv _ _ (f pα)

  module _ {l :{♭} Level} where
    Glue-from-data : GlueData l → Set l
    Glue-from-data (gluedata α cα T B f feq) = Glue α {{ cα }} (El o T) (El B) f

    Glue-universal-Cofib : {l1 :{♭} Level} → (GlueData l1) → _
    Glue-universal-Cofib = (\ x → GlueData.α x , GlueData.c x)

    Glue-universal-T = (\ x pα → El{l} (GlueData.T x pα))

    Glue-universal-B = (El{l} o GlueData.B)

    Glue-universal-comT = comEl'{l} (λ p → (GlueData.T (fst p) (snd p)))
    Glue-universal-comB = comEl'{l} GlueData.B 

    Glue-universal-wcoe = wcoe-isweq {Γ = GlueData l} Glue-universal-Cofib Glue-universal-T Glue-universal-B
                                     GlueData.f GlueData.feq Glue-universal-comT Glue-universal-comB

    comGlue-universal : relCom{_}{l} Glue-from-data
    comGlue-universal = GlueCom.comGlue {Γ = GlueData l} Glue-universal-Cofib Glue-universal-T Glue-universal-B
                               GlueData.f Glue-universal-comT Glue-universal-comB Glue-universal-wcoe
                                  
    comGlue-universal-∀α : _
    comGlue-universal-∀α = GlueCom.comGlue-∀α {Γ = GlueData l} Glue-universal-Cofib Glue-universal-T Glue-universal-B
                               GlueData.f Glue-universal-comT Glue-universal-comB Glue-universal-wcoe

    coe-comGlue-universal-0-1 = GlueCom.coe-comGlue-0-1 {Γ = GlueData l} Glue-universal-Cofib Glue-universal-T Glue-universal-B
                               GlueData.f Glue-universal-comT Glue-universal-comB Glue-universal-wcoe

  comGlue-universal-stable : {l1 :{♭} Level} {l2 : Level} {Δ : Set l2} (θ : Δ → GlueData l1) → _
  comGlue-universal-stable {l1}{l2} θ = GlueCom.GlueF-stable {Γ = GlueData l1} {θ = θ}
                               (Glue-universal-Cofib{l1}) Glue-universal-T Glue-universal-B 
                               GlueData.f Glue-universal-comT Glue-universal-comB Glue-universal-wcoe

  Glue-code-universal : {l1 :{♭} Level} → (GlueData l1 → U {l1})
  Glue-code-universal {l1} = (code (GlueData l1) (Glue-from-data {l1}) comGlue-universal) where

  GlueU : {l :{♭} Level}
          (α : Set)
          {{c : Cofib α}}
          (T : α → U{l})
          (B : U{l})
          (f : (pα : α) → Equiv (El (T pα)) (El B))
          → U{l}
  GlueU α {{c}} T B f = Glue-code-universal (gluedata α c T B (\ pα → fst (f pα)) (\ pα → snd (f pα)))

  Glue-code : {l1 l2 :{♭} Level} {Γ : Set l1} → (Γ → GlueData l2) → (Γ → U {l2})
  Glue-code {l1} {l2} C x = (Glue-code-universal {l2}) (C x) 

  abstract
    Glue-code-universal-α : {l :{♭} Level} → (H : GlueData l) 
                              → (pα : GlueData.α H) 
                              → Glue-code-universal H == GlueData.T H pα
    Glue-code-universal-α {l} (gluedata α cα T B f feq) pα = 
      Glue-code-universal (gluedata α cα T B f feq) =〈  ap-code-com (! (comEl-code-subst {Δ = (Σ \ (H : GlueData l) → GlueData.α H)} {Γ = GlueData l} {A = Glue-from-data} {comA = comGlue-universal} fst) )
                                                        ∘ code-flat-assoc {Δ = (Σ \ (H : GlueData l) → GlueData.α H)} {Γ = GlueData l} {A = Glue-from-data} {comA = comGlue-universal} fst (gluedata α cα T B f feq , pα)  〉
      (code ((Σ \ (H : GlueData l) → GlueData.α H)) 
            ((El o Glue-code-universal o fst)) 
            ((comPre (Glue-code-universal o fst) El comEl)) 
      ) ((gluedata α cα T B f feq , pα)) =〈  ap= (code= (Σ \ (H : GlueData l) → GlueData.α H)
                                                   ((El o Glue-code-universal o fst))
                                                   ( El o ( \ p → GlueData.T (fst p) (snd p)) )
                                                   ((comEl' (Glue-code-universal o fst)))
                                                   (comEl' ( \ p → GlueData.T (fst p) (snd p)))
                                                   (\ cpα → Glue-α _ {{ (GlueData.c (fst cpα)) }} (El o GlueData.T (fst cpα)) (El (GlueData.B (fst cpα))) (GlueData.f (fst cpα)) (snd cpα)) 
                                                   (\ p s s' β cβ t b → -- uses aligning here
                                                                        ((comGlue-universal-∀α{l}) (fst o p) (\ x → (snd (p x))) s s' β {{ cβ }} t b)  ∘  
                                                                        ap (\ h → fst (h p s s' β {{ cβ }} t b)) (comEl-code-subst {Δ = Σ GlueData.α} {Γ = GlueData l} {A = Glue-from-data} {comA = comGlue-universal} fst)) ) 〉  
      (code (Σ \ (H : GlueData l) → GlueData.α H) 
            (  \ p → Glue-universal-T (fst p) (snd p) )
            (comPre ( ( \ p → GlueData.T (fst p) (snd p)) ) El comEl)) ((gluedata α cα T B f feq) , pα) 
            =〈 ! (universal-code-η _) ∘ 
               ! (code-flat-assoc {Δ = (Σ \ (H : GlueData l) → GlueData.α H)} {Γ = U} {A = El} {comA = comEl} ( \ p → GlueData.T (fst p) (snd p)) ((gluedata α cα T B f feq) , pα))  〉
      (T pα ∎) 


  comGlueEquation1 : {l :{♭} Level} {Γ : Set l} → (G : Γ → GlueData l)
                  →  comEl' (Glue-code G) 
                  == comPre G (El o Glue-code-universal) comGlue-universal
  comGlueEquation1 {l} G = comEl-code-subst {Γ = GlueData l} {A = El o Glue-code-universal} {comA = comGlue-universal} G 

  comGlueEquation2 : {l1 l2 :{♭} Level} {Γ : Set l1} → (G : Γ → GlueData l2) (p : I → Γ)
                  →  comPre G Glue-from-data comGlue-universal p
                  == GlueCom.comGlue
                        (λ x → GlueData.α (G x), GlueData.c (G x))
                        (λ z pα → El (GlueData.T (G z) pα)) 
                        (\x → (El (GlueData.B (G x))))
                        (λ z → GlueData.f (G z))
                        (comEl' (\ p → (GlueData.T (G (fst p))) (snd p)))
                        (comEl' (\ x → (GlueData.B (G x))))
                        (wcoePre G Glue-from-data Glue-universal-wcoe)
                        p
  comGlueEquation2 {l} {Γ} G p = ap (\ f → f p) (comGlue-universal-stable G) 

  comGlue-equation : {l :{♭} Level} {Γ : Set l} → (G : Γ → GlueData l)
                  →  comEl' (Glue-code G) ==
                     GlueCom.comGlue
                        (λ x → GlueData.α (G x), GlueData.c (G x))
                        (λ z pα → El (GlueData.T (G z) pα)) 
                        (\x → (El (GlueData.B (G x))))
                        (λ z → GlueData.f (G z))
                        (comEl' (\ p → (GlueData.T (G (fst p))) (snd p)))
                        (comEl' (\ x → (GlueData.B (G x))))
                        (wcoePre G Glue-from-data Glue-universal-wcoe)
  comGlue-equation G = (λ= \ p → comGlueEquation2 G p) ∘ comGlueEquation1 G
