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
open import universe.Glue
open import directed.UCov

module directed.universe.FunGlueKan where

  open Layered

  -- for convenience, we only define the type when the ingredients are Kan,
  -- (but a stronger theorem that it does exist without this assumption
  --  is true)

  record FunGlueDataKan {l :{♭} Level} : Set (lmax ℓ₂ (lsuc l)) where
    constructor fungluedatakan
    field
      A : U{l}
      B : U{l}
      f : El A → El B
      i : 𝟚

  dua-α' : 𝟚 → Set
  dua-α' x = ((x == ``0) ∨ (x == ``1))

  dua-α : ∀ {l :{♭} Level} → FunGlueDataKan {l} → Set
  dua-α (fungluedatakan A B f x) = dua-α' x

  dua-T  : ∀ {l :{♭} Level} → (d : FunGlueDataKan {l}) → dua-α d → Set l
  dua-T (fungluedatakan A B f x) = El o (cased01 (\ _ → A) (\ _ → B))

  dua-B : ∀ {l :{♭} Level} → (d : FunGlueDataKan {l}) → Set l
  dua-B (fungluedatakan A B f x) = El B

  dua-f : ∀ {l :{♭} Level} → (d : FunGlueDataKan {l}) (pα : dua-α d) → (dua-T d pα) → (dua-B d)
  dua-f (fungluedatakan A B f x) = (∨-elimd01 _ (\ _ → f) (\ _ x → x) )

  duafun : ∀ {l :{♭} Level} → FunGlueDataKan {l} → Set l
  duafun d = Glue (dua-α d) (dua-T d) (dua-B d) (dua-f d)

  abstract
    dua-α-constant : {l :{♭} Level} 
                     (p : I → FunGlueDataKan{l}) →
                       Σ (λ α' → (x : I) → dua-α (p x) == α')
    dua-α-constant p = dua-α' (fst pick) , ((\ x → ap dua-α' (ap= (snd pick)))) where
      pick = (𝟚-Inull (FunGlueDataKan.i o p))

  abstract
    comFunGlue : ∀ {l :{♭} Level} → relCom (duafun{l})
    comFunGlue p = 
      Glue-Com-NoCofib.αConstant.hasComGlue (λ z → dua-α (p z) , Cofib∨ Cofib=𝟚diag Cofib=𝟚diag)
                                            (\ z → dua-T (p z) )
                                            (dua-B o p)
                                            (\ z →  dua-f (p z)   )
                                            (comEl' (λ x → (cased01 (λ _ → FunGlueDataKan.A (p (fst x))) (λ _ → FunGlueDataKan.B (p (fst x)))) (snd x)))
                                            (comEl' (FunGlueDataKan.B o p) )
                                            ( fst (dua-α-constant p)  )
                                            ( snd (dua-α-constant p) )

  -- code for function gluing in UKan
  FunGlueUKan : {l1 :{♭} Level} → FunGlueDataKan {l1} → U{l1}
  FunGlueUKan = code FunGlueDataKan duafun comFunGlue


  private
    fix0 : {l1 :{♭} Level} (x : (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``0)))
          → duafun (fst x) == El (FunGlueDataKan.A (fst x))
    fix0 ((fungluedatakan A B f .``0) , id) = Glue-α _ _ _ _ (inl id)
    
    fix1 : {l1 :{♭} Level} (x : (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``1)))
         → duafun (fst x) == El (FunGlueDataKan.B (fst x))
    fix1 ((fungluedatakan A B f .``1) , id) = Glue-α _ _ _ _ (inr id)
    
    comFunGlue0 : {l1 :{♭} Level} →
                  relCom {Γ = (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``0))}
                         (\ x → El (FunGlueUKan (fst x)))
    comFunGlue0 {l1} p r r' α t b = 
      coe (! (fix0 (p r'))) (fst c) , (λ pα → move-transport-right (λ X → X) (fix0 (p r')) ((fst (snd c)) pα)) , (λ req → move-transport-right (λ X → X) (fix0 (p r')) (((snd (snd c)) req) ∘ het-to-hom (((!h (transport-=h _ req) ∘h !h (transport-=h _ (fix0 (p r)))) ∘h transport-=h _ req) ∘h transport-=h (λ X → X) (fix0 (p r'))))) where
      c = (comEl' (λ x → FunGlueDataKan.A (fst x)) p r r' α
                  (λ z pα → coe (fix0 (p z)) (t z pα))
                            (coe (fix0 (p r)) (fst b) ,
                            (λ pα → ap (coe (fix0 (p r))) (snd b pα))))
    
    comFunGlue1 : {l1 :{♭} Level} →
                  relCom {Γ = (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``1))}
                         (\ x → El (FunGlueUKan (fst x)))
    comFunGlue1 {l1} p r r' α t b = coe (! (fix1 (p r'))) (fst c) , (λ pα → move-transport-right (λ X → X) (fix1 (p r')) ((fst (snd c)) pα)) , (λ req → move-transport-right (λ X → X) (fix1 (p r')) (((snd (snd c)) req) ∘ het-to-hom (((!h (transport-=h _ req) ∘h !h (transport-=h _ (fix1 (p r)))) ∘h transport-=h _ req) ∘h transport-=h (λ X → X) (fix1 (p r'))))) where
      c = (comEl' (λ x → FunGlueDataKan.B (fst x)) p r r' α
                  (λ z pα → coe (fix1 (p z)) (t z pα))
                            (coe (fix1 (p r)) (fst b) ,
                            (λ pα → ap (coe (fix1 (p r))) (snd b pα))))
    abstract
      restricts0 : {l1 :{♭} Level}
                   (p : I → Σ (λ d → FunGlueDataKan.i d == ``0))
                   (r r' : I)
                   (α  : Set)
                   {{cα : Cofib α}}
                   (t : (z : I) → α → (El o FunGlueUKan o fst o p) z)
                   (b : (El o FunGlueUKan o fst o p) r [ α ↦ t r ])
                 → _==_
                  (fst (comFunGlue (\ z → fst (p z)) r r' α t b))
                  (fst (comFunGlue0 {l1} p r r' α t b))
      restricts0 {l1} p r r' α t b =  het-to-hom (((!h (transport-=h (\ x → x) (! (fix0 (p r')))) ∘h eq2) ∘h transport-=h (\ x → x) (! (Glue-α _ _ _ _ _))) ∘h transport-=h (\ x → x) (C.Geq r') {(fst (C.R.comGlue-α (coe (! (snd (dua-α-constant (fst o p)) `0)) (inl (snd (p `0)))) (λ x → x) r r' α (λ z pβ → coe (! (C.Geq z)) (t z pβ)) (coe (! (C.Geq r)) (fst b) , (λ p₁ → ap (coe (! (C.Geq r))) (snd b p₁)))))}) ∘
                                      (ap (coe (C.Geq r')) (ap (\ f → fst (f (\ x → x) r r' α (\ z pβ → coe (! (C.Geq z)) (t z pβ)) (coe ((! (C.Geq r))) (fst b) , (\ p → ap (coe ((! (C.Geq _) ))) (snd b p))))) (C.R.comGlue-restricts-α (coe (! (snd (dua-α-constant (fst o p)) `0)) (inl (snd (p `0))))))) where 
      
        module C = Glue-Com-NoCofib.αConstant {l1} (λ z → dua-α (fst (p z)) , Cofib∨ Cofib=𝟚diag Cofib=𝟚diag)
                                                   (\ z → dua-T (fst (p z)) )
                                                   (dua-B o fst o p)
                                                   (\ z →  dua-f (fst (p z))   )
                                                   (comEl' (λ x → (cased01 (λ _ → FunGlueDataKan.A (fst (p (fst x)))) (λ _ → FunGlueDataKan.B (fst (p (fst x))))) (snd x)))
                                                   (comEl' (FunGlueDataKan.B o fst o p) )
                                                   ( fst (dua-α-constant (fst o p))  )
                                                   ( snd (dua-α-constant (fst o p)) )
      
        eq2 : fst (C.R.ComGlue.t-fill (\ x → x) r r' α (λ z pβ → coe (! (C.Geq z)) (t z pβ)) (coe (! (C.Geq r)) (fst b) , (λ p₁ → ap (coe (! (C.Geq r))) (snd b p₁))) (coe (! (snd (dua-α-constant (fst o p)) `0)) (inl (snd (p `0)))) r')
              =h
              fst (comEl' (λ x → FunGlueDataKan.A (fst x)) p r r' α
                     (λ z pα → coe (fix0 (p z)) (t z pα))
                            (coe (fix0 (p r)) (fst b) ,
                            (λ pα → ap (coe (fix0 (p r))) (snd b pα))))
        eq2 = comEl=h (λ= \ x →  ap (case (λ _ → FunGlueDataKan.A (fst (p x))) (λ _ → FunGlueDataKan.B (fst (p x))) (λ p₁ q → abort (diabort (q ∘ ! p₁)))) (trunc {x = (transport (λ X → X) (! (ap (λ x₁ → (x₁ == ``0) ∨ (x₁ == ``1)) (ap (λ f → f x) (λ= (𝟚-Inull' (λ x₁ → FunGlueDataKan.i (fst (p x₁)))))))) (transport (λ X → X) (! (ap (λ x₁ → (x₁ == ``0) ∨ (x₁ == ``1)) (ap (λ f → f `0) (λ= (𝟚-Inull' (λ x₁ → FunGlueDataKan.i (fst (p x₁)))))))) (inl (snd (p `0)))))} {y = inl (snd (p x))}) )
                      r r' α
                      (λ=o1 (\ x → λ=o1 \ pβ → (!h (transport-=h (\ x → x) (fix0 (p x))) ∘h transport-=h (\ x → x)  (! (C.Geq x))) ∘h transport-=h (\ x → x) (Glue-α _ _ _ _ _)))
                      ((!h (transport-=h (\ x → x) (fix0 (p r))) ∘h transport-=h (\ x → x) (! (C.Geq r))) ∘h transport-=h (\ x → x) (Glue-α _ _ _ _ _)  )

      restricts1 : {l1 :{♭} Level}
                   (p : I → Σ (λ d → FunGlueDataKan.i d == ``1))
                   (r r' : I)
                   (α  : Set)
                   {{cα : Cofib α}}
                   (t : (z : I) → α → (El o FunGlueUKan o fst o p) z)
                   (b : (El o FunGlueUKan o fst o p) r [ α ↦ t r ])
                 → _==_
                  (fst (comFunGlue (\ z → fst (p z)) r r' α t b))
                  (fst (comFunGlue1 {l1} p r r' α t b))
      restricts1 {l1} p r r' α t b =  het-to-hom (((!h (transport-=h (\ x → x) (! (fix1 (p r')))) ∘h eq2) ∘h transport-=h (\ x → x) (! (Glue-α _ _ _ _ _))) ∘h transport-=h (\ x → x) (C.Geq r') {(fst (C.R.comGlue-α (coe (! (snd (dua-α-constant (fst o p)) `0)) (inr (snd (p `0)))) (λ x → x) r r' α (λ z pβ → coe (! (C.Geq z)) (t z pβ)) (coe (! (C.Geq r)) (fst b) , (λ p₁ → ap (coe (! (C.Geq r))) (snd b p₁)))))}) ∘
                                          (ap (coe (C.Geq r')) (ap (\ f → fst (f (\ x → x) r r' α (\ z pβ → coe (! (C.Geq z)) (t z pβ)) (coe ((! (C.Geq r))) (fst b) , (\ p → ap (coe ((! (C.Geq _) ))) (snd b p))))) (C.R.comGlue-restricts-α (coe (! (snd (dua-α-constant (fst o p)) `0)) (inr (snd (p `0))))))) where 
      
        module C = Glue-Com-NoCofib.αConstant {l1} (λ z → dua-α (fst (p z)) , Cofib∨ Cofib=𝟚diag Cofib=𝟚diag)
                                                   (\ z → dua-T (fst (p z)) )
                                                   (dua-B o fst o p)
                                                   (\ z →  dua-f (fst (p z))   )
                                                   (comEl' (λ x → (cased01 (λ _ → FunGlueDataKan.A (fst (p (fst x)))) (λ _ → FunGlueDataKan.B (fst (p (fst x))))) (snd x)))
                                                   (comEl' (FunGlueDataKan.B o fst o p) )
                                                   ( fst (dua-α-constant (fst o p))  )
                                                   ( snd (dua-α-constant (fst o p)) )
      
        eq2 : fst (C.R.ComGlue.t-fill (\ x → x) r r' α (λ z pβ → coe (! (C.Geq z)) (t z pβ)) (coe (! (C.Geq r)) (fst b) , (λ p₁ → ap (coe (! (C.Geq r))) (snd b p₁))) ( (coe (! (snd (dua-α-constant (fst o p)) `0)) (inr (snd (p `0)))) ) r')
              =h
              fst (comEl' (λ x → FunGlueDataKan.B (fst x)) p r r' α
                     (λ z pα → coe (fix1 (p z)) (t z pα))
                            (coe (fix1 (p r)) (fst b) ,
                            (λ pα → ap (coe (fix1 (p r))) (snd b pα))))
        eq2 = comEl=h (λ= \ x →  ap (case (λ _ → FunGlueDataKan.A (fst (p x))) (λ _ → FunGlueDataKan.B (fst (p x))) (λ p₁ q → abort (diabort (q ∘ ! p₁)))) (trunc {x = (transport (λ X → X) (! (ap (λ x₁ → (x₁ == ``0) ∨ (x₁ == ``1)) (ap (λ f → f x) (λ= (𝟚-Inull' (λ x₁ → FunGlueDataKan.i (fst (p x₁)))))))) (transport (λ X → X) (! (ap (λ x₁ → (x₁ == ``0) ∨ (x₁ == ``1)) (ap (λ f → f `0) (λ= (𝟚-Inull' (λ x₁ → FunGlueDataKan.i (fst (p x₁)))))))) (inr (snd (p `0)))))} {y = inr (snd (p x))}) )
                      r r' α
                      (λ=o1 (\ x → λ=o1 \ pβ → (!h (transport-=h (\ x → x) (fix1 (p x))) ∘h transport-=h (\ x → x)  (! (C.Geq x))) ∘h transport-=h (\ x → x) (Glue-α _ _ _ _ _)))
                      ((!h (transport-=h (\ x → x) (fix1 (p r))) ∘h transport-=h (\ x → x) (! (C.Geq r))) ∘h transport-=h (\ x → x) (Glue-α _ _ _ _ _)  )

  private
    -- too slow if these are in an absract block directly
    FunGlueUKan0' : {l1 :{♭} Level} (d : FunGlueDataKan {l1}) →
                   FunGlueDataKan.i d == ``0
                 → FunGlueUKan d == FunGlueDataKan.A d
    FunGlueUKan0' {l1} (fungluedatakan A B f .``0) id =
      FunGlueUKan (fungluedatakan A B f ``0) =〈 code-flat-assoc {Δ = (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``0))} {Γ = FunGlueDataKan {l1}} {El o FunGlueUKan} {comFunGlue} fst ((fungluedatakan A B f ``0) , id) 〉
      code (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``0))
           (\ x → El (FunGlueUKan (fst x)))
           ( comPre fst duafun comFunGlue )
           ((fungluedatakan A B f ``0) , id) =〈 ap= (code= ((Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``0))) ((\ x → El (FunGlueUKan (fst x)))) ((\ x → El (FunGlueDataKan.A (fst x)))) ( comPre fst duafun comFunGlue )((comEl' (\ x → (FunGlueDataKan.A (fst x))) ))
                                                           fix0
                                                           (\ p r r' α cα t b →
                                                             (restricts0{l1} p r r' α {{cα}} t b))) 〉 
      code (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``0))
           (\ x → El (FunGlueDataKan.A (fst x)))
           (comEl' (\ x → (FunGlueDataKan.A (fst x))) )
           ((fungluedatakan A B f ``0) , id) =〈 ! (universal-code-η _) ∘ ! (code-flat-assoc {Δ = (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``0))} {Γ = U} {A = El} {comEl} (\ x → (FunGlueDataKan.A (fst x))) ((fungluedatakan A B f ``0) , id))   〉 
      (A ∎) 
    
    FunGlueUKan1' : {l1 :{♭} Level} (d : FunGlueDataKan {l1}) →
                   FunGlueDataKan.i d == ``1
                 → FunGlueUKan d == FunGlueDataKan.B d
    FunGlueUKan1' {l1} (fungluedatakan A B f .``1) id =
      FunGlueUKan (fungluedatakan A B f ``1) =〈 code-flat-assoc {Δ = (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``1))} {Γ = FunGlueDataKan {l1}} {El o FunGlueUKan} {comFunGlue} fst ((fungluedatakan A B f ``1) , id) 〉
      code (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``1))
           (\ x → El (FunGlueUKan (fst x)))
           ( comPre fst duafun comFunGlue )
           ((fungluedatakan A B f ``1) , id) =〈 ap= (code= ((Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``1))) ((\ x → El (FunGlueUKan (fst x)))) ((\ x → El (FunGlueDataKan.B (fst x)))) ( comPre fst duafun comFunGlue )((comEl' (\ x → (FunGlueDataKan.B (fst x))) ))
                                                           fix1
                                                           (\ p r r' α cα t b →
                                                             (restricts1{l1} p r r' α {{cα}} t b))) 〉 
      code (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``1))
           (\ x → El (FunGlueDataKan.B (fst x)))
           (comEl' (\ x → (FunGlueDataKan.B (fst x))) )
           ((fungluedatakan A B f ``1) , id) =〈 ! (universal-code-η _) ∘ ! (code-flat-assoc {Δ = (Σ (λ (d : FunGlueDataKan {l1}) → FunGlueDataKan.i d == ``1))} {Γ = U} {A = El} {comEl} (\ x → (FunGlueDataKan.B (fst x))) ((fungluedatakan A B f ``1) , id))   〉 
      (B ∎) 


  -- sides are correct
  abstract
    FunGlueUKan0 : {l1 :{♭} Level} (d : FunGlueDataKan {l1}) →
                     FunGlueDataKan.i d == ``0
                   → FunGlueUKan d == FunGlueDataKan.A d
    FunGlueUKan0 = FunGlueUKan0'

    FunGlueUKan1 : {l1 :{♭} Level} (d : FunGlueDataKan {l1}) →
                   FunGlueDataKan.i d == ``1
                 → FunGlueUKan d == FunGlueDataKan.B d
    FunGlueUKan1 = FunGlueUKan1'


