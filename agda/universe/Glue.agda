{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Glue
open import Path
open import universe.Universe
open import Glue-Weak
open import Equiv
open import universe.Path
open import Contractible

module universe.Glue where

  record GlueData (l :{♭} Level) : Set (ℓ₂ ⊔ lsuc l) where
    constructor gluedata
    field
      α : Set
      c : Cofib α
      T : α → U{l}
      B : U{l}
      f : (pα : α) → El (T pα) → El B
      feq : (pα : α) → isEquivFill _ _ (f pα)

  Glue-from-data : {l :{♭} Level} → GlueData l → Set l
  Glue-from-data (gluedata α cα T B f feq) = Glue α {{ cα }} (El o T) (El B) f

  record VData (l :{♭} Level) : Set (ℓ₂ ⊔ lsuc l) where
    constructor Vc
    field
      A : U {l}
      B : U {l}
      e : Equiv (El A) (El B)
      x : I

  V-to-Glue : {l :{♭} Level} → VData l → GlueData l
  V-to-Glue (Vc A B e x) =
         gluedata ((x == `0) ∨ (x == `1))
                  (Cofib∨ Cofib= Cofib=) 
                  ((case (\ x=0 → A) (\ x=1 → B) (\ p q → abort (iabort (q ∘ ! p)) )))
                  B
                  (∨-elim01 _ (\ _ → fst e) (\ _ x → x))
                  (∨-elim01 _ (\ _ → isEquiv-isEquivFill _ _ _ (snd e) (\ b → hcomEl (HFiber-code {A = A} {B} (fst e) b) ))
                              ((\ _ → isEquiv-isEquivFill _ _ _ (id-Equiv (hcomEl B)) ((\ b → hcomEl (HFiber-code {A = B} {B} (\ x → x) b) )) )) )


  module ComGlue {l :{♭} Level} (G : I → GlueData l) (s s' : I) (β : Set) {{ cβ : Cofib β }}
                 (u : (z : I) → β → Glue-from-data (G z))
                 (v : Glue-from-data (G s) [ β ↦ u s ]) where

    module Gs = GlueData (G s)
    module Gs' = GlueData (G s')
    
    bfill : (w : I) → _ [ β ↦ _ , _ ↦ _ ]
    bfill w = comEl' (\x → (GlueData.B x))
                G s w
                β (\ z pα → unglue (u z pα))
                (unglue (fst v) , (\ pβ → ap unglue (snd v pβ)))

    b' = bfill s'
    
    c : (pαs' : Gs'.α) → _
    c pαs' =  Gs'.feq pαs' (fst b')
                       (β ∨ (s == s'))
                       (case (\ pβ → transport (HFiber (Gs'.f pαs')) (fst (snd b') pβ) (Glue-to-fiber (u s' pβ) pαs') )
                             (\ s=s' → transport (HFiber (Gs'.f pαs'))
                                        (snd (snd b') s=s' ∘ ⇒GlueF-unglue {Γ = I} {α = λ x → GlueData.α (G x) , GlueData.c (G x)} {λ x p → El (GlueData.T (G x) p)} (\ x → x) s=s' (fst v) )
                                        (Glue-to-fiber {{ cα = Gs'.c}} (transport (Glue-from-data o G) s=s' (fst v)) pαs'))
                             (\ {pβ id →  ap (\ H → (transport (HFiber (Gs'.f pαs')) (snd (snd b') id) (H pαs')) ) (apd Glue-to-fiber (snd v pβ)) ∘
                                          het-to-hom ((!h (transport-=h (HFiber (Gs'.f pαs')) (snd (snd b') id)) ∘h (  ap=o (ap (Σe (El (Gs'.T pαs'))) (λ= \ a → ap (Path (El Gs'.B) (Gs'.f pαs' a)) (ap unglue (snd v pβ)))) (\ x → x pαs') (\ x → x pαs') (λ=o (\ x y x=y → ap=od1 (λ= \ x → ap (\ H → HFiber (Gs'.f x) (unglue H)) (snd v pβ)) x y x=y)) (!h ((transport-=h (λ z → (pα : Gs'.α) → HFiber (Gs'.f pα) (unglue z)) (snd v pβ)) {(Glue-to-fiber (u s pβ))})))) ∘h transport-=h (HFiber (Gs'.f pαs')) (fst (snd b') pβ) {(Glue-to-fiber (u s pβ) pαs')}) })) 
    
    g = glue-weak-better {α = Gs'.α} {{cα = Gs'.c}} (hcomEl Gs'.B)
                         (β ∨ (s == s'))
                         (case (\ pβ → u s' pβ)
                               (\ s=s' → transport (Glue-from-data o G) s=s' (fst v) )
                               (\ pβ s=s' → ap (transport (Glue-from-data o G) s=s') (snd v pβ) ∘ ! (apd (\ x → u x pβ) s=s')))
                         (fst b' ,
                          ∨-elim _
                                 (\ pβ → fst (snd b') pβ)
                                 (\ s=s' → snd (snd b') s=s' ∘ ⇒GlueF-unglue {Γ = I} {α = λ x → GlueData.α (G x) , GlueData.c (G x)} {λ x p → El (GlueData.T (G x) p)} (\ x → x) s=s' (fst v)  )
                                 (\ _ _ → uip))
                         (\ pαs' → fst (c pαs') ,
                                   ∨-elim _
                                         (\ pβ → snd (c pαs') (inl pβ))
                                         (\ s=s' → snd (c pαs') (inr s=s') )
                                         (\ _ _ → uip))

  abstract
    comGlue-unaligned : {l :{♭} Level} → relCom (Glue-from-data{l})
    comGlue-unaligned G s s' β u v = fst g ,
                                     (\ pβ → snd g (inl pβ)) ,
                                     (\ s=s' → snd g (inr s=s') ) where
       g = (ComGlue.g G s s' β u v)

    -- this got very slow when using reduce to finish things off
    -- changed the equational proof of reduce to make it finish faster;
    -- not sure what it's normalizing, but could probably speed it up with fewer implicits somewhere
    comGlue-unaligned-β-V-coe : ∀ {l :{♭} Level} {A B : U {l}} (e : Equiv (El A) (El B))
                                 → (a : El A)
         → Path (El B)
                (coe (Glue-α ((`1 == `0) ∨ (`1 == `1)) (El o GlueData.T (V-to-Glue (Vc A B e `1))) (El (GlueData.B (V-to-Glue (Vc A B e `1)))) (GlueData.f (V-to-Glue (Vc A B e `1))) (inr id))
                    (fst (comGlue-unaligned (\ x → (V-to-Glue (Vc A B e x))) `0 `1 ⊥ (\ x → abort)
                                            (coe (! (Glue-α ((`0 == `0) ∨ (`0 == `1)) (El o GlueData.T (V-to-Glue (Vc A B e `0))) (El (GlueData.B (V-to-Glue (Vc A B e `0)))) (GlueData.f (V-to-Glue (Vc A B e `0))) (inl id))) a , \ x → abort x))))
                (fst e a)
    comGlue-unaligned-β-V-coe {A = A} {B} e a = (\ z → fst (compose z)) ,
                                                (! reduce  ∘ fst (snd (contr-extendβ))) ∘ ! (fst (snd (compose `0)) (inl id)) ,
                                                (reduce2 ∘ fst (snd regularity-b')) ∘ ! (fst (snd (compose `1)) (inr id))   where
       p0 = (! (Glue-α ((`0 == `0) ∨ (`0 == `1)) (El o GlueData.T (V-to-Glue (Vc A B e `0))) (El (GlueData.B (V-to-Glue (Vc A B e `0)))) (GlueData.f (V-to-Glue (Vc A B e `0))) (inl id)))
       p1 = (Glue-α ((`1 == `0) ∨ (`1 == `1)) (El o GlueData.T (V-to-Glue (Vc A B e `1))) (El (GlueData.B (V-to-Glue (Vc A B e `1)))) (GlueData.f (V-to-Glue (Vc A B e `1))) (inr id))

       a' = coe p0 a
       
       b' = fst (ComGlue.b' (λ x → V-to-Glue (Vc A B e x)) `0 `1 ⊥ (λ x → abort) (a' , (λ x → abort x)))

       contr-extend = (fst (contr-extend-partial (hcomEl ((HFiber-code {A = B} {B} (\ x → x)) b')) ((id-Equiv (hcomEl B)) b') (⊥ ∨ (`0 == `1)) _))

       reduce :  coe (Glue-α ((`1 == `0) ∨ (`1 == `1)) (El o GlueData.T (V-to-Glue (Vc A B e `1))) (El (GlueData.B (V-to-Glue (Vc A B e `1)))) (GlueData.f (V-to-Glue (Vc A B e `1))) (inr id))
                     (fst (comGlue-unaligned (\ x → (V-to-Glue (Vc A B e x))) `0 `1 ⊥ (\ x → abort) (coe (! (Glue-α ((`0 == `0) ∨ (`0 == `1)) (El o GlueData.T (V-to-Glue (Vc A B e `0))) (El (GlueData.B (V-to-Glue (Vc A B e `0)))) (GlueData.f (V-to-Glue (Vc A B e `0))) (inl id))) a  , \ x → abort x)))
              == (fst contr-extend)
       reduce = glue-α _ _ (inr id)
                -- _ =〈 glue-α _ _ (inr id) 〉 
                -- fst (fst (ComGlue.c (λ x → V-to-Glue (Vc A B e x)) `0 `1 ⊥ (λ x → abort) (a' , (λ x → abort x)) (inr id))) =〈 id 〉
                -- fst (fst (isEquiv-isEquivFill _ _ _ (id-Equiv (hcomEl B)) ((\ b → hcomEl (HFiber-code {A = B} {B} (\ x → x) b) )) b' (⊥ ∨ (`0 == `1)) _)) =〈 id 〉
                -- (fst contr-extend ∎) 

       contr-extendβ : Path _ (fst contr-extend) b'
       contr-extendβ = (\ z → fst (fst p z)) , ap fst (fst (snd p)) , ap fst (snd (snd p)) where
         p : Path _ contr-extend _
         p = (contr-extend-partial-path (hcomEl ((HFiber-code {A = B} {B} (\ x → x)) b')) ((id-Equiv (hcomEl B)) b') (⊥ ∨ (`0 == `1)) _)

       reduce2 : (unglue a') == (fst e a)
       reduce2 =  ap (fst e) (ap= (transport-inv-2 (\ x → x) (Glue-α _ _ _ _ (inl id)))) ∘ ! (unglue-α a' (inl id)) 

       regularity-b' : Path _ (unglue a') b' 
       regularity-b' = (\ z → fst (ComGlue.bfill (λ x → V-to-Glue (Vc A B e x)) `0 `1 ⊥ (λ x → abort) (a' , (λ x → abort x)) z)  ) ,
                       ! (snd (snd (ComGlue.bfill (λ x → V-to-Glue (Vc A B e x)) `0 `1 ⊥ (λ x → abort) (a' , (λ x → abort x)) `0)) id) ,
                       id

       compose : (x : I) → _
       compose x =  hcomEl B `1 `0 ((x == `0) ∨ (x == `1)) (\ z → case01 (\ _ → fst contr-extendβ z) (\ _ → fst regularity-b' z))
                             (b' , ∨-elim01 _ (\ _ → snd (snd contr-extendβ)) (\ _ → snd (snd regularity-b')))  


  abstract
    hasCom-Glue-fiber : {l :{♭} Level} (G : I → GlueData l)
                      (p∀α : (x : _) → (GlueData.α (G x) ))
                    → hasCom (Glue-from-data{l} o G) 
    hasCom-Glue-fiber G p∀α s s' β {{ cβ }} t b = 
      coe (! (Glue-α _ {{ (GlueData.c (G s')) }} _ _ _ ((p∀α s')))) (fst comT) ,
      (\ pβ → ap (coe (! (Glue-α _ {{ (GlueData.c (G s')) }} _ _ _ ((p∀α s'))))) (fst (snd comT) pβ) ∘ ! (ap= (transport-inv (\ X → X) (Glue-α _ {{ (GlueData.c (G s')) }} _ _ _ ((p∀α s')))))) ,
      (\ {id → ap (coe (! (Glue-α _ {{ (GlueData.c (G s')) }} _ _ _ ((p∀α s'))))) (snd (snd comT) id) ∘ ! (ap= (transport-inv (\ X → X) (Glue-α _ {{ (GlueData.c (G s')) }} _ _ _ ((p∀α s')))))}) 
      where
      comT = comEl (\ x → GlueData.T (G x) (p∀α x)) s s' β
                   (\ w pβ → coe (Glue-α _ {{ (GlueData.c (G w)) }} _ _ _ ((p∀α w))) (t w pβ))
                   ((coe (Glue-α _ {{ (GlueData.c (G s)) }} _ _ _ ((p∀α s))) (fst b)) ,
                    ((\ pβ → ap (coe (Glue-α _ {{ GlueData.c (G s) }} _ _ _ (p∀α s))) ((snd b) pβ))))

    comGlue : {l :{♭} Level} → relCom (Glue-from-data{l})
    comGlue G = fst (adjust-hasCom (Glue-from-data o G) (comGlue-unaligned G) ((x : _) → (GlueData.α (G x) )) {{Cofib∀ (\ x → GlueData.c (G x))}} (hasCom-Glue-fiber G)) 
    
    comGlue-∀α : {l :{♭} Level}(G : I → GlueData l)
               → (p∀α : (x₁ : I) → GlueData.α (G x₁)) → hasCom-Glue-fiber G p∀α == comGlue G
    comGlue-∀α G = snd (adjust-hasCom (Glue-from-data o G) (comGlue-unaligned G) ((x : _) → (GlueData.α (G x) )) {{Cofib∀ (\ x → GlueData.c (G x))}} (hasCom-Glue-fiber G)) 

    comGlue-not∀α : {l :{♭} Level} (G : I → GlueData l)
               → (not∀α : ((x₁ : I) → GlueData.α (G x₁)) → ⊥{lzero})
               → ∀ r r' α {{cα : Cofib α}} t b
               → Path _ (fst (comGlue G r r' α t b)) (fst (comGlue-unaligned G r r' α t b)) 
    comGlue-not∀α G not∀α r r' α {{cα}} t b = fst q ,
                                              fst (snd q)   ,
                                              snd (snd q) where
      q = adjust-hasCom-not (Glue-from-data o G) (comGlue-unaligned G) ((x : _) → (GlueData.α (G x) )) {{Cofib∀ (\ x → GlueData.c (G x))}} (hasCom-Glue-fiber G)
                            not∀α r r' α t b

  Glue-code-universal : {l1 :{♭} Level} → (GlueData l1 → U {l1})
  Glue-code-universal {l1} = (code (GlueData l1) (Glue-from-data {l1}) comGlue)

  abstract
    Glue-code-universal-α : {l :{♭} Level} → (H : GlueData l) 
                              → (pα : GlueData.α H) 
                              → Glue-code-universal H == GlueData.T H pα
    Glue-code-universal-α {l} (gluedata α cα T B f feq) pα = 
      Glue-code-universal (gluedata α cα T B f feq) =〈  ap-code-com (! (comEl-code-subst {Δ = (Σ \ (H : GlueData l) → GlueData.α H)} {Γ = GlueData l} {A = Glue-from-data} {comA = comGlue} fst) )
                                                        ∘ code-flat-assoc {Δ = (Σ \ (H : GlueData l) → GlueData.α H)} {Γ = GlueData l} {A = Glue-from-data} {comA = comGlue} fst (gluedata α cα T B f feq , pα)  〉
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
                                                                        ap (\ H → fst (H s s' β {{cβ}} t b)) (! (comGlue-∀α (fst o p) (\ x → snd (p x))))     ∘  
                                                                        ap (\ h → fst (h p s s' β {{ cβ }} t b)) (comEl-code-subst {Δ = Σ GlueData.α} {Γ = GlueData l} {A = Glue-from-data} {comA = comGlue} fst)) ) 〉  
      (code (Σ \ (H : GlueData l) → GlueData.α H) 
            (  \ p →  El (GlueData.T (fst p) (snd p))  )
            (comPre ( ( \ p → GlueData.T (fst p) (snd p)) ) El comEl)) ((gluedata α cα T B f feq) , pα) 
            =〈 ! (universal-code-η _) ∘ 
               ! (code-flat-assoc {Δ = (Σ \ (H : GlueData l) → GlueData.α H)} {Γ = U} {A = El} {comA = comEl} ( \ p → GlueData.T (fst p) (snd p)) ((gluedata α cα T B f feq) , pα))  〉
      (T pα ∎) 

  Glue-code : {l1 l2 :{♭} Level} {Γ : Set l1} → (Γ → GlueData l2) → (Γ → U {l2})
  Glue-code {l1} {l2} C x = (Glue-code-universal {l2}) (C x) 

  Glue-code' : {l1 l2 :{♭} Level} {Γ : Set l1}
               (α : Γ → Set)
               (cα : (θ : Γ) → Cofib (α θ))
               (T : (θ : Γ) → α θ → U{l2})
               (B : Γ → U{l2})
               (f : (θ : Γ) (pα : α θ) → El (T θ pα) → El (B θ))
               (feq : (θ : Γ) (pα : α θ) → isEquivFill _ _ (f θ pα))
             → Γ → U{l2}
  Glue-code' α cα T B f feq = Glue-code (\ θ → (gluedata (α θ) (cα θ) (T θ) (B θ) (f θ) (feq θ)) )

  Glue-code-El : {l1 l2 :{♭} Level} {Γ : Set l1}
               (α : Γ → Set)
               (cα : (θ : Γ) → Cofib (α θ))
               (T : (θ : Γ) → α θ → U{l2})
               (B : Γ → U{l2})
               (f : (θ : Γ) (pα : α θ) → El (T θ pα) → El (B θ))
               (feq : (θ : Γ) (pα : α θ) → isEquivFill _ _ (f θ pα))
               (θ : Γ) → El (Glue-code' α cα T B f feq θ) == Glue (α θ) {{cα θ}} (El o (T θ)) (El (B θ)) (f θ)
  Glue-code-El α cα T B f feq θ = id

