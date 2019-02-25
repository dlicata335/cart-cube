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
open import Contractible

module directed.Segal where

  hasDHCom : ∀ {l} (A : Set l) → Set (lmax (lsuc lzero) l)
  hasDHCom A = (xy : Δ₂)
               → (h : (xy : Δ₂) → Λ₂ xy → A)
               → (α : Set) {{ cα  : Cofib α }}
               → (t : (xy : Δ₂) → α → A [ Λ₂ xy ↦ h xy ])
               → A [ Λ₂ xy ↦ h xy , α ↦ fst o t xy ]

  dhcom=sides : ∀ {l} (A : Set l) (dhcomA : hasDHCom A) 
                 {xy : Δ₂}
               → {h h' : (xy : Δ₂) → Λ₂ xy → A}
               → h == h'
               → {α : Set} {{ cα  : Cofib α }}
               → {t : (xy : Δ₂) → α → A [ Λ₂ xy ↦ h xy ]}
               → {t' : (xy : Δ₂) → α → A [ Λ₂ xy ↦ h' xy ]}
               → (∀ xy pα → fst (t xy pα) == fst (t' xy pα))
               → fst (dhcomA xy h α t)  == fst (dhcomA xy h' α t')
  dhcom=sides A dhcomA id p = ap (\ H → fst (dhcomA _ _ _ H)) (λ= \ xy → λ= \ pα → pair= (p xy pα) (λ= \ _ → uip))

  homHorn : ∀ {l} {A : Set l} 
           {a0 a1 a2}
           → Hom A a0 a1 → Hom A a1 a2
           → (xy : Δ₂) → Λ₂ xy → A
  homHorn p q (x , y , y≤x) =
    case (\ _ → fst p x)
         (\ _ → fst q y)
         (\ y=0 x=1 → (! (ap (fst q) y=0) ∘ ! (fst (snd q)) ) ∘ snd (snd p) ∘ ap (fst p) x=1 )

  ∘h-triangle : ∀ {l} {A : Set l} (dhcomA : hasDHCom A)
           {a0 a1 a2} → (p : Hom A a0 a1) (q : Hom A a1 a2) 
           (xy : Δ₂) → A [ Λ₂ xy ↦ homHorn p q xy ]
  ∘h-triangle dhcomA p q xy = fst c , (fst (snd c)) where
    c = dhcomA xy (\ xy → homHorn p q xy) ⊥ (\ x → abort)

  ∘h : ∀ {l} {A : Set l} (dhcomA : hasDHCom A)
           {a0 a1 a2} → Hom A a0 a1 → Hom A a1 a2 → Hom A a0 a2
  ∘h dhcomA p q = (\ z → fst (t z)) ,
                  fst (snd p) ∘ ! (snd (t ``0) (inl id)) ,
                  snd (snd q) ∘ ! ((snd (t ``1) (inr id))) where
   t : ∀ z → _
   t z = (∘h-triangle dhcomA p q (z , z , id))

  squareHorn : ∀ {l} {A : Set l}
               (p : (x : 𝟚) → (y : 𝟚) → A)
               (q : (y : 𝟚) → (z : 𝟚) → A)
             → ((y : 𝟚) → p ``1 y == q y ``0)
             → (y : 𝟚)
             → (xz : Δ₂) → Λ₂ xz
             → A
  squareHorn p q middle y (x , z , z≤x) =
    case (\ z=0 → p x y) (\ x=1 → q y z)
         (\ z=0 x=1 → ! (ap (q y) z=0) ∘ middle y ∘ (ap (\ h → p h y) x=1))


  ∘squares-at-side : ∀ {l} {A : Set l} (comA : hasDHCom A)
           → (p : 𝟚 → 𝟚 → A) (q : 𝟚 → 𝟚 → A)
           → (pq : (z : 𝟚) → p ``1 z == q z ``0)
           → (fix0 : (xz : Δ₂) → A [ Λ₂ xz ↦ squareHorn p q pq ``0 xz  ])
           → (fix1 : (xz : Δ₂) → A [ Λ₂ xz ↦ squareHorn p q pq ``1 xz  ])
           → ((xz : Δ₂) (y : 𝟚) → A [ Λ₂ xz ↦ squareHorn p q pq y xz ,
                                     ((y == ``0) ∨ (y == ``1)) ↦
                                       cased01 (\ _ → fst (fix0 xz)) (\ _ → fst (fix1 xz)) ] )
  ∘squares-at-side dhcomA p q pq fix0 fix1 xz y =
    fst c , (fst (snd c)) ,
           ∨-elimd01 _ (\ y=0 → snd (snd c) (inl y=0)) ((\ x=1 → snd (snd c) (inr x=1))) where
    c = dhcomA xz
               (\ xz l → squareHorn p q pq y xz l)
               ((y == ``0) ∨ (y == ``1))
               (\ xz → (cased01 (\ y=0 → fst (fix0 xz) , (\ l → snd (fix0 xz) l ∘ ap (\ h → squareHorn p q pq h xz l) y=0))
                                ((\ y=1 → fst (fix1 xz) , (\ l → snd (fix1 xz) l ∘ ap (\ h → squareHorn p q pq h xz l) y=1)))))

  squareHorn-top : ∀ {l} {A : Set l}
               (p : (x : 𝟚) (y : 𝟚) → A)
               (q : (x : 𝟚) (z : 𝟚) → A)
             → ((x : 𝟚) → p x ``1 == q x ``0)
             → (x : 𝟚)
             → (yz : Δ₂) → Λ₂ yz
             → A
  squareHorn-top p q middle x yz = squareHorn (\ x y → p y x) q middle x yz

  ∘squares-at-top : ∀ {l} {A : Set l} (comA : hasDHCom A)
           → (p : (x : 𝟚) (y : 𝟚) → A) (q : (x : 𝟚)(z : 𝟚) → A)
           → (pq : (x : 𝟚) → p x ``1 == q x ``0)
           → (fix0 : (xz : Δ₂) → A [ Λ₂ xz ↦ squareHorn-top p q pq ``0 xz  ])
           → (fix1 : (xz : Δ₂) → A [ Λ₂ xz ↦ squareHorn-top p q pq ``1 xz  ])
           → ((xz : Δ₂) (y : 𝟚) → A [ Λ₂ xz ↦ squareHorn-top p q pq y xz ,
                                     ((y == ``0) ∨ (y == ``1)) ↦
                                       cased01 (\ _ → fst (fix0 xz)) (\ _ → fst (fix1 xz)) ] )
  ∘squares-at-top dhcomA p q pq fix0 fix1 xz y = ∘squares-at-side dhcomA (\ x y → p y x) q pq fix0 fix1 xz y

  composite-unique : ∀ {l} {A : Set l} → hasDHCom A
                   → (f g : Δ₂ → A)
                   → (b : (t : Δ₂) → Λ₂ t → f t == g t)
                   → Path (Hom A (f (``0 , ``0 , id)) (f (``1 , ``1 , id)))
                          ((\ y → f (y , y , id)) , id , id)
                          ((\ y → g (y , y , id)) , ! (b (``0 , ``0 , id) (inl id)) , ! (b (``1 , ``1 , id) (inr id)))
  composite-unique dhcomA f g b =
     (\ x → ((\ y → fst (c x y)) , ! (fst (snd (c x ``0)) (inl id)) , ! (fst (snd (c x ``1)) (inr id)))) ,
      HomO= _ _ ((\ y → ! (snd (snd (c `0 y)) (inl id)))) ,
      HomO= _ _ (\ y → (! (snd (snd (c `1 y)) (inr id))))   where
     c : (x : _) (y : _) → _
     c = \ x y → dhcomA (y , y , id)
                      (\ yz l → f yz)
                      ((x == `0) ∨ (x == `1))
                      (\ yz → case (\ z=0 → f yz , (λ _ → id))
                                   (\ y=1 → g yz , (\ l → b yz l))
                                   (\ p q → abort (iabort (q ∘ ! p))))

  degen-triangle-to-path :
                   ∀ {l} {A : Set l} → hasDHCom A
                   → {a0 a1 : A} (f g : Hom A a0 a1)
                   → ((xy : Δ₂) → A [ Λ₂ xy ↦ homHorn ((\ _ → a0) , id , id)
                                                      f xy ,
                                      (fst xy == fst (snd xy)) ↦ (\ x=y → fst g (fst xy)) ])
                   → Path (Hom A a0 a1) f g
  degen-triangle-to-path dhcomA f g t =
      ((\ x → (\ z → fst (fst c x) z) , fst (snd f) ∘ fst (snd (fst c x)) , snd (snd f) ∘ snd (snd (fst c x))) ,
       HomO= _ _ (\ z → ap (\ h → fst h z) (fst (snd c))) , 
       HomO= _ _ ((\ z → ! (snd (snd (t (z , z , id))) id) ∘ ap (\ h → fst h z) (snd (snd c))))) where
    c = composite-unique dhcomA
                         (\ xy → fst f (fst (snd xy))) -- degeneracy
                         (\ xy → fst (t xy))
                         (\ xy → ∨-elim _
                                 (\ y=0 → ! ((! (ap (fst f) y=0) ∘ ! (fst (snd f)) ) ∘ ! (fst (snd (t xy)) (inl y=0)))  )
                                 ((\ x=1 → (fst (snd (t xy)) (inr x=1))  ))
                                 (\ _ _ → uip)) 

  -- from square with left side id, make triangle
  degen-square-to-triangle : ∀ {l} {A : Set l}
                           → hasHCom A
                           → hasDHCom A
                           → (s : (x : 𝟚) (y : 𝟚) → A)
                           → (degen : (y : 𝟚) → s ``0 y == s ``0 ``1)
                           → (xy : Δ₂) → A [ Λ₂ xy ↦ k (s (fst xy) (fst (snd xy))) ,
                                             (fst xy) == fst (snd xy) ↦ k (s (fst xy) ``1) ]
  degen-square-to-triangle {_}{A} hcomA dhcomA s dege xy = t where
    p = degen-triangle-to-path dhcomA
                               ((\ x → s x ``1) , ! (dege ``0)  , id  )
                               ((\ x → s x x) , id , id)
                               (\ xy → s (fst (snd xy)) (fst xy) ,
                                       (∨-elim _ (\ y=0 → ! (ap= (ap s y=0)) ∘ ! (dege _) ∘ dege ``0 )
                                                 (\ x=1 → ap (s (fst (snd xy))) (! x=1))
                                                 (\ _ _ → uip)) ,
                                       (\ x=y → ap= (ap s x=y)))
    t = change-triangle-composite-backwards hcomA (\ xy → s (fst xy) (fst (snd xy)) ) _ p xy

  ∘h-assoc : ∀ {l} {A : Set l} (cA : hasDHCom A) (hcomA : hasHCom A)
             {a0 a1 a2 a3} (p : Hom A a0 a1) (q : Hom A a1 a2) (r : Hom A a2 a3)
           → Path (Hom A a0 a3)
                  (∘h cA (∘h cA p q) r)
                  (∘h cA p (∘h cA q r))
  ∘h-assoc {A = A} cA hcomA {a0} p q r =
           (\ w → (\ y → fst (fst unique w) y) ,
                  ( fst (snd p)
                    ∘ ! (snd (pq-square ``0 ``0) (inl id))
                    ∘ ! (fst (snd (new-square ``0 ``0)) (inl id))
                    ∘ ! (fst (snd (p-qr-[pq-r]-tri (``0 , ``0 , id))) (inl id))
                    ∘ fst (snd (fst unique w))) ,
                  ( snd (snd r) 
                    ∘ ! (snd (pq-r-square ``1 ``1) (inr id))
                    ∘ ! (fst (snd (new-square ``1 ``1)) (inr id))
                    ∘  ! (fst (snd (p-qr-[pq-r]-tri (``1 , ``1 , id))) (inr id)) 
                    ∘ snd (snd (fst unique w)))
                    ) ,
           HomO= _ _ (\ x → ! (fst (snd (new-square ``1 x)) (inr id)) ∘ ! (snd (snd (p-qr-[pq-r]-tri (x , x , id))) id) ∘ ap (\ h → fst h x) (fst (snd unique))) ,
           HomO= _ _ (\ x → ap (\ h → fst h x) (snd (snd unique))) where
    pq-tri = ∘h-triangle cA p q
    qr-tri = ∘h-triangle cA q r
    p-qr-tri = ∘h-triangle cA p (∘h cA q r)
    pq-r-tri = ∘h-triangle cA (∘h cA p q) r

    pq-square : ∀ x y → _
    pq-square x y = pq-tri (lower-triangle x y)

    pq-r-square : ∀ y z → _
    pq-r-square y z = pq-r-tri (lower-triangle y z)

    new-square : ∀ y x → A [ Λ₂ (y , y , id) ↦ _ , (x == ``0) ∨ (x == ``1) ↦ _ ]
    new-square y x = ∘squares-at-top cA
          (\ x y → fst (pq-square x y))
          (\ y z → fst (pq-r-square y z))
          (\ z →  ((snd (pq-r-square z ``0)) (inl id))  )
          (\ _ → fst p ``0 , ∨-elim _ (\ y=0 → ! (snd (pq-square ``0 ``0) (inl id)))
                                      (\ x=1 → ! (fst (snd p)) ∘ fst (snd (∘h cA p q)) ∘ ! (snd (pq-r-square ``0 ``0) (inl id)))
                                      (\ _ _ → uip))
          (\ yz → fst (qr-tri yz) ,
                  (∨-elim _ (\ z=0 → coh1 (fst yz) (fst (snd yz)) (snd (snd yz)) z=0)
                            (\ y=1 → coh2 (fst yz) (fst (snd yz)) (snd (snd yz)) y=1)
                            (\ _ _ → uip)))
          (y , y , id)
          x where
      coh1 : (y : _) (z : _) (z≤y : z ≤ y) → (z == ``0) →
             fst (pq-square ``1 y) == fst (qr-tri (y , z , z≤y))
      coh1 y _ id id = snd (qr-tri (y , ``0 , id)) (inl id) ∘ ! (snd (pq-square ``1 y) (inr id))

      coh2 : (y : _) (z : _) (z≤y : z ≤ y) → (y == ``1) →
             fst (pq-r-square ``1 z) == fst (qr-tri (y , z , z≤y))
      coh2 _ z id id = snd (qr-tri (``1 , z , id)) (inr id) ∘ ! (snd (pq-r-square ``1 z) (inr id))

    p-qr-[pq-r]-tri = degen-square-to-triangle hcomA cA
                                 (\ x y → fst (new-square y x))
                                 (\ y → (snd (snd (new-square ``1 ``0)) (inl id)) ∘ ! (snd (snd (new-square y ``0)) (inl id)) )

    unique = composite-unique cA (\ xy → fst (p-qr-[pq-r]-tri xy)) (\ xy → fst (p-qr-tri xy))
                              (\ xy → ∨-elim _
                                             (coh1 (fst xy) (fst (snd xy)) (snd (snd (xy))))
                                             (coh2 (fst xy) (fst (snd xy)) (snd (snd (xy))))
                                             (\ _ _ → uip)) where
           coh1 : ∀ x y y≤x → y == ``0 → fst (p-qr-[pq-r]-tri (x , y , y≤x)) == fst (p-qr-tri (x , y , y≤x))
           coh1 x y id id = (snd (p-qr-tri (x , ``0 , id)) (inl id)
                             ∘ (! (snd (pq-square x ``0) (inl id)))
                             ∘ ! (fst (snd (new-square ``0 x)) (inl id))
                             ∘ ! (fst (snd (p-qr-[pq-r]-tri (x , ``0 , id))) (inl id)))

           coh2 : ∀ x y y≤x → x == ``1 → fst (p-qr-[pq-r]-tri (x , y , y≤x)) == fst (p-qr-tri (x , y , y≤x))
           coh2 x y id id = (snd (p-qr-tri (``1 , y , id)) (inr id)) ∘
                            ! (snd (snd (new-square y ``1)) (inr id)) ∘
                            ! (fst (snd (p-qr-[pq-r]-tri (``1 , y , id))) (inr id))

  hasDHCom-hasHCom : ∀ {l} (A : Set l) → hasHCom (hasDHCom A)
  hasDHCom-hasHCom A r r' α t b =
    (λ xy h β {{cβ}} u → (fst (c xy h b β {{cβ}} u) ,
                           (fst (snd (c xy h b β {{cβ}} u)) ,
                           (\ pβ → snd (snd (c xy h b β {{cβ}} u)) (inl pβ))))) ,
    ( \ pα → λ= \ xy → λ= \ h → λ= \ β → λ=inf \ cβ → λ= \ u →
      pair= (snd (snd (c xy h b β {{cβ}} u)) (inr (inl pα)))
      (pair= (λ= \ _ → uip) ((λ= \ _ → uip)))) ,
    (( \ r=r' → λ= \ xy → λ= \ h → λ= \ β → λ=inf \ cβ → λ= \ u →
       pair= ((snd (snd (c xy h b β {{cβ}} u)) (inr (inr r=r'))) )
       (pair= (λ= \ _ → uip) ((λ= \ _ → uip))))) where
    c : ∀ xy h b β {{cβ}} u → _
    c xy h b β {{cβ}} u =
      (fst b xy h
           (β ∨ (α ∨ (r == r')))
           (\ xy → case (\ pβ → u xy pβ)
                   (case (\ pα → fst (t r' pα xy h β u) , fst (snd (t r' pα xy h β u)) )
                         (\ r=r' → fst ((fst b) xy h β u) , (\ l → fst (snd ((fst b) xy h β u)) l))
                         (\ pα r=r' → pair= (ap (\ H → fst (H xy h β {{cβ}} u)) (snd b pα) ∘ ap (\ H → fst (t H pα xy h β u)) (! r=r'))
                                            (λ= \ _ → uip)))
                   ((\ pβ → ∨-elim _
                            (\ pα → pair= (snd (snd (t r' pα xy h β u)) pβ) (λ= \ _ → uip))
                            (\ r=r' → pair= (snd (snd (fst b xy h β u)) pβ) (λ= \_ → uip))
                            (\ _ _ → uip)))))

  hasDHCom-hasCoe : ∀ {l} {Γ : Set l} (A : Γ → Set l) → relCom A → relCoe (\ x → hasDHCom (A x))
  hasDHCom-hasCoe A comA p r r' dhcomAr =
    (\ xy h α {{cα}} t →
       (fst (dhcomr' xy h α {{cα}}  t)) ,
       (\ l → fst (snd (dhcomr' xy h α t)) (inl l) ∘ snd (relCom-relCoe A comA p r' r' (h xy l)) id) ,
       (\ pα → fst (snd (dhcomr' xy h α t)) (inr pα) ∘ snd (relCom-relCoe A comA p r' r' (fst (t xy pα))) id )) ,
    (\ {id → λ= \ xy → λ= \ h → λ= \ α → λ=inf \ cα → λ= \ t →
             pair= (snd (snd (dhcomr' xy h α {{cα}} t)) id ∘
                   dhcom=sides _ dhcomAr (λ= \ xy → λ= \ l → snd (relCom-relCoe A comA p r r (h xy l)) id)
                                         {{cα = cα}}
                                         (\ xy pα → (snd (relCom-relCoe A comA p r' r' (fst (t xy pα))) id)) )
       (pair= (λ= \ _ → uip) (λ= \ _ → uip))})
                                              where
    use : ∀ xy h α {{cα}} t → _
    use xy h α {{cα}} t = dhcomAr xy
                            (\ xy l → fst (relCom-relCoe A comA p r' r (h xy l)))
                            α
                            (\ xy pα → fst (relCom-relCoe A comA p r' r (fst (t xy pα))) ,
                              (\ l → ap (\ h → fst (relCom-relCoe A comA p r' r h)) (snd (t xy pα) l)))
  
    dhcomr' : ∀ xy h α {{cα}} t → _
    dhcomr' xy h α {{cα}} t =
            comA p r r'
                 (Λ₂ xy ∨ α)
                 (\ z → case (\ l → fst (relCom-relCoe A comA p r' z (h xy l)))
                             ((\ pα → fst (relCom-relCoe A comA p r' z (fst (t xy pα)))))
                             (\ l pα → ap (\ H → fst (relCom-relCoe A comA p r' z H)) (snd (t xy pα) l) ))
                 ( fst (use xy h α {{cα}} t) ,
                   ∨-elim _
                          (\ l → fst (snd (use xy h α {{cα}} t)) l)
                          (\ pα → snd (snd (use xy h α {{cα}} t)) pα )
                          (\ _ _ → uip))

  hasDHCom-hprop : ∀ {l} (A : Set l) → (dhcom1 dhcom2 : hasDHCom A) → Path (hasDHCom A) dhcom1 dhcom2
  hasDHCom-hprop A dhcom1 dhcom2 =
    (\ z xy h α {{cα}} t → fst (c z xy h α {{cα}} t) ,
     (\ l → fst (snd (c z xy h α {{cα}} t)) l ) ,
     ((\ pα → snd (snd (c z xy h α {{cα}} t)) (inl pα) ))) ,
    (λ= \ xy → λ= \ h → λ= \ α → λ=inf \ cα → λ= \ t → pair= (! (snd (snd (c `0 xy h α {{cα}} t)) (inr (inl id)))) (pair= (λ= \ _ → uip) (λ= \ _ → uip) )) ,
    (λ= \ xy → λ= \ h → λ= \ α → λ=inf \ cα → λ= \ t → pair= (! (snd (snd (c `1 xy h α {{cα}} t)) (inr (inr id)))) (pair= (λ= \ _ → uip) (λ= \ _ → uip) )) where
    c : ∀ z xy h α {{cα}} t → _
    c z xy h α {{cα}} t = dhcom1 xy h (α ∨ ((z == `0) ∨ (z == `1)))
                                 (\ xy → case (\ pα → t xy pα)
                                              (case01 (\ _ → fst (dhcom1 xy h α t) , (\ l → fst (snd (dhcom1 xy h α t)) l))
                                                      (\ _ → fst (dhcom2 xy h α t) , (\ l → fst (snd (dhcom2 xy h α t)) l )))
                                              (\ pα → ∨-elim01 _ (\ z=0 → pair= (snd (snd (dhcom1 xy h α t)) pα) (λ= \ _ → uip))
                                                                 ((\ z=1 → pair= (snd (snd (dhcom2 xy h α t)) pα) (λ= \ _ → uip))))) 

  

  private
    -- warm up special case

    hasDHCom0 : ∀ {l} (A : Set l) → Set l
    hasDHCom0 A = (x : 𝟚) (y : 𝟚) → y ≤ x
                 → (t : (y : 𝟚) → (x == ``1) → A)
                 → (b : A [ (x == ``1) ↦ t ``0 ])
                 → A [ (x == ``1) ↦ t y , y == ``0 ↦ k (fst b) ]
  
    compose0 : ∀ {l} {A : Set l} (dhcomA : hasDHCom0 A)
              {a0 a1 a2 : A}
            → Hom A a0 a1 → Hom A a1 a2
            → Hom A a0 a2
    compose0 dhcomA p q =
      (\ x → fst (c x)) , fst (snd p) ∘  ! (snd (snd (c ``0)) id)   , snd (snd q) ∘ ! (fst (snd (c ``1)) id)  where
      c : (x : _) → _
      c x = dhcomA x x
                   (id)
                   (\ y _ → fst q y ) (fst p x , (\ x=1 → ! (ap (fst p) x=1) ∘ ! (snd (snd p)) ∘ fst (snd q) ))




  private
    -- ----------------------------------------------------------------------
    -- filling operation is logically equivalent to fibrant one
    -- (this should be an isomorphism or equivalence)

    -- FIXME: redo for hasDHCom above instead of this version, which expands the horn
  
    hasDHCom' : ∀ {l} (A : Set l) → Set (lmax (lsuc lzero) l)
    hasDHCom' A = (x : 𝟚) (y : 𝟚) (y≤x : y ≤ x)
                 → (s : (y : 𝟚) → A)
                 → (b : (x : 𝟚) → A [ (x == ``1) ↦ k (s ``0) ])
                 → (α : Set) {{ cα  : Cofib α }}
                 → (t : (x y : 𝟚) → y ≤ x → α → A [ y == ``0 ↦ k (fst (b x)) , x == ``1 ↦ k (s y) ])
                 → A [ (x == ``1) ↦ k (s y) , y == ``0 ↦ k (fst (b x)) , α ↦ fst o t x y y≤x ]
  
    Triangle : ∀ {l} (A : Set l) {a0 a1 a2 : A} → Hom A a0 a1 → Hom A a1 a2 → Hom A a0 a2 → Set l
    Triangle A p q r =
      Σ \ (f : (x : 𝟚) (y : 𝟚) → y ≤ x → A) →
          ((x : 𝟚) → f x ``0 id == fst p x) ×
          (((y : 𝟚) → f ``1 y id == fst q y) ×
          ((z : 𝟚) → f z z id == fst r z))
  
    Triangle= : ∀ {l} {A : Set l} {a0 a1 a2 : A} {p : Hom A a0 a1} {q : Hom A a1 a2} {r : Hom A a0 a2}
             → (t1 t2 : Triangle A p q r)
             → ((x y : 𝟚) (l : y ≤ x) → fst t1 x y l == fst t2 x y l )
             → t1 == t2
    Triangle= t1 t2 h = pair= (λ= \ x → λ= \ y → λ= \ l → h x y l) (pair= (λ= \ _ → uip) (pair= ((λ= \ _ → uip)) ((λ= \ _ → uip))))
  
    transport-Triangle : ∀ {l} {A : Set l} {a0 a1 a2 : A} {b : Hom A a0 a1} {s : Hom A a1 a2}
                         {h h' : Hom A a0 a2} → (p : h == h')
                         (t : Triangle A b s h)
                       → (transport (Triangle A b s) p t) == (fst t , fst (snd t) , fst (snd (snd t)) , (\ z → ap (\ f → fst f z) p ∘ snd (snd (snd t)) z))
    transport-Triangle {A = A}{b = b}{s = s}{h' = h'} id t = Triangle= {A = A} {p = b} {q = s} {r = h'} t ((fst t , fst (snd t) , fst (snd (snd t)) , (\ z → id ∘ snd (snd (snd t)) z))) (\ _ _ _ → id)
  
    isSegal : ∀ {l} (A : Set l) → Set l
    isSegal A = {a0 a1 a2 : A} (p : Hom A a0 a1) (q : Hom A a1 a2) → Contractible (Σ \ r → Triangle A p q r)
  
    from-internal : ∀ {l} (A : Set l)
                  → isSegal A
                  -- FIXME: also need enough about A that Σ Triangle has hcom,
                  -- probably enough that A hasHcom?
                  → ({a0 a1 a2 : A} (p : Hom A a0 a1) (q : Hom A a1 a2) → hasHCom (Σ \ r → Triangle A p q r))
                  → hasDHCom' A
    from-internal A segA hcomΣTriangle x y y≤x s b α t = 
        fst (snd (fst e)) x y y≤x ,
        (\ {id →  ap (fst (snd (fst e)) ``1 y) (uip {p = id} {q = y≤x})  ∘ ! (fst (snd (snd (snd (fst e)))) y)}) ,
        (\ {id → ap (fst (snd (fst e)) x ``0)  (uip {p = id} {q = y≤x}) ∘ ! (fst (snd (snd (fst e))) x) }) ,
        (\ pα → ap (\ h → fst (snd h) x y y≤x) (snd e pα))   where
      p = ((\ x →  fst (b x)  ) , id , id)
      q = ((\ y → (s y)) , (snd (b ``1)) id  , id)
        
      se : _ 
      se = segA p q
  
      e = contr-extend-partial ( hcomΣTriangle p q ) se α
          (\ pα → ((\ x → fst (t x x id pα)) ,
                   ! (fst (snd (t ``0 ``0 id pα)) id) ,  ! (snd (snd (t ``1 ``1 id pα)) id)) ,
                  (\ x y y≤x → fst (t x y y≤x pα)) ,
                  (\ x → ! (fst (snd (t x ``0 id pα)) id)) , (\ y → ! (snd (snd (t ``1 y id pα)) id)  ) , (\ _ → id))
  
    to-internal : ∀ {l} (A : Set l) → hasDHCom' A → isSegal A 
    to-internal A dhcomA b s =
      -- center
      (-- mor
       centermor ,
       -- triangle
       (\ x y y≤x → fst (f x y y≤x)) ,
        (\ x → ! (fst (snd (snd (f x ``0 id))) id)) ,
        (\ y → ! (fst (snd (f ``1 y id)) id)) ,
        (\ _ → id)) ,
      -- unique
      (\ ht → -- path
              (\ z →
                 -- morphism
                 ((\ x → fst (u ht z x x id)) ,
                 -- morphism boundary
                  fst (snd b) ∘ ! (fst (snd (snd (u ht z ``0 ``0 id))) id)  ,
                  snd (snd s) ∘ ! (fst (snd (u ht z ``1 ``1 id)) id)) ,
                 -- triangle
                 (\ x y y≤x → fst (u ht z x y y≤x) ) ,
                 -- triangle boundary
                 (\ x → ! (fst (snd (snd (u ht z x ``0 id))) id)) ,
                 (\ y → ! (fst (snd (u ht z ``1 y id)) id)) ,
                 (\ _ → id)) ,
              -- path boundary        
              pair= (HomO= _ _ (\ x → ! (snd (snd (snd (u ht `0 x x id))) (inl id))))
                    ( (Triangle= {A = A} {p = b} {q = s} {r = centermor}
                                 ((\ x y y≤x → fst (u ht `0 x y y≤x)) , _)
                                 ((λ x y y≤x → fst (f x y y≤x)) , _)
                                 (\ x y y≤x → ! ((snd (snd (snd (u ht `0 x y y≤x)))) (inl id))) ∘
                       transport-Triangle {A = A} {b = b} {s = s} (HomO= _ _ (\ x → ! (snd (snd (snd (u ht `0 x x id))) (inl id)))) _ ) ) ,
              pair= (HomO= _ _ (\ x → snd (snd (snd ((snd ht)))) x ∘ ! (snd (snd (snd (u ht `1 x x id))) (inr id))))
                    (Triangle= {A = A} {p = b} {q = s} {r = fst ht}
                               ((λ x y y≤x → fst (u ht `1 x y y≤x)) , _) _
                               (\ x y y≤x → ! (snd (snd (snd (u ht `1 x y y≤x))) (inr id)) )
                     ∘ transport-Triangle {A = A} {b = b} {s = s} (HomO= _ _ (\ x → snd (snd (snd ((snd ht)))) x ∘ ! (snd (snd (snd (u ht `1 x x id))) (inr id)))) _) ) where
      f : (x : _) (y : _) → (y≤x : _) → _
      f x y y≤x = dhcomA x y y≤x
                    (\ y → fst s y )
                    (\ x → fst b x ,
                     (\ x=1 → ap (fst b) (! x=1) ∘ ! (snd (snd b)) ∘ fst (snd s) ))
                    ⊥
                    (\ _ _ _ → abort)
  
      u : (b : Σ (Triangle A b s)) (z : I) (x : _) (y : _) (y≤x : _) → _
      u (h , t) z x y y≤x =
        dhcomA x y y≤x (\ y → fst s y )
                       (\ x → fst b x ,
                       (\ x=1 → ap (fst b) (! x=1) ∘ ! (snd (snd b)) ∘ fst (snd s) ))
                       ((z == `0) ∨ (z == `1))
                       (\ x y y≤x → (case (\ z=0 → fst (f x y y≤x) , (fst (snd (snd (f x y y≤x)))) , ((fst (snd (f x y y≤x)))))
                                          (\ z=1 → (fst t x y y≤x) , ((λ { id → ap (fst t x ``0) (uip {p = id} {q = y≤x}) ∘ ! (fst (snd t) x) }) , (λ { id → ap (fst t ``1 y) (uip {p = id} {q = y≤x}) ∘ ! (fst (snd (snd t)) y)  })))
                                          (λ p q → abort (iabort (q ∘ ! p)))) )
                    
      centermor = ((\ x → fst (f x x id)) ,
                   fst (snd b) ∘ ! (fst (snd (snd (f ``0 ``0 id))) id) ,
                   snd (snd s) ∘ ! (fst (snd (f ``1 ``1 id)) id))


  -- ----------------------------------------------------------------------
  -- trying to understand some different composition conditions 
  private

    {- this one is more like a cubical hcom 
     but I don't see how to prove hasDHCom from it,
     so maybe hasDHComFixX is *stronger*?
  
     that kinds makes sense, because it has more uniformity built in,
     which is what makes it easier to go up dimensions
    -}
  
    is≤ : 𝟚 → Set
    is≤ x = Σ \ y → y ≤ x
  
    Λ₂' : (x : 𝟚) → is≤ x → Set
    Λ₂' x (y , y≤x) = (y == ``0) ∨ (x == ``1)
  
    hasDHComFixX : ∀ {l} (A : Set l) → Set (lmax (lsuc lzero) l)
    hasDHComFixX A = (x : 𝟚) (y : is≤ x)
                   → (h : (y : is≤ x) → Λ₂' x y → A)
                   → (α : Set) {{ cα  : Cofib α }}
                   → (t : (y : is≤ x) → α → A [ Λ₂' x y ↦ (h y) ])
                   → A [ Λ₂' x y ↦ h y , α ↦ fst o t y ]

    {- I don't see how to do this
    l : ∀ {l} (A : Set l) → hasDHCom A → hasDHComFixX A
    l A dhcomA x y h α t = {!!} where
      d = dhcomA (x , fst y , snd y)
                 (\ x'y l →
                   {! case 
                     (\ x'≤x → h ( fst (snd x'y) , {!!}) {!l!}) 
                     ((\ x≤x' → h ({!!} , {!!}) {!!} ) )
                     {!!}
                     (ditotal (fst x'y) x) !})
                 α
                 {!!}
    -}
  
    r : ∀ {l} (A : Set l) → hasDHComFixX A → hasDHCom A 
    r A dhcomA xy h α t = dhcomA (fst xy) (snd xy) (\ y l → h (fst xy , y) l) α (\ y pα → t (fst xy , y) pα)


    -- doesn't seem to just be about the ≤
    -- why is the condition different??
  
    Λ₂'' : (x y : 𝟚) → Set
    Λ₂'' x (y) = (y == ``0) ∨ (x == ``1)
  
    hasDHComSquare : ∀ {l} (A : Set l) → Set (lmax (lsuc lzero) l)
    hasDHComSquare A = (x : 𝟚) (y : 𝟚)
                     → (h : (y : 𝟚) → Λ₂'' x y → A)
                     → (α : Set) {{ cα  : Cofib α }}
                     → (t : (y : 𝟚) → α → A [ Λ₂'' x y ↦ (h y) ])
                     → A [ Λ₂'' x y ↦ h y , α ↦ fst o t y ]
  
    hasDHComSquareDontFixX : ∀ {l} (A : Set l) → Set (lmax (lsuc lzero) l)
    hasDHComSquareDontFixX A = (x : 𝟚) (y : 𝟚)
                         → (h : (x : 𝟚) (y : 𝟚) → Λ₂'' x y → A)
                         → (α : Set) {{ cα  : Cofib α }}
                         → (t : (x : 𝟚) (y : 𝟚) → α → A [ Λ₂'' x y ↦ (h x y) ])
                         → A [ Λ₂'' x y ↦ h x y , α ↦ fst o t x y ]

    {- I don't see how to do this
    lSquare : ∀ {l} (A : Set l) → hasDHComSquareDontFixX A → hasDHComSquare A 
    lSquare A hcomA x y h α t = hcomA x y (\ x' y l → h y {!!}) {!!} {!!}
    -}


