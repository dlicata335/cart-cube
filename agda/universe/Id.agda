{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (lzero; lsuc; Level; _⊔_)

open import Lib
open import Kan
open import Interval
open import Cofibs
open import Prop
open import Path
open import universe.Universe
open import universe.Path
open import Id

module universe.Id where

  scontrId : ∀ {l :{♭} Level} (A : U {l}) → (a : El A) → 
            (s : (Σ \ b → Id (El A) b a)) → Id (Σ \ b → Id (El A) b a) (a , refl (El A) a) s
  scontrId A a (b , (α , p , isrefl)) = 
          -- where the path in S(a) is constant
          α , 
          ((\ x → -- path in A
                  fst (square b p α isrefl x `0) , 
                  -- path in Id
                    -- where it's constant
                    ((x == `0) ∨ (fst α) , Cofib∨ Cofib= ((snd α))) , 
                    -- path in Path, with endpoints proofs
                    (((\ y → fst (square _ p α (isrefl) x y))) , 
                       id , ! (snd (snd (square _ p α (isrefl) x `1)) id)) , 
                    -- proof of constancy, because both are constant on the α from s
                    (case (\ x=0 → λ= \ y → fst (snd (square b p α isrefl x `0)) (inl (inl x=0)) ∘ ! (fst (snd (square b p α isrefl x y)) (inl (inl x=0))) ) 
                          (\ pα → λ= \ z → fst (snd (square b p α isrefl x `0)) (inr pα) ∘ 
                                   ! (fst (snd (square b p α isrefl x z)) (inr pα)))
                          (\ _ _ → uip))) , 
           -- correct boundary 1: x=0 from tube, and propositional univalence for cofibs
           pair= (! (fst (snd (square b p α isrefl `0 `0)) (inl (inl id))) ) 
                                       -- copy and paste sigh
                 ( (Id=-transport1 _ _ (! (fst (snd (square b p α isrefl `0 `0)) (inl (inl id))) )
                   ( (pair= (Cofib-propositional-univalence {{ cα = Cofib∨ Cofib= (snd α) }} {{ cβ = Cofib⊤ }} (\ _ → <>) 
                          (\ _ → inl id))
                          Cofib-prop) ) 
                   (\ x → (! (fst (snd (square b p α isrefl `0 x)) (inl (inl id))) ) )) ) , 
           -- correct boundary 2:
           pair= (fst (snd p) ∘ (! (fst (snd (square b p α isrefl `1 `0)) (inl (inr id))) ))
                 ((Id=-transport1 _ _  (fst (snd p) ∘ (! (fst (snd (square b p α isrefl `1 `0)) (inl (inr id))) ))
                                       (pair= (Cofib-propositional-univalence {{cα = Cofib∨ Cofib= (snd α)}} {{cβ = snd α}} 
                                                 (case (\q → abort (iabort (! q))) (\ p → p) (\ _ → \ pα → Cofib.eq (snd α) _ _))
                                                 inr) 
                                              Cofib-prop ) 
                                       (\ x → ! (fst (snd (square b p α isrefl `1 x)) (inl (inr id)))) ))
           ) , 
           -- path in S(a) is constant
           (\ pα → λ= \ x → pair= (! (fst (snd (square b p α isrefl x `0)) (inr pα))) 
                                   ( (Id=-transport1 _ _ (! (fst (snd (square b p α isrefl x `0)) (inr pα)))
                                      (pair= ( (Cofib-propositional-univalence {{cα = Cofib∨ Cofib= (snd α)}} {{cβ = Cofib⊤}} 
                                                                             (\ _ → <>) (\ _ → inr (pα))) )
                                             Cofib-prop) 
                                      (\ y → ! (fst (snd (square b p α isrefl x y)) (inr pα)))) ))
     where
     square : (b : _) (s : Path (El A) b a) (α : Cofibs) (isrefl : fst α → IsRefl (El A) s) (x : _) (y : _) → _
     square b s α isrefl x y = hcomEl A `1 y (((x == `0) ∨ (x == `1)) ∨ fst α)
                                {{ Cofib∨ (Cofib∨ Cofib= Cofib=) (snd α) }}
                                (\ y → case (case (\ _ → a) 
                                                   (\ _ → fst s y) 
                                                   (\ p q → abort (iabort (q ∘ ! p)) ))
                                             (\ _ → a)
                                             (∨-elim _ (\ _ _ → id) 
                                                       (\ _ pα →  (snd (snd s)) ∘ ! (ap= (isrefl pα)) ∘ ap= (isrefl pα) )
                                                       (\ _ _ → (λ= \ _ → uip))))
                                (a  , ∨-elim _ 
                                             (∨-elim _ (\ x=0 → snd (snd s) ∘ ! (snd (snd s)))
                                                         (\ x=1 → snd (snd s)) (\ _ _ → uip))
                                             (\ _ → id) 
                                             (\ _ _ → uip))

  scontrId-refl : ∀ {l :{♭} Level} (A : U {l}) → (a : El A) → 
             scontrId A a (a , refl (El A) a) == refl (Σ \ b → Id (El A) b a) (a , refl (El A) a)
  scontrId-refl A a = Id= _ _ id (\ x →  ap= (snd (snd (scontrId A a (a , refl (El A) a))) <>) {x})

  transportId : {l1 l2 :{♭} Level} (A : Set l1) (a0 : A) (C : A → U {l2}) 
    → (c : El (C a0))
    → Σ \ (f : (a1 : A) (p : Id A a0 a1) → El (C (a1))) → f a0 (refl A a0) == c
  transportId A a0 C c = 
    (\ a1 p → transport (El o C) (snd (snd (fst (snd p)))) (fst (com a1 p))) , 
     ! (fst (snd (com a0 (refl A a0))) <>)
    where
    com : (a1 : _) (p : _) → _
    com a1 p = (comEl (\ x → C (fst (fst (snd p)) x))
                       `0 `1 (fst (fst p)) {{ snd (fst p) }} 
                       (\ z pp →  transport (El o C) (! (ap= (snd (snd p) pp){z})) c )
                       (transport (El o C) (! (fst (snd (fst (snd p))))) c , 
                          (\ pp → ap (\ h → transport (El o C) h c) (uip {p = (! (ap= (snd (snd p) pp)))} {q = (! (fst (snd (fst (snd p)))))}))))

  J : {l1 l2 :{♭} Level} (A : U {l1}) → (a0 : El A)     
    → (C : (Σ \ (a : El A) → Id (El A) a a0) → U {l2}) 
    → (c : El (C (a0 , refl (El A) a0)))
    → Σ \ (f : (a1 : El A) (p : Id (El A) a1 a0) → El (C (a1 , p))) → f a0 (refl (El A) a0) == c
  J A a0 C c = (\ a1 p → (fst tr (a1 , p) (scontrId A a0  (a1 , p) ))) , 
                          snd tr ∘  ap (fst tr (a0 , refl (El A) a0)) (scontrId-refl A a0)  where 
    tr = transportId (Σ \ b → Id (El A) b a0) (a0 , refl (El A) a0) C c

  IdData : ∀ {l :{♭} Level} → Set (lsuc (lsuc lzero) ⊔ lsuc l)
  IdData {l} = (Σ \ (A : U {l}) → El(A) × El(A))

  Id-from-data : ∀ {l :{♭} Level} → IdData{l} → Set _
  Id-from-data Aab = Id (El (fst Aab)) (fst (snd (Aab))) (snd (snd (Aab)))

  comId-universal : ∀ {l :{♭} Level} → relCom (Id-from-data{l})
  comId-universal Aa0a1 r r' α {{ cα }} t b = 
    ( (newα , newα-cofib), 
     fst c , 
     -- c is constant on newα
     case (\ l → λ= \ x → ap= (snd (snd (t r' (fst l))) (snd l)) ∘ ap (\ h → fst h x) (! (fst (snd c) (fst l))) )
          (\ ri → λ= \ x → (apd (\ h → a0 h) (fst ri) ∘ ap (transport (λ z → El (A z)) (fst ri)) (ap= (snd (snd (fst b)) (snd ri)){x}) ∘ 
                            ap= (fst-transport-Path (fst ri) (fst (snd (fst b)))) )
                  ∘ ap (\ h → fst h x) (! (snd (snd c) (fst ri)))) 
          (\ _ _ → uip)) , 
    -- important that for the coherences that  α, r=r' ⊢ φ_{t r'} == φ_{b}
    (\ pα → Id= _ _ (pair= (Cofib-propositional-univalence {{ cα = (snd (fst (t r' pα))) }} {{ cβ = newα-cofib }} 
                               (\ pt → inl (pα , pt)) 
                               (case (\ p → transport (\ h → fst (fst (t r' h))) (Cofib.eq cα _ _) (snd p))
                                     (\ q → coe (ap (\ h → fst (fst (t h pα))) (fst q) ∘ ! (ap fst (ap fst (snd b pα)))) (snd q)) 
                                     (\ _ _ → Cofib.eq (snd (fst (t r' pα))) _ _))) 
                           Cofib-prop) 
                     (\ x → ap (\ h → fst h x) (fst (snd c) pα))) , 
    (\ {id → Id= _ _ (pair= ( (Cofib-propositional-univalence {{ cα = (snd (fst (fst b))) }} {{ cβ = newα-cofib }} 
                               (\ pb → inr (id , pb)) 
                               (case (\ p → coe (ap fst (ap fst ((snd b (fst p))))) (snd p)) 
                                     (\ q → snd q) 
                                     (\ _ _ → Cofib.eq (snd (fst (fst b))) _ _)
                               )) ) 
                           Cofib-prop) 
                     (\ x →  ap (\ h → fst h x) (snd (snd c) id) )}) where
  
       A = \z → fst (Aa0a1 z)
       a0 = \z → fst (snd (Aa0a1 z))
       a1 = \z → snd (snd (Aa0a1 z))
       c =  comEl   (Path-code {Γ = I} (\ z → A (fst z)) a0 a1 ) r r' 
                    α (\ z pα → (fst (snd (t z pα))))
                    (fst (snd (fst b)) , 
                      (λ x → ap (\ x → fst (snd x)) (snd b x) )) 

       newα = (Σ \ (pα : α) → (fst (fst (t r' pα)))) ∨ ((r == r') × fst (fst (fst b))) 
       newα-cofib = Cofib∨ (Cofib∧ cα (\ pα → snd (fst (t r' pα)))) (Cofib∧ (Cofib={r}{r'}) (\_ → snd (fst (fst b))))

  Id-code-universal : ∀ {l :{♭} Level} → IdData{l} → U{lsuc lzero ⊔ l}
  Id-code-universal = code (IdData) Id-from-data comId-universal

  Id-code : ∀ {l1 l2 :{♭} Level} {Γ : Set l1}
              (A : Γ → U{l2})
              (a0 : (θ : Γ) → El (A θ))
              (a1 : (θ : Γ) → El (A θ))
              → Γ → U{lsuc lzero ⊔ l2}
  Id-code A a0 a1 θ = Id-code-universal (A θ , a0 θ , a1 θ)

  
