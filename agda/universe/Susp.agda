{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Prop
open import Cofibs
open import Kan
open import Equiv
open import Susp
open import universe.Universe
open import universe.Path
open import Path

module universe.Susp where

  Susp-elim-U : ∀ {l l' :{♭} Level} {A : U {l}}
                (C : Susp (El A) → U {l'})
              → (n : El (C north))
              → (s : El (C south))
              → ((a : El A) → PathO (\ x → El(C(merid a x))) n s )
              → (x : Susp (El A)) → El(C x)
  Susp-elim-U C = Susp-elim (\ x → El (C x)) (comEl' C)

  -- Note: trying to replace the explicit com constructions here with uses of U didn't work,
  -- because we ended up needing (A r') to be crisp, when r' isn't.
  -- I guess the reason is that A r' can depend on some intervals, just not the direction of the coe

  -- Susp-closed-code-universal : ∀ {l :{♭} Level} (A :{♭} U {l}) → Unit{lzero} → U{l}
  -- Susp-closed-code-universal A = code (Unit{lzero}) (\ _ → Susp (El A)) (relCom-constant _ fcomSusp) 

  suspη : ∀ {l' :{♭} Level} (A : U {l'}) (x : Susp (El A))
          → Path (Susp (El A)) 
            (Susp-elim (\ _ → Susp (El A)) (relCom-constant _ (fcomSusp)) north south (\ a → (\ x → merid a x) , id , id ) x)
            x
  suspη A = Susp-elim _ 
                   (comPath-endpoints (\ z → (Susp-elim (λ _ → Susp (El A)) (relCom-constant (Susp (El A)) fcomSusp) north south (λ a → merid a , id , id) z)) (\ z → z)
                                      fcomSusp ) -- Note be careful when syntacticfying, this isn't necessarily hcom_(Path_(Susp A)) !
                   ((\ _ → north) , id , id) 
                   (((\ _ → south) , id , id)) 
                   (\ a → ((\ x →  (\ _ → merid a x), id , id ) , id , id) )

  -- Note: really only needs coe_A, not com; see the external version
  wcoeSusp : ∀ {l' :{♭} Level} (A : I → U {l'})
          → hasWCoe (\ x → Susp (El (A x)))
  wcoeSusp A r r' = 
    (s (\ x → fst(movea x)) , (\ {id b → fst (suspη (A r') b) ,  ap= (ap s (λ= \ x → snd (movea x) id  )) {b}  ∘ fst (snd (suspη (A r') b))  , snd (snd (suspη (A r') b))}))  where

    movea : (a : _) → _
    movea a = coeU A r r' a

    s : (movea1 : _) (b : _) → _
    s movea1 = Susp-elim (\ _ → Susp (El (A r')))
                  ((relCom-constant _ fcomSusp)) 
                  (north) 
                  (south) 
                  (\ a → (\ x → merid (movea1 a) x) , id , id) 

  comSusp-universal : {l :{♭} Level} (A : I → U {l}) → hasCom (Susp o El o A)
  comSusp-universal A = decompose-hasCom (Susp o El o A) (\ x → fcomSusp ) (hasCoe-from-hasWCoe (Susp o El o A) (\ _ → fcomSusp) (wcoeSusp A))

  Susp-code-universal : ∀ {l :{♭} Level} → U{l} → U{l}
  Susp-code-universal = code (U) (\ A → Susp (El A)) comSusp-universal 

  Susp-code : ∀ {l1 l :{♭} Level} {Γ : Set l1} → (Γ → U{l}) → Γ → U{l}
  Susp-code A = Susp-code-universal o A

  Susp-code-El : ∀ {l1 l :{♭} Level} {Γ : Set l1} → (A : Γ → U{l}) (θ : Γ) → El (Susp-code A θ) == Susp (El (A θ))
  Susp-code-El A θ = id
