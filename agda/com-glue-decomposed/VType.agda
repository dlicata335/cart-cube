{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Prop
open import Interval
open import Equiv
open import Path
open import Equiv
open import Cofibs
open import Kan
open import Glue
open import com-glue-decomposed.Glue-HCom
open import Glue-Weak
open import com-glue-decomposed.Glue-WCoe

module com-glue-decomposed.VType {l : Level} {A B : Set l} (e : Equiv A B) (hcomB : hasHCom B) where

    Vcofib : I → Cofibs
    Vcofib = (\ (x : I) → (x == `0) ∨ (x == `1) , Cofib∨ Cofib= Cofib=)
    VT : (x : I) → fst (Vcofib x) → Set l
    VT = (\ x → case (\ _ → A) (\ _ → B) (\ p q → abort (iabort (q ∘ ! p))) )
    VB : I → Set l
    VB = (\ _ → B)
    Vf : (x : I) → (p : fst (Vcofib x)) → VT x p → VB x
    Vf = (\ x → ∨-elim _ (\ _ → fst e) (\ _ x → x) (\ p q → abort (iabort (q ∘ ! p))))
    Vfeq : (x : I) → (p : fst (Vcofib x)) → isEquiv _ _ (Vf x p)
    Vfeq = (\ x → ∨-elim _ (\ _ → snd e)
                           (\ _ x → id-Equiv hcomB x)
                           (\ p q → abort (iabort (q ∘ ! p))))

    wcoe-isweq-V : (comA∨B : relCom (\ p → VT (fst p) (snd p))) (x : _) 
                   → 
                  Path B (coe ((Glue-α (fst (Vcofib `1)) (VT `1) (VB `1) (Vf `1) (inr id)))
                              (fst (wcoe-isweq {Γ = I} Vcofib VT VB Vf Vfeq 
                                    comA∨B
                                    (relCom-constant B hcomB)
                                    (\ x → x)
                                    `0
                                    `1)
                                    x))
                          (fst e (coe (Glue-α (fst (Vcofib `0)) (VT `0) (VB `0) (Vf `0) (inl id)) x))
    wcoe-isweq-V comA∨B x = (\ x → (fst p x)) , ! equations ∘ fst (snd p) , snd (snd p)  where
      x' = (coe (Glue-α (fst (Vcofib `0)) (VT `0) (VB `0) (Vf `0) (inl id)) x)

      -- copied the relevant definitions from wcoe-glue

      b' = (fst (relCom-relCoe VB (relCom-constant B hcomB) (\ x → x) `0 `1 (unglue x)))

      equations : coe (Glue-α _ _ _ _ (inr id))
                      (fst (wcoe-isweq {Γ = I} Vcofib VT VB Vf Vfeq comA∨B (relCom-constant B hcomB) (\ x → x) `0 `1) x)
               == (fst (relCom-relCoe VB (relCom-constant B hcomB) (\ x → x) `0 `1 (fst e x')))  
      equations = _ =〈 id 〉
                  coe (Glue-α _ _ _ _ (inr id))
                  (glue-weak {{snd (Vcofib `1)}}
                             hcomB
                             b'
                             ((\ pα → fst (Vfeq `1 pα _)) )) =〈 glue-α _ _ (inr id) 〉
                  fst (fst (id-Equiv hcomB b')) =〈 id 〉
                  b' =〈 ap (\ h → (fst (relCom-relCoe VB (relCom-constant B hcomB) (\ x → x) `0 `1 h))) (! (unglue-α x (inl id))) 〉
                  (_ ∎)

      p = coe-regular-path B (relCom-constant B hcomB) (\ x → x) `0 `1 (fst e x')
