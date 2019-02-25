{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib
open import Interval
open import Cofibs
open import Kan
open import Path

module Susp where


  postulate 
    Susp : {l : Level} (A : Set l) → Set l
    north : {l : Level} {A : Set l} → Susp A
    south : {l : Level} {A : Set l} → Susp A
    merid : {l : Level} {A : Set l} → A → I → (Susp A)
    merid0 : {l : Level} {A : Set l} (x : A) → merid x `0 == north
    merid1 : {l : Level} {A : Set l} (x : A) → merid x `1 == south
  {-# REWRITE merid0 #-}
  {-# REWRITE merid1 #-}
  postulate
    fcomSusp : {l : Level} {A : Set l} → hasHCom(Susp A)
    Susp-elim : {l l' : Level} {A : Set l}
                (C : Susp A → Set l')
              → (comC : relCom C)
              → (n : C north)
              → (s : C south)
              → ((a : A) → PathO (\ x → C(merid a x)) n s )
              → (x : Susp A) → C x
    Susp-elim-north : {l l' : Level} {A : Set l}
              (C : Susp A → Set l')
              → (comC : relCom C)
              → (n : C north)
              → (s : C south)
              → (m : (a : A) → PathO (\ x → C(merid a x)) n s )
              → (Susp-elim C comC n s m north) == n
    Susp-elim-south : {l l' : Level} {A : Set l}
              (C : Susp A → Set l')
              → (comC : relCom C)
              → (n : C north)
              → (s : C south)
              → (m : (a : A) → PathO (\ x → C(merid a x)) n s )
              → (Susp-elim C comC n s m south) == s
    Susp-elim-merid : {l l' : Level} {A : Set l}
              (C : Susp A → Set l')
              → (comC : relCom C)
              → (n : C north)
              → (s : C south)
              → (m : (a : A) → PathO (\ x → C(merid a x)) n s )
              → (a : A) (x : I) → (Susp-elim C comC n s m (merid a x)) == fst (m a) x
  {-# REWRITE Susp-elim-north #-}
  {-# REWRITE Susp-elim-south #-}
  {-# REWRITE Susp-elim-merid #-}
  postulate
    Susp-elim-fcom : {l l' : Level} {A : Set l}
              (C : Susp A → Set l')
              → (comC : relCom C)
              → (n : C north)
              → (s : C south)
              → (m : (a : A) → PathO (\ x → C(merid a x)) n s )
              → Strictly-Preserves-HCom (Susp A) C fcomSusp comC (Susp-elim C comC n s m)

