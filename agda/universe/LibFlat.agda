{-# OPTIONS --rewriting #-}

open import Agda.Primitive using (Level;lsuc;_⊔_;lzero)
open import Lib

module universe.LibFlat where

  ap♭ :  {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} {B : Set l2} {M N :{♭} A}
       (f : (_ :{♭} A) → B) → (_ :{♭} M == N) → (f M) == (f N)
  ap♭ f id = id

