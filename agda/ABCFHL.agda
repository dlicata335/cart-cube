-- agda library
open import Lib
open import Prop

-- axioms for the interval and cofibrations
open import Interval
open import Cofibs

-- definition of Kan operation
open import Kan

-- basic types
open import Bool
open import Path
open import Id
open import Nat
open import Susp

-- glue types
open import Strictify
open import Glue

-- lemmas
open import Contractible
open import Equiv
open import Glue-Weak

-- definition of the universe of Kan types
open import universe.LibFlat
open import universe.Universe

-- Kan operations: 
open import universe.Pi
open import universe.Sigma
open import universe.Path
open import universe.Bool
open import universe.Nat
open import universe.Glue
open import universe.Case
open import universe.U -- universe itself is Kan
open import universe.Univalence -- univalence axiom
open import universe.Id
open import universe.Susp

-- version of composition for glue from original draft
open import com-glue-decomposed.Glue-Com
open import com-glue-decomposed.Glue-HCom
open import com-glue-decomposed.Glue-WCoe
open import com-glue-decomposed.VType
open import universe.Glue-Decomposed 

-- "Dagstuhl lemma"
open import com-glue-dagstuhl.IsEquiv-FillRefl
open import com-glue-dagstuhl.LemEqConstant
-- open import com-glue-dagstuhl.Glue-Com-Combined-FillRefl

-- ----------------------------------------------------------------------
-- not used in the paper

-- "internal" proofs of fibrancy for types without mentioning the universe
open import ComInternal

-- composition for glue with a function (not nec. an equivalence)
-- if the cofibration is constant
open import Glue-Com-NoCofib

-- com is an hprop
open import Com-is-an-HProp


module ABCFHL where
