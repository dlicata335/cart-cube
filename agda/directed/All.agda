
-- axioms for the directed interval, hom types
-- this includes Theorem 2 in paper (comHom)
open import directed.DirInterval

-- definiton of covariance
-- includes Definition 4 (relCov), part of Theorem 5 (rcov-hprop, to-internal, from-internal)
open import directed.Covariant
-- rest of Theorem 5 (com-hasCov)
open import directed.Covariant-is-Fibrant

-- definition of UCov
open import directed.UCov

-- covariance for some basic types: 
open import directed.universe.Hom
open import directed.universe.Pi
open import directed.universe.Sigma 

-- directed univalence for ucov
open import directed.universe.FunGlueKan -- gluing with a function at a directed interval is Kan
open import directed.universe.FunGlue    -- gluing with a function at a directed interval is covariant
open import directed.DirUnivalenceReflection -- directed univalence for ucov (reflection part)
open import directed.DirUnivalence -- covariance equivalence axiom and rest of directed univalence

-- path univalence for ucov
open import directed.universe.Glue-Equiv-Covariant -- glue with an equivalence is covariant
open import directed.universe.UCov-Com -- UCov is Kan (note: import this late because of rewrites)
open import directed.UCov-Univalence -- path univalence for ucov

-- definition of segal, associativity
open import directed.Segal

-- dependent triangle filling in covariant types
open import directed.SegalDepCovariant
-- sigma of a covariant fibration over a segal type is segal
open import directed.Sigma

-- properties of discrete types
open import directed.Discrete


-- ----------------------------------------------------------------------
-- not mentioned in the paper

-- derivation of "Weld" types from strictification axiom 
open import directed.GlueUp

-- partial files: 

-- "chaotic" types
-- open import directed.Chaotic

-- definition of cartesian fibrations
-- open import directed.moreFibs


module directed.All where
