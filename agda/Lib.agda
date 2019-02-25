{-# OPTIONS --rewriting #-}

open import Agda.Primitive

module Lib where

  ℓ₀ = lzero
  ℓ₁ = lsuc ℓ₀
  ℓ₂ = lsuc ℓ₁
  ℓ₃ = lsuc ℓ₂

  -- FIXME rename transport/coe so they look less HoTT-like

  _o_ : ∀ {l1 l2 l3} {A : Set l1} {B : Set l2} {C : Set l3} → (B → C) → (A → B) → A → C
  g o f = \ x → g (f x)
  infixr 10 _o_

  data _==_ {l : Level} {A : Set l} (M : A) : A → Set l where
    id : M == M

  {-# BUILTIN REWRITE _==_ #-}
  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL id #-}

  postulate
    λ=  : ∀ {l1 l2} {A : Set l1} {B : A -> Set l2} {f g : (x : A) -> B x} -> ((x : A) -> (f x) == (g x)) -> f == g
    λ=i  : ∀ {l1 l2} {A : Set l1} {B : A -> Set l2} {f g : {x : A} -> B x} -> ((x : A) -> (f {x}) == (g {x})) -> (\ {x} → f {x}) == (\ {x} → g {x})
    λ=inf  : ∀ {l1 l2} {A : Set l1} {B : A -> Set l2} {f g : {{x : A}} -> B x} -> ((x : A) -> (f {{x}}) == (g {{x}})) -> (\ {{x}} → f {{x}}) == (\ {{x}} → g {{x}})

  transport : ∀ {l1 l2 : Level} {A : Set l1} (C : A →  Set l2) {M N : A} 
              (P : M == N) → C M → C N
  transport C id x = x

  coe : ∀ {l1 : Level} {A B : Set l1} (P : A == B) → A → B
  coe p x = transport (\ X → X) p x

  ap :  {l1 l2 : Level} {A : Set l1} {B : Set l2} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
  ap f id = id

  ap2 : ∀ {l1 l2 l3} {A : Set l1} {B : Set l2} {C : Set l3}
          {M N : A} {M' N' : B} (f : A -> B -> C) -> M == N -> M' == N' 
          -> (f M M') == (f N N')
  ap2 f id id = id

  ! : ∀ {l} {A : Set l} {M N : A} → M == N → N == M
  ! id = id

  _∘_  : ∀ {l} {A : Set l} {M N P : A} → N == P → M == N → M == P
  β ∘ id = β

  _=〈_〉_ : ∀ {l} {A : Set l} (x : A) {y z : A} → x == y → y == z → x == z
  _ =〈 p1 〉 p2 = (p2 ∘ p1)
 
  _∎ : ∀ {l} {A : Set l} (x : A) → x == x
  _∎ _ = id

  infix  2 _∎
  infixr 2 _=〈_〉_ 

  infixr 10 _∘_ 

{-
  data Either {l1 l2 : Level} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2) where
    Inl : A → Either A B
    Inr : B → Either A B
-}

  record Σe {l1 l2} (A : Set l1) (B : A -> Set l2) : Set (l1 ⊔ l2) where
     constructor _,_
     field
       fst : A
       snd : B fst
  open Σe public
  
  Σ : ∀ {l1 l2} {A : Set l1} -> (B : A -> Set l2) -> Set (l1 ⊔ l2)
  Σ {_}{_}{A} B = Σe A B
  
  infixr 0 _,_
  
  syntax Σe A (\ x  -> B) = Σ[ x ∶ A ] B

  record Unit{l : Level} : Set l where
    constructor <> 

  _×_ : ∀{ l1 l2} → Set l1 -> Set l2 -> Set (l1 ⊔ l2)
  a × b = Σ (\ (_ : a) -> b)

  uip : ∀ {l} {A : Set l} {x y : A} {p q : x == y} → p == q
  uip {p = id} {q = id} = id

  data ⊥ {l : Level} : Set l where 
  
  abort : ∀ {l1 l2 : Level} {A : Set l2} → ⊥{l1} → A
  abort () 

  transport-ap-assoc' : ∀ {l1 l2 l3} {A : Set l1} {B : Set l2} (C : B → Set l3) (f : A → B) {M N : A} (α : M == N) 
                     → (transport (\ x -> C (f x)) α) == (transport C (ap f α))
  transport-ap-assoc' C f id = id 

  apd  : ∀ {l1 l2} {B : Set l1} {E : B → Set l2} {b₁ b₂ : B} 
         (f : (x : B) → E x) (β : b₁ == b₂) 
      → transport E β (f b₁) == (f b₂) 
  apd f id = id 

  apd!  : ∀ {l1 l2} {B : Set l1} {E : B → Set l2} {b₁ b₂ : B} 
         (f : (x : B) → E x) (β : b₁ == b₂) 
      → (f b₁) == transport E (! β) (f b₂) 
  apd! f id = id 

  ap= : ∀ {l1 l2} {A : Set l1} {B : A → Set l2} {f g : (x : A) → B x} 
        → f == g → {x : A} → (f x) == (g x)
  ap= α {x} = ap (\ f → f x) α

  ×= :  ∀ {l1 l2} {A : Set l1} {B : Set l2} {p q : A × B} -> (α : (fst p) == (fst q)) -> (snd p) == (snd q) -> p == q
  ×= id id = id

  pair= : ∀ {l1 l2} {A : Set l1} {B : A -> Set l2} {p q : Σ B} -> (α : (fst p) == (fst q)) -> (transport B α (snd p)) == (snd q) -> p == q
  pair= {p = x , y} {q = .x , .y} id id = id

  pair=! : ∀ {l1 l2} {A : Set l1} {B : A -> Set l2} {p q : Σ B} -> (α : (fst p) == (fst q)) -> (snd p) == transport B (! α) (snd q) -> p == q
  pair=! {p = x , y} {q = .x , .y} id id = id

  transport-∘ : {l1 l2 : Level} {A : Set l1} (C : A → Set l2) {M N P : A} (β : N == P) (α : M == N)
           →  (transport C (β ∘ α)) == (\ x → transport C β (transport C α x))
  transport-∘ _ id id = id

  transport-Π : ∀ {l l1 l2} {Γ : Set l} (A : Γ -> Set l1) (B : (γ : Γ) -> A γ -> Set l2)
            {θ1 θ2 : Γ} (δ : θ1 == θ2) (f : (x : A θ1) -> B θ1 x) 
         -> transport (\ γ -> (x : A γ) -> B γ x) δ f == 
            (\ x -> transport (\ (p : Σ \ (γ : Γ) -> A γ) -> B (fst p) (snd p))
                          (pair=! δ id)
                          (f (transport A (! δ) x)))
  transport-Π _ _ id f = id

  transport-→-post' : ∀ {l l1 l2} {Γ : Set l} (A : Set l1) (B : (γ : Γ) -> Set l2)
            {θ1 θ2 : Γ} (δ : θ1 == θ2) (f : A -> B θ1) (x : A) 
         -> (transport (\ (x : Γ) -> A -> B x) δ f) x == transport B δ (f  x)
  transport-→-post' _ _ id f x = id

  transport-→-pre' : ∀ {l1 l2 l3} {Γ : Set l1} {B : Set l2} (A : Γ -> Set l3) {θ1 θ2 : Γ} 
                  (δ : θ1 == θ2) (f : (x : A θ1) → B) 
     →  (transport (\ γ → (A γ) → B) δ f)  == (\ x -> f (transport (\ γ -> A γ) (! δ) x))
  transport-→-pre' _ id f = id 

  transport-→-pre-inv : ∀ {l1 l2 l3} {Γ : Set l1} {B : Set l2} (A : Γ -> Set l3) {θ1 θ2 : Γ} 
                  (δ : θ1 == θ2) (f : (x : A θ2) → B) 
     →  (transport (\ γ → (A γ) → B) (! δ) f)  == (\ x -> f (transport (\ γ -> A γ) δ x))
  transport-→-pre-inv _ id f = id 

  fst-transport-Σ : ∀ {l1 l2 l3} {C : Set l1} {A : Set l2} {B : C → A → Set l3} {c c' : C}
                  → (p : c == c')
                  → (ab : Σ \ x → B c x)
                  → fst (transport (\ h → Σ \ (x : A) → B h x) p ab) == fst ab
  fst-transport-Σ id ab = id

  fst-transport-Σ' : ∀ {l1 l2 l3} {C : Set l1} {A : C → Set l2} {B : (c : C) → A c → Set l3} {c c' : C}
                  → (p : c == c')
                  → (ab : Σ \ x → B c x)
                  → fst (transport (\ h → Σ \ (x : A h) → B h x) p ab) == transport A p (fst ab)
  fst-transport-Σ' id ab = id

  snd-transport-×' : ∀ {l1 l2 l3} {C : Set l1} {A : C → Set l2} {B : C → Set l3} {c c' : C}
                  → (p : c == c')
                  → (ab : A c × B c)
                  → snd (transport (\ h →  A h × B h) p ab) == transport B p (snd ab)
  snd-transport-×' id ab = id

  move-transport-right : ∀ {l1 l2} {A : Set l1} {M M' : A} (B : A → Set l2)
                          (α : M == M') {b : B M} {b' : B M'}
                       -> (transport B α b == b')
                       → (b == transport B (! α) b')
  move-transport-right B id p = p

  move-transport-right! : ∀ {l1 l2} {A : Set l1} {M M' : A} (B : A → Set l2)
                          (α : M' == M) {b : B M} {b' : B M'}
                       -> (transport B (! α) b == b')
                       → (b == transport B α b')
  move-transport-right! B id p = p

  move-transport-left! : ∀ {l1 l2} {A : Set l1} {M M' : A} (B : A → Set l2)
                          (α : M' == M) {b : B M} {b' : B M'}
                       -> (b == transport B α b')
                       → (transport B (! α) b == b')
  move-transport-left! B id p = p

  transport-inv : {l1 l2 : Level} {A : Set l1} (B : A -> Set l2) {M N : A} (α : M == N) -> (\y -> transport B (! α) (transport B α y)) == (\ x -> x)
  transport-inv _ id = id

  transport-inv-2 : {l1 l2 : Level} {A : Set l1} (B : A -> Set l2) {M N : A} (α : M == N) -> (\y -> transport B α (transport B (! α) y)) == (\ x -> x)
  transport-inv-2 _ id = id

  transport-→-post : ∀ {l1 l2} {C : Set l1} {A : Set l2} {B : Set l1} (δ : B == C) (f : A -> B) 
         -> transport (\ X -> A -> X) δ f == (transport (\ X -> X) δ o f)
  transport-→-post id f = id 

  transport-constant : ∀ {l1 l2} {A : Set l1} {C : Set l2} {M N : A} -> (p : M == N) -> (transport (\ _ -> C) p) == (\ x -> x)
  transport-constant id = id 

  transport-natural-trans : {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : A → Set l3}
                   → (f : (x : A) → B x → C x)
                   → {x y : A} (p : x == y) (b : B x)
                   → f y (transport B p b) == transport (\ x → C x) p (f x b)
  transport-natural-trans f id b = id


  -- there aren't used much, but there was one spot that was unpalatable without using pathovers

  data _=h_ {l1 : Level} {A : Set l1} (M : A) : {B : Set l1} → B → Set (l1) where
    hid : M =h M

  postulate
    λ=o  : ∀ {l1 l2} {A A' : Set l1} {B : A -> Set l2} {B' : A' -> Set l2}
             {f : (x : A) -> B x} {g : (x : A') -> B' x}
          -> ((x : A) (y : A') -> x =h y → (f x) =h (g y))
          -> f =h g

    λ=o1 : ∀ {l1 l2} {A : Set l1} {B : A -> Set l2} {B' : A -> Set l2}
             {f : (x : A) -> B x} {g : (x : A) -> B' x}
          -> ((x : A) → (f x) =h (g x))
          -> f =h g

  transport-=h : ∀ {l1 l2 : Level} {A : Set l1} (C : A →  Set l2) {M N : A} (P : M == N) {c : C M}
               → transport C P c =h c
  transport-=h C id = hid

  _∘h_  : ∀ {l} {A B C : Set l} {M : A} {N : B} {P : C} → N =h P → M =h N → M =h P
  β ∘h hid = β
  infixr 10 _∘h_ 

  !h : ∀ {l} {A B : Set l} {M : A} {N : B} → M =h N → N =h M
  !h hid = hid

  het-to-hom : {l : Level} {A : Set l} {M N : A} → M =h N → M == N
  het-to-hom hid = id

  hom-to-het : ∀ {l1 : Level} {A : Set l1} {M N : A}
               → M == N
               → M =h N
  hom-to-het id = hid

  hom-to-het' : ∀ {l1 l2 : Level} {A : Set l1} (C : A →  Set l2) {M N : A} (P : M == N) {c : C M} {d : C N}
               → transport C P c == d
               → c =h d
  hom-to-het' C id id = hid

  apdo  : ∀ {l1 l2} {B : Set l1} {E : B → Set l2} {b₁ b₂ : B} 
         (f : (x : B) → E x) (β : b₁ == b₂) 
      → (f b₁) =h (f b₂) 
  apdo f id = hid 

  apdo2 :  {l1 l2 l3 : Level} {A : Set l1} {B : A → Set l2} {C : (x : A) → B x → Set l3} 
          {a a' : A} {b : B a} {b' : B a'} 
       → (f : (a : A) → (b : B a) → C a b)
       → a == a' → b =h b' → (f a b) =h (f a' b')
  apdo2 f id hid = hid

  apdo3 :  {l1 l2 l3 l4 : Level} {A : Set l1} {B : A → Set l2} {C : (x : A) → B x → Set l3} {D : (x : A) → (b : B x) (c : C x b) → Set l4}
          {a a' : A} {b : B a} {b' : B a'} {c : C a b} {c' : C a' b'}
       → (f : (a : A) → (b : B a) → (c : C a b) → D a b c)
       → a == a' → b =h b' → c =h c' → (f a b c) =h (f a' b' c')
  apdo3 f id hid hid = hid

  pair=o : ∀ {l1 l2} {A : Set l1} {B : A -> Set l2} {p q : Σ B} -> (α : (fst p) == (fst q)) -> (snd p) =h (snd q) -> p == q
  pair=o {p = x , y} {q = .x , .y} id hid = id

  ap=o1 :  {l1 l2 : Level} {A : Set l1} {B B' : Set l2} → (B == B') → {M : A} 
       (f : A → B) (g : A → B') → f =h g → (M : A) → (f M) =h (g M)
  ap=o1 id f .f hid h = hid

  ap=o :  {l1 l2 : Level} {A A' : Set l1} {B B' : Set l2} → (B == B') → {M : A} {N : A'} 
       (f : A → B) (g : A' → B') → f =h g → M =h N → (f M) =h (g N)
  ap=o Beq {M} f g p hid = ap=o1 Beq {M} f g p M

  ap=od1 : {l1 l2 : Level} {A : Set l1} {B B' : A → Set l2} → (B == B') → {M : A} 
           (f : (x : A) → B x) (g : (x' : A) → B' x') → f =h g → (f M) =h (g M)
  ap=od1 id {M} f g hid = hid

  pair=oo : ∀ {l1 l2} {A A' : Set l1}
              {B : A -> Set l2}
              {B' : A' -> Set l2}
              → (B =h B')
              → {p : Σ B} {q : Σ B'}
          -> (α : (fst p) =h (fst q)) -> (snd p) =h (snd q) -> p =h q
  pair=oo hid {x , y} {.x , .y} hid hid = hid

  uipoo : ∀ {l} {A A' B B' : Set l}
           → {x : A} {y : B} {x' : A'} {y' : B'}
             {p : x =h y} {q : x' =h y'} {r : x =h x'}
           → p =h q
  uipoo {p = hid} {q = hid} {r = hid} = hid

  uipo : ∀ {l} {A A' : Set l}
           {x : A} {y : A} {x' : A'} {y' : A'}
           {p : x == y} {q : x' == y'} {r : x =h x'}
         → p =h q
  uipo {p = id} {q = id} {r = hid} = hid


  record Iso {l1 l2 : Level} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2) where
    constructor iso
    field
      f : A → B
      g : B → A
      gf : (x : A) → g (f x) == x
      fg : (x : B) → f (g x) == x

  record isIso {l1 l2 : Level} (A : Set l1) (B : Set l2) (f : A → B) : Set (l1 ⊔ l2) where
    constructor iso
    field
      g : B → A
      gf : (x : A) → g (f x) == x
      fg : (x : B) → f (g x) == x

  eqIso :  {l1 : Level} {A : Set l1} {B : Set l1} → A == B → Iso A B
  eqIso p = iso (coe p) (coe (! p)) ((\ _ → ap= (transport-inv (\ X → X) p))) (\ _ → ap= (transport-inv-2 (\ X → X) p))

  _∘iso_ :  {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3} 
       → Iso B C
       → Iso A B 
       → Iso A C
  _∘iso_ (iso fb gb fgb gfb) (iso fa ga fga gfa) = iso (fb o fa) (ga o gb) (\ _ → fga _ ∘ ap ga (fgb _)) ((\ _ → gfb _ ∘ ap fb (gfa _)))

