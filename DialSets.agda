-- recopying Eric's file
module DialSets where 
open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma 
open import Data.Product
open import Function using (_∘_)
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)

data Two : Set where ⊤ ⊥ : Two

data Empty : Set where 

data Unit : Set where tt : Unit

_⊗²_ : Two → Two → Two 
⊤ ⊗² ⊤ = ⊤
⊤ ⊗² ⊥ = ⊥
⊥ ⊗² ⊤ = ⊥
⊥ ⊗² ⊥ = ⊥

-- modeling ⊥ → ⊤ category
_≤²_ : Two → Two → Set 
⊤ ≤² ⊤ = Unit
⊤ ≤² ⊥ = Empty
⊥ ≤² ⊤ = Unit
⊥ ≤² ⊥ = Unit 

≤-refl : {x : Two} → x ≤² x 
≤-refl {⊤} = tt
≤-refl {⊥} = tt

≤-trans : {x y z : Two} → x ≤² y → y ≤² z → x ≤² z 
≤-trans {⊤} {⊤} {⊤} _ _ = tt
≤-trans {⊤} {⊤} {⊥} _ ()
≤-trans {⊤} {⊥} {z} () _ 
≤-trans {⊥} {⊤} {⊤} _ _ = tt
≤-trans {⊥} {⊤} {⊥} _ ()
≤-trans {⊥} {⊥} {⊤} _ _ = tt
≤-trans {⊥} {⊥} {⊥} _ _ = tt

-- Objects
record DialSet {ℓ : Level} : Set (lsuc ℓ) where
    constructor ⟨_,_,_⟩
    field
        U : Set ℓ 
        X : Set ℓ
        α : U → X → Two  

-- Morphisms
record DialSetMap {ℓ} (A B : DialSet {ℓ}) : Set ℓ where 
    constructor _∧_st_
    open DialSet A 
    open DialSet B renaming (U to V ; X to Y ; α to β )
    -- ^ this brings U X α of object A := (U, X, α) in scope
    -- it also brings V Y β of object B := (V, Y, β) in scope
    field 
        f : U → V
        F : U → Y → X 
        cond-on-f&F : (u : U)(y : Y) → α u (F u y) ≤² β (f u) y

-- syntax for morphism
_⇒ᴰ_ : {o : Level} → DialSet {o} → DialSet {o} → Set o
_⇒ᴰ_ = DialSetMap

{-
    show DialSet is category  
-}

{- 
composition of morphisms 
A := (U, X, α)
B := (V, Y, β)
C := (W, Z, γ)
-}
_∘ᴰ_ : {o : Level}{A B C : DialSet {o}} → (B ⇒ᴰ C) → (A ⇒ᴰ B) → (A ⇒ᴰ C)
_∘ᴰ_ {o} {A} {B} {C} (f₂ ∧ F₂ st cond₂) (f₁ ∧ F₁ st cond₁) = f' ∧ F' st cond'
    where 
        open DialSet A 
        open DialSet B renaming (U to V ; X to Y; α to β)
        open DialSet C renaming (U to W ; X to Z; α to γ)

        f' : U → W 
        f' = f₂ ∘ f₁

        F' : U → Z → X
        F' u z = let 
                 v = f₁ u
                 y = F₂ v z 
                 x = F₁ u y
                 in x

        cond' : (u : U)(z : Z) → α u (F' u z) ≤² γ (f' u) z
        cond' u z = let 
                    v = f₁ u
                    y = F₂ v z
                    r1 = cond₁ u y       -- : α u (F₁ u (F₂ (f₁ u) z)) ≤² β (f₁ u) (F₂ (f₁ u) z)
                    r2 = cond₂ v z       -- : β (f₁ u) (F₂ (f₁ u) z) ≤² γ (f₂ (f₁ u)) z
                    in ≤-trans r1 r2
                    
 -- lines 76-100 define the composition of morphisms                   

open import CatLib using (PreCat)
open PreCat renaming (_∘_ to _∘ᶜ_)
open import Cubical.Core.Everything using (_≡_; PathP)
open import Cubical.Foundations.Prelude using (cong; cong₂;refl; transport)

-- defining equality of DialSet morphisms

-- (f,F, cond)=(g,G, cond') iff f=g and F=G and cond=cond' vcvp expects

module DialSet-eq-maps {o : Level} {A B : DialSet{o}} {m₁ m₂ : A ⇒ᴰ B} where 
    open DialSet A 
    open DialSet B renaming (U to V ; X to Y; α to β)

    open DialSetMap m₁ renaming (cond-on-f&F to cond)
    open DialSetMap m₂ renaming (f to f' ; F to F'; cond-on-f&F to cond')
    
    funext : {o : Level}{A B : Set o}{f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g 
    funext p i x = p x i

    funext₂ : {o : Level}{A B C : Set o}{f g : A → B → C} → (∀ (a : A)(b : B) → f a b ≡ g a b) → f ≡ g 
    funext₂ p i x y = p x y i

    dfunext₂ : {o : Level}{A : Set o}{B : A → Set o}{C : (a : A) → B a → Set o} {f g : (a : A) → (b : B a)  → C a b} → (∀ (a : A)(b : B a) → f a b ≡ g a b) → f ≡ g 
    dfunext₂ p i x y = p x y i

    eq-maps-cond : (p : f ≡ f') → (q : F ≡ F') → (u : U) → (y : Y) → α u (F u y) ≤² β (f u) y ≡ α u (F' u y) ≤² β (f' u) y
    eq-maps-cond p q u y = cong₂ _≤²_ (cong₂ α refl (λ i → q i u y))(cong₂ β (λ i → p i u) refl)

    cong-dial : f ≡ f' → F ≡ F' → m₁ ≡ m₂
    cong-dial p q = {!   !} --  λ i → p i ∧ q i st {! eq-cond p q  !}

open DialSet-eq-maps using (cong-dial)

-- Show DialSet is a category
DialSetCat : {o : Level} → PreCat (lsuc o) (o) 
DialSetCat .Ob      = DialSet 
DialSetCat ._⇒_     = DialSetMap
DialSetCat .Hom-set = {!   !}
DialSetCat .id      = (λ u → u) ∧ (λ u x → x) st (λ u x → ≤-refl)
DialSetCat ._∘ᶜ_    = _∘ᴰ_
DialSetCat .idr     = cong-dial refl refl 
DialSetCat .idl     = cong-dial refl refl
DialSetCat .assoc   = cong-dial refl refl


--  Next goal: show DialSet is symmetric monoidal closed

--  Need to describe the structure of DialSet:  define tensor, define interna-hom, show adjunction above


{- 
Define monoidal tensors in Dial Set
-}

-- cartesian product
-- Poly notation: Ayᴮ × Cyᴰ = ACyᴮ⁺ᴰ
-- DialSet notation (U×V, X+Y, choose (alpha, beta))

_×_ : DialSet → DialSet → DialSet
A × B = record { U × V; X + Y ; λ {(x,0) → u alpha x |
                                   (y,1) → v beta y } }
                                    
-- must show _×_ is a bifunctor,  so if (f,F):A → C, and (g,G):B → C, then A×B → C×D 
-- must show T = (1, 0, empty) is the unit for this cartesian product, 1×0 → Two has to be the empty relation
-- must show A×T=T×A=A



--tensor \otimes: parallel or Dirichlet
-- Ayᴮ × Cyᴰ = ACyᴮᴰ

_⊗_ : DialSet → DialSet → DialSet
A ⊗ B = record {  U × V; X × Y; λ (u,v,x,y) → (u alpha x)⊗² (v beta y)   }



--------------

_◃_ : DialSet → DialSet → DialSet
(p⑴ ▹ p[_] ) ◃ (q⑴ ▹ q[_]) = (Σ[ i ∈ p⑴ ] (p[ i ] → q⑴)) ▹ λ{ ( i , ĵ) → Σ[ d ∈ p[ i ] ]  q[ (ĵ d) ]}


record Polyₓ (p q : DialSet) : Set where
    field
        posₓ : pos p × pos q
        dirₓ : (pq : pos p × pos q) → (dir p) (fst pq) ⊎ (dir q) (snd pq) 


record Poly[_,_](A B : DialSet) : Set where
    constructor _⇒_
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir q (onPos i) → dir p i
open Poly[_,_]


-- Monoids and Comonoids in DialSet


