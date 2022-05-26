{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Poly where 

open import Base 
open import Data.Unit
open import Agda.Builtin.Sigma 
open import Function using (_∘_)
open import Data.Product
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)

record Poly : Set where
  constructor _▹_
  field
    pos : Set
    dir : pos -> Set
open Poly


module normalized where
    -- Poly is the generic definition, We can also build up Poly inductively
    -- Id
    -- K
    -- +
    -- × 

    -- Claim (Abbott): "Every such type expression can be normalized into a functor of the form"
    -- P X ≡ Σ(n : ℕ) (A n × n → X)
    -- Similar to the form Bartosz was using in his Ommatidia definition
    -- how are coends involved?


-- see container.agda

-- The semantics ("extension") of a container.

-- P X = Σ (b ∈ B) (E b -> X) = Σ B (λ b → E b → X)
-- in the other representation the underlying map induced a polynomial
-- p : E -> B is the representing map where E b denotes the fiber p⁻¹(b)
--  so E = Σ (b ∈ B) E b

⦅_⦆ : Poly → Set → Set
⦅ P ▹ D ⦆ X = Σ[ p ∈ P ] (D p → X)

-- the 4 monoidal structures on Poly

_⊎ₚ_ : Poly → Poly → Poly
p ⊎ₚ q = record { pos = pos p ⊎ pos q ; dir = λ { (inj₁ x) → (dir p) x
                                                ; (inj₂ y) → (dir q) y } }

-- Ayᴮ × Cyᴰ = ACyᴮ⁺ᴰ
_×ₚ_ : Poly → Poly → Poly
p ×ₚ q = record { pos = pos p × pos q ; dir = λ {(i , j) → (dir p) i ⊎ (dir q) j} }

--tensor \ox
-- Ayᴮ × Cyᴰ = ACyᴮᴰ
_⊗ₚ_ : Poly → Poly → Poly
p ⊗ₚ q = record { pos = pos p × pos q ; dir = λ {(i , j) → (dir p) i × (dir q) j} }
-- show these are all monoidal structures on poly

-- composition of polynomials
-- notation suggests that p ◃ q, means that q is substituted into p
-- show that this is an example of composition of datatypes!

_◃_ : Poly → Poly → Poly
(p⑴ ▹ p[_] ) ◃ (q⑴ ▹ q[_]) = (Σ[ i ∈ p⑴ ] (p[ i ] → q⑴)) ▹ λ{ ( i , ĵ) → Σ[ d ∈ p[ i ] ]  q[ (ĵ d) ]}


record Polyₓ (p q : Poly) : Set where
    field
        posₓ : pos p × pos q
        dirₓ : (pq : pos p × pos q) → (dir p) (fst pq) ⊎ (dir q) (snd pq) 


record Poly[_,_](p q : Poly) : Set where
    constructor _⇒ₚ_
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir q (onPos i) → dir p i
open Poly[_,_]

-- RENAME 
_⇒∘ₚ_ : {p q r : Poly} → Poly[ p , q ] → Poly[ q , r ] → Poly[ p , r ]
pq ⇒∘ₚ qr = record { onPos = (onPos pq) ؛ (onPos qr) -- forward composition on positions
                  ; onDir = λ i → ((onDir pq) i) ∘ ((onDir qr) ((onPos pq) i)) } -- backward composition on directions

-- Chart
-- forward on positions and forward on arrows
--https://www.youtube.com/watch?v=FU9B-H6Tb4w&list=PLhgq-BqyZ7i6IjU82EDzCqgERKjjIPlmh&index=9
-- found DJM's book! http://davidjaz.com/Papers/DynamicalBook.pdf
record Chart (p q : Poly) : Set where
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir p i → dir q (onPos i)

-- write out the commuting square between the 4 polys

Poly[] : Poly → Poly → Set
Poly[] p q = ∀ (i : pos p) → Σ (pos q) (λ (j : pos q) → ∀ (d : dir q j) → Σ (dir p i) λ c → Unit )


lemma-poly[]-iso : {p q : Poly} → Poly[] p q ≈ Poly[ p , q ]
lemma-poly[]-iso {p} {q} = record { to = λ p[] → record { onPos = λ ppos → fst( p[] ppos) ; onDir = λ ppos x → fst(snd(p[] ppos) x) } 
                        ; from = λ poly[p,q] ppos → (onPos poly[p,q]) ppos , λ d → (onDir poly[p,q]) ppos d , unit 
                        ; from∘to = λ poly[]pq →  {!   !} --Extensionality λ x → {! ? !}
                        ; to∘from = λ poly[p,q] → {!   !} }

elem : Poly → Set
elem p = Σ (pos p) (dir p)


lift : {X Y : Set} → (p : Poly) → (X → Y) → (⦅ p ⦆ X → ⦅ p ⦆ Y)
lift p f = λ{ (fst₁ , snd₁) → fst₁ , snd₁ ؛ f}

yˢ : (S : Set) → Poly
yˢ S = Unit ▹ λ _ → S

𝓎 : Poly
𝓎 = Unit ▹ (λ _ → Unit)

yoneda : {S : Set} → {q : Poly} → Poly[ yˢ S , q ] ≈ ⦅ q ⦆ S
yoneda =  record { to = λ{ record { onPos = onPos ; onDir = onDir } → onPos unit , λ x → onDir unit x } 
                    ; from = λ { (fst₁ , snd₁) → record { onPos = λ _ → fst₁ ; onDir = λ i → snd₁ } } 
                    ; from∘to = λ{ record { onPos = onPos ; onDir = onDir } → {! refl  !} } 
                    ; to∘from = λ { (fst₁ , snd₁) → {!   !} }}


-- Day 5 (Closures)
-- Poly(p ⊗ q , r) ≈ Poly (p , [q , r])
-- Poly(p × q , r) ≈ Poly (p , qʳ)
-- where [q , r] and qʳ are not defined here yet


-- Set^Vars → Set
-- or Set^I → Set
record Polyₘ (Vars : Set) : Set where
    constructor _▹ₘ_
    field
        Pos : Set
        Dir : Pos → ∀ (var : Vars) → Set

⦅_⦆⋆_ : {Vars : Set} → Polyₘ Vars → (Vars → Set) → Set 
(⦅_⦆⋆_) {Vars} (Pos ▹ₘ Dir) f = Σ[ p ∈ Pos ] (∀ (var : Vars) → (Dir p var → f var ))

-- https://www.youtube.com/watch?v=B8STLcbEGrE&list=PLhgq-BqyZ7i7R-fGcAmNyWmJBQg1wzex-&index=1
-- Richard Garner's talk
-- the even more general case is 
-- Set^I → Set^J 
-- "A J indexed family of polynomial functors Set^I → Set"
-- claim: this is better for composition ?

-- Alternatively functors Set/I → Set/J ??
-- slice category?

-- another representation ( I've seen this before in some papers..)
-- Set/I → Set/E → Set/B → Set/J

-- Also Girard's Normal Functors?


module ExampleMultivariate where
    open import Data.Bool
    open import Data.Nat

    -- set of variables
    data V : Set where
        X Y Z : V

    -- 3 variables X Y Z
    -- P(x,y,z) = (x^2)(z^3) + xz + 1
    mp : Polyₘ V
    mp = record { 
        Pos = Pos₃ ; 
        Dir = λ { P₁ X → Dir₂ -- x^2
                ; P₁ Y → Dir₀
                ; P₁ Z → Dir₃ -- z^3

                ; P₂ X → Dir₁ -- x
                ; P₂ Y → Dir₀
                ; P₂ Z → Dir₁ -- z

                ; P₃ X → Dir₀
                ; P₃ Y → Dir₀
                ; P₃ Z → Dir₀ }}

    assignVars : V → Set
    assignVars X = Bool
    assignVars Y = Unit
    assignVars Z = ℕ

    _ : ⦅ mp ⦆⋆ assignVars 
    _ = P₁ , λ{X D₁ → true
             ; X D₂ → false

             ; Z D₁ → 1
             ; Z D₂ → 2
             ; Z D₃ → 3}

-- PolyBoxes
module composition where
    p : Poly  
    p = Pos₂ ▹ (λ{P₁ → Dir₂
                ; P₂ → Dir₁})

    p' : Poly
    p' = Pos₂ ▹ λ{P₁ → Dir₃
                ; P₂ → Dir₁}

    q : Poly
    q = Pos₂ ▹ (λ{P₁ → Dir₂
                ; P₂ → Dir₁})

    q' : Poly
    q' = Pos₂ ▹ (λ{P₁ → Dir₁
                 ; P₂ → Dir₀})


    p→p' : Poly[ p , p' ]
    p→p' = (λ{P₁ → P₁
            ; P₂ → P₂}) ⇒ₚ λ{P₁ D₁ → D₂
                           ; P₁ D₂ → D₂
                           ; P₁ D₃ → D₁
                           ; P₂ D₁ → D₁}

    q→q' : Poly[ q , q' ]
    q→q' = (λ{P₁ → P₁
            ; P₂ → P₂}) ⇒ₚ λ{P₁ D₁ → D₂}

    _ : Poly[ p ◃ q , p' ◃ q' ]
    _ = {!   !}

    -- Sy^S is a contractible groupoid ??
    -- Day 6
    _◃→_ : {p p' q q' : Poly} → (f : Poly[ p , p' ]) → (g : Poly[ q , q' ]) → Poly[ p ◃ q , p' ◃ q' ]
    (onPos₁ ⇒ₚ onDir₁) ◃→ (onPos₂ ⇒ₚ onDir₂) = 
            (λ{ (posp , pdirtoq) → onPos₁ posp , λ{x → onPos₂ (pdirtoq (onDir₁ posp x))}}) 
            ⇒ₚ λ{(posp , snd₁) (fst₁ , snd₂) → (onDir₁ posp fst₁) , (onDir₂ (snd₁ (onDir₁ posp fst₁)) snd₂)}

    _ : {p q : Poly} → Poly[ p ⊗ₚ q , p ◃ q ]
    _ = (λ{ (posp , posq) → posp , λ _ → posq}) ⇒ₚ λ{ _ (fst₂ , snd₂) → fst₂ , snd₂}

    -- (p +ₚ q) ◃ r ≈ (p ◃ r) +ₚ (q ◃ r)
    -- (p ×ₚ q) ◃ r ≈ (p ◃ r) ×ₚ (q ◃ r)
