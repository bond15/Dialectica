{-# OPTIONS --allow-unsolved-metas #-}
module DDial where 

-- TODO copy this file, but add the condition to Poly.. see what breaks
-- And refactor definitions to not use record projections
open import Agda.Primitive using (Level; lsuc)
-- open import Data.Unit using
open import Agda.Builtin.Sigma 
open import Cubical.Categories.Category.Base
open import Cubical.Core.Everything 
open import Cubical.Foundations.Prelude 
open import Function using (_∘_)
open import Data.Product
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)

open import Lineale


module _ {ℓ}(L : Set ℓ) {{pro : Proset L}} {{ mon : MonProset L }} {{lin : Lineale L }} where 
    record DDial : Set (lsuc ℓ) where
        constructor _▹_c_
        field
            pos : Set
            dir : pos -> Set
            α : (p : pos) → dir p → L

    record DDialMap (p q : DDial) : Set ℓ where
        constructor _∧_st_
        open DDial p renaming (pos to pos₁; dir to dir₁)
        open DDial q renaming (pos to pos₂; dir to dir₂; α to β)
        open Proset pro renaming (rel to _≤_)
        field


            f : pos₁ → pos₂
            F : (p : pos₁) → dir₂ (f p) → dir₁ p
            cond  : (p : pos₁)(d' : dir₂ (f p)) → α p (F p d') ≤ β  (f p) d'
            

    _∘L_ : {A B C : DDial} → (DDialMap B C) → (DDialMap A B) → (DDialMap A C)
    _∘L_ {A} {B} {C} record { f = g ; F = G ; cond = cond₁ } record { f = f ; F = F ; cond = cond₂ } = thing
        where 
            open DDial A renaming (pos to pos₁; dir to dir₁) 
            open DDial B renaming (pos to pos₂; dir to dir₂; α to β)
            open DDial C renaming (pos to pos₃; dir to dir₃; α to ɣ)

            open Proset pro renaming (rel to _≤_) 
            
            F' : (p : pos₁) → dir₃ (g (f p)) → dir₁ p
            F' p₁ d₃ = 
                        let p₂ = f p₁
                            d₂ = G p₂ d₃
                            d₁ = F p₁ d₂
                        in  d₁
            cond' : (p : pos₁) (d' : dir₃ (g (f p))) → (α p (F' p d')) ≤ (ɣ (g (f p)) d')
            cond' p₁ d₃ = let p₂ = f p₁
                              d₂ = G p₂ d₃
                              r1 = cond₁ p₂ d₃
                              r2 = cond₂ p₁ d₂ 
                          in ptrans r2 r1

            thing : DDialMap A C
            thing = record { f = g ∘ f ; F = F' ; cond = cond' }

    open Precategory

    idD : (x : DDial) → DDialMap x x 
    idD (pos ▹ dir c α) = (λ z → z) ∧ (λ p z → z) st (λ p d' → prefl)
        where 
            open Proset pro
    
    module eqaulityofmaps {A B : DDial}{m₁ m₂ : DDialMap A B} where 
        open DDial A renaming (pos to pos₁; dir to dir₁; α to α₁)
        open DDial B renaming (pos to pos₂; dir to dir₂; α to α₂)
        open DDial B
        open DDialMap m₁ renaming (cond to cond₁)
        open DDialMap m₂ renaming (f to g; F to G; cond to cond₂)
        eq-maps : f ≡ g → PathP {!   !} F G → PathP {!   !} cond₁ cond₂ → {!   !}
        eq-maps = {!   !}
    
    DDialCat : Precategory (lsuc ℓ) ℓ
    DDialCat .ob = DDial
    DDialCat .Hom[_,_] = DDialMap
    DDialCat .id = idD 
    DDialCat ._⋆_ f g = g ∘L f
    DDialCat .⋆IdL f = {!   !}
    DDialCat .⋆IdR = {!   !}
    DDialCat .⋆Assoc = {!   !}
            
    _⊗_ : DDial → DDial → DDial 
    (pos₁ ▹ dir₁ c α₁) ⊗ (pos₂ ▹ dir₂ c α₂) = (pos₁ × pos₂) ▹ (λ { (p₁ , p₂) → dir₁ p₁ × dir₂ p₂}) c λ{ (p₁ , p₂) (d₁ , d₂) → α₁ p₁ d₁ ⊙ α₂ p₂ d₂}
        where 
            open MonProset mon

    [_,_] : DDial → DDial → DDial
    [ pos₁ ▹ dir₁ c α₁ , pos₂ ▹ dir₂ c α₂ ] = 
        Σ (pos₁ → pos₂) (λ f → (p₁ : pos₁)→ dir₂ (f p₁) → dir₁ p₁) ▹ (λ{ (f , F) → Σ pos₁ (λ p₁ → dir₂ (f p₁))}) c 
            λ{ (f , F) (u , y) → α₁ u (F u y) ⊸ α₂ (f u) y}
        where 
            open Lineale.Lineale lin

{- 
[_,_] : {ℓ : Level} → DialSet {ℓ} → DialSet {ℓ} → DialSet {ℓ}
[ ⟨ pos , dir , α ⟩ , ⟨ pos' , dir' , β ⟩ ] = ⟨ (pos → pos') × (pos × dir' → dir) , pos × dir' , m ⟩ 
    where m : (pos → pos') × ((pos × dir' → dir)) → pos × dir' → Two 
          m (uv , uyx) (u , y) = α u (uyx (u , y)) ⊗² β (uv u) y
-}

    {-
    record { pos = pos ; dir = dir ; α = α } ⊗ record { pos = pos' ; dir = dir' ; α = β } = 
        record { pos = pos × pos' ; dir = λ{(p , p') → dir p × dir' p'} ; α = λ{ (p , p') (d , d') → {!   !} }}   
-}
    
{- 


_∘ₚ_ : {p q r : Poly} → PolyMap q r →  PolyMap q p → PolyMap p r
_∘ₚ_ {p}{q}{r}(onPos₂ ⇒ₚ onDir₂)(onPos₁ ⇒ₚ onDir₁) = goal 
    where 
        goal : PolyMap p r 
        goal = {!   !} ⇒ₚ {!   !}

    


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

-} 