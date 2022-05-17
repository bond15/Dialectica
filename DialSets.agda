module DialSets where 

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma 
open import Data.Product
open import Function using (_∘_)
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂ ; cong-app; subst)
-- need to import less or equal \leq too?

data Two : Set where ⊤ ⊥ : Two

data Empty : Set where 

data Unit : Set where tt : Unit

_⊗²_ : Two → Two → Two 
⊤ ⊗² ⊤ = ⊤
⊤ ⊗² ⊥ = ⊥
⊥ ⊗² ⊤ = ⊥
⊥ ⊗² ⊥ = ⊥

_≤²_ : Two → Two → Set 
⊤ ≤² ⊤ = Unit
⊤ ≤² ⊥ = Empty
⊥ ≤² ⊤ = Empty
⊥ ≤² ⊥ = Empty

≤-trans : {x y z : Two} → x ≤² y → y ≤² z → x ≤² z 
≤-trans {⊤} {⊤} {⊤} tt tt = tt
≤-trans {⊤} {⊤} {⊥} _ ()
≤-trans {⊤} {⊥} {_} () _

record DialSet {ℓ : Level} : Set (lsuc ℓ) where
    constructor ⟨_,_,_⟩
    field
        U : Set ℓ 
        X : Set ℓ
        α : U → X → Two  

-- open DialSet
-- what this opening statement?
{-
    DialSet is a record. In Agda, Records also have Modules (Cs module not math module)
        see https://agda.readthedocs.io/en/v2.6.2.1/language/record-types.html#record-modules for details

    So there is a module DialSet and "open"ing that module causes the definitions 'U', 'X', and 'alpha' to be in scope

    Here I have commented it out and opted to only open DialSet locally seen in the definition of DialSetMap
-}


-- variables for objects of DialSet: a, b, c
-- objects are triples a= (U; X; alpha) U,X sets, alpha:U x X ->2 a function
-- maps from a to b= (V; Y; beta) are pairs of functions (f,F) f:U -> V, F:U x Y -> X such that
-- ∀ (u : U)∀ (y : Y) (u alpha F(u,y) \leq (fu beta y)

record DialSetMap {ℓ} (A B : DialSet {ℓ}) : Set ℓ where 
    constructor _∧_st_
    open DialSet A 
    open DialSet B renaming (U to V ; X to Y ; α to β )
    -- ^ this brings U X α of object A := (U, X, α) in scope
    -- it also bring V Y β of object B := (V, Y, β) in scope
    field 
        f : U → V
        F : U → Y → X 
        cond-on-f&F : (u : U)(y : Y) → α u (F u y) ≤² β (f u) y

_⇒ᴰ_ : DialSet → DialSet → Set
_⇒ᴰ_ = DialSetMap

{-
    show DialSets is category
    ! is an endofunctor on DialSets
-}

{- 
A := (U, X, α)
B := (V, Y, β)
C := (W, Z, γ)
-}
_∘ᴰ_ :{A B C : DialSet} → (B ⇒ᴰ C) → (A ⇒ᴰ B) → (A ⇒ᴰ C)
_∘ᴰ_ {A} {B} {C} (f₂ ∧ F₂ st cond₂) (f₁ ∧ F₁ st cond₁) = f' ∧ F' st cond'
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




-- need a monoidal operation to combine elements of Two
-- similar to https://github.com/heades/cut-fill-agda/blob/5ae2c4bde0b7c63930cf8ab2733e3eef071672c1/DialSets.agda#L144
{- infix 2 _⊗ᴰ_ 
_⊗ᴰ_ : DialSet → DialSet → DialSet
⟨ U ⇒ X ⇒2⟩∋ α ⊗ᴰ ⟨ V ⇒ Y ⇒2⟩∋ β = ⟨ U × V ⇒ (V → X) × (U → Y) ⇒2⟩∋ m

                where m : U × V → (V → X) × (U → Y) → Two
                      m (u , v) (V⇒X , U⇒Y) = α u (V⇒X v) ⊗² β v (U⇒Y u)
-}
-- how do I write the above?

--  monoidal structures on DialSet
-- tensor \ox
-- Ayᴮ × Cyᴰ = ACyᴮᴰ

postulate 
    _∧_  : Two → Two → Two 

infix 2 _⊗ᴰ_
_⊗ᴰ_ : DialSet → DialSet → DialSet
⟨ U , X , α ⟩ ⊗ᴰ ⟨ V , Y , β ⟩ = ⟨ U × V , X × Y , m ⟩ 
    where m : U × V  → X × Y → Two
          m (u , v) (x , y) =  α u x ∧ β v y 

--product \&
-- Ayᴮ × Cyᴰ = ACyᴮ⁺ᴰ

_&_ : DialSet → DialSet → DialSet
⟨ U , X , α ⟩ & ⟨ V , Y , β ⟩ = ⟨ U × V  , X ⊎ Y , choose ⟩
    where choose : U × V → X ⊎ Y → Two 
          choose (u , v) (inj₁ x) = α u x 
          choose (u , v) (inj₂ y) = β v y

-- internal hom (bifunctor)
-- prove "profunctor"
_[-,-]_ : DialSet → DialSet → DialSet
⟨ U , X , α ⟩ [-,-] ⟨ V , Y , β ⟩ = ⟨ (U → V) × (U × Y → X) , U × Y , {!   !} ⟩ -- prove condition

-- sym mon closed
-- content from ch 1
-- prove : A ⊗ B → C ⇔ A → [B,C] 

-- TODO renaming GC
{-
    Monoids and Comonoids for ⊗ᴰ 
    Monoids (collectives in Nelson's notes)

-}


---- Symetric monoidal Cat

-- TODO check
{- record SymetricMonoid (A : Set) : Set where
    field 
        e : A
        _∙_ : A → A → A 

        sym : (a b : A) → a ∙ b ≡ b ∙ a
        l-unit : (a : A) → e ∙ a ≡ a
        r-unit : (a : A) → a ∙ e ≡ a
        assoc : (a b c : A) → (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
-}









     
--⟨ U × V , X x Y , alpha x beta ⟩ 


{-
infix 2 _⅋_ 
_⅋_ : DialSet → DialSet → DialSet
⟨ U ⇒ X ⇒2⟩∋ α ⅋ ⟨ V ⇒ Y ⇒2⟩∋ β = ⟨ U × V ⇒ X ⊎ Y ⇒2⟩∋ m

        where m : U × V → X ⊎ Y → Two
              m (u , v) (inj₁ x) = α u x
              m (u , v) (inj₂ y) = β v y  

-}
{-
--product \&
-- Ayᴮ × Cyᴰ = ACyᴮ⁺ᴰ

_×ₚ_ : DialSet → DialSet → DialSet
a ×ₚ b = record { U × V ; X + Y; choose(alpha, beta) }
-- want to choose a relation for a pair ((u,v), s), where s= (x, o) or (y, 1). if s=(x, 0) choose  alpha, otherwise choose beta


record DialSet[_,_](a b : DialSet) : Set where
    constructor _⇒ₚ_
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir q (onPos i) → dir p i
open Dialset[_,_]

-- RENAME 
_⇒∘ₚ_ : {p q r : Poly} → Poly[ p , q ] → Poly[ q , r ] → Poly[ p , r ]
pq ⇒∘ₚ qr = record { onPos = (onPos pq) ؛ (onPos qr) -- forward composition on positions
                  ; onDir = λ i → ((onDir pq) i) o ((onDir qr) ((onPos pq) i)) } -- backward composition on directions
                  

-- Chart
-- forward on positions and forward on arrows
--https://www.youtube.com/watch?v=FU9B-H6Tb4w&list=PLhgq-BqyZ7i6IjU82EDzCqgERKjjIPlmh&index=9
-- found DJM's book! http://davidjaz.com/Papers/DynamicalBook.pdf
record Chart (p q : Poly) : Set where
    field
        onPos : pos p → pos q
        onDir : (i : pos p) → dir p i → dir q (onPos i)

-- write out the commuting square 

Poly[] : Poly → Poly → Set
Poly[] p q = ∀ (i : pos p) → Σ (pos q) (λ (j : pos q) → ∀ (d : dir q j) → Σ (dir p i) λ c → Unit )


lemma-poly[]-iso : {p q : Poly} → Poly[] p q ≈ Poly[ p , q ]
lemma-poly[]-iso {p} {q} = record { to = λ p[] → record { onPos = λ ppos → fst( p[] ppos) ; onDir = λ ppos x → fst(snd(p[] ppos) x) } 
                        ; from = λ poly[p,q] ppos → (onPos poly[p,q]) ppos , λ d → (onDir poly[p,q]) ppos d , unit 
                        ; from∘to = λ poly[]pq → Extensionality λ x → {! ? !}
                        ; to∘from = λ poly[p,q] → refl }

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
                    ; to∘from = λ { (fst₁ , snd₁) → refl } }


-- Day 5 (Closures)
-- Poly(p ⊗ q , r) ≈ Poly (p , [q , r])
-- Poly(p × q , r) ≈ Poly (p , qʳ)
-- where [q , r] and qʳ are not defined here yet



   


-}