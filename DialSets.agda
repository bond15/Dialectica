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

-- morphisms
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

-- syntax for morphism
_⇒ᴰ_ : {o : Level} → DialSet {o} → DialSet {o} → Set o
_⇒ᴰ_ = DialSetMap

id-dial : {o : Level} {A : DialSet {o}} → A ⇒ᴰ A 
id-dial = (λ u → u) ∧ (λ u x → x) st λ u x → ≤-refl

{-
    show DialSets is category
    ! is an endofunctor on DialSets
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



open import CatLib using (PreCat)
open PreCat renaming (_∘_ to _∘ᶜ_)
open import Cubical.Core.Everything using (_≡_; PathP;Path; I ; i0 ; i1 ; hcomp)
open import Cubical.Foundations.Prelude using (cong; cong₂;refl; transport)

-- defining equality of DialSet morphisms
module DialSet-eq-maps {o : Level} {A B : DialSet{o}} {m₁ m₂ : A ⇒ᴰ B} where 
    open DialSet A 
    open DialSet B renaming (U to V ; X to Y; α to β)

    open DialSetMap m₁ renaming (cond-on-f&F to cond)
    open DialSetMap m₂ renaming (f to f' ; F to F'; cond-on-f&F to cond')
    
    funext : {o : Level}{A B : Set o}{f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g 
    funext p i a = p a i

    funext₂ : {o : Level}{A B C : Set o}{f g : A → B → C} → (∀ (a : A)(b : B) → f a b ≡ g a b) → f ≡ g 
    funext₂ p i x y = p x y i

    dfunext₂ : {o : Level}{A : Set o}{B : A → Set o}{C : (a : A) → B a → Set o} {f g : (a : A) → (b : B a)  → C a b} → (∀ (a : A)(b : B a) → f a b ≡ g a b) → f ≡ g 
    dfunext₂ p i x y = p x y i

    eq-maps-cond : (p : f ≡ f') → (q : F ≡ F') → (u : U) → (y : Y) → α u (q i0 u y) ≤² β (p i0 u) y ≡ α u (q i1 u y) ≤² β (p i1 u) y
    eq-maps-cond  p q u y = cong₂ _≤²_ (cong₂ α refl (λ i → q i u y))(cong₂ β (λ i → p i u) refl)

    eq-maps-cond' : (i : I) → (p : f ≡ f') → (q : F ≡ F') → (u : U) → (y : Y) → α u (q i u y) ≤² β (p i u) y 
    eq-maps-cond' i p q u y = {!   !}

    eq-cond : (p : f ≡ f') → (q : F ≡ F') → 
        PathP (λ i → (u : U)(y : Y) → α u ((q i) u y) ≤² β ((p i) u) y) cond cond'
    eq-cond p q = {!   !}

    -- λ i u y → eq-maps-cond' i p q u y --λ i u y → {!  eq-maps-cond p q  u y  !}
    -- λ i u y → {! eq-maps-cond p q u y  !}
    
{-
    test : {ℓ : Level}{A B : Set ℓ}{g g' : A → B → Set}{p : g ≡ g'}{f  : (a : A)(b : B) → g a b}
        {f' : (a : A)(b : B) → g' a b} → PathP (λ i → (a : A)(b : B) → p i a b) f f'
    test = λ i a b → {!   !}

-}
  --  huh : (p : f ≡ f') → (q : F ≡ F') → PathP (λ i → (u : U)(y : Y) → eq-maps-cond p q u y i) cond cond'
   -- huh p q = λ i u y → {!   !}
    --λ i u y → {!  !}

 

    cong-dial : f ≡ f' → F ≡ F' → m₁ ≡ m₂
    cong-dial p q = λ i → p i ∧ q i st λ u y → eq-cond p q i u y
    -- asdf p q i u y
    --λ u y → huh p q i u y


    -- transport {! eq-maps-cond p q u y  !} (cond u y)
    -- {! transport (eq-maps-cond p q  u y) ? !}

open DialSet-eq-maps using (cong-dial)

-- Show DialSet is a category
DialSetCat : {o : Level} → PreCat (lsuc o) (o) 
DialSetCat .Ob      = DialSet 
DialSetCat ._⇒_     = DialSetMap
DialSetCat .id      = id-dial
DialSetCat ._∘ᶜ_    = _∘ᴰ_
DialSetCat .idr     = cong-dial refl refl
DialSetCat .idl     = cong-dial refl refl
DialSetCat .assoc   = cong-dial refl refl


---------------------------- Ignore following for now ---------------------------------------




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