module DialSets where 
open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma 
open import Data.Product
open import Function using (_∘_)
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)

data Two : Set where ⊤ ⊥ : Two

data Empty : Set where 

-- needs an eta law for transp in proof of eq-dial-maps
record Unit {ℓ : Level} : Set ℓ where instance constructor tt

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

compat : ∀{a b : Two} → a ≤² b → (∀{c : Two} → (a ⊗² c) ≤² (b ⊗² c))
compat {⊤} {⊤} r {⊤} = tt
compat {⊤} {⊤} r {⊥} = tt
compat {⊥} {⊤} r {⊤} = tt
compat {⊥} {⊤} r {⊥} = tt
compat {⊥} {⊥} r {⊤} = tt
compat {⊥} {⊥} r {⊥} = tt

swap-⊗ : ∀{a b : Two} → (a ⊗² b) ≤² (b ⊗² a)
swap-⊗ {⊤} {⊤} = tt
swap-⊗ {⊤} {⊥} = tt
swap-⊗ {⊥} {⊤} = tt
swap-⊗ {⊥} {⊥} = tt

bifun : ∀{a b c d : Two} → 
    a ≤² c → 
    b ≤² d → 
    (a ⊗² b) ≤² (c ⊗² d)
bifun {b = b} {c = c} aRc bRd = let abRcb = compat aRc {b}
                                    bcRdc = compat bRd {c} 
                                    abRbc = ≤-trans abRcb swap-⊗
                                    bcRcd = ≤-trans bcRdc swap-⊗
                                in ≤-trans abRbc bcRcd


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



-- defining equality of DialSet morphisms
module DialSet-eq-maps {o : Level} {A B : DialSet{o}} {m₁ m₂ : A ⇒ᴰ B} where 
    open DialSet A 
    open DialSet B renaming (U to V ; X to Y; α to β)

    open DialSetMap m₁ renaming (cond-on-f&F to cond)
    open DialSetMap m₂ renaming (f to g ; F to G; cond-on-f&F to cond')

    {-
        proof idea:
            cond and cond' have the same type, as witnessed by eq-ty
            the type of cond and cond' is either Empty or Unit

            if cond has type Empty
                then any element is trivially equal
            if cond has type Unit
                then any element is trivially equal

    https://agda.zulipchat.com/#narrow/stream/260790-cubical/topic/.E2.9C.94.20Stuck.20Proof/near/283197935
    https://gist.github.com/bond15/073ba0715e74938af50f11c22b0d5455
    -}
    
    -- start proof
    -- pull in some tools
    open import Cubical.Core.Everything using (_≡_; _[_≡_]; transp ;_∧_ ;~_)
    open import Cubical.Foundations.Prelude using (cong₂; funExt; funExt⁻; refl)
    
    -- This says that the Type returned by _≤²_ is equal when applied to pairwise equal args
    eq-ty : {x y x' y' : Two} → 
            (p : x ≡ x')(q : y ≡ y') → 
            x ≤² y ≡ x' ≤² y' 
    eq-ty p q = cong₂ _≤²_ p q

    -- uh... just ignore this... nothing to see here (and if you have better suggestions please help :))
    -- really all this says is..
    -- Either
    --      x ≤² y and x' ≤² y'  both evaluate to Unit
    --      in which case e and e' are both tt, so they are trivially equal
    -- Or 
    --      x ≤² y and x' ≤² y'  both evaluate to Empty
    --      in which case e and e' don't exist, so they are trivialy equal
    eq-elem : {x y x' y' : Two} → 
              (p : x ≡ x')(q : y ≡ y')(e : x ≤² y)(e' : x' ≤² y') → 
              (λ i → eq-ty p q i) [ e ≡ e' ]
    eq-elem {⊤} {⊤} {⊤} {⊤} p q e e' i = transp (λ j → _≤²_ (p (i ∧ j)) (q  (i ∧ j))) (~ i) e
    eq-elem {⊤} {⊤} {⊥} {⊤} p q e e' i = transp (λ j → _≤²_ (p (i ∧ j)) (q  (i ∧ j))) (~ i) e
    eq-elem {⊤} {⊤} {⊥} {⊥} p q e e' i = transp (λ j → _≤²_ (p (i ∧ j)) (q  (i ∧ j))) (~ i) e
    eq-elem {⊥} {⊤} {⊤} {⊤} p q e e' i = transp (λ j → _≤²_ (p (i ∧ j)) (q  (i ∧ j))) (~ i) e
    eq-elem {⊥} {⊤} {⊥} {⊤} p q e e' i = transp (λ j → _≤²_ (p (i ∧ j)) (q  (i ∧ j))) (~ i) e
    eq-elem {⊥} {⊤} {⊥} {⊥} p q e e' i = transp (λ j → _≤²_ (p (i ∧ j)) (q  (i ∧ j))) (~ i) e
    eq-elem {⊥} {⊥} {⊤} {⊤} p q e e' i = transp (λ j → _≤²_ (p (i ∧ j)) (q  (i ∧ j))) (~ i) e
    eq-elem {⊥} {⊥} {⊥} {⊤} p q e e' i = transp (λ j → _≤²_ (p (i ∧ j)) (q  (i ∧ j))) (~ i) e
    eq-elem {⊥} {⊥} {⊥} {⊥} p q e e' i = transp (λ j → _≤²_ (p (i ∧ j)) (q  (i ∧ j))) (~ i) e

    -- This uses the above, but instead of x and y the quantities are α u (F u y) and β (f u) y)
    eq-cond : 
        -- given p and q
        (p : f ≡ g)(q : F ≡ G) → 
        -- in Type
        (λ i → (u : U)(y : Y) → α u ((q i) u y) ≤² β ((p i) u) y) 
        -- cond and cond' are equal
        [ cond ≡ cond' ]
    eq-cond p q = funExt λ u → funExt λ y → eq-elem (cong₂ α refl (funExt⁻ (funExt⁻ (λ i y u → q i u y) y) u))
                                                    (cong₂ β (funExt⁻ p u ) refl) 
                                                    (cond  u y) 
                                                    (cond' u y)

    -- Two morphisms in Dial(Set)(2) are equal when "given the same maps f and F"
    eq-dial-maps : f ≡ g → F ≡ G → m₁ ≡ m₂
    eq-dial-maps p q = λ i → p i ∧ q i st eq-cond p q i
    -- At what point is it easier to specifically define an equality of morphisms type instead of relying on _≡_ ?


module DialCat where 
    open import Cubical.Foundations.Prelude using (refl)
    open DialSet-eq-maps using (eq-dial-maps)
    open import CatLib using (PreCat)
    open PreCat renaming (_∘_ to _∘ᶜ_)

    -- Show DialSet is a category
    DialSetCat : {o : Level} → PreCat (lsuc o) (o) 
    DialSetCat .Ob      = DialSet 
    DialSetCat ._⇒_     = DialSetMap
    DialSetCat .id      = id-dial
    DialSetCat ._∘ᶜ_    = _∘ᴰ_
    DialSetCat .idr     = eq-dial-maps refl refl
    DialSetCat .idl     = eq-dial-maps refl refl
    DialSetCat .assoc   = eq-dial-maps refl refl


{-
    ✓ show DialSets is category
    _ show ! is an endofunctor on DialSets
-}

_⊗ᴰ_ : {ℓ : Level} → DialSet {ℓ} → DialSet {ℓ} → DialSet {ℓ} 
⟨ U , X , α ⟩ ⊗ᴰ ⟨ V , Y , β ⟩ = ⟨ U × V , X × Y , m ⟩ 
    where m : U × V  → X × Y → Two
          m (u , v) (x , y) =  α u x ⊗² β v y 

module TensorBiFunctor {ℓ : Level} where
    open DialCat using (DialSetCat)
    open import CatLib using (PreCat)
    open PreCat (DialSetCat {ℓ})
    open CatLib.BiFunctor (DialSetCat {ℓ}) (DialSetCat {ℓ}) (DialSetCat {ℓ}) using (BiFunctorT)
    open BiFunctorT
    open DialSet-eq-maps using (eq-dial-maps)
    open import Cubical.Foundations.Prelude using (refl)

    tensor : BiFunctorT 
    tensor .F₀ = _⊗ᴰ_
    tensor .F₁ {A} {A'} {B} {B'} m₁ m₂ = fmap
        where 
            open DialSet A                                                      -- A  := ⟨ U  , X  , α  ⟩ 
            open DialSet A' renaming (U to U' ; X to X'; α to α')               -- A' := ⟨ U' , X' , α' ⟩ 
            open DialSet B  renaming (U to V  ; X to Y ; α to β )               -- B  := ⟨ V  , Y  , β  ⟩ 
            open DialSet B' renaming (U to V' ; X to Y'; α to β')               -- B' := ⟨ V' , Y' , β' ⟩ 
            open DialSetMap m₁ renaming (cond-on-f&F to cond)                   -- m₁ := f ∧ F st cond
            open DialSetMap m₂ renaming (f to g; F to G; cond-on-f&F to cond')  -- m₂ := g ∧ G st cond'
            
            tensor-f : (U × V) → (U' × V')
            tensor-f (u , v) = (f u) , (g v)

            tensor-F : U × V → X' × Y' → X × Y
            tensor-F (u , v) (x' , y') = (F u x') , (G v y')

            tensor-cond : (uv : U × V)(x'y' : X' × Y') → 
                (α (fst uv) (F (fst uv) (fst x'y')) ⊗² β (snd uv) (G (snd uv) (snd x'y'))) 
                    ≤² 
                (α' (f (fst uv)) (fst x'y') ⊗² β' (g (snd uv)) (snd x'y'))
            tensor-cond (u , v) (x' , y') = bifun (cond u x') (cond' v y')

            fmap : (A ⊗ᴰ B) ⇒ (A' ⊗ᴰ B')
            fmap = tensor-f ∧ tensor-F st tensor-cond

    tensor .Fid   = eq-dial-maps refl refl
    tensor .Fcomp = eq-dial-maps refl refl


module Mon {ℓ : Level} where 
    open import Cubical.Core.Everything using (_≡_)
    open import Cubical.Foundations.Prelude using (refl; transp)
    open DialSet-eq-maps using (eq-dial-maps; eq-elem)
    open DialCat using (DialSetCat)
    open import CatLib using (PreCat)
    open PreCat (DialSetCat {ℓ})
    open CatLib.Iso (DialSetCat {ℓ})
    open _≅_

    open TensorBiFunctor using (tensor)

    open CatLib.Monoidal (DialSetCat {ℓ}) using (MonoidalT)
    open MonoidalT hiding (_⊗₀_;_⊗₁_)
    
    ⊗-unit : Ob 
    ⊗-unit = ⟨ Unit , Unit , (λ{ tt tt → ⊤}) ⟩

    _⊗₀_ : Ob → Ob → Ob 
    _⊗₀_ = CatLib.BiFunctor.BiFunctorT.F₀ tensor

    _⊗₁_ : {X Y Z W : Ob} → X ⇒ Y → Z ⇒ W → (X ⊗₀ Z) ⇒ (Y ⊗₀ W)
    _⊗₁_ = CatLib.BiFunctor.BiFunctorT.F₁ tensor

    -- suspicious..?  is using the underlying product on Sets and its projections what we want?
    DialCatMonoidal : MonoidalT
    DialCatMonoidal .⊗ = tensor
    DialCatMonoidal .unit = ⊗-unit
    DialCatMonoidal .unitorˡ {A} = prf 
        where 
            open DialSet A
            prf : (⊗-unit ⊗₀ A) ≅ A
            prf .from = (λ{(tt , u) → u}) ∧ (λ{ (tt , u) x → tt , x}) st λ{ (tt , u) x → {!  !}}
            prf .to   = (λ{ u → tt , u}) ∧ (λ{ x (tt , u) → u}) st {!   !}
            prf .isoˡ = eq-dial-maps refl refl
            prf .isoʳ = eq-dial-maps refl refl 
    DialCatMonoidal .unitorʳ {A} = prf 
        where 
            prf : (A ⊗₀ ⊗-unit) ≅ A
            prf .from = (λ{ (u , tt) → u}) ∧ (λ{ (u , tt) x → x , tt}) st {!   !}
            prf .to   = (λ{ u → u , tt}) ∧ (λ{ u (x , tt) → x}) st {!   !}
            prf .isoˡ = eq-dial-maps refl refl
            prf .isoʳ = eq-dial-maps refl refl
    DialCatMonoidal .associator {X}{Y}{Z} = prf 
        where 
            prf : {X Y Z : Ob} → (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)
            prf .from = (λ{ ((x , y) , z) → x , (y , z)}) ∧ (λ{ _ (x' , y' , z') → (x' , y') , z'}) st {!   !}
            prf .to   = (λ{ (x , y , z) → (x , y) , z}) ∧ (λ{ _ ((x , y) , z) → x , ( y , z)}) st {!   !}
            prf .isoˡ = eq-dial-maps refl refl 
            prf .isoʳ = eq-dial-maps refl refl
    DialCatMonoidal .pentagon = eq-dial-maps refl refl 


[_,_] : {ℓ : Level} → DialSet {ℓ} → DialSet {ℓ} → DialSet {ℓ}
[ ⟨ U , X , α ⟩ , ⟨ V , Y , β ⟩ ] = ⟨ (U → V) × (U × Y → X) , U × Y , m ⟩ 
    where m : (U → V) × ((U × Y → X)) → U × Y → Two 
          m (uv , uyx) (u , y) = α u (uyx (u , y)) ⊗² β (uv u) y

module InternalHomBiFunctor {ℓ : Level}  where 
    open DialCat using (DialSetCat)
    open import CatLib using (PreCat)
    open PreCat (DialSetCat {ℓ})
    open CatLib.BiFunctor (DialSetCat {ℓ}) (DialSetCat {ℓ}) (DialSetCat {ℓ}) using (BiFunctorT)
    open BiFunctorT
    open DialSet-eq-maps using (eq-dial-maps)
    open import Cubical.Foundations.Prelude using (refl)

    int-hom : BiFunctorT
    int-hom .F₀     = [_,_]
    int-hom .F₁ {A} {A'} {B} {B'} m₁ m₂ = fmap
        where 
            int-f : {!   !}
            int-f = {!   !}

            int-F : {!   !}
            int-F = {!   !}

            int-cond : {!   !}
            int-cond = {!   !}

            fmap : [ A , B ] ⇒ [ A' , B' ]
            fmap = int-f ∧ int-F st int-cond
    int-hom .Fid    = {!   !}
    int-hom .Fcomp  = {!   !}
    

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


--product \&
-- Ayᴮ × Cyᴰ = ACyᴮ⁺ᴰ

_&_ : {ℓ : Level} → DialSet {ℓ} → DialSet {ℓ} → DialSet {ℓ}
⟨ U , X , α ⟩ & ⟨ V , Y , β ⟩ = ⟨ U × V , X ⊎ Y , choose ⟩
    where choose : U × V → X ⊎ Y → Two 
          choose (u , v) (inj₁ x) = α u x 
          choose (u , v) (inj₂ y) = β v y

-- internal hom (bifunctor)
-- prove "profunctor"
--[_,_] : {ℓ : Level} → DialSet {ℓ} → DialSet {ℓ} → DialSet {ℓ}
--[ ⟨ U , X , α ⟩ , ⟨ V , Y , β ⟩ ] = ⟨ (U → V) × (U × Y → X) , U × Y , m ⟩ 
--    where m : (U → V) × ((U × Y → X)) → U × Y → Two 
--          m (uv , uyx) (u , y) = α u (uyx (u , y)) ⊗² β (uv u) y

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
  