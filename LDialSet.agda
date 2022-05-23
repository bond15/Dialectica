-- proposing to rename this LDialSet for Linear Dialectica over Sets or lineale-based dialectica
module LDialSet where 
open import Agda.Primitive
open import Data.Product
open import Lineale

module defs {ℓ : Level}{L : Set ℓ}
    {{ Pro : Proset L }}
    {{ Mon : MonProset L }}
    {{ _ : Lineale L}} where    
    
    open module Pro = Proset Pro renaming (rel to _≤L_)

    {- TODO 
        * wrap these constructions in a PreCategory definition
        * Don't implicitly use Agda's Set as the base Category
            parameterize definition by a base PreCategory
                use display category?
    -}

        {-
        Obj : U → X → L 

        Hom : given 
                U    V
                |    |
               α|   β|
                |    |
                X    Y
                |    |
                L    L

            have maps f,F

                   f
                U--->V
                |    |
               α|   β|
                |  F |
                X<---Y
                |    |
                L    L

            st 
                given u,y

                α(u,F(y)) rel β(f(u),y)
    -}
    record DObj : Set (lsuc ℓ) where 
        constructor _⇒_∍_
        field 
            U : Set ℓ
            X : Set ℓ
            rl : U → X → L

    record DHom (A B : DObj): Set ℓ where 
        constructor _⟫_⟪_
        open module A = DObj A renaming (rl to α)
        open module B = DObj B renaming (U to V ; X to Y ; rl to β)
        field 
            f : U → V
            F : Y → X
            cond : ∀ {u : U} {y : Y} → α u (F y) ≤L β (f u) y 

    infixl 20 _；_
    _；_ : ∀{ℓ : Level} {A B C : Set ℓ} → (A → B) → (B → C) → (A → C) 
    _；_ f g x = g (f x)

    comp : {A B C : DObj} → DHom B C → DHom A B → DHom A C
    comp {U ⇒ X ∍ α} {V ⇒ Y ∍ β} {W ⇒ Z ∍ γ} (g ⟫ G ⟪ p₂) (f ⟫ F ⟪ p₁)
        = (f ； g) ⟫ G ； F ⟪ prf 
        where 
            prf : {u : U}{z : Z} → α u (F (G z)) ≤L γ (g (f u)) z
            prf {u} {z} = ptrans p₁ p₂

    infixl 5 _⊚_
    _⊚_ = comp

    id : {ℓ : Level}{A : Set ℓ} → A → A 
    id x = x

    Did : {A : DObj} → DHom A A 
    Did = id ⟫ id ⟪ prefl

    open import Cubical.Core.Everything using (_≡_)
    open import Cubical.Foundations.Prelude using (refl)

    infix 4 _≡h_
    
    _≡h_ : {A B : DObj} → (f g : DHom A B) → Set ℓ 
    _≡h_ (f ⟫ F ⟪ _) (g ⟫ G ⟪ _) = f ≡ g × F ≡ G


    ⊚-idl : ∀{A B}{f : DHom A B} → (Did ⊚ f) ≡h f 
    ⊚-idl = refl , refl

    ⊚-idr : ∀{A B}{f : DHom A B} → (f ⊚ Did) ≡h f 
    ⊚-idr = refl , refl

    ⊚-assoc : ∀{A B C D}{h : DHom A B}{g : DHom B C}{f : DHom C D} → (f ⊚ (g ⊚ h)) ≡h ((f ⊚ g) ⊚ h)
    ⊚-assoc = refl , refl

    
-- Symetric Monoidal Cartesian Closed 
    open module Mon = MonProset Mon renaming (_⊙_ to _⊗L_)


    _⊗ᵣ_ : ∀{U X V Y : Set ℓ} → (U → X → L) → (V → Y → L) → ((U × V) → ((V → X) × (U → Y)) → L)
    (α ⊗ᵣ β) (u , v) (f , g) = α u (f v) ⊗L β v (g u)

    -- pair inputs 
    -- cross output to input maps?
    -- utilizing the product of Set? (U × V)
    -- and the fact that Set has exponentials? (V → X)

{-
    U   V 
    |   |
   α|  β|
    |   |
    X   Y

    to

    U × V
      |
      |
      |
 (V→X)×(U→Y)
-}
    _⊗ₒ_ : (A B : DObj) → DObj
    (U ⇒ X ∍ α) ⊗ₒ (V ⇒ Y ∍ β) = (U × V) ⇒ ((V → X) × (U → Y)) ∍ (α ⊗ᵣ β)


    {-
        Intuition 
            let sz and wt be "bridges between hom squares"
            pre and post compose them with the existing "hom maps" f, F, g, G
              g          F
            V--->S....Z---->X

              f          G
            U--->W....T---->Y
    -}
    F⊗ : ∀{S Z W T V X U Y : Set ℓ} → 
            {f : U → W}{F : Z → X}{g : V → S}{G : T → Y} → 
            (S → Z) × (W → T) → (V → X) × (U → Y)
    F⊗ {f = f} {F} {g} {G} (sz , wt) = (g ； sz ； F) , (f ； wt ； G)


    {- 

        A    C    B    D
          f         g
        U--->V    W--->S
        |    |    |    |
       α|   γ|   β|   ε|
        | F  |    | G  |
        X<---Y    Z<---T

        Hom A C   Hom B D

        To

    DHom A ⊗ₒ B         C ⊗ₒ D 
                  ?
         U × W -------> V × S
           |              |
     α ⊗ᵣ β|              | γ ⊗ᵣ ε
           |       ?      |
      (W→X)×(U→Z)<---(S→Y)×(V→T)


    -}

    -- should be from an import
    ⟨_,_⟩ : {A B C D : Set ℓ} → (A → C) → (B → D) → (A × B) → C × D 
    ⟨ f , g ⟩ x = (f (proj₁ x)) , (g (proj₂ x))

    
    _⊗ₐ_ : {A B C D : DObj} → 
        DHom A C → DHom B D → DHom (A ⊗ₒ B) (C ⊗ₒ D)
    _⊗ₐ_ {U ⇒ X ∍ α} {W ⇒ Z ∍ β}
         {V ⇒ Y ∍ ɣ} {S ⇒ T ∍ ε} 
         (f ⟫ F ⟪ p₁)(g ⟫ G ⟪ p₂) = 
            -- first is a map between products 
            ⟨ f , g ⟩ ⟫ 
            -- map between pairs of maps
            F⊗ {f = f}{F}{g}{G} ⟪
            -- Hom condition
            λ {u y} → cond {u} {y}
            where      -- "corners" of the square u and y
                cond : {u : U × W}{y : (S → Y) × (V → T)} → 
                    (α ⊗ᵣ β) u ((F⊗ {f = f}{F}{g}{G}) y) ≤L (ɣ ⊗ᵣ ε) ((⟨ f , g ⟩) u) y
                cond {u , w} {sy , vt} = bifun _ _ _ _ p₁ p₂

-- show ⊗ is funtorial

module asPreCat {ℓ : Level}{L : Set ℓ}
    {{ Pro : Proset L }}
    {{ _ : MonProset L }}
    {{ _ : Lineale L}} where 

    open defs renaming (id to id')

    open import Cubical.Core.Everything using (_≡_)
    open import Data.Nat using (ℕ;suc)

    record is-contr {ℓ} (A : Set ℓ) : Set ℓ where
        constructor contr 
        field 
            centre : A 
            paths : (x : A) → centre ≡ x
    open is-contr public

    is-prop : ∀{ℓ} → Set ℓ → Set _ 
    is-prop A = (x y : A) → x ≡ y  

    is-hlevel : ∀{ℓ} → Set ℓ → ℕ → Set _ 
    is-hlevel A 0 = is-contr A
    is-hlevel A 1 = is-prop A
    is-hlevel A (suc n) = (x y : A) → is-hlevel (x ≡ y) n

    is-set : ∀{ℓ} → Set ℓ → Set ℓ 
    is-set A = is-hlevel A 2

    record PreCat (o h : Level) : Set (lsuc (o ⊔ h)) where 
        field 
            Ob : Set o
            Hom : Ob → Ob → Set h
            Hom-set : (x y : Ob) → is-set (Hom x y) -- if p : x ≡ y, q : x ≡ y, then p ≡ q
            id : ∀ {x} → Hom x x
            _≣_ : ∀{A B}→ (f g : Hom A B) → Set h
            _∘_ : ∀{x y z} → Hom y z → Hom x y → Hom x z

            idr : ∀{x y}{f : Hom x y} → (f ∘ id) ≣ f 
            idl : ∀{x y}{f : Hom x y} → id ∘ f ≣ f
            assoc : ∀{w x y z} {f : Hom y z}{g : Hom x y}{h : Hom w x} → f ∘ (g ∘ h) ≣ (f ∘ g) ∘ h
        infixr 40 _∘_

    Dial : PreCat (lsuc ℓ) ℓ
    Dial = record
        { Ob = DObj
        ; Hom = DHom
        ; Hom-set = {!   !}
        ; id = Did
        ; _≣_ = _≡h_
        ; _∘_ = _⊚_
        ; idr = {!   !} --⊚-idr
        ; idl = {!   !} --⊚-idl
        ; assoc = {!   !} --⊚-assoc
        }  
