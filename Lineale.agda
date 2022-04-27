module Lineale where

{- 
 These definitions are from 
 https://github.com/heades/cut-fill-agda/blob/master/lineale.agda
-}
open import Agda.Primitive
open import Cubical.Core.Everything using (_≡_)

record Proset {ℓ : Level}(A : Set ℓ) : Set (lsuc ℓ) where
 constructor MkProset
 field
   rel : A → A → Set
   prefl : ∀{a : A} → rel a a
   ptrans : ∀{a b c : A} → rel a b → rel b c → rel a c
open Proset {{...}}


record MonProset {ℓ : Level}(P : Set ℓ){{ P-pro : Proset P}} : Set (lsuc ℓ) where
 constructor MkMonProset
 field
   _⊙_ : P → P → P
   unit : P
   
   assoc : ∀{a b c : P} → a ⊙ (b ⊙ c) ≡ (a ⊙ b) ⊙ c
   left-ident : ∀{a : P} → unit ⊙ a ≡ a
   right-ident : ∀{a : P} → a ⊙ unit ≡ a

   symm : ∀{a b : P} → a ⊙ b ≡ b ⊙ a
   compat : ∀{a b : P} → rel a b → (∀{c : P} → (rel (a ⊙ c) (b ⊙ c)))

open MonProset {{...}}

record Lineale {ℓ : Level} (L : Set ℓ) {{ Pro : Proset L }} {{ Mpro : MonProset L}}: Set (lsuc ℓ) where
    constructor MkLineale
    field
        _⊸_ : L → L → L
        
        rlcomp : (a b : L) → rel (a ⊙ (a ⊸ b)) b
        adj : {a b y : L} → rel (a ⊙ y) b → rel y (a ⊸ b)
open Lineale {{...}}