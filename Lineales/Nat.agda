{-# OPTIONS --allow-unsolved-metas #-}
module Nat where
open import Cubical.Core.Everything using (_≡_; PathP;Path; I ; i0 ; i1 ; hcomp)
open import Cubical.Foundations.Prelude using (sym; subst; subst2; cong; cong₂;refl; transport)

open import Data.Nat hiding(_≥_)
open _≤_
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Cubical.Data.Nat 
open import Cubical.Data.Nat.Properties

open import Lineale 
open Lineale.Proset {{...}}
open Lineale.MonProset {{...}}
open Lineale.Lineale {{...}}


{-
The monoid structure is given by the sum of natural numbers, a ⊗ b := a + b, whose unit
is 0.
• The partial ordering is given by the opposite of the usual order on natural numbers.
• The implication is given by truncated subtraction: a ( b := max{b − a, 0}.
The basic suggestion of this structure on the natural numbers comes from [Law73 ]. We
can check that this structure is indeed that of a lineale.
-}
_-_ : ℕ → ℕ → ℕ 
zero - m = zero
suc n - zero = suc n
suc n - suc m = n - m

data _≥_ : ℕ → ℕ → Set where
  n≥z : ∀ {n}                 → n  ≥ zero
  s≥s : ∀ {m n} (m≥n : m ≥ n) → suc m ≥ suc n

≥-refl : {a : ℕ} → a ≥ a
≥-refl {zero} = n≥z
≥-refl {suc a} = s≥s ≥-refl

≥-trans : {a b c : ℕ} → a ≥ b → b ≥ c → a ≥ c
≥-trans n≥z n≥z = n≥z
≥-trans (s≥s p) n≥z = n≥z
≥-trans (s≥s p) (s≥s q) = s≥s (≥-trans  p q)

instance
    ℕ-Proset : Proset ℕ
    ℕ-Proset .rel = _≥_
    ℕ-Proset .prefl {a} = ≥-refl
    ℕ-Proset .ptrans = ≥-trans
    
    ℕ-MonPro : MonProset ℕ 
    ℕ-MonPro ._⊙_ = _+_
    ℕ-MonPro .unit = 0
    ℕ-MonPro .assoc {x} {y} {z} = (+-assoc x y z)
    ℕ-MonPro .left-ident {x} = refl
    ℕ-MonPro .right-ident {x} = +-zero x
    ℕ-MonPro .compatˡ = prf 
        where 
            prf : ∀{a b : ℕ} → a ≥ b → (∀{c : ℕ} → (c + a) ≥ (c + b))
            prf gte {zero} = gte
            prf gte {suc z} = s≥s (prf gte)

    ℕ-MonPro .compatʳ = prf
        where 
            prf : ∀{a b : ℕ} → a ≥ b → (∀{c : ℕ} → (a + c) ≥ (b + c))
            prf {a} {b} gte {zero} = subst2 _≥_ ((sym (+-zero a))) ((sym (+-zero b))) gte
            prf {a} {b} gte {suc c} = subst2 _≥_ ((+-comm (suc c) a))  ((+-comm (suc c) b))
                 ((s≥s (subst2 _≥_  (+-comm a c) (+-comm b c) (prf gte))))
    ℕ-Lineale : Lineale ℕ 
    ℕ-Lineale ._⊸_  x y = y - x
    ℕ-Lineale .rlcomp {a} {b} = prf a b
        where 
            prf : (a b : ℕ) → (a + (b - a)) ≥ b
            prf zero zero = ≥-refl
            prf zero (suc b) = ≥-refl
            prf (suc a) zero = n≥z
            prf (suc a) (suc b) = s≥s (prf a b)

    ℕ-Lineale .adj {a} {b} {y} = prf a b y
        where 
            prf : (a b y : ℕ) → (a + y) ≥ b → y ≥ (b - a)
            prf zero zero y p = p
            prf zero (suc b) y p = p
            prf (suc a) zero y p = n≥z
            prf (suc a) (suc b) zero p = {! p  !}
            prf (suc a) (suc b) (suc y) p = {!   !}
            --  subst2 _≥_ refl (dd a b) {! p !}
                where 
                    dd : (a b : ℕ) → (suc b) - (suc a) ≡ b - a
                    dd zero zero = refl
                    dd zero (suc b) = refl
                    dd (suc a) zero = refl
                    dd (suc a) (suc b) = refl