module Nat where
open import Cubical.Core.Everything using (_≡_; PathP;Path; I ; i0 ; i1 ; hcomp)
open import Cubical.Foundations.Prelude using (sym; subst2; cong; cong₂;refl; transport)

open import Data.Nat using (_≤_)
open _≤_
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Cubical.Data.Nat 
open import Cubical.Data.Nat.Properties

open import Lineale 
open Lineale.Proset {{...}}
open Lineale.MonProset {{...}}
open Lineale.Lineale {{...}}

_-_ : ℕ → ℕ → ℕ 
zero - m = zero
suc n - zero = suc n
suc n - suc m = n - m

instance
    ℕ-Proset : Proset ℕ
    ℕ-Proset .rel = _≤_
    ℕ-Proset .prefl = ≤-refl
    ℕ-Proset .ptrans = ≤-trans
    
    ℕ-MonPro : MonProset ℕ 
    ℕ-MonPro ._⊙_ = _+_
    ℕ-MonPro .unit = 0
    ℕ-MonPro .assoc {x} {y} {z} = (+-assoc x y z)
    ℕ-MonPro .left-ident {x} = refl
    ℕ-MonPro .right-ident {x} = +-zero x
    ℕ-MonPro .compatˡ = prf 
        where 
            prf : ∀{a b : ℕ} → a ≤ b → (∀{c : ℕ} → (c + a) ≤ (c + b))
            prf {a} {b} lt {zero} = lt
            prf {a} {b} lt {suc c} = s≤s (prf lt)
    ℕ-MonPro .compatʳ = prf
        where 
            prf : ∀{a b : ℕ} → a ≤ b → (∀{c : ℕ} → (a + c) ≤ (b + c))
            prf {a} {b} lt {zero} = subst2 (λ x y → x ≤ y) (sym (+-zero a)) (sym (+-zero b)) lt 
            prf {a} {b} lt {suc c} = subst2 (λ x y → x ≤ y) (+-comm (suc c) a) (+-comm (suc c) b) 
                (s≤s (subst2 ((λ x y → x ≤ y)) (+-comm a c) (+-comm b c) (prf lt)))

    ℕ-Lineale : Lineale ℕ 
    ℕ-Lineale ._⊸_  x y = y - x
    ℕ-Lineale .rlcomp {a} {b} = {!   !}
        where 
            prf : (a b : ℕ) → a + (b - a) ≤ b
            prf zero zero = ≤-refl
            prf zero (suc y) = ≤-refl
            prf (suc x) zero = {!  suc x + (zero - suc x) ≤ zero !}
            prf (suc x) (suc y) = {!   !}
 

    ℕ-Lineale .adj = {!   !}