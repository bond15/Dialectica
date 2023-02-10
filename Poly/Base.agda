{-# OPTIONS --without-K #-}
module Base where


open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum.Base using (_⊎_; inj₁ ; inj₂)
open import Data.Fin.Base using (Fin ; suc; zero ; fromℕ)

open import Cubical.Core.Everything using (_≡_; PathP;Path; I ; i0 ; i1 ; hcomp)
open import Cubical.Foundations.Prelude using (cong; cong₂;refl; transport)

open import Agda.Builtin.Sigma 

infix 0 _≈_
record _≈_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≈_


data Unit : Set where
    unit : Unit

eq-Σ : { I X : Set} → (e1 e2 : Σ I (λ _ → X )) → fst e1 ≡ fst e2 →  snd e1 ≡ snd e2 → e1 ≡ e2 
eq-Σ (i,f) (i',f') ieq feq = cong₂ _,_ ieq feq


lemma-funit : {A : Set} → (f :  A → Unit) → ( a : A )  → f a ≡ unit
lemma-funit f a with f a
...               | unit = refl


_؛_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
f ؛ g = λ x → g(f x)


data Dir₀ : Set where
data Dir₁ : Set where
    D₁ : Dir₁
data Dir₂ : Set where
    D₁ D₂ : Dir₂
data Dir₃ : Set where
    D₁ D₂ D₃ : Dir₃
data Dir₄ : Set where
    D₁ D₂ D₃ D₄ : Dir₄

data Pos₁ : Set where
    P₁ : Pos₁
data Pos₂ : Set where
    P₁ P₂ : Pos₂
data Pos₃ : Set where
    P₁ P₂ P₃ : Pos₃
data Pos₄ : Set where
    P₁ P₂ P₃ P₄ : Pos₄