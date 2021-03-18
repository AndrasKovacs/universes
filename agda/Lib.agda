
module Lib where

open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Function hiding (id; _∘_; _⇔_) public
open import Induction.WellFounded public
open import Relation.Binary public
open import Relation.Binary.PropositionalEquality
  hiding (decSetoid; preorder; setoid; [_]) public

import Level as L
module F where open import Function public

coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
coe refl x = x

_&_ = cong;  infixl 9 _&_; {-# DISPLAY cong  = _&_ #-}
_◾_ = trans; infixr 4 _◾_; {-# DISPLAY trans = _◾_ #-}
_⁻¹ = sym;   infix  6 _⁻¹; {-# DISPLAY sym   = _⁻¹ #-}

coe∘ : ∀ {i}{A B C : Set i}(p : B ≡ C)(q : A ≡ B)(a : A)
       → coe p (coe q a) ≡ coe (q ◾ p) a
coe∘ refl refl _ = refl

UIP : ∀ {i}{A : Set i}{x y : A}{p q : x ≡ y} → p ≡ q
UIP {p = refl}{refl} = refl

-- function extensionality
postulate
  ext : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
        → ((x : A) → f x  ≡ g x) → f ≡ g

  exti : ∀{i j}{A : Set i}{B : A → Set j}{f g : ∀ {x} → B x}
          → ((x : A) → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g

unAcc : ∀ {α β A R i} → Acc {α}{β}{A} R i → ∀ j → R j i → Acc R j
unAcc (acc f) = f

Acc-prop : ∀ {α β A R i}(p q : Acc {α}{β}{A} R i) → p ≡ q
Acc-prop (acc f) (acc g) = acc & ext λ j → ext λ p → Acc-prop (f j p) (g j p)

happly : ∀ {α β}{A : Set α}{B : Set β}{f g : A → B} → f ≡ g → ∀ a → f a ≡ g a
happly refl a = refl

_⊗_ :
  ∀ {α β}{A : Set α}{B : Set β}
    {f g : A → B}(p : f ≡ g){a a' : A}(q : a ≡ a')
  → f a ≡ g a'
refl ⊗ refl = refl
infixl 8 _⊗_

data W {α}{β}(A : Set α) (B : A → Set β) : Set (α L.⊔ β) where
  sup : (a : A) → (B a → W A B) → W A B
