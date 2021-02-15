{-# OPTIONS --prop --show-irrelevant #-}

module LibProp where

open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Function hiding (id; _∘_) public
open import Relation.Binary public
open import Relation.Binary.PropositionalEquality
  hiding (decSetoid; preorder; setoid) public
import Level as L

import Induction.WellFounded as Wf

module F where
  open import Function public

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

  extP : ∀{i j}{A : Prop i}{B : A → Set j}{f g : (x : A) → B x}
         → ((x : A) → f x  ≡ g x) → f ≡ g

  exti : ∀{i j}{A : Set i}{B : A → Set j}{f g : ∀ {x} → B x}
          → ((x : A) → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g

record Prf {α} (A : Prop α) : Set α where
  constructor prf
  field
    unprf : A
open Prf public

data Squash {α}(A : Set α) : Prop α where
  squash : A → Squash A

data Acc {i j}{A : Set i} (R : A → A → Prop j) (a : A) : Set (i L.⊔ j) where
  acc : (∀ a' → R a' a → Acc R a') → Acc R a

unAcc : ∀ {α β A R a} → Acc {α}{β}{A} R a → ∀ a' → R a' a → Acc R a'
unAcc (acc f) = f

Acc-prop : ∀ {α β A R i}(p q : Acc {α}{β}{A} R i) → p ≡ q
Acc-prop {R = R} (acc f) (acc g) = acc & ext λ j → extP λ p → Acc-prop (f j p) (g j p)

-- Acc-unprf : ∀ {α β A R i} → Acc {α}{β} {A} R i → Wf.Acc {α}{β}{A} (λ x y → Prf (R x y)) i
-- Acc-unprf (acc f) = Wf.acc (λ x p → Acc-unprf (f x (unprf p)))

-- Acc-prf : ∀ {α β A R i} → Wf.Acc {α}{β}{A} (λ x y → Prf (R x y)) i → Acc {α}{β} {A} R i
-- Acc-prf (Wf.acc f) = acc (λ x p → Acc-prf (f x (prf p)))

-- Acc-squash : ∀ {α β A R i} → Wf.Acc {α}{β}{A} R i → Acc {α}{β} {A} (λ x y → Squash (R x y)) i
-- Acc-squash (Wf.acc f) = acc (λ x p → {!!})
