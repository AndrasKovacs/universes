
{-# OPTIONS --postfix-projections #-}

-- Notes on using Palmgren's super universe


module Super where

open import Lib
open import Data.Nat
open import Function

data O : Set where
  zero : O
  suc  : O → O
  sup  : (ℕ → O) → O

ℕ→O : ℕ → O
ℕ→O zero    = zero
ℕ→O (suc n) = suc (ℕ→O n)

ω : O
ω = sup ℕ→O

module Cumulative where

  module _ {U : Set}{El : U → Set} where

    data UU : Set
    EL : UU → Set

    data UU where
      U'  : UU
      El' : U → UU
      Π'  : ∀ a → (El a → UU) → UU
      ℕ'  : UU

    EL U'       = U
    EL (El' a)  = El a
    EL (Π' a b) = ∀ x → EL (b x)
    EL ℕ'       = ℕ

  -- super universe
  data V : Set
  S : V → Set

  data V where
    UU' : (a : V) → (S a → V) → V
    EL' : ∀ {a b} → S (UU' a b) → V
    ℕ'  : V
    Π'  : (a : V) → (S a → V) → V
    Σ'  : (a : V) → (S a → V) → V

  S (UU' a b) = UU {S a} {S ∘ b}
  S (EL' x)   = EL x
  S ℕ'        = ℕ
  S (Π' a b)  = ∀ x → S (b x)
  S (Σ' a b)  = ∃ (S ∘ b)

  VFam : Set
  VFam = ∃ λ a → S a → V

  û : VFam → VFam
  û (a , b) = UU' a b , EL' {a}{b}

  û^ : ℕ → VFam
  û^ zero    = ℕ' , (λ _ → ℕ')
  û^ (suc n) = û (û^ n)

  Uω : V
  Uω = UU' (Σ' ℕ' λ n → û^ n .₁) (λ {(n , a) → û^ n .₂ a})

  Uω' : V
  Uω' = UU' ℕ' (₁ ∘ û^)

  -- x : S Uω'
  -- x = El' 4

  -- Uω : Set
  -- Uω = UU {∃ λ n → S (û^ n .₁)} {λ {(n , a) → S (û^ n .₂ a)}}


  module NatU where  -- cumulative, non-recursive sub-universes
    U : ℕ → Set
    El : ∀ {n} → U n → Set
    U  zero      = ⊥
    U  (suc n)   = UU {U n}{El {n}}
    El {suc n} a = EL a

    ↑ : ∀ {n} → U n → U (suc n)
    ↑ {suc n} a = El' a

    ↑El : ∀ {n a} → El (↑ {n} a) ≡ El a  -- not recursive: ↑ ℕ' ≢ ℕ'
    ↑El {suc n} {a} = refl

  module NatU2 where     -- cumulative, recursive sub-universes (but not transfinite)

    U : ℕ → Set
    El : ∀ {n} → U n → Set
    U zero = ⊥
    U (suc n) = UU {U n}{El {n}}
    El {suc n} U' = U n
    El {suc n} (El' a) = El a
    El {suc n} (Π' a b) = ∀ x → El (b x)
    El {suc n} ℕ' = ℕ

    ↑ : ∀ {n} → U n → U (suc n)
    El≡ : ∀ {n} a → El a ≡ El (↑ {n} a)
    ↑ {suc n} U'       = El' U'
    ↑ {suc n} (El' a)  = El' (↑ a)
    ↑ {suc n} (Π' a b) = Π' (↑ a) λ x → ↑ (b (coe (El≡ a ⁻¹) x))
    ↑ {suc n} ℕ'       = ℕ'
    El≡ {suc n} U' = refl
    El≡ {suc n} (El' a) = El≡ a
    El≡ {suc n} (Π' a b) rewrite El≡ a =
       (λ b → (∀ x → b x)) & (_∋_ ((λ x → El (b x)) ≡ (λ x → El (↑ (b x)))) (ext λ x → El≡ (b x)))
    El≡ {suc n} ℕ' = refl

  module OU where -- transfinite, but non-recursive

    U : O → Set
    El : ∀ {i} → U i → Set
    U  zero      = ⊥
    U  (suc i)   = UU {U i}{El {i}}
    U  (sup f)   = UU {∃ (U ∘ f)}{El ∘ ₂}
    El {suc i} a = EL a
    El {sup f} a = EL a

    foo : U (suc (suc (suc zero)))
    foo = Π' U' λ A → Π' (El' A) λ _ → El' (El' A)

    ex1 : U ω
    ex1 = El' (3 , foo)

    ex2 : U ω
    ex2 = Π' (3 , foo) λ _ → ℕ'

    ↑+ : ∀ {i} → U i → U (suc i)
    ↑+ {i} a = El' a

    ↑sup : ∀ {f n} → U (f n) → U (sup f)
    ↑sup {f} {n} a = El' (n , a)
