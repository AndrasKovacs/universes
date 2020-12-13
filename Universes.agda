
module Universes where

open import Lib

-- well-founded semicategory
record WfSemiCat : Set₁ where
  infix 4 _<_
  infixr 5 _∘_
  field
    Lvl         : Set
    _<_         : Lvl → Lvl → Set
    _∘_         : ∀ {i j k} → j < k → i < j → i < k
    ass         : ∀ {i j k l}{f : k < l}{g}{h : i < j} → f ∘ g ∘ h ≡ (f ∘ g) ∘ h
    instance wf : ∀ {i} → Acc _<_ i

  acyclic : ∀ {i} → i < i → ⊥
  acyclic {i} p = go wf p where
    go : ∀ {i} → Acc _<_ i → i < i → ⊥
    go {i} (acc f) q = go (f i q) q


module IR-Univ (lvl : WfSemiCat) where
  open WfSemiCat lvl public
  open import Data.Nat hiding (_<_; _≤_)

  infix 4 _<'_

  data UU {i}(l : ∀ j → j < i → Set) : Set
  EL : ∀ {i l} → UU {i} l → Set

  data UU {i} l where
    U'    : ∀ {j} → j < i → UU l
    ℕ'    : UU l
    Π' Σ' : (a : UU l) → (EL a → UU l) → UU l

    -- used for internal levels
    Lvl'  : UU l
    _<'_  : Lvl → Lvl → UU l

  EL {_}{l}(U' p) = l _ p
  EL ℕ'           = ℕ
  EL Lvl'         = Lvl
  EL (i <' j)     = i < j
  EL (Π' a b)     = ∀ x → EL (b x)
  EL (Σ' a b)     = ∃ λ x → EL (b x)

  -- Interpreting levels & lifts
  --------------------------------------------------------------------------------

  U↓ : ∀ {i} {{_ : Acc _<_ i}} j → j < i → Set
  U↓ {i} {{acc f}} j p = UU {j} (U↓ {{f j p}})

  U : Lvl → Set
  U i = UU (U↓ {i})

  El : ∀ {i} → U i → Set
  El = EL

  U↓-compute : ∀ {i a j p} → U↓ {i}{{a}} j p ≡ U j
  U↓-compute {i} {acc f} {j} {p} = (λ a → UU (U↓ {{a}})) & Acc-prop (f j p) wf

  ↑   : ∀ {i j} → i < j → U i → U j
  El↑ : ∀ {i j} p a → El (↑ {i}{j} p a) ≡ El a
  ↑   p (U' q)   = U' (p ∘ q)
  ↑   p ℕ'       = ℕ'
  ↑   p Lvl'     = Lvl'
  ↑   p (i <' j) = i <' j
  ↑   p (Π' a b) = Π' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  ↑   p (Σ' a b) = Σ' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  El↑ p (U' q)   = U↓-compute {p = p ∘ q} ◾ U↓-compute {p = q} ⁻¹
  El↑ p ℕ'       = refl
  El↑ p Lvl'     = refl
  El↑ p (i <' j) = refl
  El↑ p (Π' a b) rewrite El↑ p a = (λ f → ∀ x → f x) & ext (El↑ p F.∘ b)
  El↑ p (Σ' a b) rewrite El↑ p a = ∃ & ext (El↑ p F.∘ b)

  -- congruence helper
  ΠΣ≡ : ∀ {i}{l : ∀ j → j < i → Set}
          (F' : (a : UU l) → (EL a → UU l) → UU l)
          {a₀ a₁ : UU l}(a₂ : a₀ ≡ a₁)
          {b₀ : EL a₀ → UU l}{b₁ : EL a₁ → UU l}
        → (∀ x → b₀ x ≡ b₁ (coe (EL & a₂) x))
        → F' a₀ b₀ ≡ F' a₁ b₁
  ΠΣ≡ {i} {l} F' {a₀} refl {b₀} {b₁} b₂ = F' a₀ & ext b₂

  -- functorial lifting
  ↑∘ : ∀ {i j k}(p : i < j)(q : j < k) a → ↑ q (↑ p a) ≡ ↑ (q ∘ p) a
  ↑∘ p q (U' r)   = U' & ass
  ↑∘ p q ℕ'       = refl
  ↑∘ p q Lvl'     = refl
  ↑∘ p q (i <' j) = refl
  ↑∘ p q (Π' a b) =
    ΠΣ≡ Π' (↑∘ p q a)
        (λ x → ↑∘ p q _
             ◾ (λ x → ↑ (q ∘ p) (b x)) &
                  (coe∘ (El↑ p a) (El↑ q (↑ p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (El↑ (q ∘ p) a) (EL & ↑∘ p q a) x ⁻¹))
  ↑∘ p q (Σ' a b) =
    ΠΣ≡ Σ' (↑∘ p q a)
        (λ x → ↑∘ p q _
             ◾ (λ x → ↑ (q ∘ p) (b x)) &
                  (coe∘ (El↑ p a) (El↑ q (↑ p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (El↑ (q ∘ p) a) (EL & ↑∘ p q a) x ⁻¹))

  -- conveniences
  --------------------------------------------------------------------------------

  _⇒'_ : ∀ {i l} → UU {i} l → UU l → UU l
  a ⇒' b = Π' a λ _ → b
  infixr 3 _⇒'_

  _×'_ : ∀ {i l} → UU {i} l → UU l → UU l
  a ×' b = Σ' a λ _ → b
  infixr 4 _×'_

  -- This is convenient in code examples, where we often want to lift values in EL U'
  ↑U : ∀ {i j}(p : i < j) → El (U' p) → U j
  ↑U p a = ↑ p (coe U↓-compute a)


  -- Example fragment of a model for Jon's TT
  -- Many omitted parts are awful to formalize.
  --------------------------------------------------------------------------------

  module JonTT where
    Con : Set₁
    Con = Set

    Ty : Con → Lvl → Set
    Ty Γ j = Γ → U j

    Tm : ∀ Γ {i} → Ty Γ i → Set
    Tm Γ A = (γ : Γ) → El (A γ)

    Sub : Con → Con → Set
    Sub Γ Δ = Γ → Δ

    lift : ∀ {Γ i j} → i < j → Ty Γ i → Ty Γ j
    lift p A γ = ↑ p (A γ)

    infixl 5 _[_]T
    _[_]T : ∀ {Γ Δ i} → Ty Δ i → Sub Γ Δ → Ty Γ i
    _[_]T A σ γ = A (σ γ)

    lift[]T : ∀ {Γ Δ i j p σ A} → lift {Δ}{i}{j} p A [ σ ]T ≡ lift {Γ} p (A [ σ ]T)
    lift[]T = refl

    Cumulative : ∀ {Γ i j p A} → Tm Γ A ≡ Tm Γ (lift {Γ}{i}{j} p A)
    Cumulative {p = p}{A} = (λ f → ∀ x → f x) & ext λ γ → El↑ p (A γ) ⁻¹

    u : ∀ {Γ i j} → i < j → Ty Γ j
    u p _ = U' p

    Russell : ∀ {Γ i j p} → Tm Γ (u {Γ}{i}{j} p) ≡ Ty Γ i
    Russell = (λ f → ∀ x → f x) & ext λ _ → U↓-compute

    infixl 4 _▶_
    _▶_ : (Γ : Con) → ∀ {i} → Ty Γ i → Con
    Γ ▶ A = Σ Γ λ γ → El (A γ)

    ▶lift : ∀ {Γ i j A}{p : i < j} → (Γ ▶ A) ≡ (Γ ▶ lift p A)
    ▶lift {Γ}{A = A}{p} = Σ Γ & ext λ γ → El↑ p (A γ) ⁻¹

    Π : ∀ {Γ i}(A : Ty Γ i) → Ty (Γ ▶ A) i → Ty Γ i
    Π {Γ}{i} A B γ = Π' (A γ) λ α → B (γ , α)

    lam : ∀ {Γ i A B} → Tm (Γ ▶ A) B → Tm Γ {i} (Π A B)
    lam t γ α = t (γ , α)

    app : ∀ {Γ i A B} → Tm Γ {i} (Π A B) → Tm (Γ ▶ A) B
    app t (γ , α) = t γ α


  -- Internalized levels
  --------------------------------------------------------------------------------

  module InternalLevelTT where

    Con : Set₁
    Con = Set

    -- levels in context
    Level : Con → Set
    Level Γ = Γ → Lvl

    Ty : (Γ : Con) → Level Γ → Set
    Ty Γ i = (γ : Γ) → U (i γ)

    Tm : (Γ : Con) → ∀ {i} → Ty Γ i → Set
    Tm Γ {i} A = (γ : Γ) → El (A γ)

    Level' : ∀ {Γ i} → Ty Γ i
    Level' {Γ}{i} γ = Lvl'

    -- "Russell-style" levels
    RussellLevel : ∀ {Γ i} → Tm Γ (Level' {Γ}{i}) ≡ Level Γ
    RussellLevel = refl

    Lt : ∀ {Γ i} → Level Γ → Level Γ → Ty Γ i
    Lt i j γ = i γ <' j γ

    Comp : ∀ {Γ l i j k} → Tm Γ {l} (Lt i j) → Tm Γ {l} (Lt j k) → Tm Γ {l} (Lt i k)
    Comp t u γ = u γ ∘ t γ

    lift : ∀ {Γ}{i j : Level Γ} → Tm Γ {j} (Lt i j) → Ty Γ i → Ty Γ j
    lift {i = i}{j} p A γ = ↑ (p γ) (A γ)

    Cumulative : ∀ {Γ i j p A} → Tm Γ A ≡ Tm Γ (lift {Γ}{i}{j} p A)
    Cumulative {Γ}{i}{j}{p}{A} = (λ f → ∀ x → f x) & ext λ γ → El↑ (p γ) (A γ) ⁻¹

    u : ∀ {Γ i j} → Tm Γ {j} (Lt i j) → Ty Γ j
    u p γ = U' (p γ)

    RussellUniv : ∀ {Γ i j p} → Tm Γ (u {Γ}{i}{j} p) ≡ Ty Γ i
    RussellUniv = (λ f → ∀ x → f x) & ext λ γ → U↓-compute



-- Additional assumption: levels are ordinals (as in HoTT book 10.4). 
-- This is a realistic assumption for notions of TT models and for type checking,
-- and makes it possible to have least-upper-bound reasoning.
--------------------------------------------------------------------------------

pattern inj₂₁ x  = inj₂ (inj₁ x)
pattern inj₂₂ x  = inj₂ (inj₂ x)

record Ordinal (lvl : WfSemiCat) : Set where
  open WfSemiCat lvl
  field
    cmp    : ∀ i j → i < j ⊎ j < i ⊎ i ≡ j
    <-prop : ∀ {i j}{p q : i < j} → p ≡ q
    <-ext  : ∀ {i j} → (∀ k → (k < i → k < j) × (k < j → k < i)) → i ≡ j

  _≤_ : Lvl → Lvl → Set; infix 4 _≤_
  i ≤ j = i < j ⊎ i ≡ j

  _⊔_ : Lvl → Lvl → Lvl; infixr 5 _⊔_
  i ⊔ j with cmp i j
  ... | inj₁  _ = j
  ... | inj₂₁ _ = i
  ... | inj₂₂ _ = i

  ⊔₁ : ∀ i j → i ≤ i ⊔ j
  ⊔₁ i j with cmp i j
  ... | inj₁  p = inj₁ p
  ... | inj₂₁ p = inj₂ refl
  ... | inj₂₂ p = inj₂ refl

  ⊔₂ : ∀ i j → j ≤ i ⊔ j
  ⊔₂ i j with cmp i j
  ... | inj₁  p = inj₂ refl
  ... | inj₂₁ p = inj₁ p
  ... | inj₂₂ p = inj₂ (p ⁻¹)

  ⊔-least : ∀ {i j k} → i ≤ k → j ≤ k → i ⊔ j ≤ k
  ⊔-least {i}{j}{k} p q with cmp i j
  ... | inj₁  _ = q
  ... | inj₂₁ _ = p
  ... | inj₂₂ _ = p

  ≤-prop : ∀ {i j}{p q : i ≤ j} → p ≡ q
  ≤-prop {p = inj₁ p}    {inj₁ q}    = inj₁ & <-prop
  ≤-prop {p = inj₁ p}    {inj₂ refl} = ⊥-elim (acyclic p)
  ≤-prop {p = inj₂ refl} {inj₁ q}    = ⊥-elim (acyclic q)
  ≤-prop {p = inj₂ p}    {inj₂ q}    = inj₂ & UIP

module IR-Univ-Ordinal {lvl} (ord : Ordinal lvl) where
  open Ordinal ord public
  open IR-Univ lvl public

  -- non-strict lifts
  ↑≤ : ∀ {i j} → i ≤ j → U i → U j
  ↑≤ (inj₁ p)    a = ↑ p a
  ↑≤ (inj₂ refl) a = a

  El↑≤ : ∀ {i j} p a → El (↑≤ {i}{j} p a) ≡ El a
  El↑≤ (inj₁ p)    a = El↑ p a
  El↑≤ (inj₂ refl) a = refl

  -- example: alternative type formation with _⊔_
  -- We might need this for models of TTs.
  Π'' : ∀ {i j}(a : U i) → (El a → U j) → U (i ⊔ j)
  Π'' {i}{j} a b = Π' (↑≤ (⊔₁ i j) a) λ x → ↑≤ (⊔₂ i j) (b (coe (El↑≤ (⊔₁ i j) a) x))


-- Examples
--------------------------------------------------------------------------------

-- finite levels
module ℕ-example where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Data.Nat.Induction

  lvl : WfSemiCat
  lvl = record {
      Lvl = ℕ
    ; _<_ = _<_
    ; _∘_ = λ p q → <-trans q p
    ; wf  = <-wellFounded _
    ; ass = <-irrelevant _ _
    }

  open IR-Univ lvl hiding (_<_)

  <suc : ∀ {i} → i < suc i
  <suc {i} = ≤-refl

  id' : ∀ {i} → El {suc i} (Π' (U' <suc) λ A → ↑U <suc A ⇒' ↑U <suc A)
  id' {i} A x = x

  const₀' : El {1} (Π' (U' <suc) λ A → Π' (U' <suc) λ B → ↑U <suc A ⇒' ↑U <suc B ⇒' ↑U <suc A)
  const₀' A B x y = x


-- ω*ω levels
module ℕ*ℕ-example where

  import Data.Nat as N
  open import Data.Nat.Properties
  open import Data.Nat.Induction
  open Lexicographic N._<_ (λ _ → N._<_)

  trs : ∀ {i j k} → j < k → i < j → i < k
  trs (left  p) (left  q) = left (<-trans q p)
  trs (left  p) (right q) = left p
  trs (right p) (left  q) = left q
  trs (right p) (right q) = right (<-trans q p)

  <-irr : ∀{x y}(a b : x < y) → a ≡ b
  <-irr (left  p) (left  q) = left & <-irrelevant _ _
  <-irr (left  p) (right q) = ⊥-elim (<-irrefl refl p)
  <-irr (right p) (left  q) = ⊥-elim (<-irrefl refl q)
  <-irr (right p) (right q) = right & <-irrelevant _ _

  --  representation: (i, j) ~ (ω*i + j)
  lvl : WfSemiCat
  lvl = record {
      Lvl = N.ℕ × N.ℕ
    ; _<_ = _<_
    ; _∘_ = trs
    ; wf  = wellFounded <-wellFounded <-wellFounded _
    ; ass = <-irr _ _
    }

  open IR-Univ lvl hiding (_<_)

  -- raise by 1
  <suc : ∀ {i j} → (i , j) < (i , N.suc j)
  <suc {i} = right ≤-refl

  -- raise to closest limit level
  <Suc : ∀ {i} j → (i , j) < (N.suc i , 0)
  <Suc {i} j = left ≤-refl

  ω : Lvl
  ω = 1 , 0

  #_ : N.ℕ → Lvl; infix 10 #_
  # n = 0 , n

  _+_ : Lvl → Lvl → Lvl; infix 6 _+_
  (i , j) + (i' , j') = i N.+ i' , j N.+ j'

  idω : El {ω} (Π' ℕ' λ i → Π' (U' (<Suc i)) λ A → ↑U (<Suc i) A ⇒' ↑U (<Suc i) A)
  idω i A x = x

  idω' : El {ω} (Π' Lvl' λ i → Π' (i <' ω) λ p → Π' (U' p) λ A → ↑U p A ⇒' ↑U p A)
  idω' i p A x = x

  fω+2 : El {ω + # 2} (U' (trs <suc <suc) ⇒' U' <suc)
  fω+2 = ↑U <suc
