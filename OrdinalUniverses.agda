
{-
Inductive-recursive universes, indexed by levels which are below an arbitrary type-theoretic ordinal number (see HoTT book 10.3). This includes all kinds of transfinite levels as well.

Checked with: Agda 2.6.0.1, stdlib 1.0

My original motivation was to give inductive-recursive (or equivalently: large inductive)
semantics to to Jon Sterling's cumulative algebraic TT paper:

  https://arxiv.org/abs/1902.08848

This requires cumulativity (obviously), Russell universes and tranfinite universes because
the standard model for Jon's TT requires Setω for the interpretation of contexts.

Prior art that I know about:
  - Conor:
      https://personal.cis.strath.ac.uk/conor.mcbride/pub/Hmm/Hier.agda
  - Larry Diehl:
      gist:   https://gist.github.com/larrytheliquid/3909860
      thesis: https://pdfs.semanticscholar.org/fc9a/5a2a904a7dff3562bcf31275d4b029894b5f.pdf
              section 8.1.3

However, these don't support Russell and transfinite universes.

-}


-- Preliminaries
--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Sum
open import Function
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

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

--------------------------------------------------------------------------------

-- We demand that a type of levels has a well-founded transitive relation.
-- This is the same as the definition of an ordinal in HoTT book 10.3, except
-- that we don't require extensionality, and don't yet require <-irrelevance.

record LevelStructure : Set₁ where
  infix 4 _<_
  field
    Lvl         : Set
    _<_         : Lvl → Lvl → Set
    trs         : ∀ {i j k} → i < j → j < k → i < k
    instance wf : ∀ {i} → Acc _<_ i

  <-irrefl : ∀ {i} → i < i → ⊥
  <-irrefl {i} p = go wf p where
    go : ∀ {i} → Acc _<_ i → i < i → ⊥
    go {i} (acc f) q = go (f i q) q


-- Given any level structure, we have a cumulative IR universe hierarchy.

module IR-Univ (lvl : LevelStructure) where
  open LevelStructure lvl public
  open import Data.Nat hiding (_<_; _≤_)

  -- The actual IR type of codes. We already assume semantics for the "i" level
  -- when we define UU, in order to avoid positivity issues.
  --------------------------------------------------------------------------------

  infix 4 _<'_

  data UU {i}(l : ∀ j → j < i → Set) : Set
  EL : ∀ {i l} → UU {i} l → Set

  data UU {i} l where
    U'    : ∀ {j} → j < i → UU l   -- cumulativity appears here first, but
                                   -- it will be extended to other types as well
    ℕ'    : UU l

    -- We make it possible to write bounded level-polymorphic functions,
    -- by internalizing Lvl and _<_ in codes.
    Lvl'  : UU l
    _<'_  : Lvl → Lvl → UU l

    Π' Σ' : (a : UU l) → (EL a → UU l) → UU l

  EL {_}{l}(U' p) = l _ p  -- we just refer to the semantics of levels
  EL ℕ'           = ℕ
  EL Lvl'         = Lvl
  EL (i <' j)     = i < j
  EL (Π' a b)     = ∀ x → EL (b x)
  EL (Σ' a b)     = ∃ λ x → EL (b x)

  -- Interpreting levels
  --------------------------------------------------------------------------------

  -- U↓ i assigns a set to every j below i.

  -- We would like the defining equation as follows:
  --    U↓ : ∀ i j → i < j → Set
  --    U↓ {i} j p = UU (U↓ {j})

  -- However, this is not a well-founded definition, so we instead define U↓ by
  -- recursion on _<_ accessibility.

  U↓ : ∀ {i} {{_ : Acc _<_ i}} j → j < i → Set
  U↓ {i} {{acc f}} j p = UU (U↓ {{f j p}})

  U : Lvl → Set
  U i = UU (U↓ {i})

  El : ∀ {i} → U i → Set
  El = EL

  U↓-compute : ∀ {i a j p} → U↓ {i}{{a}} j p ≡ U j
  U↓-compute {i} {acc f} {j} {p} = (λ a → UU (U↓ {{a}})) & Acc-prop (f j p) wf


  -- Cumulativity
  --------------------------------------------------------------------------------

  -- cumulativity means that
  --   a) every type can be lifted to higher levels
  --   b) lifting doesn't change sets of elements of types

  ↑   : ∀ {i j} → i < j → U i → U j
  El↑ : ∀ {i j} p a → El (↑ {i}{j} p a) ≡ El a
  ↑   p (U' q)   = U' (trs q p)
  ↑   p ℕ'       = ℕ'
  ↑   p Lvl'     = Lvl'
  ↑   p (i <' j) = i <' j
  ↑   p (Π' a b) = Π' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  ↑   p (Σ' a b) = Σ' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  El↑ p (U' q)   = U↓-compute ◾ U↓-compute ⁻¹
  El↑ p ℕ'       = refl
  El↑ p Lvl'     = refl
  El↑ p (i <' j) = refl
  El↑ p (Π' a b) rewrite El↑ p a = (λ f → ∀ x → f x) & ext (El↑ p ∘ b)
  El↑ p (Σ' a b) rewrite El↑ p a = ∃ & ext (El↑ p ∘ b)

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


  -- Example for supporting cumulative Russell universes in TT
  --------------------------------------------------------------------------------
  private
    Con : Lvl → Set
    Con = U
    -- Jon Sterling has instead Con : Set, and his contexts are interpreted as U Top
    -- where Top is a chosen level such that every syntactic level is
    -- interpreted below it. The reason for this is that we'd like to just ignore
    -- context levels and lifts in the syntax of our TT.

    Ty : ∀ {i} → Con i → Lvl → Set
    Ty Γ j = El Γ → U j

    Tm : ∀ {i} Γ {j} → Ty {i} Γ j → Set
    Tm Γ A = (γ : El Γ) → El (A γ)

    ↑Ty : ∀ {j k i Γ} → j < k → Ty {i} Γ j → Ty Γ k
    ↑Ty p A γ = ↑ p (A γ)

    Cumulative : ∀ {i Γ j k p A} → Tm Γ A ≡ Tm Γ (↑Ty {j}{k}{i}{Γ} p A)
    Cumulative {p = p}{A} = (λ f → ∀ x → f x) & ext λ γ → El↑ p (A γ) ⁻¹

    u : ∀ {i Γ j k} → j < k → Ty {i} Γ k
    u p _ = U' p

    Russell : ∀ {i Γ j k p} → Tm Γ (u {i}{Γ}{j}{k} p) ≡ Ty Γ j
    Russell = (λ f → ∀ x → f x) & ext λ γ → U↓-compute


-- Additional assumption:
-- proof-irrelevant, strict total ordering for levels.
-- This is a realistic assumption for notions of TT models and for type checking.
--------------------------------------------------------------------------------

pattern inj₂₁ x  = inj₂ (inj₁ x)
pattern inj₂₂ x  = inj₂ (inj₂ x)


-- Corresponds to classical ordinal in HoTT book 10.4 without extensionality
record StrictTotalLevel (lvl : LevelStructure) : Set where
  open LevelStructure lvl
  field
    cmp    : ∀ i j → i < j ⊎ j < i ⊎ i ≡ j
    <-prop : ∀ {i j}{p q : i < j} → p ≡ q

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
  ≤-prop {p = inj₁ p}    {inj₂ refl} = ⊥-elim (<-irrefl p)
  ≤-prop {p = inj₂ refl} {inj₁ q}    = ⊥-elim (<-irrefl q)
  ≤-prop {p = inj₂ p}    {inj₂ q}    = inj₂ & UIP

module IR-Univ-StrictTotal {lvl} (strictTotal : StrictTotalLevel lvl) where
  open StrictTotalLevel strictTotal public
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

  -- congruence helper
  ΠΣ≡ : ∀ {i}{l : ∀ j → j < i → Set}
          (F' : (a : UU l) → (EL a → UU l) → UU l)
          {a₀ a₁ : UU l}(a₂ : a₀ ≡ a₁)
          {b₀ : EL a₀ → UU l}{b₁ : EL a₁ → UU l}
        → (∀ x → b₀ x ≡ b₁ (coe (EL & a₂) x))
        → F' a₀ b₀ ≡ F' a₁ b₁
  ΠΣ≡ {i} {l} F' {a₀} refl {b₀} {b₁} b₂ = F' a₀ & ext b₂

  -- Composing lifts. Jon Sterling also requires this equation.
  ↑↑ : ∀ {i j k}(p : i < j)(q : j < k) a → ↑ q (↑ p a) ≡ ↑ (trs p q) a
  ↑↑ p q (U' r)   = U' & <-prop -- alternative: require associative trs
  ↑↑ p q ℕ'       = refl
  ↑↑ p q Lvl'     = refl
  ↑↑ p q (i <' j) = refl
  ↑↑ p q (Π' a b) =
    ΠΣ≡ Π' (↑↑ p q a)
        (λ x → ↑↑ p q _
             ◾ (λ x → ↑ (trs p q) (b x)) &
                  (coe∘ (El↑ p a) (El↑ q (↑ p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (El↑ (trs p q) a) (EL & ↑↑ p q a) x ⁻¹))
  ↑↑ p q (Σ' a b) =
    ΠΣ≡ Σ' (↑↑ p q a)
        (λ x → ↑↑ p q _
             ◾ (λ x → ↑ (trs p q) (b x)) &
                  (coe∘ (El↑ p a) (El↑ q (↑ p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (El↑ (trs p q) a) (EL & ↑↑ p q a) x ⁻¹))


-- Examples
--------------------------------------------------------------------------------

-- finite levels
module ℕ-example where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Induction.Nat

  lvl : LevelStructure
  lvl = record {
      Lvl = ℕ
    ; _<_ = _<_
    ; trs = <-trans
    ; wf  = <-wellFounded _
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
  open import Induction.Nat
  open Lexicographic N._<_ (λ _ → N._<_)

  trs : ∀ {i j k} → i < j → j < k → i < k
  trs (left  p) (left  q) = left (<-trans p q)
  trs (left  p) (right q) = left p
  trs (right p) (left  q) = left q
  trs (right p) (right q) = right (<-trans p q)

  --  representation: (i, j) ~ (ω*i + j)
  lvl : LevelStructure
  lvl = record {
      Lvl = N.ℕ × N.ℕ
    ; _<_ = _<_
    ; trs = trs
    ; wf  = wellFounded <-wellFounded <-wellFounded _
    }

  open IR-Univ lvl hiding (_<_; trs)

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


-- W-types as levels.
-- It's clear that pretty much any inductive type has LvlStructure, although many of
-- them don't have StrictTotal structure.
module W-example (Sh : Set)(Pos : Sh → Set) where

  data W : Set where
    sup : ∀ s → (Pos s → W) → W

  infix 4 _<_
  data _<_ : W → W → Set where
    here  : ∀ {s f s*}   → f s* < sup s f
    there : ∀ {x s f s*} → x < f s* → x < sup s f

  trs : ∀ {i j k} → i < j → j < k → i < k
  trs p here      = there p
  trs p (there q) = there (trs p q)

  wf : ∀ w → Acc _<_ w
  wf (sup s f) = acc λ {_ here → wf _; y (there p) → unAcc (wf _) y p}

  lvl : LevelStructure
  lvl = record { Lvl = W ; _<_ = _<_ ; trs = trs ; wf = wf _ }
