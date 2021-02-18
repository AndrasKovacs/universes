

module IRUniv where

open import Lib

-- set with well-founded transitive relation
record LvlStruct : Set₁ where
  infix 4 _<_
  infixr 5 _∘_
  field
    Lvl         : Set
    _<_         : Lvl → Lvl → Set
    <-prop      : ∀ {i j}{p q : i < j} → p ≡ q
    _∘_         : ∀ {i j k} → j < k → i < j → i < k
    instance wf : ∀ {i} → Acc _<_ i

  acyclic : ∀ {i} → i < i → ⊥
  acyclic {i} p = go wf p where
    go : ∀ {i} → Acc _<_ i → i < i → ⊥
    go {i} (acc f) q = go (f i q) q


module IR-Univ (lvl : LvlStruct) where
  open LvlStruct lvl public
  open import Data.Nat hiding (_<_; _≤_)

  infix 4 _<'_
  infixr 1 _⊎'_

  data UU {i}(l : ∀ j → j < i → Set) : Set
  EL : ∀ {i l} → UU {i} l → Set

  data UU {i} l where
    U'       : ∀ {j} → j < i → UU l
    ℕ' ⊤' ⊥' : UU l
    _⊎'_     : UU l → UU l → UU l
    Id'      : (a : UU l) → EL a → EL a → UU l
    Π' Σ' W' : (a : UU l) → (EL a → UU l) → UU l

    -- used for internal levels
    Lvl'  : UU l
    _<'_  : Lvl → Lvl → UU l

  EL {_}{l}(U' p) = l _ p
  EL ℕ'           = ℕ
  EL ⊤'           = ⊤
  EL ⊥'           = ⊥
  EL Lvl'         = Lvl
  EL (i <' j)     = i < j
  EL (a ⊎' b)     = EL a ⊎ EL b
  EL (Π' a b)     = ∀ x → EL (b x)
  EL (Σ' a b)     = ∃ λ x → EL (b x)
  EL (Id' a t u)  = t ≡ u
  EL (W' a b)     = W (EL a) (λ x → EL (b x))

  -- Interpreting levels & lifts
  --------------------------------------------------------------------------------

  U↓ : ∀ {i} {{_ : Acc _<_ i}} j → j < i → Set
  U↓ {i} {{acc f}} j p = UU {j} (U↓ {j}{{f j p}})

  U : Lvl → Set
  U i = UU {i} (U↓ {i} {{wf}})

  El : ∀ {i} → U i → Set
  El {i} = EL {i}{U↓ {i}{{wf}}}

  U↓-compute : ∀ {i a j p} → U↓ {i}{{a}} j p ≡ U j
  U↓-compute {i} {acc f} {j} {p} = (λ a → UU (U↓ {{a}})) & Acc-prop (f j p) wf

  ↑   : ∀ {i j} → i < j → U i → U j
  El↑ : ∀ {i j} p a → El (↑ {i}{j} p a) ≡ El a
  ↑   p (U' q)      = U' (p ∘ q)
  ↑   p ℕ'          = ℕ'
  ↑   p ⊤'          = ⊤'
  ↑   p ⊥'          = ⊥'
  ↑   p Lvl'        = Lvl'
  ↑   p (i <' j)    = i <' j
  ↑   p (a ⊎' b)    = ↑ p a ⊎' ↑ p b
  ↑   p (Π' a b)    = Π' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  ↑   p (Σ' a b)    = Σ' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  ↑   p (W' a b)    = W' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  ↑   p (Id' a t u) = Id' (↑ p a) (coe (El↑ p a ⁻¹) t) (coe (El↑ p a ⁻¹) u)
  El↑ {i}{j} p (U' {k} q) = U↓-compute {p = p ∘ q} ◾ U↓-compute {p = q} ⁻¹
  El↑ p ℕ'       = refl
  El↑ p ⊤'       = refl
  El↑ p ⊥'       = refl
  El↑ p Lvl'     = refl
  El↑ p (i <' j) = refl
  El↑ p (a ⊎' b) = _⊎_ & El↑ p a ⊗ El↑ p b
  El↑ p (Π' a b) rewrite El↑ p a = (λ f → ∀ x → f x) & ext (El↑ p F.∘ b)
  El↑ p (Σ' a b) rewrite El↑ p a = Σ _ & ext (El↑ p F.∘ b)
  El↑ p (W' a b) rewrite El↑ p a = W _ & ext (El↑ p F.∘ b)
  El↑ p (Id' a t u) rewrite El↑ p a = refl

  -- congruence helper (TODO: cleanup, change to ap2, ap3 etc)
  ΠΣ≡ : ∀ {i}{l : ∀ j → j < i → Set}
          (F' : (a : UU l) → (EL a → UU l) → UU l)
          {a₀ a₁ : UU l}(a₂ : a₀ ≡ a₁)
          {b₀ : EL a₀ → UU l}{b₁ : EL a₁ → UU l}
        → (∀ x → b₀ x ≡ b₁ (coe (EL & a₂) x))
        → F' a₀ b₀ ≡ F' a₁ b₁
  ΠΣ≡ {i} {l} F' {a₀} refl {b₀} {b₁} b₂ = F' a₀ & ext b₂

  -- functorial lifting
  ↑∘ : ∀ {i j k}(p : i < j)(q : j < k) a → ↑ q (↑ p a) ≡ ↑ (q ∘ p) a
  ↑∘ p q (U' r)   = U' & <-prop
  ↑∘ p q ℕ'       = refl
  ↑∘ p q ⊤'       = refl
  ↑∘ p q ⊥'       = refl
  ↑∘ p q Lvl'     = refl
  ↑∘ p q (i <' j) = refl
  ↑∘ p q (a ⊎' b) = _⊎'_ & ↑∘ p q a ⊗ ↑∘ p q b
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
  ↑∘ p q (W' a b) =
    ΠΣ≡ W' (↑∘ p q a)
        (λ x → ↑∘ p q _
             ◾ (λ x → ↑ (q ∘ p) (b x)) &
                  (coe∘ (El↑ p a) (El↑ q (↑ p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (El↑ (q ∘ p) a) (EL & ↑∘ p q a) x ⁻¹))
  ↑∘ p q (Id' a t u) rewrite
      coe∘ (El↑ q (↑ p a) ⁻¹) (El↑ p a ⁻¹) t
    | coe∘ (El↑ q (↑ p a) ⁻¹) (El↑ p a ⁻¹) u =
    TODO where postulate TODO : _

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



-- Additional assumption: levels bounded by ordinals.
-- Corresponds to type-theoretic ordinal in HoTT book section 10.4
record Ordinal (lvl : LvlStruct) : Set where
  open LvlStruct lvl
  field
    cmp    : ∀ i j → i < j ⊎ j < i ⊎ i ≡ j
    <-ext  : ∀ {i j} → (∀ k → (k < i → k < j) × (k < j → k < i)) → i ≡ j

  private
    pattern inj₂₁ x = inj₂ (inj₁ x)
    pattern inj₂₂ x = inj₂ (inj₂ x)

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

  -- alternative type formation with _⊔_
  Π'' : ∀ {i j}(a : U i) → (El a → U j) → U (i ⊔ j)
  Π'' {i}{j} a b = Π' (↑≤ (⊔₁ i j) a) λ x → ↑≤ (⊔₂ i j) (b (coe (El↑≤ (⊔₁ i j) a) x))


-- Examples
--------------------------------------------------------------------------------

-- finite levels
module ℕ-example where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Data.Nat.Induction

  lvl : LvlStruct
  lvl = record {
      Lvl = ℕ
    ; _<_ = _<_
    ; <-prop = <-irrelevant _ _
    ; _∘_ = λ p q → <-trans q p
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
  lvl : LvlStruct
  lvl = record {
      Lvl = N.ℕ × N.ℕ
    ; _<_ = _<_
    ; <-prop = <-irr _ _
    ; _∘_ = trs
    ; wf  = wellFounded <-wellFounded <-wellFounded _
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
