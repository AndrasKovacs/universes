
module IR where

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

  data UU {i}(l : ∀ j → j < i → Set) : Set
  EL : ∀ {i l} → UU {i} l → Set

  data UU {i} l where
    U'       : ∀ {j} → j < i → UU l
    ℕ'       : UU l
    Π' Σ' W' : (a : UU l) → (EL a → UU l) → UU l
    Id'      : (a : UU l) → EL a → EL a → UU l

    -- used for internal levels
    Lvl'  : UU l
    _<'_  : Lvl → Lvl → UU l

  EL {_}{l}(U' p) = l _ p
  EL ℕ'           = ℕ
  EL Lvl'         = Lvl
  EL (i <' j)     = i < j
  EL (Π' a b)     = ∀ x → EL (b x)
  EL (Σ' a b)     = ∃ λ x → EL (b x)
  EL (Id' a t u)  = t ≡ u
  EL (W' a b)     = W (EL a) (λ x → EL (b x))

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
  ↑   p (U' q)      = U' (p ∘ q)
  ↑   p ℕ'          = ℕ'
  ↑   p Lvl'        = Lvl'
  ↑   p (i <' j)    = i <' j
  ↑   p (Π' a b)    = Π' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  ↑   p (Σ' a b)    = Σ' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  ↑   p (W' a b)    = W' (↑ p a) λ x → ↑ p (b (coe (El↑ p a) x))
  ↑   p (Id' a t u) = Id' (↑ p a) (coe (El↑ p a ⁻¹) t) (coe (El↑ p a ⁻¹) u)
  El↑ p (U' q)   = U↓-compute {p = p ∘ q} ◾ U↓-compute {p = q} ⁻¹
  El↑ p ℕ'       = refl
  El↑ p Lvl'     = refl
  El↑ p (i <' j) = refl
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
    {!!}


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


  -- Example fragment of a model with generalized hierarchies
  --------------------------------------------------------------------------------

  module Model where
    Con : Set₁
    Con = Set

    Ty : Con → Lvl → Set
    Ty Γ j = Γ → U j

    Tm : ∀ Γ {i} → Ty Γ i → Set
    Tm Γ A = (γ : Γ) → El (A γ)

    Sub : Con → Con → Set
    Sub Γ Δ = Γ → Δ

    Lift : ∀ {Γ i j} → i < j → Ty Γ i → Ty Γ j
    Lift p A γ = ↑ p (A γ)

    infixl 5 _[_]T
    _[_]T : ∀ {Γ Δ i} → Ty Δ i → Sub Γ Δ → Ty Γ i
    _[_]T A σ γ = A (σ γ)

    lift[]T : ∀ {Γ Δ i j p σ A} → Lift {Δ}{i}{j} p A [ σ ]T ≡ Lift {Γ} p (A [ σ ]T)
    lift[]T = refl

    infixl 4 _▶_
    _▶_ : (Γ : Con) → ∀ {i} → Ty Γ i → Con
    Γ ▶ A = Σ Γ λ γ → El (A γ)

    Cumulative : ∀ {Γ i j p A} → Tm Γ A ≡ Tm Γ (Lift {Γ}{i}{j} p A)
    Cumulative {p = p}{A} = (λ f → ∀ x → f x) & ext λ γ → El↑ p (A γ) ⁻¹

    CumulativeCon : ∀ {Γ i j A}{p : i < j} → (Γ ▶ A) ≡ (Γ ▶ Lift p A)
    CumulativeCon {Γ}{A = A}{p} = Σ Γ & ext λ γ → El↑ p (A γ) ⁻¹

    lift : ∀ {Γ i j}(p : i < j){A : Ty Γ i} → Tm Γ A → Tm Γ (Lift p A)
    lift p {A} t = λ γ → coe (El↑ p (A γ) ⁻¹) (t γ)

    lower : ∀ {Γ i j}(p : i < j){A : Ty Γ i} → Tm Γ (Lift p A) → Tm Γ A
    lower p {A} t = λ γ → coe (El↑ p (A γ)) (t γ)
    -- term lifting/lowering is definitionally the identity function in ETT

    u : ∀ {Γ i j} → i < j → Ty Γ j
    u p _ = U' p

    u[] : ∀ {Γ Δ σ i j p} → u {Δ}{i}{j} p [ σ ]T ≡ u {Γ}{i}{j} p
    u[] = refl

    RussellU : ∀ {Γ i j p} → Tm Γ (u {Γ}{i}{j} p) ≡ Ty Γ i
    RussellU = (λ f → ∀ x → f x) & ext λ _ → U↓-compute

    Π : ∀ {Γ i}(A : Ty Γ i) → Ty (Γ ▶ A) i → Ty Γ i
    Π {Γ}{i} A B γ = Π' (A γ) λ α → B (γ , α)

    lam : ∀ {Γ i A B} → Tm (Γ ▶ A) B → Tm Γ {i} (Π A B)
    lam t γ α = t (γ , α)

    app : ∀ {Γ i A B} → Tm Γ {i} (Π A B) → Tm (Γ ▶ A) B
    app t (γ , α) = t γ α

    -- note: type/term constructors in the model don't depend on levels at all, so lifting always preserves them.
    Nat : ∀ {Γ} i → Ty Γ i
    Nat i _ = ℕ'

    LiftNat : ∀ {Γ i j p} → Lift {Γ}{i}{j} p (Nat i) ≡ Nat j
    LiftNat = refl

    Zero : ∀ {Γ i} → Tm Γ (Nat i)
    Zero _ = zero

    Suc : ∀ {Γ i} → Tm Γ (Nat i) → Tm Γ (Nat i)
    Suc t γ = suc (t γ)

    ↑Zero : ∀ {Γ i j p} → lift {Γ}{i}{j} p {Nat i} (Zero {Γ}{i}) ≡ (Zero {Γ}{j})
    ↑Zero = refl

    ↑Suc : ∀ {Γ i j p t} → lift {Γ}{i}{j} p {Nat i} (Suc {Γ}{i} t) ≡ Suc {Γ}{j} (lift {Γ}{i}{j} p {Nat i} t)
    ↑Suc = refl


  -- Model of TT with internalized levels (fragment)
  --------------------------------------------------------------------------------

  module InternalLevelTT (l₀ : Lvl) (l₁ : Lvl) (l₀₁ : l₀ < l₁) where

    -- Base CwF
    Con : Set₁
    Con = Set

    Sub : Con → Con → Set
    Sub Γ Δ = Γ → Δ

    Level : Con → Set
    Level Γ = Γ → Lvl

    Ty : (Γ : Con) → Level Γ → Set
    Ty Γ i = (γ : Γ) → U (i γ)

    Tm : (Γ : Con) → ∀ {i} → Ty Γ i → Set
    Tm Γ {i} A = (γ : Γ) → El (A γ)

    ∙ : Con
    ∙ = ⊤

    _▶_ : ∀(Γ : Con){i} → Ty Γ i → Con
    Γ ▶ A = Σ Γ (El F.∘ A)

    -- type formers
    --------------------------------------------------------------------------------

    Id : ∀ {Γ i} A → Tm Γ {i} A → Tm Γ A → Ty Γ i
    Id A t u γ = Id' (A γ) (t γ) (u γ)




    -- level structure
    --------------------------------------------------------------------------------
    LvlTy : ∀ {Γ i} → Ty Γ i
    LvlTy {Γ}{i} γ = Lvl'

    Lt : ∀ {Γ i} → Tm Γ {i} LvlTy → Tm Γ {i} LvlTy → Ty Γ i
    Lt i j γ = i γ <' j γ

    Compose : ∀ {Γ l i j k} → Tm Γ {l} (Lt j k) → Tm Γ {l} (Lt i j) → Tm Γ {l} (Lt i k)
    Compose t u γ = t γ ∘ u γ

    Lt-prop : ∀ {Γ i j k}(t u : Tm Γ {k} (Lt i j)) → Tm Γ {k} (Id (Lt i j) t u)
    Lt-prop t u γ = <-prop

    RussellLvl : ∀ {Γ i} → Tm Γ (LvlTy {Γ}{i}) ≡ Level Γ
    RussellLvl = refl

    Univ : ∀ {Γ i j} → Tm Γ {j} (Lt i j) → Ty Γ j
    Univ p γ = U' (p γ)

    RussellUniv : ∀ {Γ i j p} → Tm Γ (Univ {Γ}{i}{j} p) ≡ Ty Γ i
    RussellUniv = (λ f → ∀ x → f x) & ext λ γ → U↓-compute

    Lift : ∀ {Γ}{i j : Level Γ} → Tm Γ {j} (Lt i j) → Ty Γ i → Ty Γ j
    Lift {i = i}{j} p A γ = ↑ (p γ) (A γ)

    CumulativeTm : ∀ {Γ i j p A} → Tm Γ A ≡ Tm Γ (Lift {Γ}{i}{j} p A)
    CumulativeTm {Γ}{i}{j}{p}{A} = (λ f → ∀ x → f x) & ext λ γ → El↑ (p γ) (A γ) ⁻¹

    CumulativeCon : ∀ {Γ i j p A} → (Γ ▶ A) ≡ (Γ ▶ Lift {Γ}{i}{j} p A)
    CumulativeCon {Γ} {i} {j} {p} {A} = Σ Γ & ext λ γ → El↑ (p γ) (A γ) ⁻¹





-- Additional assumption: levels bounded by ordinals
--------------------------------------------------------------------------------

pattern inj₂₁ x  = inj₂ (inj₁ x)
pattern inj₂₂ x  = inj₂ (inj₂ x)

-- Corresponds to type-theoretic ordinal in HoTT book 10.4
record Ordinal (lvl : LvlStruct) : Set where
  open LvlStruct lvl
  field
    cmp    : ∀ i j → i < j ⊎ j < i ⊎ i ≡ j
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
