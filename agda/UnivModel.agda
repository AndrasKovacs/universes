
open import IRUniv
open import Lib
open import Data.Nat using (ℕ; zero; suc)

module UnivModel (L : LvlStruct) where

  open IR-Univ L

  Con : Set₁
  Con = Set

  Ty : Con → Lvl → Set
  Ty Γ i = Γ → U i

  Tm : ∀ Γ {i} → Ty Γ i → Set
  Tm Γ A = (γ : Γ) → El (A γ)

  Sub : Con → Con → Set
  Sub Γ Δ = Γ → Δ

  infixl 5 _[_]T
  _[_]T : ∀ {Γ Δ i} → Ty Δ i → Sub Γ Δ → Ty Γ i
  _[_]T A σ γ = A (σ γ)

  infixl 5 _[_]
  _[_] : ∀ {Γ Δ i A} → Tm Δ {i} A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
  _[_] t σ = λ γ → t (σ γ)

  ∙ : Con
  ∙ = ⊤

  infixl 4 _▶_
  _▶_ : (Γ : Con) → ∀ {i} → Ty Γ i → Con
  Γ ▶ A = Σ Γ λ γ → El (A γ)

  Lift : ∀ {Γ i j} → i < j → Ty Γ i → Ty Γ j
  Lift p A γ = ↑ p (A γ)

  Lift∘ : ∀ {Γ i j k p q A} → Lift {Γ}{j}{k} p (Lift {Γ}{i}{j} q A) ≡ Lift (p ∘ q) A
  Lift∘ {p = p} {q} {A} = ext λ γ → ↑∘ q p (A γ)

  lift[]T : ∀ {Γ Δ i j p σ A} → Lift {Δ}{i}{j} p A [ σ ]T ≡ Lift {Γ} p (A [ σ ]T)
  lift[]T = refl

  CumulativeTm : ∀ {Γ i j p A} → Tm Γ A ≡ Tm Γ (Lift {Γ}{i}{j} p A)
  CumulativeTm {p = p}{A} = (λ f → ∀ x → f x) & ext λ γ → El↑ p (A γ) ⁻¹

  CumulativeCon : ∀ {Γ i j A}{p : i < j} → (Γ ▶ A) ≡ (Γ ▶ Lift p A)
  CumulativeCon {Γ}{A = A}{p} = Σ Γ & ext λ γ → El↑ p (A γ) ⁻¹

  -- term lifting/lowering is definitionally the identity function in ETT
  -- also, since semantic term/type formers (with the exception of U) don't depend
  -- on levels, lifting/lowering preserves everything.

  lift : ∀ {Γ i j}(p : i < j){A : Ty Γ i} → Tm Γ A → Tm Γ (Lift p A)
  lift p {A} t = λ γ → coe (El↑ p (A γ) ⁻¹) (t γ)

  lower : ∀ {Γ i j}(p : i < j){A : Ty Γ i} → Tm Γ (Lift p A) → Tm Γ A
  lower p {A} t = λ γ → coe (El↑ p (A γ)) (t γ)

  -- lift[] : ∀ {Γ Δ i j A}{p : i < j}{t : Tm Δ {i} A}{σ : Sub Γ Δ} → (lift p t) [ σ ] ≡ lift p (t [ σ ])
  --     t ∘ σ = t ∘ σ

  -- universe
  Univ : ∀ {Γ i j} → i < j → Ty Γ j
  Univ p _ = U' p

  Univ[] : ∀ {Γ Δ σ i j p} → Univ {Δ}{i}{j} p [ σ ]T ≡ Univ {Γ}{i}{j} p
  Univ[] = refl

  RussellUniv : ∀ {Γ i j p} → Tm Γ (Univ {Γ}{i}{j} p) ≡ Ty Γ i
  RussellUniv = (λ f → ∀ x → f x) & ext λ _ → U↓-compute

  Π : ∀ {Γ i}(A : Ty Γ i) → Ty (Γ ▶ A) i → Ty Γ i
  Π {Γ}{i} A B γ = Π' (A γ) λ α → B (γ , α)

  lam : ∀ {Γ i A B} → Tm (Γ ▶ A) B → Tm Γ {i} (Π A B)
  lam t γ α = t (γ , α)

  app : ∀ {Γ i A B} → Tm Γ {i} (Π A B) → Tm (Γ ▶ A) B
  app t (γ , α) = t γ α

  -- liftapp : lift (lam {Γ} {A} {B} t) = lam {Γ}{Lift p A}{Lift p B}{lift p t}
   -- already making use of CumulativeCon in Lift p B above
   -- λ γ α. t (γ, α) = λ γ α. t (γ, α)   OK


  -- note: type/term constructors in the model don't depend on levels at all, so lifting always preserves them.
  Nat : ∀ {Γ} i → Ty Γ i
  Nat i _ = ℕ' {i}


  --  (El, c) is not natural wrt lifting!
  --  term lifting is a different semantic operation than type lifting.
  --  For example, ↑Nat₀ = Nat₀, Lift Nat₀ = Nat₁
  --  term lifting does nothing, type lifting shifts levels

  -- Nat₀  : Tm Γ (U 0 1)
  -- ↑Nat₀ : Tm Γ (Lift (U 0 1))
  --       : Tm Γ (U 0 1)
  -- Nat₀ = ↑Nat₀

  -- Nat₀      : Ty Γ 0
  -- Lift Nat₀ : Ty Γ 1
  --     Ty Γ 0 ≠ Ty Γ 1
  cNat : ∀ {Γ} i j p → Tm Γ (Univ {Γ}{i}{j} p)
  cNat {Γ} i j p = coe (RussellUniv ⁻¹) (Nat {Γ} i)

  -- lem : ∀ {Γ i j}{p : i < j} → Nat {Γ} i ≡ coe {!!} (Nat {Γ} j)
  -- lem = {!!}

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
