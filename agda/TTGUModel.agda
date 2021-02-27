
{-
  Sketch of the IR model of TTGU, over an arbitrary level structure.
-}

open import IRUniverse
open import Lib
open import Data.Nat using (ℕ; zero; suc)

module TTGUModel (L : LvlStruct) where

  module IR = IR-Universe L
  open IR hiding (Lift; Lift∘)

  -- base category
  Con : Set₁
  Con = Set

  Sub : Con → Con → Set
  Sub Γ Δ = Γ → Δ

  idₛ : ∀ {Γ} → Sub Γ Γ
  idₛ γ = γ

  infixr 4 _∘ₛ_
  _∘ₛ_ : ∀ {Γ Δ ξ} → Sub Δ ξ → Sub Γ Δ → Sub Γ ξ
  σ ∘ₛ δ = λ γ → σ (δ γ)

  ∙ : Con
  ∙ = ⊤

  -- family diagram
  Ty : Con → Lvl → Set
  Ty Γ i = Γ → U i

  infixl 5 _[_]T
  _[_]T : ∀ {Γ Δ i} → Ty Δ i → Sub Γ Δ → Ty Γ i
  _[_]T A σ γ = A (σ γ)

  Tm : ∀ Γ {i} → Ty Γ i → Set
  Tm Γ A = (γ : Γ) → El (A γ)

  infixl 5 _[_]
  _[_] : ∀ {Γ Δ i A} → Tm Δ {i} A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
  _[_] t σ = λ γ → t (σ γ)

  infixl 3 _▶_
  _▶_ : ∀(Γ : Con){i} → Ty Γ i → Con
  Γ ▶ A = Σ Γ (λ γ → El (A γ))

  p : ∀ {Γ i}(A : Ty Γ i) → Sub (Γ ▶ A) Γ
  p A (γ , α) = γ

  q : ∀ {Γ i}(A : Ty Γ i) → Tm (Γ ▶ A) (A [ p A ]T)
  q A (γ , α) = α

  infixl 3 _,ₛ_
  _,ₛ_ : ∀ {Γ Δ}(σ : Sub Γ Δ){i A} → Tm Γ {i} (_[_]T {i = i} A σ) → Sub Γ (Δ ▶ A)
  _,ₛ_ σ t γ = (σ γ) , (t γ)

  Lift : ∀ {Γ i j} → i < j → Ty Γ i → Ty Γ j
  Lift p A γ = IR.Lift p (A γ)

  Lift∘ : ∀ {Γ i j k p q A} → Lift {Γ}{j}{k} p (Lift {Γ}{i}{j} q A) ≡ Lift (p ∘ q) A
  Lift∘ {p = p} {q} {A} = ext λ γ → IR.Lift∘ q p (A γ)

  lift[]T : ∀ {Γ Δ i j p σ A} → Lift {Δ}{i}{j} p A [ σ ]T ≡ Lift {Γ} p (A [ σ ]T)
  lift[]T = refl

  TmLift : ∀ {Γ i j p A} → Tm Γ A ≡ Tm Γ (Lift {Γ}{i}{j} p A)
  TmLift {p = p}{A} = (λ f → ∀ x → f x) & ext λ γ → ElLift p (A γ) ⁻¹

  ▶Lift : ∀ {Γ i j A}{p : i < j} → (Γ ▶ A) ≡ (Γ ▶ Lift p A)
  ▶Lift {Γ}{A = A}{p} = Σ Γ & ext λ γ → ElLift p (A γ) ⁻¹

  -- term lifting/lowering is definitionally the identity function in ETT
  -- also, since semantic term/type formers (with the exception of U) don't depend
  -- on levels, lifting/lowering preserves everything.
  lift : ∀ {Γ i j}(p : i < j){A : Ty Γ i} → Tm Γ A → Tm Γ (Lift p A)
  lift p {A} t = λ γ → coe (ElLift p (A γ) ⁻¹) (t γ)

  lower : ∀ {Γ i j}(p : i < j){A : Ty Γ i} → Tm Γ (Lift p A) → Tm Γ A
  lower p {A} t = λ γ → coe (ElLift p (A γ)) (t γ)

  -- universe
  Univ : ∀ {Γ i j} → i < j → Ty Γ j
  Univ p _ = U' p

  Univ[] : ∀ {Γ Δ σ i j p} → Univ {Δ}{i}{j} p [ σ ]T ≡ Univ {Γ}{i}{j} p
  Univ[] = refl

  RussellUniv : ∀ {Γ i j p} → Tm Γ (Univ {Γ}{i}{j} p) ≡ Ty Γ i
  RussellUniv = (λ f → ∀ x → f x) & ext λ _ → U<-compute

  -- some type formers
  Π : ∀ {Γ i}(A : Ty Γ i) → Ty (Γ ▶ A) i → Ty Γ i
  Π {Γ}{i} A B γ = Π' (A γ) λ α → B (γ , α)

  lam : ∀ {Γ i A B} → Tm (Γ ▶ A) B → Tm Γ {i} (Π A B)
  lam t γ α = t (γ , α)

  app : ∀ {Γ i A B} → Tm Γ {i} (Π A B) → Tm (Γ ▶ A) B
  app t (γ , α) = t γ α

  Nat : ∀ {Γ} i → Ty Γ i
  Nat i _ = ℕ' {i}

  LiftNat : ∀ {Γ i j p} → Lift {Γ}{i}{j} p (Nat i) ≡ Nat j
  LiftNat = refl

  Zero : ∀ {Γ i} → Tm Γ (Nat i)
  Zero _ = zero

  Suc : ∀ {Γ i} → Tm Γ (Nat i) → Tm Γ (Nat i)
  Suc t γ = suc (t γ)

  liftZero : ∀ {Γ i j p} → lift {Γ}{i}{j} p {Nat i} (Zero {Γ}{i}) ≡ (Zero {Γ}{j})
  liftZero = refl

  liftSuc : ∀ {Γ i j p t} → lift {Γ}{i}{j} p {Nat i} (Suc {Γ}{i} t) ≡ Suc {Γ}{j} (lift {Γ}{i}{j} p {Nat i} t)
  liftSuc = refl
