
module InternalLevelModel where

open import Lib
open import IRUniv

module _ (L : LvlStruct)(l₀ : _)(l₁ : _) (l₀₁ : L .LvlStruct._<_ l₀ l₁) where

  open IR-Univ L

  -- Base CwF
  --------------------------------------------------------------------------------

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

  -- univ/lift
  --------------------------------------------------------------------------------

  RussellLvl : ∀ {Γ i} → Tm Γ (LvlTy {Γ}{i}) ≡ Level Γ
  RussellLvl = refl

  Univ : ∀ {Γ i j} → Tm Γ {j} (Lt i j) → Ty Γ j
  Univ p γ = U' (p γ)

  RussellUniv : ∀ {Γ i j p} → Tm Γ (Univ {Γ}{i}{j} p) ≡ Ty Γ i
  RussellUniv = (λ f → ∀ x → f x) & ext λ γ → U↓-compute

  Lift : ∀ {Γ}{i j : Level Γ} → Tm Γ {j} (Lt i j) → Ty Γ i → Ty Γ j
  Lift {i = i}{j} p A γ = ↑ (p γ) (A γ)

  LiftU : ∀ {Γ i j k p q} → Lift {Γ}{j}{k} q (Univ {Γ} {i}{j} p) ≡ Univ {Γ}{i}{k} (Compose {Γ} {k}{i}{j} q p)
  LiftU = refl

  CumulativeTm : ∀ {Γ i j p A} → Tm Γ A ≡ Tm Γ (Lift {Γ}{i}{j} p A)
  CumulativeTm {Γ}{i}{j}{p}{A} = (λ f → ∀ x → f x) & ext λ γ → El↑ (p γ) (A γ) ⁻¹

  CumulativeCon : ∀ {Γ i j p A} → (Γ ▶ A) ≡ (Γ ▶ Lift {Γ}{i}{j} p A)
  CumulativeCon {Γ} {i} {j} {p} {A} = Σ Γ & ext λ γ → El↑ (p γ) (A γ) ⁻¹
