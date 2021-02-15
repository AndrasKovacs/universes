
module InternalLevelModel2 where

open import Lib
open import IRUniv
open import Data.Nat using (ℕ; zero; suc)

ℕ-elim : ∀ {α}(P : ℕ → Set α) → P zero → (∀ {n} → P n → P (suc n)) → ∀ n → P n
ℕ-elim P z s zero    = z
ℕ-elim P z s (suc n) = s (ℕ-elim P z s n)

infix 3 _<*_
_<*_ : ℕ → ℕ → Set
_<*_ a b = ℕ-elim _ ⊥ (λ {b} hyp → (a ≡ b) ⊎ hyp) b

<*-pred : ∀ i j → suc i <* suc j → i <* j
<*-pred i .(suc i) (inj₁ refl) = inj₁ refl
<*-pred i (suc j) (inj₂ p) = inj₂ (<*-pred i j p)

<*-irrefl : ∀ i → i <* i → ⊥
<*-irrefl (suc i) p = <*-irrefl i (<*-pred _ _ p)

lem : ∀ i j → i <* j → i ≢ j
lem i (suc .i) (inj₁ refl) ()
lem .(suc j) (suc j) (inj₂ p) refl = <*-irrefl (suc j) (inj₂ p)

<-prop* : ∀ i j (p q : i <* j) → p ≡ q
<-prop* i (suc j) (inj₁ p) (inj₁ q) = inj₁ & UIP
<-prop* i (suc j) (inj₁ p) (inj₂ q) = ⊥-elim (lem _ _ q p)
<-prop* i (suc j) (inj₂ p) (inj₁ q) = ⊥-elim (lem _ _ p q)
<-prop* i (suc j) (inj₂ p) (inj₂ q) = inj₂ & <-prop* i j p q

<*-comp : {i j k : ℕ} → j <* k → i <* j → i <* k
<*-comp {i} {.k} {suc k} (inj₁ refl) q = inj₂ q
<*-comp {i} {j} {suc k} (inj₂ p) q = inj₂ (<*-comp {i}{j}{k} p q)

postulate
  <*-wf : {i : ℕ} → Acc _<*_ i

L : LvlStruct
L = record {
  Lvl    = ℕ ;
  _<_    = _<*_ ;
  <-prop = λ {i}{j}{p}{q} → <-prop* i j p q;
  _∘_    = λ {i}{j}{k} → <*-comp {i}{j}{k};
  wf     = <*-wf }

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

Nat : ∀ {Γ i} → Ty Γ i
Nat γ = ℕ'

-- levels & lifts
--------------------------------------------------------------------------------

LvlTy : ∀ {Γ i} → Ty Γ i
LvlTy {Γ}{i} γ = Lvl'

RussellLvl : ∀ {Γ i} → Tm Γ (LvlTy {Γ}{i}) ≡ Level Γ
RussellLvl = refl

Lt : ∀ {Γ i} → Tm Γ {i} LvlTy → Tm Γ {i} LvlTy → Ty Γ i
Lt i j γ = i γ <' j γ

Lift : ∀ {Γ}{i j : Level Γ} → Tm Γ {j} (Lt i j) → Ty Γ i → Ty Γ j
Lift {i = i}{j} p A γ = ↑ (p γ) (A γ)

-- + (↑, ↓), preserves all term formers
-- + (↑t = t)

Compose : ∀ {Γ l i j k} → Tm Γ {l} (Lt j k) → Tm Γ {l} (Lt i j) → Tm Γ {l} (Lt i k)
Compose {Γ}{l}{i}{j}{k} t u γ = _∘_ {i γ}{j γ}{k γ} (t γ) (u γ)

Lt-prop : ∀ {Γ i j k}(t u : Tm Γ {k} (Lt i j)) → Tm Γ {k} (Id (Lt i j) t u)
Lt-prop {Γ} {i} {j} {k} t u γ = <-prop {i γ}{j γ} {t γ} {u γ}

L₀ : ∀ {Γ} → Level Γ
L₀ _ = 0  -- +[]

L₁ : ∀ {Γ} → Level Γ
L₁ _ = 1  -- +[]


-- univ/lift
--------------------------------------------------------------------------------


Univ : ∀ {Γ i j} → Tm Γ {j} (Lt i j) → Ty Γ j
Univ p γ = U' (p γ)

RussellUniv : ∀ {Γ i j p} → Tm Γ (Univ {Γ}{i}{j} p) ≡ Ty Γ i
RussellUniv {Γ}{i}{j} = (λ f → ∀ x → f x) & ext λ γ → U↓-compute

CumulativeTm : ∀ {Γ i j p A} → Tm Γ A ≡ Tm Γ (Lift {Γ}{i}{j} p A)
CumulativeTm {Γ}{i}{j}{p}{A} = (λ f → ∀ x → f x) & ext λ γ → El↑ (p γ) (A γ) ⁻¹

CumulativeCon : ∀ {Γ i j p A} → (Γ ▶ A) ≡ (Γ ▶ Lift {Γ}{i}{j} p A)
CumulativeCon {Γ} {i} {j} {p} {A} = Σ Γ & ext λ γ → El↑ (p γ) (A γ) ⁻¹

-- Nat level reflection
--------------------------------------------------------------------------------

natLvl : ∀ {Γ i} → Tm Γ {i} LvlTy ≡ Tm Γ {L₀ {Γ}} Nat
natLvl = {!!}
