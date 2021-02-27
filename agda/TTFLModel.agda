
module TTFLModel where

{-
This file contains a sketch model of the TTFL model when we have ω levels, and
levels are strictly identified with internal natural numbers.
-}

open import Lib
open import IRUniverse
open import Data.Nat using (ℕ; zero; suc)

-- First, we construct a concrete level structure with Lvl = ℕ
--------------------------------------------------------------------------------

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

-- instantiate IR universe with ℕ
module IR = IR-Universe L
open IR hiding (Lvl'; _<'_; Lift; Lift∘)

-- Model of TTFL
--------------------------------------------------------------------------------


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

-- level structure
Level : Con → Set
Level Γ = Γ → Lvl

Lt : ∀ {Γ} → Level Γ → Level Γ → Set
Lt {Γ} i j = (γ : Γ) → i γ < j γ

infixl 5 _[_]L
_[_]L : ∀ {Γ Δ} → Level Δ → Sub Γ Δ → Level Γ
_[_]L σ i γ = σ (i γ)

infixr 4 _∘<_
_∘<_ : ∀ {Γ i j k} → Lt {Γ} j k → Lt i j → Lt i k
_∘<_ {Γ}{i}{j}{k} p q γ = _∘_ {i γ} {j γ}{k γ} (p γ) (q γ)

infixl 5 _[_]<
_[_]< : ∀ {Γ Δ i j} → Lt i j → (σ : Sub Γ Δ) → Lt (i [ σ ]L) (j [ σ ]L)
_[_]< p σ γ = p (σ γ)

<prop : ∀ {Γ i j}{p q : Lt {Γ} i j} → p ≡ q
<prop {Γ} {i} {j} {p} {q} = ext λ γ → <-prop {i γ}{j γ}{p γ}{q γ}


-- bootstrapping assumption
L0 : ∀ {Γ} → Level Γ
L0 γ = 0

L1 : ∀ {Γ} → Level Γ
L1 γ = 1

L01 : ∀ {Γ} → Lt (L0 {Γ}) (L1 {Γ})
L01 γ = inj₁ refl

-- family structure
Ty : (Γ : Con) → Level Γ → Set
Ty Γ i = (γ : Γ) → U (i γ)

infixl 5 _[_]T
_[_]T : ∀ {Γ Δ i} → Ty Δ i → (σ : Sub Γ Δ) → Ty Γ (i [ σ ]L)
_[_]T A σ γ = A (σ γ)

Tm : (Γ : Con) → ∀ {i} → Ty Γ i → Set
Tm Γ {i} A = (γ : Γ) → El (A γ)

_[_] : ∀ {Γ Δ i A} → Tm Δ {i} A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_] t σ γ = t (σ γ)

infixl 3 _▶_
_▶_ : ∀(Γ : Con){i} → Ty Γ i → Con
Γ ▶ A = Σ Γ (λ γ → El (A γ))

p : ∀ {Γ i}(A : Ty Γ i) → Sub (Γ ▶ A) Γ
p A (γ , α) = γ

q : ∀ {Γ i}(A : Ty Γ i) → Tm (Γ ▶ A) (A [ p A ]T)
q A (γ , α) = α

infixl 3 _,ₛ_
_,ₛ_ : ∀ {Γ Δ}(σ : Sub Γ Δ){i A} → Tm Γ {i [ σ ]L} (_[_]T {i = i} A σ) → Sub Γ (Δ ▶ A)
_,ₛ_ σ t γ = (σ γ) , (t γ)

-- Lifting structure
Lift : ∀ {Γ i j} → Lt {Γ} i j → Ty Γ i → Ty Γ j
Lift p A = λ γ → IR.Lift (p γ) (A γ)

Lift∘ : ∀ {Γ i j k p q A} → Lift {Γ}{j}{k} p (Lift {Γ}{i}{j} q A) ≡ Lift {Γ}{i}{k} (_∘<_ {Γ}{i}{j}{k} p q) A
Lift∘ {Γ} {i} {j} {k} {p} {q} {A} = ext λ γ → IR.Lift∘ {i γ}{j γ}{k γ} (q γ) (p γ) (A γ)

TmLift : ∀ {Γ i j p A} → Tm Γ {i} A ≡ Tm Γ {j} (Lift p A)
TmLift {Γ}{i}{j}{p}{A} = (λ f → ∀ x → f x) & ext λ γ → ElLift (p γ) (A γ) ⁻¹

▶Lift : ∀ {Γ i j p A} → (Γ ▶ A) ≡ (Γ ▶ Lift {Γ}{i}{j} p A)
▶Lift {Γ} {i} {j} {p} {A} = Σ Γ & ext λ γ → ElLift (p γ) (A γ) ⁻¹

lift : ∀ {Γ i j p A} → Tm Γ {i} A → Tm Γ {j} (Lift p A)
lift {p = p}{A} t γ = coe (ElLift (p γ) (A γ) ⁻¹) (t γ)

lower : ∀ {Γ i j p A} → Tm Γ {j} (Lift p A) → Tm Γ {i} A
lower {p = p}{A} t γ = coe (ElLift (p γ) (A γ)) (t γ)

-- Universes
Univ : ∀ {Γ} i j → Lt {Γ} i j → Ty Γ j
Univ {Γ} i j p = λ γ → U' (p γ)

RussellUniv : ∀ {Γ i j p} → Tm Γ (Univ {Γ} i j p) ≡ Ty Γ i
RussellUniv {Γ}{i}{j} = (λ f → ∀ x → f x) & ext λ γ → U<-compute

Elem : ∀ {Γ i j p} → Tm Γ (Univ {Γ} i j p) → Ty Γ i
Elem t γ = coe U<-compute (t γ)

Code : ∀ {Γ i j p} → Ty Γ i → Tm Γ (Univ {Γ} i j p)
Code A γ = coe (U<-compute ⁻¹) (A γ)

-- some type formers
Nat : ∀ {Γ} i → Ty Γ i
Nat i γ = ℕ'

LiftNat : ∀ {Γ i j p} → Lift {Γ}{i}{j} p (Nat i) ≡ Nat j
LiftNat = refl

Zero : ∀ {Γ i} → Tm Γ (Nat i)
Zero γ = 1

liftZero : ∀ {Γ i j p} → lift {Γ}{i}{j} {p}{Nat {Γ} i} (Zero {Γ}{i}) ≡ (Zero {Γ}{j})
liftZero = refl

Suc : ∀ {Γ i} → Tm Γ (Nat i) → Tm Γ (Nat i)
Suc t γ = suc (t γ)

Π : ∀ {Γ i}(A : Ty Γ i) → Ty (Γ ▶ A) (i [ p A ]L) → Ty Γ i
Π A B γ = Π' (A γ) (λ x → B (γ , x))

Top : ∀ {Γ i} → Ty Γ i
Top γ = ⊤'

Bot : ∀ {Γ i} → Ty Γ i
Bot γ = ⊥'


-- Level reflection

-- with identity type + large elimination on Nat, we could verbatim reproduce
-- the definition of _<*_ internally. We skip formalizing that, as it would very
-- verbose and would stretch the implicit argument inference ability of Agda.

Levelᴵ : ∀ {Γ} → Ty Γ L0
Levelᴵ = Nat L0

ReflectLevel : ∀ {Γ} → Tm Γ Levelᴵ ≡ Level Γ
ReflectLevel {Γ} = refl
