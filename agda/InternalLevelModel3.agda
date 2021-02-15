
module InternalLevelModel3 where

{-

Internal levels
- Everything is natural wrt Sub
- Every Ty and Tm former is additionally natural wrt lifting

-- category with terminal object
Con   : Set
Sub   : Con → Con → Set

Level  : Con → Set
_<_    : {Γ : Con} → Level Γ → Level Γ → Set
<-prop : (p q : i < j) → p = q
_∘_    : j < k → i < j → i < k

Ty    : (Γ : Con) → Level Γ → Set
Tm    : (Γ : Con){i : Level Γ} → Ty Γ i → Set

+ CwF, only Tm representable

-- lifting
Lift  : i < j → Ty Γ i → Ty Γ j     -- natural, functorial, preserves all Ty formers
Lift (p ∘ q) A = Lift p (Lift q A)

(↑,↓) : Tm Γ A ~ Tm Γ (Lift p A)    -- natural, functorial, preserves all Tm formers
↑ (p ∘ q) t = ↑ p (↑ q t)

Lift= : Tm Γ A = Tm Γ (Lift p A)    -- strict inclusion
▶=    : (Γ ▶ A) = (Γ ▶ Lift p A)
↑=    : ↑t = t

-- type formers
+ Π, Σ, Id, ⊤, ⊥, Bool, W   in  every Ty Γ i, all rules stay in same Level

-- ↑(lam Γ A B t) = lam Γ (Lift A) (Lift(B[p, ↓q])) (↑(t[p, ↓q]))
-- ↑(λ x. t) = (λ x. ↑(t[x↦ ↓x]))

-- universes
U : ∀ i → i < j → Ty Γ j
Lift p (U i j q) = Lift (U i k (p ∘ q))

(El, c)   : Tm Γ (U i j p) ~ Ty Γ i    -- natural wrt Sub, *not* natural wrt lifting
Russell   : Tm Γ (U i p) = Ty Γ i
El=       : El A = A

-- Level reflection
--------------------------------------------------------------------------------

We can pick an external LvlStruct s.t. its Lvl and _<_ can be represented up to bijection
  using internal types.

We need to assume at least one Level in syntax, because otherwise we can't define anything.
Accordingly, the external level structure needs to be non-empty.

  0 : Level
  0[σ] = 0

Now, let's pick (Lvl = ⊤; _<_ = λ _ _. ⊥) externally. Add to the signature of the theory the following:

  reflectLvl : Tm Γ ⊤₀ = Level Γ           -- natural
  reflect₀   : 0 = tt
  reflect<   : Tm Γ ⊥₀ = (i < j)           -- natural

Checking the semantics:
  Tm Γ ⊤ = Γ → El ⊤' = Γ → ⊤

  Level Γ = Γ → ⊤

  Tm Γ ⊥ = Γ → ⊥

  _<_ : (Γ : Con)(i j : Level Γ) → Set
  _<_ Γ i j = (γ : Γ) → i γ < j γ
            = (γ : Γ) → ⊥

  Tm Γ ⊤ = Γ → El ⊤' = Γ → ⊤ = Level Γ
  Tm Γ ⊥ = Γ → ⊥
  OK

Only having 0 as basic universe is a bit boring, so let's have 0 < 1 as assumption. This makes the
level-reflection-free syntax a lot more powerful, so we can reflect as levels more interesting types.

  refLvl : Tm Γ Nat₀ = Level Γ           -- natural
  ref0   : 0 = 0
  ref1   : 1 = 1
  ref<   : Tm Γ (i < j) ~ (i < j)        -- natural, the type < defined by large elim into U1




-}

-- We pick the external level structure to be (ℕ, <)

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

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ γ = γ

infixr 4 _∘ₛ_
_∘ₛ_ : ∀ {Γ Δ ξ} → Sub Δ ξ → Sub Γ Δ → Sub Γ ξ
σ ∘ₛ δ = λ γ → σ (δ γ)

∙ : Con
∙ = ⊤

Level : Con → Set
Level Γ = Γ → Lvl

L0 : ∀ {Γ} → Level Γ
L0 γ = 0

L1 : ∀ {Γ} → Level Γ
L1 γ = 1

infixl 5 _[_]L
_[_]L : ∀ {Γ Δ} → Level Δ → Sub Γ Δ → Level Γ
_[_]L σ i γ = σ (i γ)

Lt : ∀ {Γ} → Level Γ → Level Γ → Set
Lt {Γ} i j = (γ : Γ) → i γ < j γ

L01 : ∀ {Γ} → Lt (L0 {Γ}) (L1 {Γ})
L01 γ = inj₁ refl

infixr 4 _∘<_
_∘<_ : ∀ {Γ i j k} → Lt {Γ} j k → Lt i j → Lt i k
_∘<_ {Γ}{i}{j}{k} p q γ = _∘_ {i γ} {j γ}{k γ} (p γ) (q γ)

infixl 5 _[_]<
_[_]< : ∀ {Γ Δ i j} → Lt i j → (σ : Sub Γ Δ) → Lt (i [ σ ]L) (j [ σ ]L)
_[_]< p σ γ = p (σ γ)

Ty : (Γ : Con) → Level Γ → Set
Ty Γ i = (γ : Γ) → U (i γ)

Lift : ∀ {Γ i j} → Lt {Γ} i j → Ty Γ i → Ty Γ j
Lift p A γ = ↑ (p γ) (A γ)

infixl 5 _[_]T
_[_]T : ∀ {Γ Δ i} → Ty Δ i → (σ : Sub Γ Δ) → Ty Γ (i [ σ ]L)
_[_]T A σ γ = A (σ γ)

Tm : (Γ : Con) → ∀ {i} → Ty Γ i → Set
Tm Γ {i} A = (γ : Γ) → El (A γ)

CumulativeTm : ∀ {Γ i j p A} → Tm Γ {i} A ≡ Tm Γ {j} (Lift p A)
CumulativeTm {Γ}{i}{j}{p}{A} = (λ f → ∀ x → f x) & ext λ γ → El↑ (p γ) (A γ) ⁻¹

lift : ∀ {Γ i j p A} → Tm Γ {i} A → Tm Γ {j} (Lift p A)
lift {p = p}{A} t γ = coe (El↑ (p γ) (A γ) ⁻¹) (t γ)

lower : ∀ {Γ i j p A} → Tm Γ {j} (Lift p A) → Tm Γ {i} A
lower {p = p}{A} t γ = coe (El↑ (p γ) (A γ)) (t γ)

_[_] : ∀ {Γ Δ i A} → Tm Δ {i} A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
_[_] t σ γ = t (σ γ)

infixl 3 _▶_
_▶_ : ∀(Γ : Con){i} → Ty Γ i → Con
Γ ▶ A = Σ Γ (λ γ → El (A γ))

CumulativeCon : ∀ {Γ i j p A} → (Γ ▶ A) ≡ (Γ ▶ Lift {Γ}{i}{j} p A)
CumulativeCon {Γ} {i} {j} {p} {A} = Σ Γ & ext λ γ → El↑ (p γ) (A γ) ⁻¹

p : ∀ {Γ i}(A : Ty Γ i) → Sub (Γ ▶ A) Γ
p A (γ , α) = γ

q : ∀ {Γ i}(A : Ty Γ i) → Tm (Γ ▶ A) (A [ p A ]T)
q A (γ , α) = α

infixl 3 _,ₛ_
_,ₛ_ : ∀ {Γ Δ}(σ : Sub Γ Δ){i A} → Tm Γ {i [ σ ]L} (_[_]T {i = i} A σ) → Sub Γ (Δ ▶ A)
_,ₛ_ σ t γ = (σ γ) , (t γ)

-- type formers
--------------------------------------------------------------------------------

Id : ∀ {Γ i} A → Tm Γ {i} A → Tm Γ A → Ty Γ i
Id A t u γ = Id' (A γ) (t γ) (u γ)

-- we define here only recursion, and only for L1 level, to reduce Agda inference issues
Nat : ∀ {Γ} i → Ty Γ i
Nat i γ = ℕ'

Zero₁ : ∀ {Γ} → Tm Γ (Nat L1)
Zero₁ γ = 1

Suc₁ : ∀ {Γ} → Tm Γ (Nat L1) → Tm Γ (Nat L1)
Suc₁ t γ = suc (t γ)

NatRec₁ : ∀ {Γ}(B : Ty Γ L1) → Tm Γ B
          → Tm (Γ ▶ Nat L1 ▶ B [ p (Nat L1) ]T) (B [ p (Nat L1) ∘ₛ p (B [ p (Nat L1) ]T) ]T)
          → Tm Γ (Nat L1) → Tm Γ B
NatRec₁ B z s n γ = ℕ-elim (λ _ → EL (B γ)) (z γ) (λ {n} b → s ((γ , n) , b)) (n γ)

Either : ∀ {Γ i} → Ty Γ i → Ty Γ i → Ty Γ i
Either A B γ = A γ ⊎' B γ

Π : ∀ {Γ i}(A : Ty Γ i) → Ty (Γ ▶ A) (i [ p A ]L) → Ty Γ i
Π A B γ = Π' (A γ) (λ x → B (γ , x))

Top : ∀ {Γ i} → Ty Γ i
Top γ = ⊤'

Bot : ∀ {Γ i} → Ty Γ i
Bot γ = ⊥'

--------------------------------------------------------------------------------

Univ : ∀ {Γ} i j → Lt {Γ} i j → Ty Γ j
Univ {Γ} i j p γ = U' (p γ)

RussellUniv : ∀ {Γ i j p} → Tm Γ (Univ {Γ} i j p) ≡ Ty Γ i
RussellUniv {Γ}{i}{j} = (λ f → ∀ x → f x) & ext λ γ → U↓-compute

Elem : ∀ {Γ i j p} → Tm Γ (Univ {Γ} i j p) → Ty Γ i
Elem t γ = coe U↓-compute (t γ)

Code : ∀ {Γ i j p} → Ty Γ i → Tm Γ (Univ {Γ} i j p)
Code A γ = coe (U↓-compute ⁻¹) (A γ)

-- internal Lvl
ILevel : ∀ {Γ} → Ty Γ L0
ILevel = Nat L0

ReflectLvl : ∀ {Γ} → Tm Γ ILevel ≡ Level Γ
ReflectLvl {Γ} = refl

-- internal Lt
ILt : ∀ {Γ} → Tm Γ ILevel → Tm Γ ILevel → Ty Γ L0
ILt {Γ} i j =
  Elem (
    NatRec₁
      (Univ {Γ} L0 L1 L01)
      (Code Bot)
      (Code (Either (Id ILevel (_[_] {_}{Γ}{L0}{ILevel} i (p ILevel ∘ₛ p (Univ L0 L1 L01)))
                               (_[_] {A = ILevel} (q ILevel) (p (Univ L0 L1 L01))))
                    (Elem (q {Γ ▶ ILevel} (Univ L0 L1 L01)))))
      j)

--   ((γ : Γ) → EL (ℕ-elim (λ _ → UU 0) ⊥' (λ {n} b → (Id' ℕ' (i γ) n ⊎' b)) (j γ)))
-- ≡ ((γ : Γ) → ℕ-elim (λ _ → Set) ⊥ (λ {b} → _⊎_ (i γ ≡ b)) (j γ))

ReflectLt→ : ∀ {Γ i j} → Tm Γ (ILt i j) → Lt {Γ} i j
ReflectLt→ {Γ} {i} {j} t γ = {!!}

ReflectLt← : ∀ {Γ i j} → Lt {Γ} i j → Tm Γ (ILt i j)
ReflectLt← {Γ}{i}{j} p γ = {!!}
