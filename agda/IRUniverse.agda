
module IRUniverse where

{-
Inductive-recursive universes over arbitrary level structures.

We give a full formalization of Section 4.1 of the paper.

Additionally, we give some examples for type codes using ω and ω*ω levels.

We also give a simple example for having _⊔_ operation on levels when levels
form a type theoretic ordinal.
-}

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

module IR-Universe (lvl : LvlStruct) where
  open LvlStruct lvl public
  open import Data.Nat hiding (_<_; _≤_)

  infix 4 _<'_
  infixr 1 _⊎'_

  data Uⁱʳ {i}(l : ∀ j → j < i → Set) : Set
  Elⁱʳ : ∀ {i l} → Uⁱʳ {i} l → Set

  data Uⁱʳ {i} l where
    U'       : ∀ {j} → j < i → Uⁱʳ l
    ℕ' ⊤' ⊥' : Uⁱʳ l
    _⊎'_     : Uⁱʳ l → Uⁱʳ l → Uⁱʳ l
    Π' Σ' W' : (a : Uⁱʳ l) → (Elⁱʳ a → Uⁱʳ l) → Uⁱʳ l

    -- codes for levels and morphisms, only used in level-polymorphic code examples
    Lvl'  : Uⁱʳ l
    _<'_  : Lvl → Lvl → Uⁱʳ l

  Elⁱʳ {_}{l}(U' p) = l _ p
  Elⁱʳ ℕ'           = ℕ
  Elⁱʳ ⊤'           = ⊤
  Elⁱʳ ⊥'           = ⊥
  Elⁱʳ Lvl'         = Lvl
  Elⁱʳ (i <' j)     = i < j
  Elⁱʳ (a ⊎' b)     = Elⁱʳ a ⊎ Elⁱʳ b
  Elⁱʳ (Π' a b)     = ∀ x → Elⁱʳ (b x)
  Elⁱʳ (Σ' a b)     = ∃ λ x → Elⁱʳ (b x)
  Elⁱʳ (W' a b)     = W (Elⁱʳ a) (λ x → Elⁱʳ (b x))

  -- Interpreting levels & lifts
  --------------------------------------------------------------------------------

  U< : ∀ {i} {{_ : Acc _<_ i}} j → j < i → Set
  U< {i} {{acc f}} j p = Uⁱʳ {j} (U< {j}{{f j p}})

  U : Lvl → Set
  U i = Uⁱʳ {i} (U< {i} {{wf}})

  El : ∀ {i} → U i → Set
  El {i} = Elⁱʳ {i}{U< {i}{{wf}}}

  U<-compute : ∀ {i a j p} → U< {i}{{a}} j p ≡ U j
  U<-compute {i} {acc f} {j} {p} = (λ a → Uⁱʳ (U< {{a}})) & Acc-prop (f j p) wf

  Lift   : ∀ {i j} → i < j → U i → U j
  ElLift : ∀ {i j} p a → El (Lift {i}{j} p a) ≡ El a
  Lift   p (U' q)      = U' (p ∘ q)
  Lift   p ℕ'          = ℕ'
  Lift   p ⊤'          = ⊤'
  Lift   p ⊥'          = ⊥'
  Lift   p Lvl'        = Lvl'
  Lift   p (i <' j)    = i <' j
  Lift   p (a ⊎' b)    = Lift p a ⊎' Lift p b
  Lift   p (Π' a b)    = Π' (Lift p a) λ x → Lift p (b (coe (ElLift p a) x))
  Lift   p (Σ' a b)    = Σ' (Lift p a) λ x → Lift p (b (coe (ElLift p a) x))
  Lift   p (W' a b)    = W' (Lift p a) λ x → Lift p (b (coe (ElLift p a) x))
  ElLift {i}{j} p (U' {k} q) = U<-compute {p = p ∘ q} ◾ U<-compute {p = q} ⁻¹
  ElLift p ℕ'       = refl
  ElLift p ⊤'       = refl
  ElLift p ⊥'       = refl
  ElLift p Lvl'     = refl
  ElLift p (i <' j) = refl
  ElLift p (a ⊎' b) = _⊎_ & ElLift p a ⊗ ElLift p b
  ElLift p (Π' a b) rewrite ElLift p a = (λ f → ∀ x → f x) & ext (ElLift p F.∘ b)
  ElLift p (Σ' a b) rewrite ElLift p a = Σ _ & ext (ElLift p F.∘ b)
  ElLift p (W' a b) rewrite ElLift p a = W _ & ext (ElLift p F.∘ b)

  -- congruence helper lemma
  congr2 : ∀ {i}{l : ∀ j → j < i → Set}
          (F' : (a : Uⁱʳ l) → (Elⁱʳ a → Uⁱʳ l) → Uⁱʳ l)
          {a₀ a₁ : Uⁱʳ l}(a₂ : a₀ ≡ a₁)
          {b₀ : Elⁱʳ a₀ → Uⁱʳ l}{b₁ : Elⁱʳ a₁ → Uⁱʳ l}
        → (∀ x → b₀ x ≡ b₁ (coe (Elⁱʳ & a₂) x))
        → F' a₀ b₀ ≡ F' a₁ b₁
  congr2 {i} {l} F' {a₀} refl {b₀} {b₁} b₂ = F' a₀ & ext b₂

  -- functorial lifting
  Lift∘ : ∀ {i j k}(p : i < j)(q : j < k) a → Lift q (Lift p a) ≡ Lift (q ∘ p) a
  Lift∘ p q (U' r)   = U' & <-prop
  Lift∘ p q ℕ'       = refl
  Lift∘ p q ⊤'       = refl
  Lift∘ p q ⊥'       = refl
  Lift∘ p q Lvl'     = refl
  Lift∘ p q (i <' j) = refl
  Lift∘ p q (a ⊎' b) = _⊎'_ & Lift∘ p q a ⊗ Lift∘ p q b
  Lift∘ p q (Π' a b) =
    congr2 Π' (Lift∘ p q a)
        (λ x → Lift∘ p q _
             ◾ (λ x → Lift (q ∘ p) (b x)) &
                  (coe∘ (ElLift p a) (ElLift q (Lift p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (ElLift (q ∘ p) a) (Elⁱʳ & Lift∘ p q a) x ⁻¹))
  Lift∘ p q (Σ' a b) =
    congr2 Σ' (Lift∘ p q a)
        (λ x → Lift∘ p q _
             ◾ (λ x → Lift (q ∘ p) (b x)) &
                  (coe∘ (ElLift p a) (ElLift q (Lift p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (ElLift (q ∘ p) a) (Elⁱʳ & Lift∘ p q a) x ⁻¹))
  Lift∘ p q (W' a b) =
    congr2 W' (Lift∘ p q a)
        (λ x → Lift∘ p q _
             ◾ (λ x → Lift (q ∘ p) (b x)) &
                  (coe∘ (ElLift p a) (ElLift q (Lift p a)) x
                ◾ (λ y → coe y x) & UIP
                ◾ coe∘ (ElLift (q ∘ p) a) (Elⁱʳ & Lift∘ p q a) x ⁻¹))

  -- conveniences
  --------------------------------------------------------------------------------

  _⇒'_ : ∀ {i l} → Uⁱʳ {i} l → Uⁱʳ l → Uⁱʳ l
  a ⇒' b = Π' a λ _ → b
  infixr 3 _⇒'_

  _×'_ : ∀ {i l} → Uⁱʳ {i} l → Uⁱʳ l → Uⁱʳ l
  a ×' b = Σ' a λ _ → b
  infixr 4 _×'_

  -- This is convenient in code examples, where we often want to lift values in Elⁱʳ U'
  LiftU : ∀ {i j}(p : i < j) → El (U' p) → U j
  LiftU p a = Lift p (coe U<-compute a)


-- Type-theoretic ordinals
--------------------------------------------------------------------------------

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
  open IR-Universe lvl public

  -- non-strict lifts
  Lift≤ : ∀ {i j} → i ≤ j → U i → U j
  Lift≤ (inj₁ p)    a = Lift p a
  Lift≤ (inj₂ refl) a = a

  ElLift≤ : ∀ {i j} p a → El (Lift≤ {i}{j} p a) ≡ El a
  ElLift≤ (inj₁ p)    a = ElLift p a
  ElLift≤ (inj₂ refl) a = refl

  -- alternative Π type formation with _⊔_ and Lift.
  Π'' : ∀ {i j}(a : U i) → (El a → U j) → U (i ⊔ j)
  Π'' {i}{j} a b = Π' (Lift≤ (⊔₁ i j) a) λ x → Lift≤ (⊔₂ i j) (b (coe (ElLift≤ (⊔₁ i j) a) x))


-- Examples. Here we instantiate level structures, and give examples for some
-- type codes and their El interpretations.
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

  open IR-Universe lvl hiding (_<_)

  <suc : ∀ {i} → i < suc i
  <suc {i} = ≤-refl

  id' : ∀ {i} → El {suc i} (Π' (U' <suc) λ A → LiftU <suc A ⇒' LiftU <suc A)
  id' {i} A x = x

  const₀' : El {1} (Π' (U' <suc) λ A → Π' (U' <suc) λ B → LiftU <suc A ⇒' LiftU <suc B ⇒' LiftU <suc A)
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

  open IR-Universe lvl hiding (_<_)

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

  idω : El {ω} (Π' ℕ' λ i → Π' (U' (<Suc i)) λ A → LiftU (<Suc i) A ⇒' LiftU (<Suc i) A)
  idω i A x = x

  idω' : El {ω} (Π' Lvl' λ i → Π' (i <' ω) λ p → Π' (U' p) λ A → LiftU p A ⇒' LiftU p A)
  idω' i p A x = x

  fω+2 : El {ω + # 2} (U' (trs <suc <suc) ⇒' U' <suc)
  fω+2 = LiftU <suc
