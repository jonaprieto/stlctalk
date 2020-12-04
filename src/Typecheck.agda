open import Relation.Binary using (IsDecEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

module Typecheck {U : Set} (UEq : IsDecEquivalence {A = U} _≡_) where

------------------------------------------------------------------------------

open IsDecEquivalence UEq using (_≟_)

open import Typing U
  using (Type; base; _↣_; _⊢_∶_; Ctxt; tVar; tLam; _∙_)
open import Bound Type

open import Data.Nat      hiding (_≟_)
open import Data.Product  hiding (∃-syntax; ∄-syntax) renaming (_,_ to _-and-_)
open import Data.Product  using (∃; ∄)
open import Data.Vec      using (Vec; _∷_; lookup)

open import Function         using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality
  using (refl; cong; cong₂; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Utils            using (∃-syntax; ∄-syntax)

------------------------------------------------------------------------------

-- Equality between Types.
_T≟_ : (τ τ′ : Type) → Dec (τ ≡ τ′)

base A T≟ base B with A ≟ B
... | yes A≡B = yes (cong base A≡B)
... | no  A≢B = no (A≢B ∘ helper)
  where
    helper : base A ≡ base B → A ≡ B
    helper refl = refl
base A T≟ (_ ↣ _) = no (λ ())

(τ₁ ↣ τ₂) T≟ base B = no (λ ())
(τ₁ ↣ τ₂) T≟ (τ₁′ ↣ τ₂′) with τ₁ T≟ τ₁′
... | no  τ₁≢τ₁′ = no (τ₁≢τ₁′ ∘ helper)
  where
    helper :  τ₁ ↣ τ₂ ≡ τ₁′ ↣ τ₂′ → τ₁ ≡ τ₁′
    helper refl = refl

... | yes τ₁≡τ₁′ with τ₂ T≟ τ₂′
...            | yes τ₂≡τ₂′ = yes (cong₂ _↣_ τ₁≡τ₁′ τ₂≡τ₂′)
...            | no  τ₂≢τ₂′ = no (τ₂≢τ₂′ ∘ helper)
  where
    helper : τ₁ ↣ τ₂ ≡ τ₁′ ↣ τ₂′ → τ₂ ≡ τ₂′
    helper refl = refl


⊢-inj : ∀ {n Γ} {t : Expr n} → ∀ {τ σ}
      → Γ ⊢ t ∶ τ
      → Γ ⊢ t ∶ σ
      → τ ≡ σ
⊢-inj tVar tVar = refl
⊢-inj {t = lam τ t} (tLam Γ,τ⊢t:τ′) (tLam Γ,τ⊢t:τ″)
  = cong (_↣_ τ) (⊢-inj Γ,τ⊢t:τ′ Γ,τ⊢t:τ″)
⊢-inj (Γ⊢t₁:τ↣τ₂ ∙ Γ⊢t₂:τ) (Γ⊢t₁:τ₁↣σ ∙ Γ⊢t₂:τ₁)
  = helper (⊢-inj Γ⊢t₁:τ↣τ₂ Γ⊢t₁:τ₁↣σ)
  where
    helper : ∀ {τ τ₂ τ₁ σ} → (τ ↣ τ₂ ≡ τ₁ ↣ σ) → τ₂ ≡ σ
    helper refl = refl

-- Typability.
infer : ∀ {n} Γ (t : Expr n) → Dec (∃[ τ ] (Γ ⊢ t ∶ τ))

-- Var case.
infer Γ (var x) = yes (lookup Γ x -and- tVar)

-- Abstraction case.
infer Γ (lam τ t) with infer (τ ∷ Γ) t
... | yes (σ -and- Γ,τ⊢t:σ) = yes (τ ↣ σ -and- tLam Γ,τ⊢t:σ)
... | no  Γ,τ⊬t:σ = no helper
  where
    helper : ∄[ τ′ ] (Γ ⊢ lam τ t ∶ τ′)
    helper (base A -and- ())
    helper (.τ ↣ σ -and- tLam Γ,τ⊢t:σ) = Γ,τ⊬t:σ (σ -and- Γ,τ⊢t:σ)

-- Application case.
infer Γ (t₁ ∙ t₂) with infer Γ t₁ | infer Γ t₂
... | no  ∄τ⟨Γ⊢t₁:τ⟩ | _ = no helper
    where
      helper : ∄[ σ ] (Γ ⊢ t₁ ∙ t₂ ∶ σ)
      helper (τ -and- Γ⊢t₁:τ ∙ _) = ∄τ⟨Γ⊢t₁:τ⟩ (_ ↣ τ -and- Γ⊢t₁:τ)

... | yes (base x -and- Γ⊢t₁:base) | _ = no helper
    where
      helper : ∄[ σ ] (Γ ⊢ t₁ ∙ t₂ ∶ σ)
      helper (τ -and- Γ⊢t₁:_↣_ ∙ _)
        with ⊢-inj Γ⊢t₁:_↣_ Γ⊢t₁:base
      ...  | ()

... | yes (τ₁ ↣ τ₂ -and- Γ⊢t₁:τ₁↣τ₂) | no  ∄τ⟨Γ⊢t₂:τ⟩ = no helper
    where
      helper : ∄[ σ ] (Γ ⊢ t₁ ∙ t₂ ∶ σ)
      helper (τ -and- Γ⊢t₁:τ₁′↣τ₂′ ∙ Γ⊢t₂:τ)
        with ⊢-inj Γ⊢t₁:τ₁↣τ₂ Γ⊢t₁:τ₁′↣τ₂′
      ...  | refl = ∄τ⟨Γ⊢t₂:τ⟩ (τ₁ -and- Γ⊢t₂:τ)

... | yes (τ₁ ↣ τ₂ -and- Γ⊢t₁:τ₁↣τ₂) | yes (τ₁′ -and- Γ⊢t₂:τ₁′)
    with τ₁ T≟ τ₁′
...  | yes τ₁≡τ₁′ = yes (τ₂ -and- Γ⊢t₁:τ₁↣τ₂ ∙ helper)
     where
       helper : Γ ⊢ t₂  ∶ τ₁
       helper = subst (_⊢_∶_ Γ t₂) (sym τ₁≡τ₁′) Γ⊢t₂:τ₁′
...  | no  τ₁≢τ₁′ = no helper
     where
       helper : ∄[ σ ] (Γ ⊢ t₁ ∙ t₂ ∶ σ)
       helper (_ -and- Γ⊢t₁:τ↣τ₂ ∙ Γ⊢t₂:τ₁)
         with ⊢-inj  Γ⊢t₁:τ↣τ₂ Γ⊢t₁:τ₁↣τ₂
       ...  | refl = τ₁≢τ₁′ (⊢-inj Γ⊢t₂:τ₁ Γ⊢t₂:τ₁′)


-- Type-checking.
check : ∀ {n} Γ (t : Expr n) → ∀ τ → Dec (Γ ⊢ t ∶ τ)

-- Var case.
check Γ (var x) τ with lookup Γ x T≟ τ
... | yes refl = yes tVar
... | no ¬p    = no (¬p ∘ ⊢-inj tVar)

-- Abstraction case.
check Γ (lam τ t) (base A) = no (λ ())
check Γ (lam τ t) (τ₁ ↣ τ₂) with τ₁ T≟ τ
... | no τ₁≢τ = no (τ₁≢τ ∘ helper)
    where
      helper : Γ ⊢ lam τ t ∶ (τ₁ ↣ τ₂) → τ₁ ≡ τ
      helper (tLam t) = refl

... | yes refl with check (τ ∷ Γ) t τ₂
...               | yes Γ,τ⊢t:τ₂ = yes (tLam Γ,τ⊢t:τ₂)
...               | no  Γ,τ⊬t:τ₂ = no helper
  where
    helper : ¬ Γ ⊢ lam τ t ∶ τ ↣ τ₂
    helper (tLam Γ,τ⊢t:_) = Γ,τ⊬t:τ₂ Γ,τ⊢t:_

-- Application case.
check Γ (t₁ ∙ t₂) σ with infer Γ t₂
... | yes (τ -and- Γ⊢t₂:τ)
    with check Γ t₁ (τ ↣ σ)
...    | yes Γ⊢t₁:τ↣σ = yes (Γ⊢t₁:τ↣σ ∙ Γ⊢t₂:τ)
...    | no  Γ⊬t₁:τ↣σ = no helper
  where
    helper : ¬ Γ ⊢ t₁ ∙ t₂ ∶ σ
    helper (Γ⊢t₁:_↣_ ∙ Γ⊢t₂:τ′)
      with ⊢-inj Γ⊢t₂:τ Γ⊢t₂:τ′
    ...  | refl = Γ⊬t₁:τ↣σ Γ⊢t₁:_↣_

check Γ (t₁ ∙ t₂) σ | no Γ⊬t₂:_ = no helper
  where
    helper : ¬ Γ ⊢ t₁ ∙ t₂ ∶ σ
    helper (_∙_ {τ = σ} t Γ⊢t₂:τ′) = Γ⊬t₂:_ (σ -and- Γ⊢t₂:τ′)
