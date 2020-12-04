module Bound (Type : Set) where

------------------------------------------------------------------------------

open import Data.Nat    hiding (_≟_)
open import Data.Fin    using (Fin; #_; suc)
open import Data.String using (_≟_)
open import Data.Vec    using (Vec; _∷_; [])

open import Relation.Nullary.Decidable using (False)

open import Syntax Type as S           hiding (Expr; module Expr)

------------------------------------------------------------------------------

data Expr (n : ℕ) : Set where
  var : Fin n  → Expr n
  lam : Type   → Expr (suc n) → Expr n
  _∙_ : Expr n → Expr n       → Expr n

infixl 20 _∙_

Binder : ℕ → Set
Binder = Vec Name

_,_ : ∀ {n} → Binder n → Name → Binder (suc n)
Γ , x = x ∷ Γ

infixl 5 _,_

infixl 3 _⊢_⇝_

data _⊢_⇝_ : ∀ {n} → Binder n → S.Expr → Expr n → Set where

  var-zero  : ∀ {n x} {Γ : Binder n}
            → Γ , x ⊢ var x ⇝ var (# 0)

  var-suc   : ∀ {n x y k} {Γ : Binder n} {p : False (x ≟ y)}
            → Γ ⊢ var x ⇝ var k
            → Γ , y ⊢ var x ⇝ var (suc k)

  lam       : ∀ {n x τ t t′} {Γ : Binder n}
            → Γ , x ⊢ t ⇝ t′
            → Γ ⊢ lam (x ∶ τ) t ⇝ lam τ t′

  _∙_       : ∀ {n t₁ t₁′ t₂ t₂′} {Γ : Binder n}
            → Γ ⊢ t₁ ⇝ t₁′
            → Γ ⊢ t₂ ⇝ t₂′
            → Γ ⊢ t₁ ∙ t₂ ⇝ t₁′ ∙ t₂′


private
  ∅ : Binder 0
  ∅ = []

  Γ : Binder 2
  Γ = [] , "x" , "y"

  e1 : Γ ⊢ var "x" ⇝ var (# 1)
  e1 = var-suc var-zero

  postulate A : Type

  I : [] ⊢ lam ("x" ∶ A) (var "x")
        ⇝ lam A (var (# 0))
  I = lam var-zero

  K : [] ⊢ lam ("x" ∶ A) (lam ("y" ∶ A) (var "x"))
        ⇝ lam A (lam A (var (# 1)))
  K = lam (lam (var-suc var-zero))

  K₂ : [] ⊢ lam ("x" ∶ A) (lam ("y" ∶ A) (var "y"))
          ⇝ lam A (lam A (var (# 0)))
  K₂ = lam (lam var-zero)

  -- P : Γ ⊢ lam ("x" ∶ A) (lam ("y" ∶ A) (lam ("z" ∶ A) (var "x")))
  --        ⇝ lam A (lam A (lam A (var (# 2))))
  -- P = {!!}
