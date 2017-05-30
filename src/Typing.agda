module Typing (U : Set) where

data Type : Set where
  base  : U    → Type
  _⟶_  : Type → Type → Type

------------------------------------------------------------------------------

open import Bound Type hiding (_,_)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_; lookup)
open import Data.Fin using (Fin)

------------------------------------------------------------------------------

Ctxt : ℕ → Set
Ctxt = Vec Type

_,_ : ∀ {n} → Ctxt n → Type → Ctxt (suc n)
Γ , x = x ∷ Γ

infixl 20 _,_

data _⊢_∶_ : ∀ {n} → Ctxt n → Expr n → Type → Set where
  tVar : ∀ {n Γ} {x : Fin n}
       → Γ ⊢ var x ∶ lookup x Γ

  tLam : ∀ {n} {Γ : Ctxt n} {t} {τ τ′}
       → Γ , τ ⊢ t ∶ τ′
       → Γ ⊢ lam τ t ∶ τ ⟶ τ′

  _∙_  :  ∀ {n} {Γ : Ctxt n} {t₁ t₂} {τ τ′}
       → Γ ⊢ t₁ ∶ τ ⟶ τ′
       → Γ ⊢ t₂ ∶ τ
       → Γ ⊢ t₁ ∙ t₂ ∶ τ′

infixr 30 _⟶_
infixl 20 _∙_
infixl 20 _⊢_∶_
