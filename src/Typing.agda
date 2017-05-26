module Typing (U : Set) where

------------------------------------------------------------------------------

data Type : Set where
  el  : (A : U) → Type
  _↣_ : Type → Type → Type

open import Bound Type

open import Data.Nat
open import Data.Vec
open import Data.Fin

Ctxt : ℕ → Set
Ctxt = Vec Type

data _⊢_∶_ : ∀ {n} → Ctxt n → Expr n → Type → Set where
  tVar : ∀ {n Γ} {x : Fin n}
       → Γ ⊢ var x ∶ lookup x Γ

  tLam : ∀ {n} {Γ : Ctxt n} {τ E τ′}
       → (τ ∷ Γ) ⊢ E ∶ τ′
       → Γ ⊢ lam τ E ∶ τ ↣ τ′

  _∙_ :  ∀ {n} {Γ : Ctxt n} {E τ τ′} {F}
      → Γ ⊢ E ∶ τ ↣ τ′
      → Γ ⊢ F ∶ τ
      → Γ ⊢ E ∙ F ∶ τ′

infixr 30 _↣_
infixl 20 _∙_
infixl 20 _⊢_∶_
