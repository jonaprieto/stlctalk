module Typing (U : Set) where

data Type : Set where
  base  : U    → Type
  _⟶_  : Type → Type → Type

------------------------------------------------------------------------------

open import Bound Type hiding (_,_)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_; lookup; [])
open import Data.Fin using (Fin; #_)

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

  _∙_  : ∀ {n} {Γ : Ctxt n} {t₁ t₂} {τ τ′}
       → Γ ⊢ t₁ ∶ τ ⟶ τ′
       → Γ ⊢ t₂ ∶ τ
       → Γ ⊢ t₁ ∙ t₂ ∶ τ′

infixr 30 _⟶_
infixl 20 _∙_
infixl 20 _⊢_∶_


-- Examples

-- postulate
--   Bool : Type

-- ex : [] , Bool ⊢ var (# 0) ∶ Bool
-- ex = tVar

-- ex2 : [] ⊢ lam Bool (var (# 0)) ∶ Bool ⟶ Bool
-- ex2 = tLam tVar

-- postulate
--   Word : Type
--   Num  : Type

-- K : [] ⊢ lam Word (lam Num (var (# 1))) ∶ Word ⟶ Num ⟶ Word
-- K = tLam (tLam tVar)

-- postulate
--   A : Type
--   B : Type
--   C : Type

-- S : [] ⊢ lam (A ⟶ (B ⟶ C))
--              (lam (A ⟶ B)
--                   (lam A
--                     ((var (# 2)) ∙ (var (# 0))) ∙ ((var (# 1)) ∙ (var (# 0))) ))
--        ∶ (A ⟶ (B ⟶ C)) ⟶ (A ⟶ B) ⟶ A ⟶ C
-- S = {!!} --  tLam (tLam (tLam ((tVar ∙ tVar) ∙ (tVar ∙ tVar))))
