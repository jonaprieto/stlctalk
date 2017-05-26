
module Syntax (Type : Set) where

open import Data.String

Name : Set
Name = String

-- Judgments (x ∶ A).
data Formal : Set where
  _∶_ : Name → Type → Formal

-- Grammar.
data Expr : Set where
  var : Name   → Expr         -- var "x"
  lam : Formal → Expr → Expr  -- λ(x ∶ A).t
  _∙_ : Expr   → Expr → Expr  -- MN

infixl 20 _∙_

