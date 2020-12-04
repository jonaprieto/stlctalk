module Syntax (Type : Set) where

------------------------------------------------------------------------------

open import Data.String using (String)

------------------------------------------------------------------------------

Name : Set
Name = String

data Formal : Set where
  _∶_ : Name → Type → Formal

data Expr : Set where
  var : Name   → Expr
  lam : Formal → Expr → Expr
  _∙_ : Expr   → Expr → Expr

infixl 20 _∙_

-- -- Examples.
private
  postulate A : Type

  x = var "x"
  y = var "y"
  z = var "z"

  -- λx.x
  I : Expr
  I = lam ("x" ∶ A) x

  -- λxy.x
  K : Expr
  K = lam ("x" ∶ A) (lam ("y" ∶ A) x)

  -- λxyz.xz(yz)
  S : Expr
  S =
    lam ("x" ∶ A)
      (lam ("y" ∶ A)
        (lam ("z" ∶ A)
          ((x ∙ z) ∙ (y ∙ z))))
