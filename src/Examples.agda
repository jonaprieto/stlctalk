module Examples (U : Set) where

data Type : Set where
  base : U    → Type
  _⟶_ : Type → Type → Type

open import Syntax (Type) as S

postulate A : Type

x = var "x"
y = var "y"
z = var "z"

-- λx.x
I : S.Expr
I = lam ("x" ∶ A) x

-- λxy.x
K : S.Expr
K = lam ("x" ∶ A) (lam ("y" ∶ A) x)

-- λxyz.xz(yz)
S : S.Expr
S =
  lam ("x" ∶ A)
    (lam ("y" ∶ A)
      (lam ("z" ∶ A)
        ((x ∙ z) ∙ (y ∙ z))))
