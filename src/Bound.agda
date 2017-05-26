module Bound (Type : Set) where

------------------------------------------------------------------------------

open import Data.Nat hiding (_≟_)
open import Data.Fin

open import Syntax as S hiding (Expr; module Expr)

------------------------------------------------------------------------------

data Expr (n : ℕ) : Set where
  var : Fin n  → Expr n
  lam : Type   → Expr (suc n) → Expr n
  _∙_ : Expr n → Expr n       → Expr n

infixl 20 _∙_

x : Expr 1
x = var (# 0)

postulate
  A : Type

λx→x : Expr 0
λx→x = lam A x

y : Expr 2
y = var (# 1)

s : Expr 1
s = lam A y

λxy→x : Expr 3
λxy→x = lam A (lam A (var (# 3)))

λλλ→x : Expr 3
λλλ→x = lam A (lam A (var (# 3)))

------------------------------------------------------------------------------



