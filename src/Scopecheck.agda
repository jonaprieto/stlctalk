module Scopecheck (Type : Set) where

------------------------------------------------------------------------------

open import Bound Type

open import Data.Fin     using (Fin; suc; #_)
open import Data.Nat     hiding (_≟_)
open import Data.Product renaming (_,_ to _-and-_)
open import Data.Product using (∃; ∄)
open import Data.String  using (_≟_)
open import Data.Sum     using (_⊎_; inj₁ ; inj₂)
open import Data.Vec     using (Vec; []; _∷_)

open import Function     using (_$_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary                      using (Dec; no; yes)
open import Relation.Nullary.Decidable
  using (fromWitnessFalse; fromWitness; toWitness; True)

open import Syntax Type as S hiding (Expr; module Expr)
open import Utils            using  (∃-syntax; ∄-syntax)

------------------------------------------------------------------------------

name-dec : ∀ {n} {Γ : Binder n} {x y : Name} {t : Expr (suc n)}
         → Γ , y ⊢ var x ⇝ t
         → x ≡ y ⊎ ∃[ t′ ] (Γ ⊢ var x ⇝ t′)

name-dec {n}{Γ}{x}{.x} {.(var (# 0))} var-zero = inj₁ refl
name-dec {n}{Γ}{x}{y}  {.(var (suc k))}
  (var-suc {n = .n} {x = .x} {y = .y} {k} {Γ = .Γ} {p} Γ,y⊢varx⇝vark)
  = inj₂ (var k -and- Γ,y⊢varx⇝vark)
--          ↪ witness

⊢subst : ∀ {n} {x y} {Γ : Binder n} {t}
       → x ≡ y
       → Γ , x ⊢ var x ⇝ t
       → Γ , y ⊢ var x ⇝ t
⊢subst {n}{x}{y}{Γ}{t} x≡y Γ,x⊢varx⇝t
 = subst (λ z → Γ , z ⊢ var x ⇝ t) x≡y Γ,x⊢varx⇝t


find-name : ∀ {n}
          → (Γ : Binder n)
          → (x : Name)
          → Dec (∃[ t ] (Γ ⊢ var x ⇝ t))

find-name [] x = no helper
  where
    helper : ∄[ t ] ([] ⊢ var x ⇝ t)
    helper (_ -and- ())

find-name (y ∷ Γ) x with x ≟ y
... | yes x≡y = yes (var (# 0) -and- ⊢subst x≡y var-zero)
... | no  x≢y
  with find-name Γ x
...  | yes (var k   -and- Γ⊢x⇝vark)
  = yes $ var (suc k) -and- var-suc {p = fromWitnessFalse x≢y} Γ⊢x⇝vark
...  | yes (lam _ _ -and- ())
...  | yes (_ ∙ _   -and- ())
...  | no ∄t⟨Γ⊢varx⇝t⟩ = no helper
     where
       helper : ∄[ t ] (Γ , y ⊢ var x ⇝ t)
       helper (t -and- Γ,y⊢varx⇝t)
         with name-dec Γ,y⊢varx⇝t
       ...  | inj₁ x≡y                     = x≢y x≡y
       ...  | inj₂ p@(t′ -and- Γ⊢varx⇝t′) = ∄t⟨Γ⊢varx⇝t⟩ p

check : ∀ {n}
      → (Γ : Binder n)
      → (t : S.Expr)
      → Dec (∃[ t′ ] (Γ ⊢ t ⇝ t′))

check Γ (var x) = find-name Γ x
check Γ (lam (x ∶ τ) t)
  with check (Γ , x) t
...  | yes (t′ -and- Γ,x⊢t⇝t′)
       = yes (lam τ t′ -and- lam Γ,x⊢t⇝t′)
...  | no ∄t′⟨Γ,x⊢t⇝t′⟩ = no helper
     where
       helper : ∄[ t′ ] (Γ ⊢ lam (x ∶ τ) t ⇝ t′)
       helper (var x′ -and- ())
       helper (_ ∙ _  -and- ())
       helper (lam .τ t′ -and- lam Γ,x⊢t⇝t′)
         = ∄t′⟨Γ,x⊢t⇝t′⟩ (t′ -and- Γ,x⊢t⇝t′)

check Γ (t₁ ∙ t₂)
  with check Γ t₁ | check Γ t₂
...  | yes (t₁′ -and- Γ⊢t₁⇝t₁′) | (yes (t₂′ -and- Γ⊢t₂⇝t₂′))
       = yes (t₁′ ∙ t₂′ -and- Γ⊢t₁⇝t₁′ ∙ Γ⊢t₂⇝t₂′)
...  | yes (t₁′ -and- Γ⊢t₁⇝t₁′) | (no ∄t⟨Γ⊢t₂⇝t⟩) = no helper
     where
       appʳ : ∀ {n} {Γ : Binder n} {t₁ t₂ t₁′ t₂′}
            → Γ ⊢ t₁ ∙ t₂ ⇝ t₁′ ∙ t₂′
            → Γ ⊢ t₂ ⇝ t₂′
       appʳ (_ ∙ Γ⊢t₂⇝t₂′) = Γ⊢t₂⇝t₂′

       helper : ∄[ t ] (Γ ⊢ t₁ ∙ t₂ ⇝ t)
       helper (var _ -and- ())
       helper (lam _ _ -and- ())
       helper (t₁″ ∙ t₂″ -and- Γ⊢t₁∙t₂⇝t)
         = ∄t⟨Γ⊢t₂⇝t⟩ (t₂″ -and- appʳ Γ⊢t₁∙t₂⇝t)

... | no ∄t⟨Γ⊢t₁⇝t⟩  | _ = no helper
    where
      appˡ : ∀ {n} {Γ : Binder n} {t₁ t₂ t₁′ t₂′}
        → Γ ⊢ t₁ ∙ t₂ ⇝ t₁′ ∙ t₂′
        → Γ ⊢ t₁ ⇝ t₁′
      appˡ (Γ⊢t₁⇝t₁′ ∙ _) = Γ⊢t₁⇝t₁′

      helper : ∄[ t₁′ ] (Γ ⊢ (t₁ ∙ t₂) ⇝ t₁′)
      helper (var _ -and- ())
      helper (lam _ _ -and- ())
      helper (t₁″ ∙ t₂″ -and- Γ⊢t₁∙t₂⇝t)
        = ∄t⟨Γ⊢t₁⇝t⟩ (t₁″ -and- appˡ Γ⊢t₁∙t₂⇝t)

-- Go from a representation that uses Names to one that uses de Bruijn indices
scope : (t : S.Expr) → {p : True (check [] t)} → Expr 0
scope t {p} = proj₁ (toWitness p)


-- Examples.

-- postulate
--   A : Type

-- I₁ : S.Expr
-- I₁ = S.lam ("x" ∶ A) (S.var "x")

-- open import Data.Unit

-- I : Expr 0
-- I = scope I₁ {p = ⊤.tt}

postulate A : Type
x : S.Expr
x = var "x"

y : S.Expr
y = var "y"

z : S.Expr
z = var "z"

S₁ : S.Expr
S₁ =
  lam ("x" ∶ A)
    (lam ("y" ∶ A)
    (lam ("z" ∶ A)
    ((x ∙ z) ∙ (y ∙ z))))

w = check [] S₁
-- S = scope S₁ {p = ⊤.tt}
