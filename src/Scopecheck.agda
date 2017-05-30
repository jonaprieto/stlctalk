module Scopecheck (Type : Set) where

------------------------------------------------------------------------------

open import Syntax Type as S hiding (Expr; module Expr)
open import Bound Type

open import Data.Nat hiding (_≟_)
open import Data.Fin using (Fin; suc; #_)
open import Data.Vec using ([]; _∷_)
open import Data.String using (_≟_)

open import Relation.Nullary.Decidable using (fromWitnessFalse)
open import Relation.Nullary using (Dec; no; yes)
-- open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Product renaming (_,_ to _-and-_)
open import Data.Product using (∃; ∄)

open import Function using (_$_)
open import Data.Sum using (_⊎_; inj₁ ; inj₂)
-- open import Utils

------------------------------------------------------------------------------

appˡ : ∀ {n} {Γ : Binder n} {t₁ t₂ t₁′ t₂′}
     → Γ ⊢ t₁ ∙ t₂ ⇝ t₁′ ∙ t₂′
     → Γ ⊢ t₁ ⇝ t₁′
appˡ (δ ∙ _) = δ

appʳ  : ∀ {n} {Γ : Binder n} {t₁ t₂ t₁′ t₂′}
      → Γ ⊢ t₁ ∙ t₂ ⇝ t₁′ ∙ t₂′
      → Γ ⊢ t₂ ⇝ t₂′
appʳ (_ ∙ δ) = δ


--
∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set _
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B

∄-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set _
∄-syntax = ∄

syntax ∄-syntax (λ x → B) = ∄[ x ] B
--


name-dec : ∀ {n} {Γ : Binder n} {x y : Name} {t : Expr (suc n)}
         → Γ , y ⊢ var x ⇝ t
         → x ≡ y ⊎ ∃[ t′ ] (Γ ⊢ var x ⇝ t′)

name-dec {n} {Γ} {x} {.x} {.(var (# 0))} var-zero = inj₁ refl
name-dec {n} {Γ} {x} {y}  {.(var (suc k))} (var-suc {n = .n} {x = .x} {y = .y} {k} {Γ = .Γ} {p} Γ,y⊢varx⇝vark)
  = inj₂ (var k -and- Γ,y⊢varx⇝vark)
      --   ↪ witness for t₂

⊢subst : ∀ {n} {x y} {Γ : Binder n} {t}
        → x ≡ y
        → Γ , x ⊢ var x ⇝ t
        → Γ , y ⊢ var x ⇝ t
⊢subst {n}{x}{y}{Γ}{t} x≡y Γ,x⊢varx⇝t =
       subst (λ z → z ∷ Γ ⊢ var x ⇝ t) x≡y Γ,x⊢varx⇝t

find-name : ∀ {n}
          → (Γ : Binder n)
          → (x : Name)
          → Dec (∃[ t ] (Γ ⊢ var x ⇝ t))
find-name [] x = no lem
  where
    lem : ∄[ t ] ([] ⊢ var x ⇝ t)
    lem (_ -and- ())   -- TODO

find-name (y ∷ Γ) x with x ≟ y
... | yes x≡y = yes (var (# 0) -and- ⊢subst x≡y var-zero)
... | no  x≢y
      with find-name Γ x
...      | yes (var k   -and- δ) =
                yes $ var (suc k) -and- var-suc {p = fromWitnessFalse x≢y} δ
...      | yes (lam _ _ -and- ())
...      | yes (_ ∙ _   -and- ())
...      | (no ∄t⟨Γ⊢varx⇝t⟩) = no lem
  where
    lem : ∄[ t ] (Γ , y ⊢ var x ⇝ t)
    lem (t -and- Γ,y⊢varx⇝t)
        with name-dec Γ,y⊢varx⇝t
    ...    | inj₁ x≡y                     = x≢y x≡y
    ...    | inj₂ p@(t′ -and- Γ⊢varx⇝t′) = ∄t⟨Γ⊢varx⇝t⟩ p

check : ∀ {n}
      → (Γ : Binder n)
      → (t : S.Expr)
      → Dec (∃[ t′ ] (Γ ⊢ t ⇝ t′))
check Γ (var x)   = find-name Γ x
check Γ (lam (x ∶ τ) t) with check (Γ , x) t
... | z = {!!}
check Γ (t ∙ t₁)  = {!!}

-- check : ∀ {n} → (Γ : Binder n) → (E : S.Expr) → Dec (∃[ E′ ] Γ ⊢ E ↝ E′)
-- check Γ (var x) = find-name Γ x
-- check Γ (lam (x ∶ τ) E) with check (x ∷ Γ) E
-- check Γ (lam (x ∶ τ) E) | yes (E′ , δ) = yes (lam _ E′ , lam δ)
-- check Γ (lam (x ∶ τ) E) | no ¬p = no lem
--   where
--   lem : ∄[ E′ ] Γ ⊢ lam (x ∶ τ) E ↝ E′
--   lem (var _ , ())
--   lem (_ · _ , ())
--   lem (lam .τ E′ , lam δ) = ¬p (E′ , δ)
-- check Γ (E · F) with check Γ E
-- check Γ (E · F) | yes (E′ , δ₁) with check Γ F
-- check Γ (E · F) | yes (E′ , δ₁) | yes (F′ , δ₂) = yes (E′ · F′ , δ₁ · δ₂)
-- check Γ (E · F) | yes (E′ , δ₁) | no ¬p = no lem
--   where
--   lem : ∄[ E′ ] Γ ⊢ E · F ↝ E′
--   lem (var _ , ())
--   lem (lam _ _ , ())
--   lem (E₁ · E₂ , δ) = ¬p (E₂ , appʳ δ)
-- check Γ (E · F) | no ¬p = no lem
--   where
--   lem : ∄[ E′ ] Γ ⊢ (E · F) ↝ E′
--   lem (var _ , ())
--   lem (lam _ _ , ())
--   lem (E₁ · E₂ , δ) = ¬p (E₁ , appˡ δ)

-- -- Go from a representation that uses Names to one that uses de Bruijn indices
-- scope : (E : S.Expr) → {p : True (check [] E)} → Expr 0
-- scope E {p} = proj₁ (toWitness p)
