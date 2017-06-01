module Utils where

open import Data.Product renaming (_,_ to _-and-_)
open import Data.Product using (∃; ∄)

∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set _
∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∄-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set _
∄-syntax = ∄
syntax ∄-syntax (λ x → B) = ∄[ x ] B