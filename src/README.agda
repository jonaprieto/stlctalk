-- Disclaimer: this implementation of the simple lambda calculus is a refactor
-- of the implementation by @gergoerdi (https://github.com/gergoerdi/stlc-agda).
-- Specifically in the Scopecheck and Typecheck module.

module README where

-- First definition of Typed Lambda Calculus.
open import Syntax

-- Lambda Terms using De Bruijn indexes.
open import Bound

-- Check representation of λ-terms using de Bruijn indexes.
-- Get a λ-term using de Bruijn indexes by given a λ-term with names.
open import Scopecheck

-- Type system and its derivation rules.
open import Typing

-- Typability and Type-checking.
open import Typecheck
