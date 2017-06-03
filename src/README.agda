module README where

-- First definition of Typed Lambda Calculus.
import Syntax

-- Lambda Terms using De Bruijn indexes.
import Bound

-- Check representation of λ-terms using de Bruijn indexes.
-- Get a λ-term using de Bruijn indexes by given a λ-term with names.
import Scopecheck

-- Type system and its derivation rules.
import Typing

-- Typability and Type-checking.
import Typecheck
