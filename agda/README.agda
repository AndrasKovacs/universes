
module README where

{-
Agda supplement to the paper "Generalized Universe Hierarchies and First-Class Universe Levels".

This module was checked using Agda 2.6.1, with standard library version 1.3.

For instructions on installing the standard library, see the following:
https://agda.readthedocs.io/en/v2.6.1.3/tools/package-system.html
-}

import Lib          -- library, for equational reasoning and exporting some definitions
import IRUniverse   -- semantic inductive-recursive universes over level structures
import TTGUModel    -- model of type theory with generalized levels
import TTFLModel    -- model of type theory with first-class levels, where levels are strictly the same as internal Nat
import Super        -- some notes on Palmgren's super universes and transfinite hierarchies
