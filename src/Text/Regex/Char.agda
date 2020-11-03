module Text.Regex.Char where

open import Data.Char.Base using (Char; toLower; toUpper)
import Data.Char.Properties as Charₚ
open import Data.List.Base using (List; _∷_; []; concatMap)

------------------------------------------------------------------------
-- Re-exporting the base definitions

open import Text.Regex.Base Charₚ.≤-preorder-≈ public

------------------------------------------------------------------------
-- Additional functions

ignoreCaseRange : Range → List Range
ignoreCaseRange [ a ]     = [ toLower a ] ∷ [ toUpper a ] ∷ []
ignoreCaseRange (lb ─ ub) = (toLower lb ─ toLower ub) ∷ (toUpper lb ─ toUpper ub) ∷ []

ignoreCaseRanges : List Range → List Range
ignoreCaseRanges = concatMap ignoreCaseRange

ignoreCase : Exp → Exp
ignoreCase ∅       = ∅
ignoreCase ε       = ε
ignoreCase [ a ]   = [  ignoreCaseRanges a ]
ignoreCase [^ a ]  = [^ ignoreCaseRanges a ]
ignoreCase (e ∣ f) = ignoreCase e ∣ ignoreCase f
ignoreCase (e ∙ f) = ignoreCase e ∙ ignoreCase f
ignoreCase (e ⋆)   = ignoreCase e ⋆
