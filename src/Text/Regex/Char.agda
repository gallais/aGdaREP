module Text.Regex.Char where

open import Data.Char.Base using (Char; toLower; toUpper; _≈_; _<_)
import Data.Char.Properties as Charₚ
open import Data.List.Base using (List; _∷_; []; concatMap)

open import Relation.Unary using (IUniversal)
open import Relation.Binary
open import Relation.Binary.Construct.StrictToNonStrict _≈_ _<_

------------------------------------------------------------------------
-- Re-exporting the base definitions

open import Level using (0ℓ)
open import Level.Bounded as Level≤ using (embed)
open import Data.List.Sized.Interface using (Sized)
open import Text.Parser.Types
open import Text.Parser.Types.Core
open import Text.Parser.Monad
open import Text.Parser.Combinators
open import Text.Regex.Lexer

private
  P : Parameters 0ℓ
  P = Agdarsec′.vec Level≤.[ TOK ]

letter : ∀[ Parser P (embed Char) ]
letter = let instance _ = Agdarsec′.monadPlus in maybeTok isCHAR

open import Text.Regex.String public
open import Text.Regex.Parser Charₚ.≤-preorder letter using (parse) public

------------------------------------------------------------------------
-- Additional functions

ignoreCaseRange : Range → List Range
ignoreCaseRange [ a ]     = [ toLower a ] ∷ [ toUpper a ] ∷ []
ignoreCaseRange (lb ─ ub) = (toLower lb ─ toLower ub) ∷ (toUpper lb ─ toUpper ub) ∷ []

ignoreCaseRanges : List Range → List Range
ignoreCaseRanges = concatMap ignoreCaseRange

module _ where

  open Exp using (_∣_; _∙_; _⋆)

  ignoreCase : Exp → Exp
  ignoreCase ∅       = ∅
  ignoreCase ε       = ε
  ignoreCase [ a ]   = [  ignoreCaseRanges a ]
  ignoreCase [^ a ]  = [^ ignoreCaseRanges a ]
  ignoreCase (e ∣ f) = ignoreCase e Exp.∣ ignoreCase f
  ignoreCase (e ∙ f) = ignoreCase e Exp.∙ ignoreCase f
  ignoreCase (e ⋆)   = ignoreCase e Exp.⋆


-- test
open import Data.Maybe using (from-just)
open import Relation.Binary.PropositionalEquality

_ : Regex.expression (from-just (parse "[a-zA-Z0-9-]*\\.agd(a|ai)"))
    ≡ [ ('a' ─ 'z') ∷ ('A' ─ 'Z') ∷ ('0' ─ '9') ∷ [ '-' ] ∷ [] ] ⋆
    ∙ [ [ '.' ] ∷ [] ]
    ∙ [ [ 'a' ] ∷ [] ]
    ∙ [ [ 'g' ] ∷ [] ]
    ∙ [ [ 'd' ] ∷ [] ]
    ∙ ([ [ 'a' ] ∷ [] ] ∣ [ [ 'a' ] ∷ [] ] ∙ [ [ 'i' ] ∷ [] ])
_ = refl
