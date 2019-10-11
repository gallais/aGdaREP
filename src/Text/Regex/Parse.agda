module Text.Regex.Parse where

open import Text.Parser.Types
open import Text.Parser.Monad
open import Text.Parser.Position
open import Induction.Nat.Strong
open import Text.Parser.Combinators
open import Text.Parser.Combinators.Char

import Data.Nat.Properties as ℕₚ
open import Data.Bool.Base
open import Data.Char as Char
import Data.Char.Properties as Charₚ
open import Data.Vec as Vec using (Vec)
open import Data.List.Base as List using (List; []; _∷_)
import Data.List.NonEmpty as List⁺
import Data.List.Sized.Interface
open import Data.Maybe
open import Data.Product
import Data.String as String
open import Function
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary as B
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Decidable

open import Relation.Binary.Construct.StrictToNonStrict

open import Text.Regex.Base
  (record { isPreorder = isPreorder₂ _ _ Charₚ.<-isStrictPartialOrder-≈ })
  using (Range; Exp; singleton); open Range; open Exp

data TOK : Set where
  OPEN NOPEN CLOSE : TOK
  ANY STAR DOTS OR : TOK
  LPAR RPAR        : TOK
  CHAR             : Char → TOK

CHAR-injective : ∀ {a b} → CHAR a ≡ CHAR b → a ≡ b
CHAR-injective refl = refl

isCHAR : TOK → Maybe Char
isCHAR (CHAR c) = just c
isCHAR _        = nothing

eqTOK : B.Decidable {A = TOK} _≡_
eqTOK OPEN     OPEN     = yes refl
eqTOK NOPEN    NOPEN    = yes refl
eqTOK CLOSE    CLOSE    = yes refl
eqTOK STAR     STAR     = yes refl
eqTOK ANY      ANY      = yes refl
eqTOK DOTS     DOTS     = yes refl
eqTOK OR       OR       = yes refl
eqTOK LPAR     LPAR     = yes refl
eqTOK RPAR     RPAR     = yes refl
eqTOK (CHAR c) (CHAR d) with c Char.≟ d
... | yes eq = yes (cong CHAR eq)
... | no ¬eq = no (¬eq ∘′ CHAR-injective)
eqTOK _ _ = no whatever where
  private postulate whatever : ∀ {A} → A

toTOKs : List Char → List TOK
toTOKs []               = []
toTOKs ('\\' ∷ c ∷ cs)  = CHAR c ∷ toTOKs cs
toTOKs ('[' ∷ '^' ∷ cs) = NOPEN  ∷ toTOKs cs
toTOKs ('[' ∷ cs)       = OPEN   ∷ toTOKs cs
toTOKs (']' ∷ cs)       = CLOSE  ∷ toTOKs cs
toTOKs ('.' ∷ '.' ∷ cs) = DOTS   ∷ toTOKs cs
toTOKs ('.' ∷ cs)       = ANY    ∷ toTOKs cs
toTOKs ('(' ∷ cs)       = LPAR   ∷ toTOKs cs
toTOKs (')' ∷ cs)       = RPAR   ∷ toTOKs cs
toTOKs ('*' ∷ cs)       = STAR   ∷ toTOKs cs
toTOKs ('|' ∷ cs)       = OR     ∷ toTOKs cs
toTOKs (c ∷ cs)         = CHAR c ∷ toTOKs cs

instance

  _ : DecidableEquality TOK
  _ = record { decide = eqTOK }

  _ = Agdarsec′.monadPlus
  _ = Agdarsec′.monadState

P : Parameters
P = Agdarsec′.vec TOK

letter : ∀[ Parser P Char ]
letter = maybeTok isCHAR

range : ∀[ Parser P Range ]
range = (uncurry $ λ c md → maybe (c ─_) [ c ] md)
        <$> (letter <&?> box (exact DOTS &> box letter))

regex : ∀[ Parser P Exp ]
regex = fix (Parser P Exp) $ λ rec →
  let parens   = between (exact LPAR) (box (exact RPAR))
      parens?  = between? (exact LPAR) (box (exact RPAR))
      ranges   = ([_] <$ exact OPEN <|> [^_] <$ exact NOPEN)
                 <*> box (List⁺.toList <$> list⁺ range
                <& box (exact CLOSE))
      base     = ranges <|> [^ [] ] <$ exact ANY
                        <|> singleton <$> letter
                        <|> parens rec
      star?    = (uncurry $ λ r → maybe (const $ r ⋆) r)
                  <$> (base <&?> box (exact STAR))
      conj     = List⁺.foldr _∙_ id <$> list⁺ star?
      disj     = chainr1 conj (box (_∣_ <$ exact OR))
  in List⁺.foldr _∙_ id <$> list⁺ (parens? disj)

-- test

_ : let chars = String.toList "[a..zA..Z0..9-]*\\.agd(a|ai)"
        input = Vec.fromList (toTOKs chars)
    in (case runParser regex ℕₚ.≤-refl input (start , []) of λ where
         (Value (s , _)) → Success.value s
         _ → [ [] ])
    ≡ [ ('a' ─ 'z') ∷ ('A' ─ 'Z') ∷ ('0' ─ '9') ∷ [ '-' ] ∷ [] ] ⋆
    ∙ [ [ '.' ] ∷ [] ]
    ∙ [ [ 'a' ] ∷ [] ]
    ∙ [ [ 'g' ] ∷ [] ]
    ∙ [ [ 'd' ] ∷ [] ]
    ∙ ([ [ 'a' ] ∷ [] ] ∣ [ [ 'a' ] ∷ [] ] ∙ [ [ 'i' ] ∷ [] ])
_ = refl
