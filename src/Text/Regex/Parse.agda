module Text.Regex.Parse where

import Level.Bounded as Level≤
import Text.Parser.Success as Success
open import Text.Parser.Types
open import Text.Parser.Monad
open import Text.Parser.Monad.Result as Result using (Value)
open import Text.Parser.Position
open import Induction.Nat.Strong
open import Text.Parser.Combinators

open import Level using (0ℓ)
import Data.Nat.Properties as ℕₚ
open import Data.Char as Char
import Data.Char.Properties as Charₚ
open import Data.Vec as Vec using (Vec)
open import Data.List.Base as List using (List; []; _∷_)
import Data.List.NonEmpty as List⁺
import Data.List.Sized.Interface
open import Data.Maybe.Base using (Maybe; just; nothing; maybe; from-just)
open import Data.Product using (proj₁; uncurry; _,_)
open import Data.String as String using (String)
open import Function
open import Relation.Nullary using (yes; no)
open import Relation.Unary
import Relation.Binary as B
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Decidable

open import Relation.Binary.Construct.StrictToNonStrict

open import Text.Regex.Base Charₚ.≤-preorder-≈
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

P : Parameters 0ℓ
P = Agdarsec′.vec Level≤.[ TOK ]

letter : ∀[ Parser P Level≤.[ Char ] ]
letter = maybeTok isCHAR

ranges : ∀[ Parser P (Level≤.List Level≤.[ Range ]) ]
ranges =
  let range : Parser P (Level≤.[ Range ]) _
      range = (uncurry $ λ c md → maybe (c ─_) [ c ] md)
              <$> (letter <&?> box (exact DOTS &> box letter))
  in List⁺.toList <$> list⁺ range

regex : ∀[ Parser P Level≤.[ Exp ] ]
regex = fix (Parser P Level≤.[ Exp ]) $ λ rec →
  let parens   = between (exact LPAR) (box (exact RPAR))
      parens?  = between? (exact LPAR) (box (exact RPAR))
      ranges   : Parser P Level≤.[ Exp ] _
      ranges   = ([_] <$ exact OPEN <|> [^_] <$ exact NOPEN)
                 <*> box (ranges <& box (exact CLOSE))
      base     = ranges <|> [^ [] ] <$ exact ANY
                        <|> singleton <$> letter
                        <|> parens rec
      star?    : Parser P Level≤.[ Exp ] _
      star?    = (uncurry $ λ r → maybe (const $ r ⋆) r)
                  <$> (base <&?> box (exact STAR))
      conj     : Parser P Level≤.[ Exp ] _
      conj     = List⁺.foldr _∙_ id <$> list⁺ star?
      disj     = chainr1 conj (box (_∣_ <$ exact OR))
  in List⁺.foldr _∙_ id <$> list⁺ (parens? disj)

parse : String → Maybe Exp
parse str =
  let chars  = String.toList str
      input  = Vec.fromList (toTOKs chars)
      init   = Level≤.lift (start , [])
      result = runParser regex ℕₚ.≤-refl (Level≤.lift input) init
   in case Result.map proj₁ result of λ where
         (Value s) → just $ Level≤.lower $ Success.value s
         _ → nothing

-- test

_ : from-just (parse "[a..zA..Z0..9-]*\\.agd(a|ai)")
    ≡ [ ('a' ─ 'z') ∷ ('A' ─ 'Z') ∷ ('0' ─ '9') ∷ [ '-' ] ∷ [] ] ⋆
    ∙ [ [ '.' ] ∷ [] ]
    ∙ [ [ 'a' ] ∷ [] ]
    ∙ [ [ 'g' ] ∷ [] ]
    ∙ [ [ 'd' ] ∷ [] ]
    ∙ ([ [ 'a' ] ∷ [] ] ∣ [ [ 'a' ] ∷ [] ] ∙ [ [ 'i' ] ∷ [] ])
_ = refl
