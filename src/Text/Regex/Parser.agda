open import Level.Bounded as Level≤ using (embed)
open import Text.Parser.Types
open import Text.Parser.Monad

open import Relation.Binary using (Preorder)
open import Relation.Unary

open import Text.Regex.Lexer

module Text.Regex.Parser
       {a e r} (PO : Preorder a e r)
       (let open Preorder PO using (Carrier))
       (let P = Agdarsec′.vec Level≤.[ TOK ])
       (p : ∀[ Parser P (embed Carrier) ])
       where

open import Data.List.Base using ([])
import Data.List.NonEmpty as List⁺
import Data.List.Sized.Interface
open import Data.Maybe.Base using (Maybe; nothing; just; maybe′)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_,_; proj₁; uncurry)
open import Data.String.Base using (String)
import Data.Vec.Base as Vec
open import Function.Base using (_$_; const; id; case_of_)

open import Induction.Nat.Strong
open import Text.Parser.Combinators
open import Text.Parser.Monad.Result as Result using (Value)
open import Text.Parser.Position using (start)

open import Relation.Binary.PropositionalEquality.Decidable

open import Text.Regex.Base PO
  using (Range; Exp; singleton); open Range; open Exp

instance

  _ : DecidableEquality TOK
  _ = record { decide = _≟_ }

  _ = Agdarsec′.monadPlus
  _ = Agdarsec′.monadState

ranges : ∀[ Parser P (Level≤.List (embed Range)) ]
ranges =
  let range : Parser P (embed Range) _
      range = (uncurry $ λ c md → maybe′ (c ─_) [ c ] md)
              <$> (p <&?> box (exact DOTS &> box p))
  in List⁺.toList <$> list⁺ range

regex : ∀[ Parser P (embed Exp) ]
regex = fix (Parser P (embed Exp)) $ λ rec →
  let parens   = between (exact LPAR) (box (exact RPAR))
      parens?  = between? (exact LPAR) (box (exact RPAR))
      ranges   : Parser P (embed Exp) _
      ranges   = ([_] <$ exact OPEN <|> [^_] <$ exact NOPEN)
                 <*> box (ranges <& box (exact CLOSE))
      base     = ranges <|> [^ [] ] <$ exact ANY
                        <|> singleton <$> p
                        <|> parens rec
      star?    : Parser P (embed Exp) _
      star?    = (uncurry $ λ r → maybe′ (const $ r ⋆) r)
                  <$> (base <&?> box (exact STAR))
      conj     : Parser P (embed Exp) _
      conj     = List⁺.foldr _∙_ id <$> list⁺ star?
      disj     = chainr1 conj (box (_∣_ <$ exact OR))
  in List⁺.foldr _∙_ id <$> list⁺ (parens? disj)

parse : String → Maybe Exp
parse str =
  let toks   = lex str
      input  = Vec.fromList toks
      init   = Level≤.lift (start , [])
      result = runParser regex ℕₚ.≤-refl (Level≤.lift input) init
   in case Result.map proj₁ result of λ where
         (Value s) → just $ Level≤.lower $ Success.value s
         _ → nothing
