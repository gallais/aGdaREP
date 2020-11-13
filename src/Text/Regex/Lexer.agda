{-# OPTIONS --without-K --safe #-}

module Text.Regex.Lexer where

open import Data.Char as Char using (Char)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.String.Base using (String; toList)
open import Function.Base using (_∘′_)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; inspect; [_])

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

------------------------------------------------------------------------
-- Decidable equality (linear in the number of constructors)

data _∼_ : (t u : TOK) → Set where
  OPEN  : OPEN ∼ OPEN
  NOPEN : NOPEN ∼ NOPEN
  CLOSE : CLOSE ∼ CLOSE
  ANY   : ANY ∼ ANY
  STAR  : STAR ∼ STAR
  DOTS  : DOTS ∼ DOTS
  OR    : OR ∼ OR
  LPAR  : LPAR ∼ LPAR
  RPAR  : RPAR ∼ RPAR
  CHAR  : ∀ c d → CHAR c ∼ CHAR d

view : ∀ t u → Maybe (t ∼ u)
view OPEN     OPEN     = just OPEN
view NOPEN    NOPEN    = just NOPEN
view CLOSE    CLOSE    = just CLOSE
view ANY      ANY      = just ANY
view STAR     STAR     = just STAR
view DOTS     DOTS     = just DOTS
view OR       OR       = just OR
view LPAR     LPAR     = just LPAR
view RPAR     RPAR     = just RPAR
view (CHAR c) (CHAR d) = just (CHAR c d)
view _ _ = nothing

view-diag : ∀ {t u} → view t u ≡ nothing → ¬ (t ≡ u)
view-diag {OPEN}   () refl
view-diag {NOPEN}  () refl
view-diag {CLOSE}  () refl
view-diag {ANY}    () refl
view-diag {STAR}   () refl
view-diag {DOTS}   () refl
view-diag {OR}     () refl
view-diag {LPAR}   () refl
view-diag {RPAR}   () refl
view-diag {CHAR c} () refl

_≟_ : DecidableEquality TOK
_≟_ t u with view t u | inspect (view t) u
... | nothing | [ eq ] = no (view-diag eq)
... | just OPEN       | _ = yes refl
... | just NOPEN      | _ = yes refl
... | just CLOSE      | _ = yes refl
... | just ANY        | _ = yes refl
... | just STAR       | _ = yes refl
... | just DOTS       | _ = yes refl
... | just OR         | _ = yes refl
... | just LPAR       | _ = yes refl
... | just RPAR       | _ = yes refl
... | just (CHAR c d) | _ = map′ (cong CHAR) CHAR-injective (c Char.≟ d)

------------------------------------------------------------------------
-- Lexing functions

-- Excerpt from https://www.gnu.org/software/sed/manual/html_node/Regular-Expressions.html
-- [list] [^list]
-- Matches any single character in list: for example, [aeiou] matches all vowels.
-- A list may include sequences like char1-char2, which matches any character between (inclusive) char1 and char2.
-- A leading ^ reverses the meaning of list, so that it matches any single character not in list.

-- To include ] in the list, make it the first character (after the ^ if needed)
-- To include - in the list, make it the first or last
-- To include ^ put it after the first character

-- The characters $, *, ., [, and \ are normally not special within list.
-- For example, [\*] matches either ‘\’ or ‘*’, because the \ is not special here.

-- NOT SUPPORTED YET:
-- However, strings like [.ch.], [=a=], and [:space:] are special within list
-- and represent collating symbols , equivalence classes, and character classes,
-- respectively, and [ is therefore special within list when it is followed by ., =, or :.

-- To accomodate this complexity, we introduce 3 mutually defined lexers
-- outRange the state we are in outside of a range
-- preRange the state we enter after reading an opening bracket
-- inRange  the state we are in deep inside of a range

outRange : List Char → List TOK
preRange : List Char → List TOK
inRange : List Char → List TOK

outRange []              = []
outRange ('[' ∷ cs)      = preRange cs
outRange ('\\' ∷ c ∷ cs) = CHAR c ∷ outRange cs
outRange ('.' ∷ cs)      = ANY ∷ outRange cs
outRange ('(' ∷ cs)      = LPAR ∷ outRange cs
outRange (')' ∷ cs)      = RPAR ∷ outRange cs
outRange ('*' ∷ cs)      = STAR ∷ outRange cs
outRange ('|' ∷ cs)      = OR ∷ outRange cs
outRange (c ∷ cs)        = CHAR c ∷ outRange cs

preRange []               = OPEN ∷ []
-- special cases for ']'
preRange (']' ∷ cs)       = OPEN ∷ CHAR ']' ∷ inRange cs
preRange ('^' ∷ ']' ∷ cs) = NOPEN ∷ CHAR ']' ∷ inRange cs
-- special cases for '-'
preRange ('-' ∷ cs)       = OPEN ∷ CHAR '-' ∷ inRange cs
preRange ('^' ∷ '-' ∷ cs) = NOPEN ∷ CHAR '-' ∷ inRange cs
-- negation
preRange ('^' ∷ cs)       = NOPEN ∷ inRange cs
-- default: usual open
preRange cs               = OPEN ∷ inRange cs

inRange [] = []
-- special cases for closing
inRange ('-' ∷ ']' ∷ cs) = CHAR '-' ∷ CLOSE ∷ outRange cs
inRange (']' ∷ cs)       = CLOSE ∷ outRange cs
-- rest
inRange ('-' ∷ cs)       = DOTS ∷ inRange cs
inRange (c ∷ cs)         = CHAR c ∷ inRange cs

------------------------------------------------------------------------
-- Entrypoint for the lexer: outside of a range

lex : List Char → List TOK
lex = outRange
