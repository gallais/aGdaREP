module RegExp.Parse where

open import Data.Sum
open import Data.Char   as Chr
open import lib.Char
open import Data.String as Str
open import Data.List   as List
open import Function

open import Relation.Nullary

import RegExp.Search
module S = RegExp.Search Char _≤_ Chr._≟_ _≤?_
open S

data Error : Set where
  TooManyClosingParentheses   : Error
  NotEnoughClosingParentheses : Error
  UnfinishedRange             : Error

showError : Error → String
showError TooManyClosingParentheses   = "Too many closing parentheses"
showError NotEnoughClosingParentheses = "Open parenthesis: missing ')'"
showError UnfinishedRange             = "Open range: missing ']'"

mutual

  parse : List (RegExp → RegExp) → List Char → RegExp ⊎ Error
  parse []           _                = inj₂ TooManyClosingParentheses
  parse (e ∷ [])     []               = inj₁ $ e ε
  parse _            []               = inj₂ NotEnoughClosingParentheses
  parse (e ∷ es)     ('\\' ∷ x ∷ xs)  = parse ((λ f → e RE.[ List.[ exact x ] ] `∙ f) ∷ es) xs
  parse es           ('(' ∷ xs)       = parse (id ∷ es) xs
  parse es           ('[' ∷ '^' ∷ xs) = parseRange [^_]  es xs
  parse es           ('[' ∷ xs)       = parseRange S.[_] es xs
  parse (e ∷ es)     ('|' ∷ xs)       = parse ((λ f → e ε ∣ f) ∷ es) xs
  parse (e ∷ [])     (')' ∷ xs)       = inj₂ TooManyClosingParentheses
  parse (e ∷ f ∷ es) (')' ∷ '?' ∷ xs) = parse ((λ g → f (e ε ⁇ `∙ g)) ∷ es) xs
  parse (e ∷ f ∷ es) (')' ∷ '*' ∷ xs) = parse ((λ g → f (e ε `⋆ `∙ g)) ∷ es) xs
  parse (e ∷ f ∷ es) (')' ∷ '+' ∷ xs) = parse ((λ g → f (e ε + `∙ g)) ∷ es) xs
  parse (e ∷ f ∷ es) (')' ∷ xs)       = parse ((λ g → f (e ε `∙ g)) ∷ es) xs
  parse (e ∷ es)     ('.' ∷ '?' ∷ xs) = parse ((λ f → e (─ ⁇ `∙ f)) ∷ es) xs
  parse (e ∷ es)     ('.' ∷ '*' ∷ xs) = parse ((λ f → e (─ `⋆ `∙ f)) ∷ es) xs
  parse (e ∷ es)     ('.' ∷ '+' ∷ xs) = parse ((λ f → e (─ + `∙ f)) ∷ es) xs
  parse (e ∷ es)     ('.' ∷ xs)       = parse ((λ f → e (─ `∙ f)) ∷ es) xs
  parse (e ∷ es)     (a   ∷ '?' ∷ xs) = parse ((λ f → e (RE.[ List.[ exact a ] ] ⁇ `∙ f)) ∷ es) xs
  parse (e ∷ es)     (a   ∷ '*' ∷ xs) = parse ((λ f → e (RE.[ List.[ exact a ] ] `⋆ `∙ f)) ∷ es) xs
  parse (e ∷ es)     (a   ∷ '+' ∷ xs) = parse ((λ f → e (RE.[ List.[ exact a ] ] + `∙ f)) ∷ es) xs
  parse (e ∷ es)     (a   ∷ xs)       = parse ((λ f → e (RE.[ List.[ exact a ] ] `∙ f)) ∷ es) xs

  parseRange : (List Range → RegExp) → List (RegExp → RegExp) → List Char → RegExp ⊎ Error
  parseRange _ []       _                    = inj₂ TooManyClosingParentheses
  parseRange _ _        []                   = inj₂ UnfinishedRange
  parseRange k es       ('\\' ∷ x ∷ xs)      = parseRange (k ∘ (_∷_ (exact x))) es xs
  parseRange k (e ∷ es) (']' ∷ '?' ∷ xs)     = parse ((λ f → e (k List.[] ⁇ `∙ f)) ∷ es) xs
  parseRange k (e ∷ es) (']' ∷ '*' ∷ xs)     = parse ((λ f → e (k List.[] ⋆ `∙ f)) ∷ es) xs
  parseRange k (e ∷ es) (']' ∷ '+' ∷ xs)     = parse ((λ f → e (k List.[] + `∙ f)) ∷ es) xs
  parseRange k (e ∷ es) (']' ∷ xs)           = parse ((λ f → e (k List.[]   `∙ f)) ∷ es) xs
  parseRange k es       (x   ∷ '-' ∷ y ∷ xs) = parseRange (k ∘ (_∷_ (range x y))) es xs
  parseRange k es       (x   ∷ xs)           = parseRange (k ∘ (_∷_ (exact x)))   es xs

parseRegExp : String → RegExp ⊎ Error
parseRegExp = parse (id ∷ []) ∘ Str.toList
