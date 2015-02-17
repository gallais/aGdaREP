module RegExp.Parse where

open import Data.Sum
open import Data.Char   as Chr
open import Data.String as Str
open import Data.List   as List
open import Function

import RegExp.Search
module S = RegExp.Search Char Chr._≟_
open S

data Error : Set where
  TooManyClosingParentheses   : Error
  NotEnoughClosingParentheses : Error

showError : Error → String
showError TooManyClosingParentheses   = "Too many closing parentheses"
showError NotEnoughClosingParentheses = "Not enough closing parentheses"

parse : List (RegExp → RegExp) → List Char → RegExp ⊎ Error
parse []           _                = inj₂ TooManyClosingParentheses
parse (e ∷ [])     []               = inj₁ $ e ε
parse _            []               = inj₂ NotEnoughClosingParentheses
parse (e ∷ es)     ('\\' ∷ x ∷ xs)  = parse ((λ f → e RE.[ x ] `∙ f) ∷ es) xs
parse es           ('(' ∷ xs)       = parse (id ∷ es) xs
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
parse (e ∷ es)     (a   ∷ '?' ∷ xs) = parse ((λ f → e (RE.[ a ] ⁇ `∙ f)) ∷ es) xs
parse (e ∷ es)     (a   ∷ '*' ∷ xs) = parse ((λ f → e (RE.[ a ] `⋆ `∙ f)) ∷ es) xs
parse (e ∷ es)     (a   ∷ '+' ∷ xs) = parse ((λ f → e (RE.[ a ] + `∙ f)) ∷ es) xs
parse (e ∷ es)     (a   ∷ xs)       = parse ((λ f → e (RE.[ a ] `∙ f)) ∷ es) xs

parseRegExp : String → RegExp ⊎ Error
parseRegExp = parse (id ∷ []) ∘ Str.toList
