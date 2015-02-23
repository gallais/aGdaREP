open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Data.Empty
open import Data.Bool     hiding (_≟_)
open import Data.Maybe    as Maybe
open import Data.Product  as Product
open import Data.List     as List    using (List ; [] ; _∷_)

open import lib.Nullary
open import Function

module RegExp.RegExp
       (Alphabet : Set)
       (_≤_ : (a b : Alphabet) → Set)
       where

  infixr 5 _∣_
  infixr 6 _∙_
  infixl 7 _⋆

  -- inductive definition of regular expressions
  -- on the alphabet Alphabet

  data Range : Set where
    exact : (a : Alphabet)     → Range
    range : (lb ub : Alphabet) → Range

  data RegExp : Set where
    ε    : RegExp
    [_]  : (as : List Range) → RegExp
    [^_] : (as : List Range) → RegExp
    _∣_  : (e₁ e₂ : RegExp) → RegExp
    _∙_  : (e₁ e₂ : RegExp) → RegExp
    _⋆   : (e : RegExp) → RegExp

  -- Extra notions encoded using the existing language

  pattern ∅ = [ List.[] ]

  ─ : RegExp
  ─ = [^ List.[] ]

  infixl 7 _+ _⁇
  _+ : (e : RegExp) → RegExp
  e + = e ∙ e ⋆

  _⁇ : (e : RegExp) → RegExp
  ∅ ⁇ = ε
  e ⁇ = ε ∣ e

  -- semantics in terms of words (lists of letters
  -- in Alphabet)

  infix 3 _∈[_]
  data _∈[_] (a : Alphabet) : (as : List Range) → Set where
    z≡  : {as : List Range} → a ∈[ exact a ∷ as ]
    z≥≤ : {as : List Range} {lb ub : Alphabet} → lb ≤ a → a ≤ ub → a ∈[ range lb ub ∷ as ]
    s   : {as : List Range} {b : Range} → a ∈[ as ] → a ∈[ b ∷ as ]

  infixr 5 _∣₁_ _∣₂_
  infixr 6 _∙_⇚_
  infix 3 _∈_
  data _∈_ : (xs : List Alphabet) (e : RegExp) → Set where
    ε     : [] ∈ ε
    [_]   : {a : Alphabet} {as : List Range} → a ∈[ as ] → List.[ a ] ∈ RegExp.[ as ]
    [^_]  : {a : Alphabet} {as : List Range} → (a ∈[ as ] → ⊥) → List.[ a ] ∈ RegExp.[^ as ]
    _∣₁_  : {xs : List Alphabet} {e : RegExp} (pr : xs ∈ e) (f : RegExp) → xs ∈ e ∣ f
    _∣₂_  : {xs : List Alphabet} (e : RegExp) {f : RegExp} (pr : xs ∈ f) → xs ∈ e ∣ f
    _∙_⇚_ : {xs ys zs : List Alphabet} {e f : RegExp}
            (pr₁ : xs ∈ e) (pr₂ : ys ∈ f) (eq : zs ≡ xs List.++ ys) → zs ∈ e ∙ f
    _⋆    : {xs : List Alphabet} {e : RegExp} →
            xs ∈ ε ∣ e ∙ e ⋆ → xs ∈ e ⋆

  ∈∅-invert : {xs : List Alphabet} → ¬ (xs ∈ ∅)
  ∈∅-invert [ () ]