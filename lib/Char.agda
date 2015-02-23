module lib.Char where

open import Data.Nat as Nat hiding (_≤_ ; _≤?_)
open import Data.Char
open import Relation.Nullary

_≤_ : (a b : Char) → Set
a ≤ b = toNat a Nat.≤ toNat b

_≤?_ : (a b : Char) → Dec (a ≤ b)
a ≤? b = toNat a Nat.≤? toNat b