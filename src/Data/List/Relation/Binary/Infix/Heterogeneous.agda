------------------------------------------------------------------------
-- An inductive definition of the heterogeneous infix relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Infix.Heterogeneous where

open import Level
open import Relation.Binary using (REL; _⇒_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous
  as Prefix using (Prefix; []; _∷_)

module _ {a b r} {A : Set a} {B : Set b} (R : REL A B r) where

  data Infix : REL (List A) (List B) (a ⊔ b ⊔ r) where
    here  : ∀ {as bs}   → Prefix R as bs → Infix as bs
    there : ∀ {b as bs} → Infix as bs → Infix as (b ∷ bs)
