{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecPoset)

module Text.Regex.Search {a e r} (P? : DecPoset a e r) where

open import Level using (_⊔_)
open import Data.Empty
open import Data.List.Base using (List; []; _∷_)
open import Function

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary using (Rel; Decidable)
open import Relation.Binary.PropositionalEquality hiding (preorder)

open DecPoset P? using (preorder) renaming (Carrier to A)
open import Text.Regex.Base preorder
open import Text.Regex.Properties P?
open import Text.Regex.Derivative P?

infix 4 _∈?_
_∈?_ : Decidable _∈_
[]     ∈? e = []∈? e
x ∷ xs ∈? e = map′ (eat-sound x e) (eat-complete x e)
            $ xs ∈? eat x e

record Match {s} (R : Rel (List A) s) (xs : List A) (exp : Exp)
       : Set (a ⊔ e ⊔ r ⊔ s) where
  constructor MkMatch
  field list    : List A
        match   : list ∈ exp
        related : R list xs
open Match public

map : ∀ {r s} {R : Rel (List A) r} {S : Rel (List A) s} {xs ys e} →
      (∀ {a} → R a xs → S a ys) → Match R xs e → Match S ys e
map f (MkMatch ys ys∈e pys) = MkMatch ys ys∈e (f pys)

module Prefix where

  open import Data.List.Relation.Binary.Prefix.Heterogeneous
  open import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties

  []ᴹ : ∀ {xs e} → [] ∈ e → Match (Prefix _≡_) xs e
  []ᴹ p = MkMatch [] p []

  []⁻¹ᴹ : ∀ {e} → Match (Prefix _≡_) [] e → [] ∈ e
  []⁻¹ᴹ (MkMatch .[] p []) = p

  _∷ᴹ_ : ∀ {xs e} x → Match (Prefix _≡_) xs (eat x e) → Match (Prefix _≡_) (x ∷ xs) e
  x ∷ᴹ (MkMatch ys ys∈e\x ys≤xs) = MkMatch (x ∷ ys) (eat-sound x _ ys∈e\x) (refl ∷ ys≤xs)

  _∷⁻¹ᴹ_ : ∀ {xs x e} → ¬ ([] ∈ e) →
           Match (Prefix _≡_) (x ∷ xs) e → Match (Prefix _≡_) xs (eat x e)
  []∉e ∷⁻¹ᴹ (MkMatch .[]       []∈e [])             = ⊥-elim ([]∉e []∈e)
  []∉e ∷⁻¹ᴹ (MkMatch (._ ∷ ys) ys∈e (refl ∷ ys≤xs)) = MkMatch ys (eat-complete _ _ ys∈e) ys≤xs

  shortest : Decidable (Match (Prefix _≡_))
  shortest xs e with []∈? e
  ... | yes []∈e = yes ([]ᴹ []∈e)
  shortest []       e | no ¬[]∈e = no (¬[]∈e ∘′ []⁻¹ᴹ)
  shortest (x ∷ xs) e | no ¬[]∈e with shortest xs (eat x e)
  ... | yes p = yes (x ∷ᴹ p)
  ... | no ¬p = no (¬p ∘ (¬[]∈e ∷⁻¹ᴹ_))

  longest : Decidable (Match (Prefix _≡_))
  longest []       e = map′ []ᴹ []⁻¹ᴹ ([]∈? e)
  longest (x ∷ xs) e with longest xs (eat x e)
  ... | yes p = yes (x ∷ᴹ p)
  ... | no ¬p with []∈? e
  ... | yes []∈e = yes ([]ᴹ []∈e)
  ... | no ¬[]∈e = no (¬p ∘ (¬[]∈e ∷⁻¹ᴹ_))

module Infix where

  open import Data.List.Relation.Binary.Infix.Heterogeneous

  search : Decidable (Match (Infix _≡_))
  search xs e with Prefix.shortest xs e
  ... | yes p = yes (map here p)
  search [] e       | no ¬p = no (¬p ∘ map λ where (here p) → p)
  search (x ∷ xs) e | no ¬p with search xs e
  ... | yes q = yes (map there q)
  ... | no ¬q = no λ where
    (MkMatch ys ys∈e (here p))  → ¬p (MkMatch ys ys∈e p)
    (MkMatch ys ys∈e (there q)) → ¬q (MkMatch ys ys∈e q)
