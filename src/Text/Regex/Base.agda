{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Preorder; Setoid)

module Text.Regex.Base {a e r} (P : Preorder a e r) where

open import Level using (_⊔_)

open import Data.Empty
open import Data.List.Base as L using (List; []; _∷_; _++_)
open import Data.List.Properties
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Function

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality

open Preorder P using (_≈_) renaming (Carrier to A; _∼_ to _≤_)

------------------------------------------------------------------------
-- Regular expressions on the alphabet A

data Range : Set a where
  [_] : (a : A)     → Range
  _─_ : (lb ub : A) → Range

infixr 5 _∣_
infixr 6 _∙_
infixl 7 _⋆

data Exp : Set a where
  ε    : Exp
  [_]  : (rs : List Range) → Exp
  [^_] : (rs : List Range) → Exp
  _∣_  : (e f : Exp) → Exp
  _∙_  : (e f : Exp) → Exp
  _⋆   : (e : Exp) → Exp

-- Derived notions: nothing, anything, at least one and maybe one

pattern ∅ = [ List.[] ]
pattern · = [^ List.[] ]

infixl 7 _+ _⁇
_+ : Exp → Exp
e + = e ∙ e ⋆

_⁇ : Exp → Exp
∅ ⁇ = ε
e ⁇ = ε ∣ e

-- View: is⊘, isε

is-∅ : ∀ (e : Exp) → Dec (e ≡ ∅)
is-∅ ε          = no (λ ())
is-∅ [ [] ]     = yes refl
is-∅ [ r ∷ rs ] = no (λ ())
is-∅ [^ rs ]    = no (λ ())
is-∅ (e ∣ f)    = no (λ ())
is-∅ (e ∙ f)    = no (λ ())
is-∅ (e ⋆)      = no (λ ())

is-ε : ∀ (e : Exp) → Dec (e ≡ ε)
is-ε ε       = yes refl
is-ε [ rs ]  = no (λ ())
is-ε [^ rs ] = no (λ ())
is-ε (e ∣ f) = no (λ ())
is-ε (e ∙ f) = no (λ ())
is-ε (e ⋆)   = no (λ ())

------------------------------------------------------------------------
-- Semantics: matching words

infix 4 _∈ᴿ_
data _∈ᴿ_ (c : A) : Range → Set (a ⊔ r ⊔ e) where
  [_] : ∀ {val}   → c ≈ val         → c ∈ᴿ [ val ]
  _─_ : ∀ {lb ub} → lb ≤ c → c ≤ ub → c ∈ᴿ (lb ─ ub)

infix 4 _∈_
data _∈_ : List A → Exp → Set (a ⊔ r ⊔ e) where
  ε      :                                                []      ∈ ε
  [_]    : ∀ {a rs} → Any (a ∈ᴿ_) rs →                    L.[ a ] ∈ [ rs ]
  [^_]   : ∀ {a rs} → All (¬_ ∘ (a ∈ᴿ_)) rs →             L.[ a ] ∈ [^ rs ]
  sum    : ∀ {w e f} → (w ∈ e) ⊎ (w ∈ f) →                w       ∈ (e ∣ f)
  prod   : ∀ {v w vw e f} → v ++ w ≡ vw → v ∈ e → w ∈ f → vw      ∈ (e ∙ f)
  star   : ∀ {v e} → v ∈ (ε ∣ e ∙ (e ⋆)) →                v       ∈ (e ⋆)

------------------------------------------------------------------------
-- Small inversion lemmas

∈⁻¹-∅ : ∀ {xs} → ¬ (xs ∈ ∅)
∈⁻¹-∅ [ () ]

∈⁻¹-ε⋆ : ∀ {w} → w ∈ (ε ⋆) → w ∈ ε
∈⁻¹-ε⋆ (star (sum (inj₁ ε)))               = ε
∈⁻¹-ε⋆ (star (sum (inj₂ (prod refl ε q)))) = ∈⁻¹-ε⋆ q

∈⁻¹-∅⋆ : ∀ {w} → w ∈ (∅ ⋆) → w ∈ ε
∈⁻¹-∅⋆ (star (sum (inj₁ ε)))             = ε
∈⁻¹-∅⋆ (star (sum (inj₂ (prod eq p q)))) = ⊥-elim (∈⁻¹-∅ p)

∈⁻₁-ε∙f : ∀ {w f} → w ∈ (ε ∙ f) → w ∈ f
∈⁻₁-ε∙f (prod refl ε p) = p

∈⁻₁-e∙ε : ∀ {w e} → w ∈ (e ∙ ε) → w ∈ e
∈⁻₁-e∙ε (prod eq p ε) with trans (sym (++-identityʳ _)) eq
...  | refl = p
