{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Preorder)

module Text.Regex.SmartConstructors {a e r} (P : Preorder a e r) where

open import Data.Empty
open import Data.List.Base using ([]; _∷_)
open import Data.List.Properties
open import Data.Sum.Base using (inj₁; inj₂; [_,_]′)
open import Function
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality hiding (preorder)

open import Text.Regex.Base P as R hiding (_∣_; _∙_; _⋆)

------------------------------------------------------------------------
-- Sum

infixr 5 _∣_

_∣_ : (e f : Exp) → Exp
e ∣ f with is-∅ e | is-∅ f
... | yes _ | _ = f
... | _ | yes _ = e
... | _ | _     = e R.∣ f

∣-sound : ∀ {w} e f → w ∈ (e ∣ f) → w ∈ (e R.∣ f)
∣-sound e f p with is-∅ e | is-∅ f
... | yes _ | _     = sum (inj₂ p)
... | no _  | yes _ = sum (inj₁ p)
... | no _  | no _  = p

∣-complete : ∀ {w} e f → w ∈ (e R.∣ f) → w ∈ (e ∣ f)
∣-complete e f pr@(sum p) with is-∅ e | is-∅ f
... | yes refl | _        = [ ⊥-elim ∘′ ∈⁻¹-∅ , id ]′ p
... | no _     | yes refl = [ id , ⊥-elim ∘′ ∈⁻¹-∅ ]′ p
... | no _     | no _     = pr

------------------------------------------------------------------------
-- Product

infixr 6 _∙_

_∙_ : (e f : Exp) → Exp
e ∙ f with is-∅ e | is-ε e | is-∅ f | is-ε f
... | yes _ | _ | _ | _ = R.∅
... | _ | yes _ | _ | _ = f
... | _ | _ | yes _ | _ = R.∅
... | _ | _ | _ | yes _ = e
... | _ | _ | _ | _ = e R.∙ f

∙-sound : ∀ {w} e f → w ∈ (e ∙ f) → w ∈ (e R.∙ f)
∙-sound e f p with is-∅ e | is-ε e | is-∅ f | is-ε f
... | yes refl | _        | _        | _        = ⊥-elim (∈⁻¹-∅ p)
... | no _     | yes refl | _        | _        = prod refl ε p
... | no _     | no _     | yes refl | _        = ⊥-elim (∈⁻¹-∅ p)
... | no _     | no _     | no _     | yes refl = prod (++-identityʳ _) p ε
... | no _     | no _     | no _     | no _     = p

∙-complete : ∀ {w} e f → w ∈ (e R.∙ f) → w ∈ (e ∙ f)
∙-complete e f pr@(prod eq p q) with is-∅ e | is-ε e | is-∅ f | is-ε f
... | yes refl | _        | _        | _        = ⊥-elim (∈⁻¹-∅ p)
... | no _     | yes refl | _        | _        = ∈⁻₁-ε∙f pr
... | no _     | no _     | yes refl | _        = ⊥-elim (∈⁻¹-∅ q)
... | no _     | no _     | no _     | yes refl = ∈⁻₁-e∙ε pr
... | no _     | no _     | no _     | no _     = pr


------------------------------------------------------------------------
-- Kleene star

infix  7 _⋆

_⋆ : Exp → Exp
e ⋆ with is-∅ e | is-ε e
... | yes _ | _ = R.ε
... | _ | yes _ = R.ε
... | _ | _ = e R.⋆

⋆-sound : ∀ {w} e → w ∈ (e ⋆) → w ∈ (e R.⋆)
⋆-sound e p with is-∅ e | is-ε e
... | yes refl | _        = star (sum (inj₁ p))
... | no _     | yes refl = star (sum (inj₁ p))
... | no _     | no _     = p

⋆-complete : ∀ {w} e → w ∈ (e R.⋆) → w ∈ (e ⋆)
⋆-complete e pr with is-∅ e | is-ε e
... | yes refl | no _     = ∈⁻¹-∅⋆ pr
... | no _     | yes refl = ∈⁻¹-ε⋆ pr
... | no _     | no _     = pr
