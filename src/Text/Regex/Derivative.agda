{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecPoset)

module Text.Regex.Derivative {a e r} (P? : DecPoset a e r) where

open import Data.Empty
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Properties
open import Data.Sum.Base as Sum

open import Function
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; cong)

open DecPoset P? using (preorder) renaming (Carrier to A)
open import Text.Regex.Base preorder as R hiding (_∣_; _∙_; _⋆)
open import Text.Regex.Properties P?
open import Text.Regex.SmartConstructors preorder

------------------------------------------------------------------------
-- Action of characters on regular expressions

private
  decToExp : ∀ {p} {P : Set p} → Dec P → Exp
  decToExp (yes _) = ε
  decToExp (no _)  = ∅

eat : A → Exp → Exp
eat a ε         = ∅
eat a [ rs ]    = decToExp ((a ∷ []) ∈?[ rs ])
eat a [^ rs ]   = decToExp ((a ∷ []) ∈?[^ rs ])
eat a (e R.∣ f) = eat a e ∣ eat a f
eat a (e R.∙ f) = case []∈? e of λ where
  (yes _) → (eat a e ∙ f) ∣ (eat a f)
  (no ¬p) → eat a e ∙ f
eat a (e R.⋆)   = eat a e ∙ (e ⋆)

eat-sound : ∀ x {xs} e → xs ∈ eat x e → (x ∷ xs) ∈ e
eat-sound x ε         pr = ⊥-elim (∈⁻¹-∅ pr)
eat-sound x [ rs ]    pr with (x ∷ []) ∈?[ rs ]
... | yes p = case pr of λ where ε → p
... | no _  = ⊥-elim (∈⁻¹-∅ pr)
eat-sound x [^ rs ]   pr with (x ∷ []) ∈?[^ rs ]
... | yes p = case pr of λ where ε → p
... | no _  = ⊥-elim (∈⁻¹-∅ pr)
eat-sound x (e R.∣ f) pr with ∣-sound (eat x e) (eat x f) pr
... | sum pr′ = sum $ Sum.map (eat-sound x e) (eat-sound x f) pr′
eat-sound x (e R.∙ f) pr with []∈? e
... | yes []∈e with ∣-sound (eat x e ∙ f) (eat x f) pr
... | sum (inj₂ pr') = prod refl []∈e (eat-sound x f pr')
... | sum (inj₁ pr') with ∙-sound (eat x e) f pr'
... | prod eq p q = prod (cong (x ∷_) eq) (eat-sound x e p) q
eat-sound x (e R.∙ f) pr | no ¬p with ∙-sound (eat x e) f pr
... | prod eq p q = prod (cong (x ∷_) eq) (eat-sound x e p) q
eat-sound x (e R.⋆) pr with ∙-sound (eat x e) (e ⋆) pr
... | prod eq p q =
  star (sum (inj₂ (prod (cong (x ∷_) eq) (eat-sound x e p) (⋆-sound e q))))

eat-complete :  ∀ x {xs} e → (x ∷ xs) ∈ e → xs ∈ eat x e
eat-complete x [ rs ] [ pr ] with (x ∷ []) ∈?[ rs ]
... | yes p = ε
... | no ¬p = ⊥-elim (¬p [ pr ])
eat-complete x [^ rs ] [^ pr ] with (x ∷ []) ∈?[^ rs ]
... | yes p = ε
... | no ¬p = ⊥-elim (¬p [^ pr ])
eat-complete x (e R.∣ f) (sum pr) =
  ∣-complete (eat x e) (eat x f) $ sum $
  Sum.map (eat-complete x e) (eat-complete x f) pr
eat-complete x (e R.∙ f) (prod {v} eq p q) with []∈? e
eat-complete x (e R.∙ f) (prod {[]} eq p q) | no []∉e = ⊥-elim ([]∉e p)
eat-complete x (e R.∙ f) (prod {_ ∷ _} refl p q) | no []∉e =
  ∙-complete (eat x e) f (prod refl (eat-complete x e p) q)
eat-complete x (e R.∙ f) (prod {[]} refl p q) | yes []∈e =
  ∣-complete (eat x e ∙ f) (eat x f) $ sum $ inj₂ $
  eat-complete x f q
eat-complete x (e R.∙ f) (prod {_ ∷ _} refl p q) | yes []∈e =
  ∣-complete (eat x e ∙ f) (eat x f) $ sum $ inj₁ $
  ∙-complete (eat x e) f (prod refl (eat-complete x e p) q)
eat-complete x (e R.⋆) (star (sum (inj₂ (prod {[]} refl p q)))) =
  eat-complete x (e R.⋆) q
eat-complete x (e R.⋆) (star (sum (inj₂ (prod {_ ∷ _} refl p q)))) =
  ∙-complete (eat x e) (e ⋆) $ prod refl (eat-complete x e p) $
  ⋆-complete e q
