{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecPoset)

module Text.Regex.Search {a e r} (P? : DecPoset a e r) where

open import Level using (_⊔_)
open import Data.Bool.Base using (if_then_else_; true; false)
open import Data.Empty
open import Data.List.Base using (List; []; _∷_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function

open import Data.List.Relation.Binary.Prefix.Heterogeneous
  using (Prefix; []; _∷_) hiding (module Prefix)
open import Data.List.Relation.Binary.Infix.Heterogeneous
  using (Infix; here; there) hiding (module Infix)
import Data.List.Relation.Binary.Infix.Heterogeneous.Properties as Infixₚ
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Suffix.Heterogeneous
  using (Suffix; here; there) hiding (module Suffix)

open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary using (Rel; Decidable; _⇒_)
open import Relation.Binary.PropositionalEquality hiding (preorder)

open DecPoset P? using (preorder) renaming (Carrier to A)
open import Text.Regex.Base preorder
open import Text.Regex.Properties P?
open import Text.Regex.Derivative P?

------------------------------------------------------------------------
-- Type corresponding to a match

-- Users have control over whether the match should start at the beginning
-- or stop at the end. So we have a precise type of spans ensuring their
-- demands are respected
Span : ∀ {r} → Regex → Rel A r → Rel (List A) (a ⊔ r)
Span regex =
  if Regex.fromStart regex
  then if Regex.tillEnd regex
       then Pointwise
       else Prefix
  else if Regex.tillEnd regex
       then Suffix
       else Infix

-- All matches are selecting an infix sublist
toInfix : ∀ {r} {R : Rel A r} e → Span e R ⇒ Infix R
toInfix e with Regex.fromStart e | Regex.tillEnd e
... | true  | true  = Infixₚ.fromPointwise
... | true  | false = here
... | false | true  = Infixₚ.fromSuffix
... | false | false = id

-- A match is a list, a proof it matches the regular expression,
-- and a proof it is the right sort of sublist.
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

------------------------------------------------------------------------
-- Search algorithms

module Prefix where

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

  []ᴹ : ∀ {e acc xs} → [] ∈ e ⊎ [] ∈ acc → Match (Infix _≡_) xs e ⊎ Match (Prefix _≡_) xs acc
  []ᴹ (inj₁ p) = inj₁ (MkMatch [] p (here []))
  []ᴹ (inj₂ p) = inj₂ (MkMatch [] p [])

  []⁻¹ᴹ : ∀ {e acc} → Match (Infix _≡_) [] e ⊎ Match (Prefix _≡_) [] acc → [] ∈ e ⊎ [] ∈ acc
  []⁻¹ᴹ (inj₁ (MkMatch .[] []∈e (here []))) = inj₁ []∈e
  []⁻¹ᴹ (inj₂ (MkMatch .[] []∈acc []))      = inj₂ []∈acc

  step : ∀ {e acc} x {xs} → Match (Infix _≡_) xs e ⊎ Match (Prefix _≡_) xs (eat x (e ∣ acc)) →
                            Match (Infix _≡_) (x ∷ xs) e ⊎ Match (Prefix _≡_) (x ∷ xs) acc
  step x (inj₁ (MkMatch ys ys∈e p)) = inj₁ (MkMatch ys ys∈e (there p))
  step {e} {acc} x (inj₂ (MkMatch ys ys∈e p)) with eat-sound x (e ∣ acc) ys∈e
  ... | sum (inj₁ xys∈e) = inj₁ (MkMatch (x ∷ ys) xys∈e (here (refl ∷ p)))
  ... | sum (inj₂ xys∈e) = inj₂ (MkMatch (x ∷ ys) xys∈e (refl ∷ p))

  step⁻¹ : ∀ {e acc} x {xs} →
           ¬ ([] ∈ e) → ¬ ([] ∈ acc) →
           Match (Infix _≡_) (x ∷ xs) e ⊎ Match (Prefix _≡_) (x ∷ xs) acc →
           Match (Infix _≡_) xs e ⊎ Match (Prefix _≡_) xs (eat x (e ∣ acc))
  -- can't possibly be the empty match
  step⁻¹ x ¬[]∈e ¬[]∈acc (inj₁ (MkMatch .[] ys∈e (here []))) = ⊥-elim (¬[]∈e ys∈e)
  step⁻¹ x ¬[]∈e ¬[]∈acc (inj₂ (MkMatch .[] ys∈e []))        = ⊥-elim (¬[]∈acc ys∈e)
  -- if it starts 'there', it's an infix solution
  step⁻¹ x ¬[]∈e ¬[]∈acc (inj₁ (MkMatch ys ys∈e (there p))) = inj₁ (MkMatch ys ys∈e p)
  -- if it starts 'here' we're in prefix territory
  step⁻¹ {e} {acc} x ¬[]∈e ¬[]∈acc (inj₁ (MkMatch (.x ∷ ys) ys∈e (here (refl ∷ p))))
    = inj₂ (MkMatch ys (eat-complete x (e ∣ acc) (sum (inj₁ ys∈e))) p)
  step⁻¹ {e} {acc} x ¬[]∈e ¬[]∈acc (inj₂ (MkMatch (.x ∷ ys) ys∈e (refl ∷ p)))
    = inj₂ (MkMatch ys (eat-complete x (e ∣ acc) (sum (inj₂ ys∈e))) p)

  -- search non-deterministically: at each step, the `acc` regex is changed
  -- to accomodate the fact the match may be starting just now
  searchND : ∀ xs e acc → Dec (Match (Infix _≡_) xs e ⊎ Match (Prefix _≡_) xs acc)
  searchND xs e acc with []∈? e | []∈? acc
  ... | yes p | _     = yes ([]ᴹ (inj₁ p))
  ... | _     | yes q = yes ([]ᴹ (inj₂ q))
  searchND [] e acc | no ¬p | no ¬q = no ([ ¬p , ¬q ]′ ∘′ []⁻¹ᴹ)
  searchND (x ∷ xs) e acc | no ¬p | no ¬q
    = map′ (step x) (step⁻¹ x ¬p ¬q) (searchND xs e (eat x (e ∣ acc)))

  search : Decidable (Match (Infix _≡_))
  search xs e with searchND xs e ∅
  ... | no ¬p        = no (¬p ∘′ inj₁)
  ... | yes (inj₁ p) = yes p
  ... | yes (inj₂ p) = ⊥-elim (∈⁻¹-∅ (match p))

module Whole where

  []ᴹ : ∀ {e} → [] ∈ e → Match (Pointwise _≡_) [] e
  []ᴹ p = MkMatch [] p []

  []⁻¹ᴹ : ∀ {e} → Match (Pointwise _≡_) [] e → [] ∈ e
  []⁻¹ᴹ (MkMatch .[] p []) = p

  _∷ᴹ_ : ∀ {xs e} x → Match (Pointwise _≡_) xs (eat x e) → Match (Pointwise _≡_) (x ∷ xs) e
  x ∷ᴹ (MkMatch ys ys∈e\x ys≤xs) = MkMatch (x ∷ ys) (eat-sound x _ ys∈e\x) (refl ∷ ys≤xs)

  _∷⁻¹ᴹ_ : ∀ {xs e} x → Match (Pointwise _≡_) (x ∷ xs) e → Match (Pointwise _≡_) xs (eat x e)
  x ∷⁻¹ᴹ (MkMatch (._ ∷ ys) ys∈e (refl ∷ ys≤xs)) = MkMatch ys (eat-complete _ _ ys∈e) ys≤xs

  search : Decidable (Match (Pointwise _≡_))
  search [] e = map′ []ᴹ []⁻¹ᴹ ([]∈? e)
  search (x ∷ xs) e = map′ (x ∷ᴹ_) (x ∷⁻¹ᴹ_) (search xs (eat x e))

module Suffix where

  search : Decidable (Match (Suffix _≡_))
  search xs e with Whole.search xs e
  ... | yes p = yes (map here p)
  search []       e | no ¬p = no (¬p ∘′ map λ where (here p) → p)
  search (x ∷ xs) e | no ¬p with search xs e
  ... | yes q = yes (map there q)
  ... | no ¬q = no λ where
    (MkMatch ys ys∈e (here p))  → ¬p (MkMatch ys ys∈e p)
    (MkMatch ys ys∈e (there q)) → ¬q (MkMatch ys ys∈e q)

------------------------------------------------------------------------
-- Search for the user-specified span

search : ∀ xs e → Dec (Match (Span e _≡_) xs (Regex.expression e))
search xs e with Regex.fromStart e | Regex.tillEnd e
... | true  | true  = Whole.search    xs (Regex.expression e)
... | true  | false = Prefix.shortest xs (Regex.expression e)
... | false | true  = Suffix.search   xs (Regex.expression e)
... | false | false = Infix.search    xs (Regex.expression e)
