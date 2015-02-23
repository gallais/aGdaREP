module aGdaREP where

open import Level
open import Coinduction
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Char     as Chr
open import Data.String   as Str
open import Data.List     as List
open import Data.Maybe    as Maybe

open import Bindings.Char
open import Bindings.Arguments

open import Function
open import Relation.Nullary
open import lib.Nullary

open import RegExp.Parse
open import aGdaREP.Options
open S

ignoreCaseRanges : List Range → List Range
ignoreCaseRanges = List.foldr (List._++_ ∘ ignoreCase) []
  where
    ignoreCase : Range → List Range
    ignoreCase (exact a)     = exact (toLower a) ∷ exact (toUpper a) ∷ []
    ignoreCase (range lb ub) = range (toLower lb) (toLower ub) ∷ range (toUpper lb) (toUpper ub) ∷ []

ignoreCase : RegExp → RegExp
ignoreCase ∅       = ∅
ignoreCase ε       = ε
ignoreCase [ a ]   = S.[  ignoreCaseRanges a ]
ignoreCase [^ a ]  = S.[^ ignoreCaseRanges a ]
ignoreCase (e ∣ f) = ignoreCase e ∣ ignoreCase f
ignoreCase (e ∙ f) = ignoreCase e ∙ ignoreCase f
ignoreCase (e ⋆)   = ignoreCase e ⋆

select : grepOptions → RegExp → String → Maybe String
select opt e str = dec (substring match target) ifYes ifNo
  where
    match : RegExp
    match = (if -i opt then ignoreCase else id) e

    target : List Char
    target = Str.toList str

    grab : Substring match target → String
    grab (ss , ts , us , _ , _) =
        Str.fromList $ ss List.++ Str.toList "\x1B[1m\x1B[31m"
                          List.++ ts
                          List.++ Str.toList "\x1B[0m"
                          List.++ us

    ifYes = if -v opt then const nothing    else (just ∘′ grab)
    ifNo  = if -v opt then const (just str) else const nothing

open import IO           as IO
open import Data.Colist  as Colist

breakOn : {A : Set} (P? : A → Bool) (xs : List A) → List (List A)
breakOn {A} P? = uncurry _∷_ ∘ foldr step ([] , [])
  where
    step : A → (List A × List (List A)) → (List A × List (List A))
    step a (xs , xss) = if (P? a) then [] , xs ∷ xss else a ∷ xs , xss

lines : String → List String
lines = List.map Str.fromList ∘ breakOn isNewLine ∘ Str.toList
  where
    isNewLine : Char → Bool
    isNewLine y = dec (y Chr.≟ '\n') (const true) (const false)

usage : IO ⊤
usage = IO.putStrLn "Usage: aGdaREP [OPTIONS] regexp [filename]"

display : FilePath → String → String
display fp str = "\x1B[35m" Str.++ fp Str.++ "\x1B[36m:\x1B[0m" Str.++ str

grep : grepOptions → RegExp → List FilePath → IO ⊤
grep opt reg []        = return tt
grep opt reg (fp ∷ xs) = 
  ♯ IO.readFiniteFile fp >>= λ content →
  ♯ (♯ (IO.mapM′ (maybe (putStrLn ∘ display fp) (return tt))
       $ Colist.fromList
       $ List.map (select opt reg)
       $ lines content) >>
       ♯ (grep opt reg xs))

main : _
main =
  IO.run $
  ♯ getArgs >>= λ args →
    ♯ let options = parseOptions args in
      if -V options
      then putStrLn "aGdaREP: version 0.1"
      else case Maybe.map parseRegExp (regexp options) of λ
             { nothing         → usage
             ; (just (inj₂ e)) → putStrLn ("*** Error: invalid regexp (" Str.++ showError e Str.++ ")")
             ; (just (inj₁ r)) → grep options r (files options) }