module aGdaREP where

open import Level
open import Coinduction
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Char   as Chr
open import Data.String as Str
open import Data.List   as List
open import Data.Maybe  as Maybe

open import Function
open import Relation.Nullary
open import lib.Nullary

import Search
module S = Search Char Chr._≟_
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
parse (e ∷ f ∷ es) (')' ∷ xs)       = parse ((λ g → f (e ε `∙ g)) ∷ es) xs
parse (e ∷ es)     ('.' ∷ '?' ∷ xs) = parse ((λ f → e (─ ⁇ `∙ f)) ∷ es) xs
parse (e ∷ es)     ('.' ∷ '*' ∷ xs) = parse ((λ f → e (─ `⋆ `∙ f)) ∷ es) xs
parse (e ∷ es)     ('.' ∷ xs)       = parse ((λ f → e (─ `∙ f)) ∷ es) xs
parse (e ∷ es)     (a   ∷ '?' ∷ xs) = parse ((λ f → e (RE.[ a ] ⁇ `∙ f)) ∷ es) xs
parse (e ∷ es)     (a   ∷ '*' ∷ xs) = parse ((λ f → e (RE.[ a ] `⋆ `∙ f)) ∷ es) xs
parse (e ∷ es)     (a   ∷ xs)       = parse ((λ f → e (RE.[ a ] `∙ f)) ∷ es) xs

parseRegExp : String → RegExp ⊎ Error
parseRegExp = parse (id ∷ []) ∘ Str.toList

FilePath : Set
FilePath = String

record grepOptions : Set where
  field
    -V     : Bool
    -v     : Bool
    -i     : Bool
    regexp : Maybe String
    files  : List FilePath
open grepOptions public

module myCharBase where

  {-# IMPORT GHC.Unicode #-}

  postulate
    toLower : Char → Char
    toUpper : Char → Char
  
  {-# COMPILED toLower GHC.Unicode.toLower #-}
  {-# COMPILED toUpper GHC.Unicode.toUpper #-}

IgnoreCase : RegExp → RegExp
IgnoreCase ∅       = ∅
IgnoreCase ε       = ε
IgnoreCase ─       = ─
IgnoreCase [ a ]   = S.[ myCharBase.toUpper a ] ∣ S.[ myCharBase.toLower a ]
IgnoreCase (e ∣ f) = IgnoreCase e ∣ IgnoreCase f
IgnoreCase (e ∙ f) = IgnoreCase e ∙ IgnoreCase f
IgnoreCase (e ⋆)   = IgnoreCase e ⋆

select : grepOptions → RegExp → String → Maybe String
select opt e str = dec (substring match target) ifYes ifNo
  where
    match : RegExp
    match = (if -i opt then IgnoreCase else id) e

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
import IO.Primitive      as Prim
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

module myPrimIO where

  {-# IMPORT System.Environment #-}

  postulate
    getArgs : Prim.IO (List String)

  {-# COMPILED getArgs System.Environment.getArgs #-}

getArgs : IO (List String)
getArgs = lift myPrimIO.getArgs

usage : IO ⊤
usage = IO.putStrLn "Usage: aGdaREP [OPTIONS] regexp [filename]"


defaultGrepOptions : grepOptions
defaultGrepOptions = record { -V = false ; -v = false ; -i = false ; regexp = nothing ; files = [] }

set-v : grepOptions → grepOptions
set-v opt = record { -V = -V opt ; -v = true ; -i = -i opt ; regexp = regexp opt ; files = files opt }

set-V : grepOptions → grepOptions
set-V opt = record { -V = true ; -v = -v opt ; -i = -i opt ; regexp = regexp opt ; files = files opt }

set-i : grepOptions → grepOptions
set-i opt = record { -V = -V opt ; -v = -v opt ; -i = true ; regexp = regexp opt ; files = files opt }

set-regexp : String → grepOptions → grepOptions
set-regexp str opt = record { -V = -V opt ; -v = -v opt ; -i = -i opt ; regexp = just str ; files = files opt }

set-files : List FilePath → grepOptions → grepOptions
set-files fps opt = record { -V = -V opt ; -v = -v opt ; -i = -i opt ; regexp = regexp opt ; files = fps }

add-file : FilePath → grepOptions → grepOptions
add-file fp opt = set-files (fp ∷ files opt) opt

parseOptions : List String → grepOptions
parseOptions args = set-files (List.reverse $ files result) result
  where
    cons : grepOptions → String → grepOptions
    cons opt "-v" = set-v opt
    cons opt "-V" = set-V opt
    cons opt "-i" = set-i opt
    cons opt str  =
      if is-nothing (regexp opt)
      then set-regexp str opt
      else add-file str opt

    result : grepOptions
    result = List.foldl cons defaultGrepOptions args

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