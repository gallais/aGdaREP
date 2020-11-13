module aGdaREP.Options where

open import Data.Bool
open import Data.Maybe
open import Data.String
open import Data.List
open import Function

FilePath : Set
FilePath = String

record Options : Set where
  field
    -V     : Bool
    -h     : Bool
    -v     : Bool
    -i     : Bool
    regexp : Maybe String
    files  : List FilePath
open Options public

defaultOptions : Options
defaultOptions =
  record { -V     = false
         ; -h     = false
         ; -v     = false
         ; -i     = false
         ; regexp = nothing
         ; files  = [] }

parse : List String → Options
parse args = record result { files = reverse $ files result }
  where
    cons : Options → String → Options
    cons opt "-V" = record opt { -V = true }
    cons opt "-h" = record opt { -h = true }
    cons opt "-v" = record opt { -v = true }
    cons opt "-i" = record opt { -i = true }
    cons opt str  =
      if is-nothing (regexp opt)
      then record opt { regexp = just str }
      else record opt { files  = str ∷ files opt }

    result : Options
    result = foldl cons defaultOptions args

usage : String
usage = unlines
 $ "Usage: aGdaREP [OPTIONS] PATTERN [FILENAME]"
 ∷ ""
 ∷ "OPTIONS:"
 ∷ "  -h  Print this help"
 ∷ "  -V  Version"
 ∷ "  -v  Invert the match"
 ∷ "  -i  Ignore case"
 ∷ []
