module aGdaREP.Options where

open import Data.Bool
open import Data.Maybe
open import Data.String
open import Data.List
open import Function

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

defaultGrepOptions : grepOptions
defaultGrepOptions =
  record { -V     = false
         ; -v     = false
         ; -i     = false
         ; regexp = nothing
         ; files  = [] }

parseOptions : List String → grepOptions
parseOptions args = record result { files = reverse $ files result }
  where
    cons : grepOptions → String → grepOptions
    cons opt "-v" = record opt { -v = true }
    cons opt "-V" = record opt { -V = true }
    cons opt "-i" = record opt { -i = true }
    cons opt str  =
      if is-nothing (regexp opt)
      then record opt { regexp = just str }
      else record opt { files  = str ∷ files opt }

    result : grepOptions
    result = foldl cons defaultGrepOptions args