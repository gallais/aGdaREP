module Bindings.Arguments where

open import Data.List
open import Data.String
open import IO
import Bindings.Arguments.Primitive as Prim

getArgs : IO (List String)
getArgs = lift Prim.getArgs
