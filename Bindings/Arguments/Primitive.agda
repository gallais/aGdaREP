module Bindings.Arguments.Primitive where

open import IO.Primitive
open import Data.List
open import Data.String

{-# IMPORT System.Environment #-}

postulate
  getArgs : IO (List String)

{-# COMPILED getArgs System.Environment.getArgs #-}