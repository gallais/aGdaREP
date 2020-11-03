module Bindings.Arguments.Primitive where

open import IO.Primitive
open import Data.List
open import Data.String

{-# FOREIGN GHC import qualified System.Environment as SE #-}
{-# FOREIGN GHC import qualified Data.Text          as T  #-}

postulate
  getArgs : IO (List String)

{-# COMPILE GHC getArgs = fmap (fmap T.pack) SE.getArgs #-}
