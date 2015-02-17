module Bindings.Char where

open import Data.Char

{-# IMPORT GHC.Unicode #-}

postulate
  toLower : Char → Char
  toUpper : Char → Char
  
{-# COMPILED toLower GHC.Unicode.toLower #-}
{-# COMPILED toUpper GHC.Unicode.toUpper #-}