{-# LANGUAGE StrictData #-}
module F.Type where

import Data.Text (Text)

type Info = ()

data Type
  -- primitive
  = TyBool
  -- constructors
  | TyVar Int Int     -- type variable
  | TyArr Type Type   -- type of functions
  | TyAll Text Type   -- universal type
  | TySome Text Type  -- existential type
  deriving (Eq, Show)



data Term
  = Var Info Text                     -- variable
  | Abs Info Text Type Term           -- abstraction
  | App Info Term Term                -- application
-- type stuff
  | TAbs Info Text Term               -- type abstraction
  | TApp Info Term Type               -- type application
  | TPack Info Type Term Type         -- packing
  | TUnpack Info Text Text Term Term  -- unpacking
  deriving (Eq, Show)
