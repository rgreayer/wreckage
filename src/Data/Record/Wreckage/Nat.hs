{-# LANGUAGE EmptyDataDecls, TypeFamilies, UndecidableInstances,
             ScopedTypeVariables, OverlappingInstances, TypeOperators,
             FlexibleInstances, NoMonomorphismRestriction #-}
module Data.Record.Wreckage.Nat where

import Data.Record.Wreckage.Bool

data Zero
data Succ a

type family PNEq x y
type instance PNEq Zero Zero = TRUE
type instance PNEq (Succ n) Zero = FALSE
type instance PNEq Zero (Succ n) = FALSE
type instance PNEq (Succ n) (Succ m) = PNEq n m

type family PNGT x y
type instance PNGT Zero Zero = FALSE
type instance PNGT (Succ n) Zero = TRUE
type instance PNGT Zero (Succ n) = FALSE
type instance PNGT (Succ n) (Succ m) = PNGT n m

type family PNLT x y
type instance PNLT Zero Zero = FALSE
type instance PNLT (Succ n) Zero = FALSE
type instance PNLT Zero (Succ n) = TRUE
type instance PNLT (Succ n) (Succ m) = PNLT n m

type family PNMinus x y
type instance PNMinus n Zero = n
type instance PNMinus (Succ n) (Succ m) = PNMinus n m
