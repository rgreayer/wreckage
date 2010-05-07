{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
module Data.Record.Wreckage.Product where

import Data.Record.Wreckage.TShow

data (:*) a b = a :* b deriving (Show,Eq)

infixr 6 :*

instance (TShow a, TShow b) => TShow (a :* b) where
    tshow _ = tshow (undefined :: a) ++ " :* " ++ tshow (undefined :: b)