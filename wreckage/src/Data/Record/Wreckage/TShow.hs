{-# LANGUAGE FlexibleInstances, ScopedTypeVariables #-}
module Data.Record.Wreckage.TShow where

class TShow t where
    tshow :: t -> String

instance TShow [Char] where
    tshow _ = "String"

instance TShow Int where
    tshow _ = "Int"

instance TShow Double where
    tshow _ = "Double"

instance TShow () where
    tshow _ = "()"

instance (TShow a, TShow b) => TShow (a,b) where
    tshow _ = "(" ++ tshow (undefined :: a) ++ "," ++ tshow (undefined :: b) ++ ")"

