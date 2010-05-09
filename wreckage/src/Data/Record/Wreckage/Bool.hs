{-# LANGUAGE TypeFamilies #-}
module Data.Record.Wreckage.Bool where

data TRUE = TRUE deriving Show
data FALSE = FALSE deriving Show

type family Or x y
type instance Or TRUE TRUE = TRUE
type instance Or TRUE FALSE = TRUE
type instance Or FALSE TRUE = TRUE
type instance Or FALSE FALSE = FALSE

type family And x y
type instance And TRUE TRUE = TRUE
type instance And TRUE FALSE = FALSE
type instance And FALSE TRUE = FALSE
type instance And FALSE FALSE = FALSE

type family Cond p a b

type instance Cond TRUE a b = a
type instance Cond FALSE a b = b

type family Not x
type instance Not TRUE = FALSE
type instance Not FALSE = TRUE


