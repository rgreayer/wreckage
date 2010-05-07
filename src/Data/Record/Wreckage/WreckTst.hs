{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators, FlexibleInstances,
             MultiParamTypeClasses, QuasiQuotes, ViewPatterns #-}
module Data.Record.Wreckage.WreckTst where

import Data.Record.Wreckage.Wreck
import Language.Haskell.TH

wreck [d|data Rec1 = Rec1 {
    w :: !Int,
    x :: Double,
    y :: String } deriving (Show)|]

wreck [d|data Rec2 = Rec2 {
    x :: Rec1,
    y :: Int,
    z :: String } deriving (Show)|]

wreck [d|
        data Rec3 = Rec3 {
            name :: String,
            weight :: Int,
            height :: Int
            }
          |]

r1 = mkRec1 (ℓw =: 1 :* ℓx =: 2 :* ℓy =: "r1" :* ())

r1' = mkRec1 (ℓw =: 2 :* ℓy =: "r1" :* ())
r3 = mkRec3 (ℓweight =: 1 :* ℓname =: "x" :* ℓheight =: 2 :* ())

r2 = mkRec2 (ℓx =: r1 :* ℓy =: 2 :* ℓz =: "r2" :* ())

foo = get ℓx r2
ffoo = get (ℓx :- ℓw) r2
bar = get (ℓx :- ℓy :* ℓw) r2

er1 = r1 `extend` (ℓf =: 10)

xer1 = get ℓx er1

rxer1 = er1 `restrict` ℓf

look (get (ℓx:*ℓy) -> (x:*y)) = show y ++ show x
r1ish r@(get ℓx -> x) = (r,x)