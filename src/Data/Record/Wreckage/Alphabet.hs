{-# LANGUAGE TemplateHaskell, TypeOperators, FlexibleInstances, TypeFamilies,
             ScopedTypeVariables, UndecidableInstances #-}
module Data.Record.Wreckage.Alphabet where

import Data.Record.Wreckage.Nat
import Data.Record.Wreckage.Bool
import Data.Record.Wreckage.TShow
import Data.Record.Wreckage.Product
import Data.Char.Properties
import Language.Haskell.TH


data LTT = LTT
data EQT = EQT
data GTT = GTT

type family ORDLT x
type instance ORDLT LTT = TRUE
type instance ORDLT EQT = FALSE
type instance ORDLT GTT = FALSE
type family ORDGT x
type instance ORDGT LTT = FALSE
type instance ORDGT EQT = FALSE
type instance ORDGT GTT = TRUE

type family LTTLC c0 c1
type instance LTTLC c0 c1 = ORDLT (CmpTLC c0 c1)

type family CmpD d0 d1
type family CmpLD l0 l1
type family CmpLD' l0 l1 -- compare digit lists of the same length

type family CmpTLC c0 c1

type instance CmpTLC c0 c1 = CmpLD (TypeNameIndex c0) (TypeNameIndex c1)

type instance CmpLD' () () = EQT
type instance CmpLD' (d0 :* d0s) (d1 :* d1s) = 
    Cond (EqD d0 d1) (CmpLD' d0s d1s) (CmpD d0 d1)

type instance CmpLD ld0 ld1 = 
    Cond (PNGT (LenP ld0) (LenP ld1)) 
        (CmpLD' ld0 (PadLD (PNMinus (LenP ld0) (LenP ld1)) ld1))
        (CmpLD' (PadLD (PNMinus (LenP ld1) (LenP ld0)) ld0) ld1)

type family PadLD n l
type instance PadLD Zero l = l
type instance PadLD (Succ n) l = PadLD n (D0 :* l)

type family LenP p
type instance LenP () = Zero
type instance LenP (x :* y) = Succ (LenP y)

type family EqD d0 d1   -- equivalence over type level digits
type family EqTLC c0 c1 -- equivalence over type level characters
type family EqLD l0 l1  -- equivalence over lists of type level digits
type family EqTLS s0 s1 -- equivalence over type level strings

type instance EqLD () () = TRUE
type instance EqLD (d0 :* d0s) (d1 :* d1s) = And (EqD d0 d1) (EqLD d0s d1s)

type instance EqTLS () () = TRUE
type instance EqTLS (c0 :* c0s) (c1 :* c1s) = And (EqTLC c0 c1) (EqTLS c0s c1s)

-- type level digits
data D0 = D0 deriving Show
data D1 = D1 deriving Show
data D2 = D2 deriving Show
data D3 = D3 deriving Show
data D4 = D4 deriving Show
data D5 = D5 deriving Show
data D6 = D6 deriving Show
data D7 = D7 deriving Show
data D8 = D8 deriving Show
data D9 = D9 deriving Show

type family TypeNameIndex t

let f (x,y) = tySynInstD ''EqD [mkCon x, mkCon y] (conT (if x == y then ''TRUE else ''FALSE))
    mkCon i = conT (mkName $ "D" ++ show i) in sequence $ map f [(x,y) | x <- [0..9], y <- [0..9]]
let f (x,y) = tySynInstD ''CmpD [mkCon x, mkCon y]
        (conT $ case compare x y of
             LT -> ''LTT
             EQ -> ''EQT
             GT -> ''GTT)
    mkCon i = conT (mkName $ "D" ++ show i) in sequence $ map f [(x,y) | x <- [0..9], y <- [0..9]]


type instance EqTLC c0 c1 = EqLD (TypeNameIndex c0) (TypeNameIndex c1)

class CharVal a where
    charVal :: a -> Char

let f i = [ dataD (return []) (nm i) [] [normalC (nm i) []] [], mkTyInst i, mkTShowInst i, mkCharValInst i]
    nm i = mkName ("C" ++ show (fromEnum i))
    mkTyInst c = tySynInstD ''TypeNameIndex [conT $ nm i]
              (foldr (\ l r -> (appT (appT (conT ''(:*)) l) r)) (conT ''()) cons)
        where i = fromEnum c
              cons = map (conT . mkName) (digits i)
    mkTShowInst c = instanceD (return []) (conT ''TShow `appT` conT (nm c))
        [funD 'tshow [clause [wildP] (normalB (stringE $ ("C" ++ show (fromEnum c)))) []]]
    mkCharValInst c = instanceD (return []) (conT ''CharVal `appT` conT (nm c))
        [funD 'charVal [clause [wildP] (normalB (litE $ charL c)) []]]
    digits 0 = ["D0"]
    digits n = reverse $ dig n
        where dig 0 = []
              dig n = ("D" ++ show (n `mod` 10)) : dig (n `div` 10)
    in sequence $ concatMap f $ '\'':[ c | c <- [minBound .. toEnum 1000], isIDStart c || isIDContinue c ]

instance TShow D0 where
    tshow _ = "D0"
instance TShow D1 where
    tshow _ = "D1"
instance TShow D2 where
    tshow _ = "D2"
instance TShow D3 where
    tshow _ = "D3"
instance TShow D4 where
    tshow _ = "D4"
instance TShow D5 where
    tshow _ = "D5"
instance TShow D6 where
    tshow _ = "D6"
instance TShow D7 where
    tshow _ = "D7"
instance TShow D8 where
    tshow _ = "D8"
instance TShow D9 where
    tshow _ = "D9"

instance TShow TRUE where
    tshow _ = "TRUE"
instance TShow FALSE where
    tshow _ = "FALSE"

ff :: LTTLC C122 C110
ff = undefined