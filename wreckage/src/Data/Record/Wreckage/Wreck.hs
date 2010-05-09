{-# LANGUAGE NoMonomorphismRestriction,
             FlexibleContexts,
             FlexibleInstances,
             TypeFamilies,
             TypeOperators,
             MultiParamTypeClasses,
             ScopedTypeVariables,
             UndecidableInstances,
             RankNTypes,
             TemplateHaskell #-}
module Data.Record.Wreckage.Wreck(
    module Data.Record.Wreckage.Wreck,
    module Data.Record.Wreckage.Alphabet,
    module Data.Record.Wreckage.TShow,
    module Data.Record.Wreckage.Bool,
    module Data.Record.Wreckage.Product,
    module Data.Record.Wreckage.ProductSort) where

import Data.Record.Wreckage.ProductSort
import Control.Monad
import Data.Record.Wreckage.Bool
import Data.Record.Wreckage.Alphabet
import Data.Record.Wreckage.Nat
import Data.Record.Wreckage.TShow
import Data.Record.Wreckage.Product
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Debug.Trace

-- a data type for 'chaining' (composing) selectors
data a :- b = a :- b deriving Show

infixr 5 :-

newtype Selector s = Selector s

instance TStringVal s => Show (Selector s) where
    show (Selector _) = "[$m|" ++ tstringVal (undefined :: s) ++ "|]"

class TStringVal a where
   tstringVal :: a -> String

instance TStringVal () where
   tstringVal _ = []

instance (CharVal a,TStringVal b) => TStringVal (a :* b) where
   tstringVal _ = charVal (undefined :: a) : tstringVal (undefined :: b)

instance (TShow s) => TShow (Selector s) where
    tshow _ = "Selector (" ++ tshow (undefined :: s) ++ ")"

newtype ADTNode r a = ADTNode a deriving (Show)
newtype FieldNode s v = FieldNode v deriving (Show)

embiggen :: ADTWreck a => a -> ADTNode () a :* ()
embiggen x = ADTNode x :* ()

class WreckExtend a where
    type WreckExtendBase a
    extend :: a -> (s,v) -> FieldNode s v :* WreckExtendBase a

instance WreckExtend (h :* t) where
    type WreckExtendBase (h :* t) = (h :* t)
    extend r (s,v) = FieldNode v :* r

restrict r s = restriction (restricter r s) r s

class WreckRestricter op r s where
    type Restricted op r s
    restriction :: op ->  r -> s -> Restricted op r s

class WreckRestrictable r s where
    type RestricterT r s
    restricter :: r -> s -> RestricterT r s

addRestriction :: s -> ADTNode r a -> ADTNode (s :* r) a
addRestriction _ (ADTNode v) = ADTNode v

instance WreckRestricter HC (ADTNode r a :* b) s where
    type Restricted HC (ADTNode r a :* b) s = ADTNode (s :* r) a :* b
    restriction _ (x :* y) s = addRestriction s x :* y

instance WreckRestricter HC (FieldNode s1 v :* b) s where
    type Restricted HC (FieldNode s1 v :* b) s = b
    restriction _ (x :* y) _ = y

instance (WreckRestrictable b s,
          WreckRestricter (RestricterT b s) b s) =>
        WreckRestricter TC (a :* b) s where
    type Restricted TC (a :* b) s = a :* Restricted (RestricterT b s) b s
    restriction _ (x :* y) s = x :* restrict y s

instance WreckRestrictable (h :* t) s where
    type RestricterT (h :* t) s = Cond (HasSelector h s) HC TC
    restricter = undefined

type family HasSelector r s

type instance HasSelector (ADTNode r a) s = And (Not (Contains s r)) (Contains s (ADTWreckSelectorsType a))
type instance HasSelector (FieldNode (Selector s0) v) (Selector s1) = EqTLS s0 s1

type family Contains t tl
type instance Contains (Selector s) () = FALSE
type instance Contains (Selector s) (Selector t :* r) = Or (EqTLS t s) (Contains (Selector s) r)

get s r = nchooseG (nchooser r s) s r
set s r v = nchooseS (nchooser r s) s r v

class NodeChooser op r s where
    type Chosen op r s
    nchooseG :: op -> s -> r -> Chosen op r s
    nchooseS :: op -> s -> r -> Chosen op r s -> r

class NodeChoosable r s where
    type NodeChooserT r s
    nchooser :: r -> s -> NodeChooserT r s

data HC = HC
data TC = TC
data ID = ID

instance (NodeChooser (NodeChooserT h (Selector s)) h (Selector s),
          NodeChoosable h (Selector s)) =>
         NodeChooser HC (ADTNode r h :* t) (Selector s) where
    type Chosen HC (ADTNode r h :* t) (Selector s) = Chosen (NodeChooserT h (Selector s)) h (Selector s)
    nchooseG _ sel (ADTNode h :* t) = get sel h
    nchooseS _ sel (ADTNode h :* t) v = ADTNode (set sel h v) :* t

instance NodeChooser HC (FieldNode (Selector s1) v :* t) (Selector s) where
    type Chosen HC (FieldNode (Selector s1) v :* t) (Selector s) = v
    nchooseG _ sel (FieldNode v :* _) = v
    nchooseS _ sel (FieldNode v0 :* t) v = FieldNode v :* t

instance (NodeChoosable r s,
          NodeChooser (NodeChooserT r s) r s,
          NodeChoosable (Chosen (NodeChooserT r s) r s) ss,
          NodeChooser (NodeChooserT (Chosen (NodeChooserT r s) r s) ss) (Chosen (NodeChooserT r s) r s) ss) => 
        NodeChooser ID r (s :- ss) where
    type Chosen ID r (s :- ss) =
        Chosen (NodeChooserT (Chosen (NodeChooserT r s) r s) ss) (Chosen (NodeChooserT r s) r s) ss
    nchooseG _ (s :- ss) r = get ss (get s r)
    nchooseS _ (x :- xx) r v = set x r (set xx (get x r) v)

instance (NodeChoosable r l,
          NodeChooser (NodeChooserT r l) r l,
          NodeChooser (NodeChooserT r ll) r ll,
          NodeChoosable r ll) =>
        NodeChooser ID r (l :* ll) where
    type Chosen ID r (l :* ll) = Chosen (NodeChooserT r l) r l :* Chosen (NodeChooserT r ll) r ll
    nchooseG _ (l :* ll) r = get l r :* get ll r
    nchooseS _ (l :* ll) r (v0 :* v1) = set ll (set l r v0) v1 

instance (NodeChoosable t (Selector s),
          NodeChooser (NodeChooserT t (Selector s)) t (Selector s)) =>
         NodeChooser TC (h :* t) (Selector s) where
    type Chosen TC (h :* t) (Selector s) = Chosen (NodeChooserT t (Selector s)) t (Selector s)
    nchooseG _ s (h :* t) = get s t
    nchooseS _ s (h :* t) v = h :* set s t v

instance NodeChoosable (h :* t) (Selector s) where
    type NodeChooserT (h :* t) (Selector s) =
        Cond (HasSelector (h) (Selector s)) HC TC
    nchooser = undefined

instance NodeChoosable r (s :- ss) where
    type NodeChooserT r (s :- ss) = ID
    nchooser = undefined

instance NodeChoosable r (l :* ll) where
    type NodeChooserT r (l :* ll) = ID
    nchooser = undefined

class Taggable r t where
   type TaggedT r t
   tag :: r -> t -> TaggedT r t

instance Taggable r () where
    type TaggedT r () = ()
    tag _ _ = ()

instance (Selection r (Selector a), Taggable r b) => Taggable r ((Selector a,v) :* b) where
    type TaggedT r ((Selector a,v) :* b) = Tagged (SelectorIndex r (Selector a)) v :* TaggedT r b
    tag r ((_,v) :* b) = Tagged v :* tag r b

class Selection a b where
    type SelectorIndex a b

class ADTWreck a where
    type ADTWreckDefaultsType a
    type ADTWreckSelectorsType a
    defaults :: a -> ADTWreckDefaultsType a

selToType :: String -> Q Type
selToType cs = (conT $ ''Selector) `appT` (foldr appT (conT ''()) $ map f cs)
    where f c = (conT ''(:*)) `appT` (conT $ mkName $ "C" ++ show (fromEnum c))
selToType' :: String -> Type
selToType' cs = (ConT $ ''Selector) `AppT` (foldr AppT (ConT ''()) $ map f cs)
    where f c = (ConT ''(:*)) `AppT` (ConT $ mkName $ "C" ++ show (fromEnum c))

wreck :: Q [Dec] -> Q [Dec]
wreck = liftM (concatMap f)
    where f (DataD _ tnm [] [RecC dnm fs] ders) = 
              [mkData tnm dnm fs] ++
              [mkCon tnm dnm fs] ++
              [mkADTRec tnm dnm fs] ++
              [mkWreckExtend tnm] ++
              mkNCInsts tnm dnm fs ++
              zipWith (mkSelectionInst tnm) [0..] fs ++
              -- ddInstances tnm dnm fs ++
              mkChoosables tnm fs
          nat i = foldr AppT (ConT ''Zero) $ replicate i (ConT ''Succ)
          lastT = ConT ''()
          prodT = ConT ''(:*)
          applyT = foldr AppT
          undefinedV = VarE 'undefined
          selNmToType fnm = selToType' $ fst $ break (=='\'') (nameBase fnm)
          mkData tnm dnm fs = DataD [] tnm [] [(NormalC dnm (map (\ (_,s,t) -> (s,t)) fs))] [''Show]
          mkWreckExtend tnm = InstanceD [] (ConT ''WreckExtend `AppT` ConT tnm) [
                  TySynInstD ''WreckExtendBase [ConT tnm] (prodT `AppT` (ConT ''ADTNode `AppT` lastT `AppT` ConT tnm) `AppT` lastT),
                  FunD 'extend [Clause [VarP rnm,TupP [VarP snm,VarP vnm]]
                      (NormalB $ ConE '(:*) `AppE` (ConE 'FieldNode `AppE` VarE vnm)
                          `AppE` (VarE 'embiggen `AppE` VarE rnm)) []]
              ]
              where rnm = mkName "r"
                    snm = mkName "s"
                    vnm = mkName "v"
          mkSelectionInst tnm i (fnm,_,_) = 
             InstanceD [] (ConT ''Selection `AppT` ConT tnm `AppT` selNmToType fnm)
                 [TySynInstD ''SelectorIndex [ConT tnm, selNmToType fnm] indexT]
             where indexT = nat i
          mkChoosables tnm fs =  map (mkChoosable tnm) fs
          mkChoosable tnm (s,_,_) = InstanceD [] ((ConT $ ''NodeChoosable) `AppT` rt `AppT` st)
              [ -- the associated type (NodeChooserT)
               TySynInstD ''NodeChooserT [rt,st] (ConT ''ID),
               ValD (VarP 'nchooser) (NormalB undefinedV) []
              ]
              where st = selToType' $ nameBase s
                    rt = ConT tnm
          mkNCInsts tcnm dcnm fs = zipWith (mkNCInst (length fs) tcnm dcnm) [0..] fs
          mkNCInst k tcnm dcnm i (fn,_,t) =
              InstanceD [] ((ConT $ ''NodeChooser) `AppT` (ConT ''ID) `AppT` tct `AppT` st)
                [ TySynInstD ''Chosen [ConT ''ID,tct,st] t,
                  FunD 'nchooseG [Clause [WildP,WildP,ConP dcnm $ take k nameVarPs] (NormalB ve) []],
                  FunD 'nchooseS [Clause [WildP,WildP,ConP dcnm $ take k nameVarPs, nvp] (NormalB conExpr) []]]
              where st = selNmToType fn
                    tct = ConT tcnm
                    names = map (mkName . ("v" ++) . show) [0..]
                    nameVarPs = xs ++ vp:ys where (xs,y:ys) = splitAt i $ map VarP names
                    nameVarEs = xs ++ nve:ys where (xs,y:ys) = splitAt i $ map VarE names
                    (vp,ve) = (VarP val, VarE val) where val = mkName "val"
                    (nvp,nve) = (VarP val, VarE val) where val = mkName "newVal"
                    conExpr = foldl AppE (ConE dcnm) $ take k nameVarEs
          mkADTRec tnm dnm fs = InstanceD [] (ConT ''ADTWreck `AppT` ConT tnm) 
                  [ TySynInstD ''ADTWreckDefaultsType targs dt,
                    TySynInstD ''ADTWreckSelectorsType targs st,
                    FunD 'defaults [Clause [WildP] (NormalB dv) []]
                  ]
              where targs = [ConT tnm]
                    nonStricts = [ (i,t) | (i,(_,NotStrict,t)) <- zip [0..] fs]
                    dt = applyT lastT (map (\ (i,t) -> prodT `AppT` (ConT ''Tagged `AppT` nat i `AppT` t)) nonStricts)
                    st = applyT lastT (map (\ (fnm,_,_) -> prodT `AppT` selNmToType fnm) fs)
                    dv = foldr AppE (ConE '()) (map (const (ConE '(:*) `AppE` undefinedV)) nonStricts)
          mkCon tnm dnm fs = FunD fnm [Clause [vp] (NormalB (mk `AppE` mergeE )) decs]
              where fnm = mkName $ "mk" ++ nameBase dnm
                    mknm = mkName "mk"
                    mk = VarE mknm
                    (vp,ve) = (VarP v, VarE v) where v = mkName "val"
                    mergeE = VarE 'merge `AppE` sortE `AppE` defaultsE
                    sortE = VarE 'sort `AppE` tagE
                    defaultsE = VarE 'defaults `AppE` r1E
                    tagE = VarE 'tag `AppE` r1E `AppE` ve
                    r1E = SigE undefinedV (ConT tnm)
                    nfs = length fs
                    tvnms = take nfs $ map (mkName . ("b" ++) . show) [0..]
                    vnms = take nfs $ map (mkName . ("v" ++) . show) [0..]
                    taggedTs = zipWith (\ (fn,_,t) (vnm) -> ConT ''Tagged `AppT` (VarT vnm) `AppT` t) fs tvnms
                    argT = (applyT (lastT) $ map f taggedTs) where f t = (prodT) `AppT` t
                    mkT = ForallT (map PlainTV tvnms) [] (ConT ''(->) `AppT` argT `AppT` (ConT tnm))
                    decs = [SigD mknm mkT,
                            FunD mknm [Clause [argP] (NormalB (bodyE)) []]]
                    bodyE = foldl (\ x y -> AppE x (VarE y)) (ConE dnm) vnms
                    argP = foldr g (ConP '() []) taggedPs
                        where g :: Pat -> Pat -> Pat
                              g t r = ConP '(:*) [t,r]
                              taggedPs = map (\ nm -> ConP 'Tagged [VarP nm]) vnms

selToExp :: String -> Q Exp
selToExp cs = return (ConE 'Selector `AppE` (foldr AppE (ConE '()) $ map f cs))
   where f c = (ConE '(:*)) `AppE` (ConE $ mkName $ "C" ++ show (fromEnum c))

selToPat :: String -> Q Pat
selToPat _ = fail "sorry, unimplemented"

m = QuasiQuoter selToExp selToPat

(=:) = (,)

infixl 7 =: