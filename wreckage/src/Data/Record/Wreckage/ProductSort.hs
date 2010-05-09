{-# LANGUAGE EmptyDataDecls, TypeFamilies, UndecidableInstances,
             ScopedTypeVariables, OverlappingInstances, TypeOperators,
             FlexibleInstances, NoMonomorphismRestriction,
             MultiParamTypeClasses #-}
module Data.Record.Wreckage.ProductSort where

import Data.Record.Wreckage.Nat
import Data.Record.Wreckage.Bool
import Data.Record.Wreckage.TShow
import Data.Record.Wreckage.Product

instance TShow Zero where
    tshow _ = "Zero"

instance (TShow t) => TShow (Succ t) where
    tshow _ = "Succ (" ++ tshow (undefined :: t) ++ ")"

type family Equals m n
type instance Equals Zero Zero = TRUE
type instance Equals (Succ a) Zero = FALSE
type instance Equals Zero (Succ a) = FALSE
type instance Equals (Succ a) (Succ b) = Equals a b

type family LessThan m n
type instance LessThan Zero Zero = FALSE
type instance LessThan (Succ n) Zero = FALSE
type instance LessThan Zero (Succ n) = TRUE
type instance LessThan (Succ m) (Succ n) = LessThan m n

type family Index r s

newtype Tagged n a = Tagged a deriving (Show,Eq)

instance (TShow n, TShow a) => TShow (Tagged n a) where
    tshow _ = "Tagged (" ++ tshow (undefined :: n) ++ ") (" ++ tshow (undefined :: a) ++ ")"


-- Definitions for an insertion sort of a heterogeneous list of
-- Tagged n a values (where sorting is by the phantom type parameter
-- n, which should be a type level natural built from the Zero type
-- and the Succ type constructor, above).

data Id a
data SortInsert h t
data Insert x y

class Sorter a where
    type Sorted a
    type Unsorted a
    mkSort :: a -> Unsorted a -> Sorted a

class Sortable a where
    type SorterType a
    sorter :: a -> SorterType a

class Insertable a where
    type InserterType a
    inserter :: a -> InserterType a

class Inserter a where
    type Inserted a
    type Uninserted a
    mkInsert :: a -> Uninserted a -> Inserted a

sort v = mkSort (sorter v) v

instance Sorter (Id a) where
    type Sorted (Id a) = a
    type Unsorted (Id a) = a
    mkSort _ v = v

instance Sortable () where
    type SorterType () = Id ()
    sorter = undefined

instance Sortable (Tagged m a :* ()) where
    type SorterType (Tagged m a :* ()) = Id (Tagged m a :* ())
    sorter = undefined

instance Insertable (Tagged m a :* Tagged n b :* c) where
    type InserterType (Tagged m a :* Tagged n b :* c) =
             Cond (LessThan n m)
                 (Insert (Tagged m a) (Tagged n b :* c))
                 (Id (Tagged m a :* Tagged n b :* c))
    inserter = undefined

instance Insertable () where
    type InserterType () = Id ()
    inserter = undefined

instance Insertable (Tagged n a :* ()) where
    type InserterType (Tagged n a :* ()) = Id (Tagged n a :* ())
    inserter = undefined

instance Inserter (Id a) where
    type Inserted (Id a) = a
    type Uninserted (Id a) = a
    mkInsert _ v = v

instance (Insertable (a :* c)
         , Inserter (InserterType (a :* c)) 
         ,(a :* c) ~ Uninserted (InserterType (a :* c))
         ) => Inserter (Insert a (b :* c)) where
    type Inserted (Insert a (b :* c)) = b :* Inserted (InserterType (a :* c))
    type Uninserted (Insert a (b :* c)) = a :* b :* c
    mkInsert _ (x :* y :* z) = y :* mkInsert (inserter $ x :* z) (x :* z)

instance (Sortable (b :* c)
          ,Unsorted (SorterType (b :* c)) ~ (b :* c)
          ,Uninserted (InserterType (a :* Sorted (SorterType (b :* c)))) ~
               (a :* Sorted (SorterType (b :* c)))
          ,Sorter (SorterType (b :* c))
          ,Insertable (a :* Sorted (SorterType (b :* c)))
          ,Inserter (InserterType (a :* Sorted (SorterType (b :* c))))
          ) => 
        Sorter (SortInsert a (b :* c)) where
    type Sorted (SortInsert a (b :* c)) =
        Inserted (InserterType (a :* (Sorted (SorterType (b :* c)))))
    type Unsorted (SortInsert a (b :* c)) = a :* b :* c
    mkSort _ (a :* b :* c) = mkInsert (inserter preinsert) preinsert
        where preinsert = a :* sort (b :* c)

instance (Sortable (b :* c), Sorter (SortInsert a (b :* c))) => 
     Sortable (a :* b :* c) where
    type SorterType (a :* b :* c) = SortInsert a (b :* c) 
    sorter = undefined

class Merger a where
    type Merged a
    type UnmergedLeft a
    type UnmergedRight a
    mkMerge :: a -> UnmergedLeft a -> UnmergedRight a -> Merged a

class Mergeable a b where
    type MergerType a b
    merger :: a -> b -> MergerType a b

merge x y = mkMerge (merger x y) x y

data TakeRight a
data TakeLeft a
data DiscardRightHead a b c d
data LeftHeadFirst a b c d
data RightHeadFirst a b c d
data EndMerge

instance Mergeable () () where
    type MergerType () () = EndMerge
    merger = undefined

instance Mergeable () (a :* b) where
    type MergerType () (a :* b) = TakeRight (a :* b)
    merger = undefined
instance Mergeable (a :* b) () where
    type MergerType (a :* b) () = TakeLeft (a :* b)
    merger = undefined

instance Mergeable (Tagged m a :* t1) (Tagged n b :* t2) where
    type MergerType (Tagged m a :* t1) (Tagged n b :* t2) =
        Cond (Equals m n) (DiscardRightHead (Tagged m a) t1 (Tagged n b) t2)
           (Cond (LessThan m n) (LeftHeadFirst (Tagged m a) t1 (Tagged n b) t2)
               (RightHeadFirst (Tagged m a ) t1 (Tagged n b) t2))
    merger = undefined

instance Merger EndMerge where
    type Merged EndMerge = ()
    type UnmergedLeft EndMerge = ()
    type UnmergedRight EndMerge = ()
    mkMerge _ () () = ()

instance Merger (TakeRight a) where
    type Merged (TakeRight a) = a
    type UnmergedLeft (TakeRight a) = ()
    type UnmergedRight (TakeRight a) = a
    mkMerge _ () a = a

instance Merger (TakeLeft a) where
    type Merged (TakeLeft a) = a
    type UnmergedLeft (TakeLeft a) = a
    type UnmergedRight (TakeLeft a) = ()
    mkMerge _ a () = a

instance
    (Mergeable t1 t2,
     Merger (MergerType t1 t2),
     t1 ~ UnmergedLeft (MergerType t1 t2),
     t2 ~ UnmergedRight (MergerType t1 t2)) => 
    Merger (DiscardRightHead h1 t1 h2 t2) where
    type Merged (DiscardRightHead h1 t1 h2 t2) = h1 :* Merged (MergerType t1 t2)
    type UnmergedLeft (DiscardRightHead h1 t1 h2 t2) = h1 :* t1
    type UnmergedRight (DiscardRightHead h1 t1 h2 t2) = h2 :* t2
    mkMerge _ (h1 :* t1) (h2 :* t2) = h1 :* mkMerge (merger t1 t2) t1 t2

instance 
    (Mergeable t1 (h2 :* t2),
     Merger (MergerType t1 (h2 :* t2)),
     t1 ~ UnmergedLeft (MergerType t1 (h2 :* t2)),
     (h2 :* t2) ~ UnmergedRight (MergerType t1 (h2 :* t2))) =>
    Merger (LeftHeadFirst h1 t1 h2 t2) where
    type Merged (LeftHeadFirst h1 t1 h2 t2) = h1 :* Merged (MergerType t1 (h2 :* t2))
    type UnmergedLeft (LeftHeadFirst h1 t1 h2 t2) = h1 :* t1
    type UnmergedRight (LeftHeadFirst h1 t1 h2 t2) = h2 :* t2
    mkMerge _ (h1 :* t1) (h2 :* t2) = h1 :* mkMerge (merger t1 (h2 :* t2)) t1 (h2 :* t2)

instance 
    (Mergeable (h1 :* t1) t2,
     Merger (MergerType (h1 :* t1) t2),
     (h1 :* t1) ~ UnmergedLeft (MergerType (h1 :* t1) t2),
     t2 ~ UnmergedRight (MergerType (h1 :* t1) t2)) =>
    Merger (RightHeadFirst h1 t1 h2 t2) where
    type Merged (RightHeadFirst h1 t1 h2 t2) = h2 :* Merged (MergerType (h1 :* t1) t2)
    type UnmergedLeft (RightHeadFirst h1 t1 h2 t2) = h1 :* t1
    type UnmergedRight (RightHeadFirst h1 t1 h2 t2) = h2 :* t2
    mkMerge _ (h1 :* t1) (h2 :* t2) = h2 :* mkMerge (merger (h1 :* t1) t2) (h1 :* t1) t2

type ONE = Succ Zero
type TWO = Succ ONE
type THREE = Succ TWO

x0 :: Tagged Zero String
x0 = Tagged "x0"
x1 :: Tagged ONE String
x1 = Tagged "x1"
x2 :: Tagged TWO String
x2 = Tagged "x2"
x3 :: Tagged THREE String
x3 = Tagged "x3"

y0 :: Tagged Zero String
y0 = Tagged "y0"
y1 :: Tagged ONE String
y1 = Tagged "y1"
y2 :: Tagged TWO String
y2 = Tagged "y2"
y3 :: Tagged THREE String
y3 = Tagged "y3"
