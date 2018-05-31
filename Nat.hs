{-# LANGUAGE GADTs, DataKinds, StandaloneDeriving, TypeFamilies, KindSignatures, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, ExistentialQuantification #-}

module Nat where

import Data.Monoid


data Nat = Z | S Nat

data SNat n where
    SZ :: SNat Z
    SS :: (SNat n) -> (SNat (S n))
deriving instance Show (SNat n)
deriving instance Eq (SNat n)

addSingleton :: SNat m -> SNat n -> SNat (m:+n)
SZ     `addSingleton` n = n
(SS m) `addSingleton` n = SS $ m `addSingleton` n

type family Pred (n :: Nat) :: Nat
type instance Pred Z = Z
type instance Pred (S n) = n

data FinOrd n where
    OZ :: FinOrd (S n)
    OS :: (FinOrd n) -> (FinOrd (S n))
deriving instance Show (FinOrd n)
deriving instance Eq (FinOrd n)

instance Num (FinOrd Z)

instance (Num (FinOrd n)) => Num (FinOrd (S n)) where{
    fromInteger 0   = OZ
;   fromInteger n   = OS $ fromInteger $ n-1
;   OZ     + n      = n
;   m      + OZ     = m
;   (OS m) + (OS n) = OS $ m+n+1
;   OZ     * _      = OZ
;   _      * OZ     = OZ
;   (OS m) * (OS n) = OS $ m*n + m + n
;   abs OZ          = OZ
;   abs x           = x 
;   signum OZ       = OZ
;   signum _        = 1
;   m-OZ            = m
;   (OS m) - (OS n) = i $ m - n where i :: FinOrd n -> FinOrd (S n)
                                      i OZ     = OZ
                                      i (OS n) = OS $ i n
;   _-_             = error "negative ordinal"
}

instance Ord (FinOrd Z)

instance (Ord (FinOrd n)) => Ord (FinOrd (S n)) where
    compare OZ      OZ    = EQ
    compare OZ      _     = LT
    compare _       OZ    = GT
    compare (OS m) (OS n) = compare m n

infixr 5 :-
data List n a where
    E    :: List Z a
    (:-) :: a -> (List n a) -> List (S n) a
deriving instance (Show a) => Show (List n a)
deriving instance (Eq a) => Eq (List n a)

(!) :: (List n a) -> (FinOrd n) -> a
(x:-_)  ! (OZ)    = x
(_:-xs) ! (OS o)  = xs!o
_       ! _       = error "index out of range"

instance Functor (List n) where
    fmap f E       = E
    fmap f (x:-xs) = (f x):-(fmap f xs)

fasten :: List n a -> List n b -> List n (a,b)
fasten E E             = E
fasten (x:-xs) (y:-ys) = (x,y):-(fasten xs ys)

instance (KnownNat n) => Applicative (List n) where
    pure    = rep knownNat
    xs<*>ys = (uncurry ($)) <$> fasten xs ys

instance Foldable (List Z) where
    foldMap _ E = mempty

instance (Foldable (List n)) => Foldable (List (S n)) where
    foldMap f (x:-xs) = (f x) <> (foldMap f xs)

(.+) :: List m a -> List n a -> List (m:+n) a
E .+ ys       = ys
(x:-xs) .+ ys = x:-(xs.+ys)

-- The free monoid on a
-- [a] is sometimes described as the free monoid on a, but this is false as [a] includes infinite lists
data FinList a = forall n. FinList (List n a)
deriving instance Show a => Show (FinList a)

instance (Eq a) => Eq (FinList a) where
    (FinList E)       == (FinList E)       = True
    (FinList E)       == (FinList (_:-_))  = False
    (FinList (_:-_))  == (FinList E)       = False
    (FinList (x:-xs)) == (FinList (y:-ys)) = (x==y) && ((FinList xs) == (FinList ys))

instance Foldable FinList where
    foldMap f (FinList E)       = mempty
    foldMap f (FinList (x:-xs)) = (f x) <> (foldMap f $ FinList xs)

instance Functor FinList where
    fmap f (FinList xs) = FinList $ f<$>xs

instance Applicative FinList where
    pure      = return
    fs <*> xs = do f <- fs
                   x <- xs
                   return $ f x

instance Monad FinList where
    return   = FinList . (:-E)
    xs >>= f = foldr (<>) mempty $ f <$> xs
--    xs >>= f = c $ f <$> xs where c :: FinList (FinList a) -> FinList a
--                                  c (FinList E)           = FinList E
--                                  c (FinList (x:-E))      = x
--                                  c (FinList (x:-xx:-xs)) = c $ FinList $ (x<>xx):-xs

instance Monoid (FinList a) where
    mempty = FinList E
    (FinList xs) `mappend` (FinList ys) = FinList $ xs.+ys

rev :: FinList a -> FinList a
rev (FinList E) = FinList E
rev (FinList (x:-xs)) = (rev $ FinList xs) <> pure x

type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Z:+n     = n
type instance (S m):+n = S (m:+n)

type family (m :: Nat) :* (n :: Nat) :: Nat
type instance Z:*n     = Z
type instance (S m):*n = n:+(m:*n)

flatten :: List m (List n a) -> List (m:*n) a
flatten E       = E
flatten (x:-xs) = x.+(flatten xs)

cross :: List m a -> List n b -> List m (List n (a,b))
E `cross` _        = E
(x:-xs) `cross` ys = ((\y -> (x,y))<$>ys):-(cross xs ys)

rep :: SNat n -> a -> List n a
rep SZ _     = E
rep (SS n) x = x:-(rep n x)

first :: List (S n) a -> a
first (x:-_) = x

rest :: List (S n) a -> List n a
rest (_:-xs) = xs

class KnownNat n where knownNat :: SNat n
instance KnownNat Z where knownNat = SZ
instance (KnownNat n) => KnownNat (S n) where knownNat = SS $ knownNat

transpose :: (KnownNat n) => List m (List n a) -> List n (List m a)
transpose (E:-_)  = E
transpose E       = pure E
transpose (x:-xs) = ((:-)<$>x) <*> (transpose xs)

finOrdList :: SNat n -> List n (FinOrd n)
finOrdList SZ     = E
finOrdList (SS n) = OZ:-(OS <$> finOrdList n)

-- Permutations of [0..n-1]
infixr 5 :#
data Permutation n where
    EP   :: Permutation Z
    (:#) :: FinOrd (S n) -> Permutation n -> Permutation (S n)
deriving instance Show (Permutation n)
deriving instance Eq (Permutation n)

permToList :: Permutation n -> List n (FinOrd n)
permToList EP = E
permToList (OZ :# p) = OZ :- (OS <$> permToList p)
--permToList ((OS o) :# p) = (first l) :- (i o $ rest l) where l = OS <$> permList p
--                                                             i :: FinOrd n -> List n (FinOrd n) -> List (S n) (FinOrd n)
--                                                             i OZ l = OZ :- l
--                                                             i (OS o) l = (first l) :- (i o $ rest l)

data Parity = Even | Odd deriving (Show, Eq)
parity :: Permutation n -> Parity
parity EP = Even
parity (OZ:#p) = parity p
parity ((OS o):#p) = r $ parity $ (i o):#p where r Even = Odd
                                                 r Odd = Even
                                                 i :: FinOrd n -> FinOrd (S n)
                                                 i OZ = OZ
                                                 i (OS o) = OS $ i o

-- Subsets of [n] of size k
-- X's mark chosen elements, O's mark omitted elements
-- E.g., X (X (O (X EC))) represents 013 as a subset of [0..4)
-- EC is the empty set as a subset of itself
data Comb n k where
    EC :: Comb Z Z
    X  :: Comb n k -> Comb (S n) (S k)
    O  :: Comb n k -> Comb (S n) k
deriving instance Show (Comb n k)
deriving instance Eq (Comb n k)

combToList :: Comb n k -> List k (FinOrd n)
combToList EC    = E
combToList (X c) = OZ:-(OS <$> combToList c)
combToList (O c) = OS <$> combToList c

-- List of all (n choose k) combinations
combList :: SNat n -> SNat k -> List (Choose n k) (Comb n k)
combList SZ SZ = EC:-E
combList SZ (SS k) = E
combList (SS n) SZ = O <$> combList n SZ
combList (SS n) (SS k) = (X <$> combList n k) .+ (O <$> combList n (SS k))

-- Partitions of [n] into k cycles
infixr 5 :@
data CyclePartition n k where
    NC   :: CyclePartition Z Z
    SC   :: CyclePartition n k -> CyclePartition (S n) (S k)
    (:@) :: FinOrd n -> CyclePartition n k -> CyclePartition (S n) k
deriving instance Show (CyclePartition n k)
deriving instance Eq (CyclePartition n k)

cyclePartitionToList :: CyclePartition n k -> List k (FinList (FinOrd n))
cyclePartitionToList NC = E
cyclePartitionToList (SC c) = (return OZ) :- ((OS<$>) <$> cyclePartitionToList c)
--cyclePartitionToList (o :@ c) = f o l  where l = (OS<$>) <$> cyclePartitionToList c
--                                             f :: FinOrd n -> List k (FinList (FinOrd n)) -> List k (FinList (FinOrd n))
--                                             f o (x:-xs) = if (finOrdVal o)>=length x then x:-(f (o`m`x) xs) else g o x
--                                             o`m`x = undefined
--                                             g o x = undefined

-- List of all (n cycle k) partitions of [n] into k cycles
cyclePartitionList :: SNat n -> SNat k -> List (Cycle n k) (CyclePartition n k)
cyclePartitionList SZ SZ = NC:-E
cyclePartitionList (SS n) SZ = E
cyclePartitionList SZ (SS k) = E
cyclePartitionList (SS n) (SS k) = ((uncurry (:@)) <$> (flatten $ (finOrdList n) `cross` (cyclePartitionList n (SS k)))) .+ (SC <$> cyclePartitionList n k) 

-- Partitions of [n] into k subsets
infixr 5 :\
data Partition n k where
    NP   :: Partition Z Z
    SP   :: Partition n k -> Partition (S n) (S k)
    (:\) :: FinOrd k -> Partition n k -> Partition (S n) k
deriving instance Show (Partition n k)
deriving instance Eq (Partition n k)

-- List of all (n subset k) partitions of [n] into k subsets
partitionList :: SNat n -> SNat k -> List (Subset n k) (Partition n k)
partitionList SZ SZ = NP:-E
partitionList (SS n) SZ = E
partitionList SZ (SS k) = E
partitionList (SS n) (SS k) = ((uncurry (:\)) <$> (flatten $ (finOrdList (SS k)) `cross` (partitionList n (SS k)))) .+ (SP <$> partitionList n k) 

-- Partitions of [n] into k lists
infixr 5 :|
data ListPartition n k where
    NL   :: ListPartition Z Z
    SL   :: ListPartition n k -> ListPartition (S n) (S k)
    (:|) :: FinOrd (n:+k) -> ListPartition n k -> ListPartition (S n) k
deriving instance Show (ListPartition n k)
deriving instance Eq (ListPartition n k)

listPartitionList :: SNat n -> SNat k -> List (Lah n k) (ListPartition n k)
listPartitionList SZ SZ = NL:-E
listPartitionList (SS n) SZ = E
listPartitionList SZ (SS k) = E
listPartitionList (SS n) (SS k) = ((uncurry (:|)) <$> (flatten $ (finOrdList $ n `addSingleton` (SS k)) `cross` (listPartitionList n (SS k)))) .+ (SL <$> listPartitionList n k) 

-- Number of subsets of [n]
type family Power (n :: Nat) :: Nat
type instance Power Z = S Z
type instance Power (S n) = (Power n):+(Power n)

-- Number of permutations of [n]
type family Factorial (n :: Nat) :: Nat
type instance Factorial Z = S Z
type instance Factorial (S n) = (S n):*(Factorial n)

type family BellTriangle (i :: Nat) (j :: Nat) :: Nat
type instance BellTriangle Z Z = S Z
type instance BellTriangle (S i) Z = BellTriangle i i
type instance BellTriangle (S i) (S j) = (BellTriangle i j) :+ (BellTriangle (S i) j)

-- Bell numbers
-- Number of partitions of [n] into nonempty sets
type family Bell (n :: Nat) :: Nat
type instance Bell Z = S Z
type instance Bell (S n) = BellTriangle n n

-- Binomial coefficients
-- Number of subsets of [n] with k elements
type family Choose (n :: Nat) (k :: Nat) :: Nat
type instance Choose Z (S k) = Z
type instance Choose n Z = S Z
type instance Choose (S n) (S k) = (Choose n k):+(Choose n (S k))

-- Stirling numbers of the first kind
-- Number of permutations of [n] with k cycles
type family Cycle (n :: Nat) (k :: Nat) :: Nat
type instance Cycle Z Z = S Z
type instance Cycle Z (S k) = Z
type instance Cycle (S n) Z = Z
type instance Cycle (S n) (S k) = (n:*(Cycle n (S k))) :+ (Cycle n k)

-- Stirling numbers of the second kind
-- Number of ways of partitioning [n] into k nonempty sets
type family Subset (n :: Nat) (k :: Nat) :: Nat
type instance Subset Z Z = S Z
type instance Subset Z (S k) = Z
type instance Subset (S n) Z = Z
type instance Subset (S n) (S k) = ((S k):*(Subset n (S k))) :+ (Subset n k)

-- Lah numbers, or Stirling numbers of the third kind
-- Number of partitions of [n] into k lists
type family Lah (n :: Nat) (k :: Nat) :: Nat
type instance Lah Z Z = S Z
type instance Lah Z (S k) = Z
type instance Lah (S n) Z = Z
type instance Lah (S n) (S k) = ((n:+(S k)):*(Lah n (S k))) :+ (Lah n k)

permList :: SNat n -> List (Factorial n) (Permutation n)
permList SZ     = EP:-E
permList (SS n) = uncurry (:#) <$> (flatten $ (finOrdList $ SS n) `cross` (permList n))

finOrdVal :: FinOrd n -> Int
finOrdVal OZ = 0
finOrdVal (OS o) = 1+(finOrdVal o)

sNatVal :: SNat n -> Int
sNatVal SZ = 0
sNatVal (SS n) = 1+(sNatVal n)

