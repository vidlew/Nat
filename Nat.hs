-- High-tech solutions to low-tech problems

{-# LANGUAGE GADTs, DataKinds, StandaloneDeriving, TypeFamilies, KindSignatures, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, TupleSections, IncoherentInstances, PolyKinds #-}

module Nat where

import Data.Monoid
import Control.Applicative
import Control.Monad
import Data.Maybe (fromJust)

data Nat = Z | S Nat deriving (Show, Eq)

data SNat n where
    SZ :: SNat Z
    SS :: (SNat n) -> (SNat (S n))
deriving instance Show (SNat n)
deriving instance Eq (SNat n)

data SBool b where
    STrue  :: SBool True
    SFalse :: SBool False
deriving instance Show (SBool b)
deriving instance Eq (SBool b)

instance Num Nat where
    fromInteger 0 = Z
    fromInteger n = S . fromInteger $ n-1
    Z + n = n
    (S m) + n = S $ m+n
    Z * n = Z
    (S m) * n = n + (m*n)
    m - Z = m
    Z - _ = error "negative"
    (S m) - (S n) = m-n
    abs = id
    signum Z = Z
    signum _= 1

instance Ord Nat where
    Z <= _ = True
    _ <= Z = False
    (S m) <= (S n) = m<=n

instance Real Nat where
    toRational Z = 0
    toRational (S n) = 1 + toRational n

instance Enum Nat where
    fromEnum Z = 0
    fromEnum (S n) = 1 + fromEnum n
    toEnum 0 = Z
    toEnum n = S . toEnum $ n-1

instance Integral Nat where
    toInteger Z = 0
    toInteger (S n) =  1 + toInteger n
    a `divMod` b = if a<b then (0,a) else let (q,r) = (a-b)`divMod`b in (q+1,r)

addSingleton :: SNat m -> SNat n -> SNat (m:+n)
SZ     `addSingleton` n = n
(SS m) `addSingleton` n = SS $ m `addSingleton` n

multiplySingleton :: SNat m -> SNat n -> SNat (m:*n)
SZ     `multiplySingleton` _ = SZ
(SS m) `multiplySingleton` n = n `addSingleton` (m `multiplySingleton` n)

data FinOrd n where
    OZ :: FinOrd (S n)
    OS :: (FinOrd n) -> (FinOrd (S n))
--deriving instance Show (FinOrd n)
instance Show (FinOrd a) where show = show . finOrdVal
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
;   signum OZ       = 0
;   signum _        = 1
;   m-OZ            = m
;   (OS m) - (OS n) = finOrdVal $ m - n --where i :: FinOrd n -> FinOrd (S n)
                                --      i OZ     = OZ
                                --      i (OS n) = OS $ i n
;   _-_             = error "negative ordinal"
}

instance Enum (FinOrd Z)

instance (Enum (FinOrd n)) => Enum (FinOrd (S n)) where{
    toEnum 0 = OZ
;   toEnum n = OS $ toEnum $ n-1
;   fromEnum OZ = 0
;   fromEnum (OS n) = 1 + fromEnum n
}

instance (Num (FinOrd n), Enum (FinOrd n), Ord (FinOrd n)) => Real (FinOrd n) where
    toRational = toRational . fromEnum

instance (Real (FinOrd n), Enum (FinOrd n)) => Integral (FinOrd n) where{
    toInteger = toInteger . fromEnum
;   quotRem m n = if m < n then (0,m) else let (a,b) = quotRem (m-n) n in (a+1,b)
}

instance Ord (FinOrd Z)

instance (Ord (FinOrd n)) => Ord (FinOrd (S n)) where
    compare OZ      OZ    = EQ
    compare OZ      _     = LT
    compare _       OZ    = GT
    compare (OS m) (OS n) = compare m n

type family IsList a :: Bool where
    IsList (List n a) = True
    IsList _ = False

infixr 5 :-
data List n a where
    E    :: List Z a
    (:-) :: a -> (List n a) -> List (S n) a
--deriving instance (Show a) => Show (List n a)
instance (Show a, Foldable (List n), (IsList a)~False) => Show (List n a) where show = show . (foldr (:) [])
instance ((IsList a)~False, Show a, Foldable (List m), Foldable (List n)) => Show (List m (List n a)) where
    show l = f m l where m = foldr max 0 $ (foldr max 0) . ((length . show)<$>) <$> l
                         f :: Show a => Int -> List m (List n a) -> String
                         f _ E = "[]"
                         f m (l:-E)  = '[':g m l ++ "]"
                         f m (l:-ls) = '[':g m l ++ "]\n" ++ f m ls
                         g :: Show a => Int -> List n a -> String
                         g _ E = ""
                         g m (k:-E)  = (take ((m-(length $ show k)+1)`div`2) $ cycle " ") ++ show k ++ (take ((m-(length $ show k)+2)`div`2-1) $ cycle " ")
                         g m (k:-ks) = (take ((m-(length $ show k)+1)`div`2) $ cycle " ") ++ show k ++ (take ((m-(length $ show k)+2)`div`2) $ cycle " ") ++ g m ks
deriving instance (Eq a) => Eq (List n a)

(!) :: (List n a) -> (FinOrd n) -> a
(x:-_)  ! (OZ)    = x
(_:-xs) ! (OS o)  = xs!o
_       ! _       = error "index out of range"

instance Functor (List n) where
    fmap f E       = E
    fmap f (x:-xs) = (f x):-(fmap f xs)

-- "zip" was already taken
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

-- Lists that are guaranteed to be finite
-- FinList a is (as close as you can get in Haskell to) the free monoid on a
-- [a] is sometimes described as the free monoid on a, but this is fake news as [a] includes infinite lists
data FinList a where FinList :: List n a -> FinList a
-- This definition is essentially a dependent sum, 𝝨_(n:Nat) (List n a)
--deriving instance Show a => Show (FinList a)
instance (Show a) => Show (FinList a) where show = show . (foldr (:) [])
instance (Eq a) => Eq (FinList a) where
    (FinList E)       == (FinList E)       = True
    (FinList E)       == (FinList (_:-_))  = False
    (FinList (_:-_))  == (FinList E)       = False
    (FinList (x:-xs)) == (FinList (y:-ys)) = (x==y) && ((FinList xs) == (FinList ys))

-- Exercise: What happens when you apply toFinList to an infinite list?
toFinList :: [a] -> FinList a
toFinList []      = FinList E
toFinList (x:xs) = return x <> toFinList xs

instance Foldable FinList where
    foldMap f (FinList E)       = mempty
    foldMap f (FinList (x:-xs)) = (f x) <> (foldMap f $ FinList xs)

instance Functor FinList where
    fmap f (FinList xs) = FinList $ f<$>xs

instance Applicative FinList where
    pure      = FinList . (:-E)
    fs <*> xs = do f <- fs
                   x <- xs
                   return $ f x

instance Monad FinList where
    xs >>= f = foldr (<>) mempty $ f <$> xs
--    xs >>= f = c $ f <$> xs where c :: FinList (FinList a) -> FinList a
--                                  c (FinList E)           = FinList E
--                                  c (FinList (x:-E))      = x
--                                  c (FinList (x:-xx:-xs)) = c $ FinList $ (x<>xx):-xs

instance Monoid (FinList a) where
    mempty                              = FinList E
    (FinList xs) `mappend` (FinList ys) = FinList $ xs.+ys

instance Alternative FinList where
    empty = mempty
    (<|>) = (<>)

instance MonadPlus FinList

grabWhile :: (a -> Bool) -> FinList a -> FinList a
grabWhile _ (FinList E) = empty
grabWhile p (FinList (x:-xs)) = if p x then return x <> (grabWhile p $ FinList xs) else empty

loseWhile :: (a -> Bool) -> FinList a -> FinList a
loseWhile _ (FinList E) = empty
loseWhile p (FinList (x:-xs)) = if p x then loseWhile p $ FinList xs else FinList $ x:-xs

split :: (Eq a) => FinList a -> FinList (FinList a)
split (FinList E) = empty
split (FinList (x:-xs)) = return (grabWhile (x==) $ FinList $ x:-xs) <> (split $ loseWhile (x==) $ FinList xs)

splitWith :: (a -> a -> Bool) -> FinList a -> FinList (FinList a)
splitWith _ (FinList E) = empty
splitWith p (FinList (x:-xs)) = return (grabWhile (p x) $ FinList $ x:-xs) <> (splitWith p $ loseWhile (p x) $ FinList xs)

--rev :: FinList a -> FinList a
--rev (FinList E)       = FinList E
--rev (FinList (x:-xs)) = (rev $ FinList xs) <> pure x

rev :: List n a -> List n a
rev E          = E
rev (l@(_:-_)) = (final l):-(rev $ butFinal l)

lshift :: List n a -> List n a
lshift E       = E
lshift (x:-xs) = rev $ x:-(rev xs)

rshift :: List n a -> List n a
rshift E          = E
rshift (l@(_:-_)) = (final l):-(butFinal l)

final :: List (S n) a -> a
final (x:-E)      = x
final (x:-xx:-xs) = final $ xx:-xs

butFinal :: List (S n) a -> List n a
butFinal (_:-E)      = E
butFinal (x:-xx:-xs) = x:-(butFinal $ xx:-xs)

insert :: FinOrd (S n) -> a -> List n a -> List (S n) a
insert OZ y xs          = y:-xs
insert (OS o) y E       = y:-E
insert (OS o) y (x:-xs) = x:-(insert o y xs)

delete :: FinOrd (S n) -> List (S n) a -> List n a
delete OZ     (_:-xs)     = xs
delete (OS o) (x:-xx:-xs) = x:-(delete o $ xx:-xs)

applyAt :: FinOrd n -> (a->a) -> List n a -> List n a
applyAt OZ f (x:-xs)     = (f x):-xs
applyAt (OS o) f (x:-xs) = x:-(applyAt o f xs)

-- Index of first occurence of x if it exists, Nothing otherwise
firstIndex :: (Eq a) => a -> List n a -> Maybe (FinOrd n)
firstIndex _ E       = Nothing
firstIndex x (y:-ys) = if x==y then Just OZ else OS <$> firstIndex x ys

isIn :: (Eq a) => a -> List n a -> Bool
_ `isIn` E = False
x `isIn` (y:-ys) = x==y || x`isIn`ys

type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Z:+n     = n
type instance (S m):+n = S (m:+n)

type family (m :: Nat) :* (n :: Nat) :: Nat
type instance Z:*n     = Z
type instance (S m):*n = n:+(m:*n)

type family (m :: Nat) :^ (n :: Nat) :: Nat
type instance m:^Z     = S Z
type instance m:^(S n) = m:*(m:^n)

flatten :: List m (List n a) -> List (m:*n) a
flatten E       = E
flatten (x:-xs) = x.+(flatten xs)

cross :: List m a -> List n b -> List m (List n (a,b))
E       `cross` _  = E
(x:-xs) `cross` ys = ((x,)<$>ys):-(cross xs ys)

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

class KnownBool b where knownBool :: SBool b
instance KnownBool True where knownBool = STrue
instance KnownBool False where knownBool = SFalse

transpose :: (KnownNat n) => List m (List n a) -> List n (List m a)
transpose (E:-_)  = E
transpose E       = pure E
transpose (x:-xs) = ((:-)<$>x) <*> transpose xs

finOrdList :: SNat n -> List n (FinOrd n)
finOrdList SZ     = E
finOrdList (SS n) = OZ:-(OS <$> finOrdList n)

-- Permutations of [n] = [0..n-1]
-- EP is the empty permutation of []
-- o:#p is the permutation obtained by adding 1 to everything in p, then adding 0 in the o'th position
infixr 5 :#
data Permutation n where
    EP   :: Permutation Z
    (:#) :: FinOrd (S n) -> Permutation n -> Permutation (S n)
--deriving instance Show (Permutation n)
instance (Foldable (List n)) => Show (Permutation n) where show = show . permToList
deriving instance Eq (Permutation n)

permToList :: Permutation n -> List n (FinOrd n)
permToList EP     = E
permToList (o:#p) = insert o OZ (OS <$> permToList p)

permList :: SNat n -> List (Factorial n) (Permutation n)
permList SZ     = EP:-E
permList (SS n) = uncurry (:#) <$> (flatten $ (finOrdList $ SS n) `cross` (permList n))

-- Return the unique permutation p such that l = permToList p if it exists, Nothing otherwise
listToPerm :: List n (FinOrd n) -> Maybe (Permutation n)
listToPerm E          = Just EP
listToPerm (l@(_:-_)) = do i <- firstIndex OZ l
                           let l' = delete i l
                           guard $ not $ OZ `isIn` l'
                           p <- listToPerm $ (\(OS o) -> o) <$> l'
                           return $ i:#p

data Parity = Even | Odd deriving (Show, Eq)

instance Num Parity where{
    fromInteger n = if even n then Even else Odd
;   Even + Even = Even
;   Even + Odd  = Odd
;   Odd  + Even = Odd
;   Odd  + Odd  = Even
;   Even * _    = Even
;   _    * Even = Even
;   _    * _    = Odd
;   abs         = id
;   signum      = id
;   negate      = id
}

parity :: Permutation n -> Parity
parity EP          = Even
parity (OZ:#p)     = parity p
parity ((OS o):#p) = Odd + (parity $ (i o):#p) where i :: FinOrd n -> FinOrd (S n)
                                                     i OZ     = OZ
                                                     i (OS o) = OS $ i o

inverse :: (KnownNat n) => Permutation n -> Permutation n
inverse l = fromJust $ listToPerm $ fromJust <$> ((pure $ flip firstIndex $ permToList l) <*> finOrdList knownNat)

instance Monoid (Permutation Z) where
    mempty          = EP
    EP `mappend` EP = EP

instance (Monoid (Permutation n), KnownNat n) => Monoid (Permutation (S n)) where
    mempty        = OZ:#mempty
    p `mappend` q = fromJust $ listToPerm $ ((permToList q)!) <$> permToList p

permute :: Permutation n -> List n a -> List n a
permute EP E           = E
permute (o:#p) (x:-xs) = insert o x $ permute p xs

inversePermute :: Permutation n -> List n a -> List n a
inversePermute EP E     = E
inversePermute (o:#p) l = (l!o):-(inversePermute p $ delete o l)

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
combList SZ     SZ     = EC:-E
combList SZ     (SS k) = E
combList (SS n) SZ     = O <$> combList n SZ
combList (SS n) (SS k) = (X <$> combList n k) .+ (O <$> combList n (SS k))

-- Partitions of [n] into k cycles
infixr 5 :@
data CyclePartition n k where
    NC   :: CyclePartition Z Z
    SC   :: CyclePartition n k -> CyclePartition (S n) (S k)
    (:@) :: FinOrd n -> CyclePartition n k -> CyclePartition (S n) k
--deriving instance Show (CyclePartition n k)
instance (Foldable (List k)) => Show (CyclePartition n k) where show = show . cyclePartitionToList
deriving instance Eq (CyclePartition n k)

cyclePartitionToList :: CyclePartition n k -> List k (FinList (FinOrd n))
cyclePartitionToList NC     = E
cyclePartitionToList (SC c) = (return OZ) :- ((OS<$>) <$> cyclePartitionToList c)
cyclePartitionToList (o:@c) = f (finOrdVal o) $ (OS<$>) <$> cyclePartitionToList c where f :: Int -> List k (FinList (FinOrd (S n))) -> List k (FinList (FinOrd (S n)))
                                                                                         f x (l:-ls)           = if x < length l then (i x l):-ls else l:-(f (x - length l) ls)
                                                                                         i :: Int -> FinList (FinOrd (S n)) -> FinList (FinOrd (S n))
                                                                                         i 0 l                 = (return OZ) <> l
                                                                                         i n (FinList (x:-xs)) = (return x) <> (i (n-1) $ FinList xs)

-- List of all (n cycle k) partitions of [n] into k cycles
cyclePartitionList :: SNat n -> SNat k -> List (Cycle n k) (CyclePartition n k)
cyclePartitionList SZ     SZ     = NC:-E
cyclePartitionList (SS n) SZ     = E
cyclePartitionList SZ     (SS k) = E
cyclePartitionList (SS n) (SS k) = ((uncurry (:@)) <$> (flatten $ (finOrdList n) `cross` (cyclePartitionList n (SS k)))) .+ (SC <$> cyclePartitionList n k) 

-- Partitions of [n] into k subsets
infixr 5 :\
data Partition n k where
    NP   :: Partition Z Z
    SP   :: Partition n k -> Partition (S n) (S k)
    (:\) :: FinOrd k -> Partition n k -> Partition (S n) k
--deriving instance Show (Partition n k)
instance (Foldable (List k)) => Show (Partition n k) where show = show . partitionToList
deriving instance Eq (Partition n k)

partitionToList :: Partition n k -> List k (FinList (FinOrd n))
partitionToList NP     = E
partitionToList (SP p) = (return OZ) :- ((OS<$>) <$> partitionToList p)
partitionToList (o:\p) = applyAt o (return OZ <>) ((OS<$>) <$> partitionToList p)

-- List of all (n subset k) partitions of [n] into k subsets
partitionList :: SNat n -> SNat k -> List (Subset n k) (Partition n k)
partitionList SZ     SZ     = NP:-E
partitionList (SS n) SZ     = E
partitionList SZ     (SS k) = E
partitionList (SS n) (SS k) = ((uncurry (:\)) <$> (flatten $ (finOrdList (SS k)) `cross` (partitionList n (SS k)))) .+ (SP <$> partitionList n k) 

-- Partitions of [n] into k lists
infixr 5 :|
data ListPartition n k where
    NL   :: ListPartition Z Z
    SL   :: ListPartition n k -> ListPartition (S n) (S k)
    (:|) :: FinOrd (n:+k) -> ListPartition n k -> ListPartition (S n) k
--deriving instance Show (ListPartition n k)
instance (Foldable (List k)) => Show (ListPartition n k) where show = show . listPartitionToList
deriving instance Eq (ListPartition n k)

listPartitionToList :: ListPartition n k -> List k (FinList (FinOrd n))
listPartitionToList NL     = E
listPartitionToList (SL l) = (return OZ) :- ((OS<$>) <$> listPartitionToList l)
listPartitionToList (o:|l) = f (finOrdVal o) $ (OS<$>) <$> listPartitionToList l where f :: Int -> List k (FinList (FinOrd (S n))) -> List k (FinList (FinOrd (S n)))
                                                                                       f x (l:-ls)           = if x <= length l then (i x l):-ls else l:-(f (x - 1 - length l) ls)
                                                                                       i :: Int -> FinList (FinOrd (S n)) -> FinList (FinOrd (S n))
                                                                                       i 0 l                 = (return OZ) <> l
                                                                                       i n (FinList (x:-xs)) = (return x) <> (i (n-1) $ FinList xs)


-- List of all (n list k) partitions of [n] into k lists
listPartitionList :: SNat n -> SNat k -> List (Lah n k) (ListPartition n k)
listPartitionList SZ     SZ     = NL:-E
listPartitionList (SS n) SZ     = E
listPartitionList SZ     (SS k) = E
listPartitionList (SS n) (SS k) = ((uncurry (:|)) <$> (flatten $ (finOrdList $ n `addSingleton` (SS k)) `cross` (listPartitionList n (SS k)))) .+ (SL <$> listPartitionList n k) 

-- Number of subsets of [n]
type family Power (n :: Nat) :: Nat
type instance Power Z     = S Z
type instance Power (S n) = (Power n):+(Power n)

-- Number of permutations of [n]
type family Factorial (n :: Nat) :: Nat
type instance Factorial Z     = S Z
type instance Factorial (S n) = (S n):*(Factorial n)

type family BellTriangle (i :: Nat) (j :: Nat) :: Nat
type instance BellTriangle Z     Z     = S Z
type instance BellTriangle (S i) Z     = BellTriangle i i
type instance BellTriangle (S i) (S j) = (BellTriangle i j) :+ (BellTriangle (S i) j)

-- Bell numbers
-- Number of partitions of [n] into nonempty sets
type family Bell (n :: Nat) :: Nat
type instance Bell Z     = S Z
type instance Bell (S n) = BellTriangle n n

-- Binomial coefficients
-- Number of subsets of [n] with k elements
type family Choose (n :: Nat) (k :: Nat) :: Nat
type instance Choose Z     (S k) = Z
type instance Choose n     Z     = S Z
type instance Choose (S n) (S k) = (Choose n k):+(Choose n (S k))

-- Stirling numbers of the first kind
-- Number of permutations of [n] with k cycles
type family Cycle (n :: Nat) (k :: Nat) :: Nat
type instance Cycle Z     Z     = S Z
type instance Cycle Z     (S k) = Z
type instance Cycle (S n) Z     = Z
type instance Cycle (S n) (S k) = (n:*(Cycle n (S k))) :+ (Cycle n k)

-- Stirling numbers of the second kind
-- Number of ways of partitioning [n] into k nonempty sets
type family Subset (n :: Nat) (k :: Nat) :: Nat
type instance Subset Z     Z     = S Z
type instance Subset Z     (S k) = Z
type instance Subset (S n) Z     = Z
type instance Subset (S n) (S k) = ((S k):*(Subset n (S k))) :+ (Subset n k)

-- Lah numbers, or Stirling numbers of the third kind
-- Number of partitions of [n] into k lists
type family Lah (n :: Nat) (k :: Nat) :: Nat
type instance Lah Z     Z     = S Z
type instance Lah Z     (S k) = Z
type instance Lah (S n) Z     = Z
type instance Lah (S n) (S k) = ((n:+(S k)):*(Lah n (S k))) :+ (Lah n k)

-- Minimum of two natural numbers
type family Min (m :: Nat) (n :: Nat) :: Nat
type instance Min Z n = Z
type instance Min m Z = Z
type instance Min (S m) (S n) = S (Min m n)

-- Absolute difference between two natural numbers
type family Difference (m :: Nat) (n :: Nat) :: Nat
type instance Difference Z n = n
type instance Difference m Z = m
type instance Difference (S m) (S n) = Difference m n

-- Greatest common divisor of two natural numbers
type family GCD (m :: Nat) (n :: Nat) :: Nat
type instance GCD Z n = n
type instance GCD m Z = m
type instance GCD (S m) (S n) = GCD (Min (S m) (S n)) (Difference (S m) (S n))

-- Maximum of m-n and 0
type family Minus (m :: Nat) (n :: Nat) :: Nat
type instance Minus Z n = Z
type instance Minus m Z = m
type instance Minus (S m) (S n) = Minus m n

type family (:<=) (m :: Nat) (n :: Nat) :: Bool
type instance (Z :<= n) = True
type instance ((S m) :<= Z) = False
type instance ((S m) :<= (S n)) = m :<= n

type family Cond (c :: Bool) (m :: a) (n :: a) :: a
type instance Cond True m n = m
type instance Cond False m n = n

type family (:&&) (p :: Bool) (q :: Bool) :: Bool
type instance True :&& True = True
type instance True :&& False = False
type instance False :&& True = False
type instance False :&& False = False

type family (:||) (p :: Bool) (q :: Bool) :: Bool
type instance True :|| True = True
type instance True :|| False = True
type instance False :|| True = True
type instance False :|| False = False

type family Not (p :: Bool) :: Bool
type instance Not True = False
type instance Not False = True

-- Remainder when m is divided by n
type family Mod (m :: Nat) (n :: Nat) :: Nat
type instance Mod Z (S n) = Z
type instance Mod (S m) (S n) = Cond ((S m) :<= n) (S m) (Mod (Minus m n) (S n))

-- Quotient of m and n, rounded down
type family Div (m :: Nat) (n :: Nat) :: Nat
type instance Div Z (S n) = Z
type instance Div (S m) (S n) = Cond ((S m) :<= n) Z (S (Div (Minus m n) (S n)))

type family Coprime (m :: Nat) (n :: Nat) :: Bool
type instance Coprime Z n = False
type instance Coprime m Z = False
type instance Coprime (S m) (S Z) = True
type instance Coprime (S Z) (S n) = True
type instance Coprime (S (S m)) (S (S n)) = Coprime (Min (S (S m)) (S (S n))) (Difference m n)

-- Floor of base 2 logarithm
type family FloorLog (n :: Nat) :: Nat
type instance FloorLog (S Z) = Z
type instance FloorLog (S (S n)) = S (FloorLog (Div (S (S n)) (S (S Z))))

-- Ceiling of base 2 logarithm
type family CeilLog (n :: Nat) :: Nat
type instance CeilLog Z = Z
type instance CeilLog (S Z) = Z
type instance CeilLog (S (S n)) = S (CeilLog (Div (S (S (S n))) (S (S Z))))

--type family IsPrimeLoop (m :: Nat) (n :: Nat) :: Bool
--type instance IsPrimeLoop m Z = False
--type instance IsPrimeLoop m (S Z) = True
--type instance IsPrimeLoop m (S (S n)) = (Coprime m (S (S n))) :&& (IsPrimeLoop m (S n))

type family IsPrimeLoop (m :: Nat) (n :: Nat) (k :: Nat) :: Bool
type instance IsPrimeLoop m Z k = True
type instance IsPrimeLoop m (S n) k = (Coprime m k) :&& (IsPrimeLoop m n (S k))

type family IsPrime (n :: Nat) :: Bool
type instance IsPrime Z = False
type instance IsPrime (S Z) = False
--type instance IsPrime (S n) = IsPrimeLoop (S n) (Div (S n) (S (S Z)))
type instance IsPrime (S (S n)) = IsPrimeLoop (S (S n)) (Power (Div (S (CeilLog (S n))) (S (S Z)))) (S Z)

infixr 5 :%
data ReducedFraction m n where
    (:%) :: ((Coprime m n)~True) => SNat m -> SNat n -> ReducedFraction m n
deriving instance Eq (ReducedFraction m n)
instance Show (ReducedFraction m n) where
    show (m:%n) = (show $ sNatVal m) ++ '/':(show $ sNatVal n)

addFraction :: ((Coprime (Div ((a:*d):+(b:*c)) (GCD ((a:*d):+(b:*c)) (b:*d))) (Div (b:*d) (GCD ((a:*d):+(b:*c)) (b:*d))))~True,
                 KnownNat (Div ((a:*d):+(b:*c)) (GCD ((a:*d):+(b:*c)) (b:*d))), KnownNat (Div (b:*d) (GCD ((a:*d):+(b:*c)) (b:*d)))) =>
               ReducedFraction a b -> ReducedFraction c d -> ReducedFraction (Div ((a:*d):+(b:*c)) (GCD ((a:*d):+(b:*c)) (b:*d))) (Div (b:*d) (GCD ((a:*d):+(b:*c)) (b:*d)))
addFraction _ _ = knownNat :% knownNat

finOrdVal :: (Num a) => FinOrd n -> a
finOrdVal OZ     = 0
finOrdVal (OS o) = 1+(finOrdVal o)

sNatVal :: (Num a) => SNat n -> a
sNatVal SZ     = 0
sNatVal (SS n) = 1+(sNatVal n)

sBoolVal :: SBool b -> Bool
sBoolVal STrue = True
sBoolVal SFalse = False

infixr 4 :-:
data Triangle n a where
    ET :: Triangle Z a
    (:-:) :: List (S n) a -> Triangle n a -> Triangle (S n) a
deriving instance Eq a => Eq (Triangle n a)
instance Show a => Show (Triangle Z a) where
    show ET = ""
instance (Show a, Show (List (S n) a), Show (Triangle n a)) => Show (Triangle (S n) a) where
    show (r:-:t) = show r ++ (if (length $ show t) == 0 then show t else '\n':show t)
instance Functor (Triangle n) where
    fmap _ ET = ET
    fmap f (x:-:xs) = (f<$>x):-:(f<$>xs)
instance Applicative (Triangle Z) where
    pure _ = ET
    ET <*> ET = ET
instance (Applicative (List (S n)), Applicative (Triangle n)) => Applicative (Triangle (S n)) where
    pure x = pure x :-: pure x
    (f:-:fs) <*> (x:-:xs) = (f<*>x) :-: (fs<*>xs)

--data SomeNat = forall n. SomeNat (SNat n)
data SomeNat where
    SomeNat :: SNat n -> SomeNat
instance Show SomeNat where show (SomeNat x) = show $ sNatVal x
instance Eq SomeNat where
    SomeNat SZ     == SomeNat SZ     = True
    SomeNat (SS _) == SomeNat SZ     = False
    SomeNat SZ     == SomeNat (SS _) = False
    SomeNat (SS x) == SomeNat (SS y) = SomeNat x == SomeNat y

instance Num SomeNat where{
    fromInteger 0                       = SomeNat SZ
;   fromInteger n                       = (\(SomeNat m) -> SomeNat $ SS m) $ fromInteger $ n-1
;   (SomeNat m) + (SomeNat n)           = SomeNat $ m `addSingleton` n
;   (SomeNat m) * (SomeNat n)           = SomeNat $ m `multiplySingleton` n
;   abs                                 = id
;   signum 0                            = 0
;   signum _                            = 1
;   m                - (SomeNat SZ)     = m
;   (SomeNat (SS m)) - (SomeNat (SS n)) = SomeNat m - SomeNat n
;   _                - _                = error "Negative"
}

data PrimeField p where
    FieldElement :: ((IsPrime p)~True) => FinOrd p -> PrimeField p
--deriving instance Show (PrimeField p)
instance Show (PrimeField p) where
    show (FieldElement n) = show n
deriving instance Eq (PrimeField p)

instance (KnownNat p, (IsPrime p)~True, Integral (FinOrd p)) => Num (PrimeField p) where
    fromInteger n = f k $ FieldElement . fromInteger $ n `mod` sNatVal k where f :: SNat p -> PrimeField p -> PrimeField p
                                                                               f _ x = x
                                                                               k = knownNat
    (FieldElement m) + (FieldElement n) = f k $ FieldElement . fromInteger $ (toInteger m + toInteger n) `mod` sNatVal k where f :: SNat p -> PrimeField p -> PrimeField p
                                                                                                                               f _ x = x
                                                                                                                               k = knownNat
    (FieldElement m) * (FieldElement n) = f k $ FieldElement . fromInteger $ (toInteger m * toInteger n) `mod` sNatVal k where f :: SNat p -> PrimeField p -> PrimeField p
                                                                                                                               f _ x = x
                                                                                                                               k = knownNat
    negate (FieldElement n) = fromInteger . negate $ toInteger n
    abs      = id
    signum 0 = 0
    signum _ = 1

-- fromRational only makes sense for fields of characteristic 0
instance (KnownNat p, Num (PrimeField p)) => Fractional (PrimeField p) where
    recip 0 = error "divide by zero"
    recip n = f k (^(sNatVal k - 2)) n where f :: SNat p -> (PrimeField p -> PrimeField p) -> PrimeField p -> PrimeField p
                                             f _ x = x
                                             k = knownNat

modPrime :: (Num (PrimeField p)) => Integer -> SNat p -> PrimeField p
modPrime n _ = fromInteger n
