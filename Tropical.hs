{-# LANGUAGE GADTs, DataKinds, StandaloneDeriving, FlexibleContexts, FlexibleInstances, DeriveLift, UndecidableInstances #-}

module Tropical where

import Nat
import TemplateNat
import Matrix
import Language.Haskell.TH.Lift

-- Think of Tropical x as ∞^x.
-- ∞^x + ∞^y = ∞^(max x y) because t^x + t^y ≈ t^(max x y) when t is very large.
-- To be more precise, suppose x>=y. Then t^x <= t^x + t^y <= 2t^x = t^(x + log_t 2),
--  so t^x + t^y = t^(x + o(1)) as t -> ∞.
-- (∞^x) * (∞^y) = ∞^(x+y).
-- MInf represents ∞^-∞ = 0.
data Tropical a where
    MInf :: (Ord a, Num a) => Tropical a
    Tropical :: (Ord a, Num a) => a -> Tropical a
deriving instance Show a => Show (Tropical a)
deriving instance Eq a => Eq (Tropical a)
deriving instance Lift a => Lift (Tropical a)

instance (Num a, Ord a) => Num (Tropical a) where{
      fromInteger 0               = MInf
    ; fromInteger _               = Tropical 0
    ; MInf         + y            = y
    ; x            + MInf         = x
    ; (Tropical x) + (Tropical y) = Tropical $ max x y
    ; MInf         * _            = MInf
    ; _            * MInf         = MInf
    ; (Tropical x) * (Tropical y) = Tropical $ x+y
}

instance (Num a, Ord a) => Fractional (Tropical a) where{
      recip (Tropical x) = Tropical $ negate x
    ; recip MInf = error "positive infinity"
}

instance (Num a, Ord a) => Ord (Tropical a) where{
      compare MInf         MInf         = EQ
    ; compare              MInf _       = LT
    ; compare _            MInf         = GT
    ; compare (Tropical x) (Tropical y) = compare x y
}

-- n-dimensional projective geometry
data PG n a where
    Affine :: Num a => List n a -> PG n a
    Infinity :: Num a => PG n a -> PG (S n) a
--instance Show (PG Z a) where show (Affine E) = "Affine E"
--deriving instance (Show a, Foldable (List (S n)), Show (PG n a)) => Show (PG (S n) a)
instance (Num a, Show (List (S n) a)) => Show (PG n a) where show = show . toHomogeneousCoords
deriving instance Eq a => Eq (PG n a)

-- Homogeneous coordinates are normalised so the first nonzero coordinate is 1
toHomogeneousCoords :: Num a => PG n a -> List (S n) a
toHomogeneousCoords (Affine l) = 1 :- l
toHomogeneousCoords (Infinity p) = 0 :- toHomogeneousCoords p

fromHomogeneousCoords :: (Fractional a, Eq a) => List (S n) a -> PG n a
fromHomogeneousCoords (x:-E) = if x==0 then error "origin is not part of projective space" else Affine E
fromHomogeneousCoords (x:-(xs@(_:-_))) = if x==0 then Infinity $ fromHomogeneousCoords $ xs else Affine $ (/x) <$> xs

-- Determine whether or not x is a zero of the homogeneous polynomial p of degree k
-- Homogenous polynomials of degree k are represented as elements of the k-th symmetric power of a^(n+1)
zeroLocusIndicator :: (Num a, Eq a, KnownNat (S n), Foldable (List k), Foldable (List (MultiChoose (S n) k))) => SNat k -> List (MultiChoose (S n) k) a -> PG n a -> Bool
zeroLocusIndicator k p x = (==0) . sum . fmap (uncurry (*)) . fasten p $ product . fmap (toHomogeneousCoords x !) . multiCombToList <$> multiCombList knownNat k

-- Determine whether or not x is a corner of the homogeneous tropical polynomial p of degree k
cornerLocusIndicator :: (Num a, Ord a, Eq a, KnownNat (S n), Foldable (List k), Foldable (List (MultiChoose (S n) k))) => SNat k -> List (MultiChoose (S n) k) (Tropical a) -> PG n (Tropical a) -> Bool
cornerLocusIndicator k p x = (\y -> f y $ sum y) . fmap (uncurry (*)) . fasten p $ product . fmap (toHomogeneousCoords x !) . multiCombToList <$> multiCombList knownNat k where f :: Eq a => List n a -> a -> Bool
                                                                                                                                                                                 f E z = False
                                                                                                                                                                                 f (y:-ys) z = if y==z then z`isIn`ys else f ys z
