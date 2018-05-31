{-# LANGUAGE GADTs, DataKinds, StandaloneDeriving, TypeFamilies, KindSignatures, TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, ExistentialQuantification #-}

module Planar where

import Nat

-- A lambda skeleton is a linear lambda term with the variable names omitted.
-- Every lambda skeleton is the skeleton of exactly one planar linear lambda term.
infixl 5 :.
data Skeleton n where
    V    :: Skeleton (S Z) -- Placeholder for variable name
    (:.) :: Skeleton m -> Skeleton n -> Skeleton (m:+n) -- Function application
    L    :: Skeleton (S n) -> Skeleton n -- Lambda abstraction. The restriction ensures that every lambda skeleton is the skeleton of at least one linear lambda term.
deriving instance Show (Skeleton n)

data Colour = Blue | Red deriving (Show, Eq)

infixl 5 :&
data ColouredSkeleton c n where
    BV   :: ColouredSkeleton Blue (S Z) -- v-rule
    (:&) :: ColouredSkeleton Blue m -> ColouredSkeleton Red n -> ColouredSkeleton Blue (m:+n) -- a-rule
    RB   :: ColouredSkeleton Blue n -> ColouredSkeleton Red n -- s-rule
    RL   :: ColouredSkeleton Red (S n) -> ColouredSkeleton Red n
deriving instance Show (ColouredSkeleton c n)

size :: (Num a) => ColouredSkeleton c n -> a
size BV     = 0
size (u:&v) = (size u)+(size v)
size (RB u) = (size u)+1
size (RL u) = size u

unColour :: ColouredSkeleton c n -> Skeleton n
unColour BV     = V
unColour (u:&v) = (unColour u):.(unColour v)
unColour (RB u) = unColour u
unColour (RL u) = L $ unColour u

-- Returns the unique blue colouring of u if u is neutral, nothing otherwise
neut :: Skeleton n -> Maybe (ColouredSkeleton Blue n)
neut V      = Just BV
neut (u:.v) = do x <- neut u
                 y <- norm v
                 return $ x:&y
neut _      = Nothing

-- Returns the unique red colouring of u if u is normal, nothing otherwise
norm :: Skeleton n -> Maybe (ColouredSkeleton Red n)
norm (L u) = RL <$> norm u
norm u     = RB <$> neut u

-- Motzkin trees. Essentially lambda skeletons without the linearity restriction.
data Motzkin = P | B Motzkin Motzkin | U Motzkin deriving (Show, Eq)

toMotzkin :: (Skeleton n) -> Motzkin
toMotzkin V = P
toMotzkin (u:.v) = B (toMotzkin u) (toMotzkin v)
toMotzkin (L u) = U (toMotzkin u)

instance Eq (Skeleton n) where
    u==v = (toMotzkin u) == (toMotzkin v)

-- A lambda term is normal if it contains no beta-redexes.
-- A lambda term u is neutral if, for every lambda term v, u(v) is normal.
isNeutral :: Skeleton n -> Bool
isNeutral V = True
isNeutral (u:.v) = isNeutral u && isNormal v
isNeutral _ = False

isNormal :: Skeleton n -> Bool
isNormal (L u) = isNormal u
isNormal u = isNeutral u
--isNormal V = True
--isNormal ((L u):.v) = False
--isNormal (u:.v) = isNormal u && isNormal v
--isNormal (L u) = isNormal u

-- Pseudo-lambda terms
infixl 5 :!
data PseudoLambda n where
    Var  :: Int -> PseudoLambda (S Z)
    (:!) :: PseudoLambda m -> PseudoLambda n -> PseudoLambda (m:+n)
    Lam  :: Int -> PseudoLambda (S n) -> PseudoLambda n
deriving instance Show (PseudoLambda n)

skel :: PseudoLambda n -> Skeleton n
skel (Var _) = V
skel (u:!v) = (skel u):.(skel v)
skel (Lam _ u) = L $ skel u
