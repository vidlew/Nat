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

data BlueSkeleton n where
    BV :: BlueSkeleton (S Z)
    BA :: BlueSkeleton m -> RedSkeleton n -> BlueSkeleton (m:+n)
deriving instance Show (BlueSkeleton n)

data RedSkeleton n where
    RB :: BlueSkeleton n -> RedSkeleton n
    RL :: RedSkeleton (S n) -> RedSkeleton n
deriving instance Show (RedSkeleton n)

data ColouredSkeleton n = Blue (BlueSkeleton n) | Red (RedSkeleton n)

size :: ColouredSkeleton n -> Int
size (Blue BV) = 0
size (Blue (BA u v)) = (size $ Blue u)+(size $ Red v)
size (Red (RB u)) = 1+(size $ Blue u)
size (Red (RL u)) = size $ Red u

unColour :: ColouredSkeleton n -> Skeleton n
unColour (Blue BV) = V
unColour (Blue (BA u v)) = (unColour $ Blue u):.(unColour $ Red v)
unColour (Red (RB u)) = unColour $ Blue u
unColour (Red (RL u)) = L $ unColour $ Red u

neut :: Skeleton n -> BlueSkeleton n
neut V = BV
neut (u:.v) = BA (neut u) (norm v)
neut _ = error "no blue colouring exists"

norm :: Skeleton n -> RedSkeleton n
norm (L u) = RL $ norm u
norm u = RB $ neut u

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
