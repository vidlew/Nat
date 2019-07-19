-- Non-empty finite lists

{-# LANGUAGE DataKinds, GADTs #-}

module NonEmptyFinite where

import Nat
--import Control.Comonad
import Data.Semigroup

class Functor w => Comonad w where
    extract    :: w a -> a
    duplicate  :: w a -> w (w a)
    extend     :: (w a -> b) -> w a -> w b
    duplicate = extend id
    extend f  = fmap f . duplicate

infixr 1 =>=
(=>=) :: Comonad w => (w a -> b) -> (w b -> c) -> w a -> c
(f=>=g) x = g $ x =>> f

infixr 1 =<=
(=<=) :: Comonad w => (w b -> c) -> (w a -> b) -> w a -> c
(f=<=g) x = f $ x =>> g

infixr 1 <<=
(<<=) :: Comonad w => (w a -> b) -> w a -> w b
(<<=) = extend

infixl 1 =>>
(=>>) :: Comonad w => w a -> (w a -> b) -> w b
(=>>) = flip extend

--data NonEmptyFinite a = forall n. NonEmptyFinite (List (S n) a)
data NonEmptyFinite a where NonEmptyFinite :: List (S n) a -> NonEmptyFinite a

instance (Show a) => Show (NonEmptyFinite a) where show = show . (foldr (:) [])

instance (Eq a) => Eq (NonEmptyFinite a) where
    (NonEmptyFinite (x:-E))      == (NonEmptyFinite (y:-E))      = x==y
    (NonEmptyFinite (_:-E))      == (NonEmptyFinite (_:-_:-_))   = False
    (NonEmptyFinite (_:-_:-_))   == (NonEmptyFinite (_:-E))      = False
    (NonEmptyFinite (x:-xx:-xs)) == (NonEmptyFinite (y:-yy:-ys)) = x==y && NonEmptyFinite (xx:-xs) == NonEmptyFinite (yy:-ys)

instance Foldable (NonEmptyFinite) where
    foldMap f (NonEmptyFinite (x:-E))      = f x
    foldMap f (NonEmptyFinite (x:-xx:-xs)) = (f x) `mappend` (foldMap f $ NonEmptyFinite $ xx:-xs)

instance Functor NonEmptyFinite where
    fmap f (NonEmptyFinite l) = NonEmptyFinite $ f<$>l

instance Semigroup (NonEmptyFinite a) where
    (NonEmptyFinite k) <> (NonEmptyFinite l) = NonEmptyFinite $ k.+l

instance Comonad NonEmptyFinite where
    extract (NonEmptyFinite l)                = first l
    duplicate (l@(NonEmptyFinite (_:-E)))     = NonEmptyFinite $ l:-E
    duplicate (l@(NonEmptyFinite (_:-x:-xs))) = (NonEmptyFinite $ l:-E) <> (duplicate $ NonEmptyFinite $ x:-xs)

instance Applicative NonEmptyFinite where
    pure x = NonEmptyFinite $ x:-E
    fs <*> xs = do f <- fs
                   x <- xs
                   return $ f x

instance Monad NonEmptyFinite where
    l >>= f = (\(NonEmptyFinite (x:-xs)) -> foldl (<>) x $ FinList xs) $ f<$> l

toNonEmptyFinite :: [a] -> Maybe (NonEmptyFinite a)
toNonEmptyFinite (x:xx:xs) = (return x <>) <$> toNonEmptyFinite (xx:xs)
toNonEmptyFinite [x]       = Just $ return x
toNonEmptyFinite []        = Nothing
