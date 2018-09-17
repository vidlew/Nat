{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -freduction-depth=0 #-}

module Matrix where

import Nat
import TemplateNat

$(genNats 127)
$(genOnes 127)

matrixPlus :: (Num a) => Matrix m n a -> Matrix m n a -> Matrix m n a
x `matrixPlus` y = ((uncurry (+))<$>) . uncurry fasten <$> fasten x y

matrixTimes :: (Num a, KnownNat m, Foldable (List l)) => Matrix k l a -> Matrix l m a -> Matrix k m a
x `matrixTimes` y =  (sum<$>) . (((uncurry (*))<$>)<$>) . ((uncurry fasten)<$>) <$> x `cross` transpose y

-- Multiply a vector by a matrix on the left
lTimes :: (Num a, Foldable (List n)) => Matrix m n a -> List n a -> List m a
x `lTimes` y = sum . ((uncurry (*))<$>) . fasten y <$> x

-- Multiply a vector by a matrix on the right
rTimes :: (Num a, KnownNat n, Foldable (List m)) => List m a -> Matrix m n a -> List n a
x `rTimes` y = transpose y `lTimes` x

-- Tensor product of vectors
tens :: (Num a) => List m a -> List n a -> List (m:*n) a
u `tens` v = uncurry (*) <$> (flatten $ u `cross` v)

-- Matrix tensor product, aka Kronecker product
-- Satisfies the identity (x⊗y) `lTimes` (u`tens`v) = (x`lTimes`u) `tens` (y`lTimes`v)
(⊗) :: (Num a) => Matrix k l a -> Matrix m n a -> Matrix (k:*m) (l:*n) a
x⊗y = flatten <$> (flatten $ ((((uncurry (*))<$>)<$>)<$>) . ((uncurry cross)<$>) <$> x`cross`y)
otimes :: (Num a) => List k (List l a) -> List m (List n a) -> List (k:*m) (List (l:*n) a)
otimes = (⊗)

-- Matrix direct sum
-- Satisfies the identity (x⊕y) `lTimes` (u.+v) = (x`lTimes`u) .+ (y`lTimes`v)
-- ((.+) is the direct sum of vectors)
(⊕) :: (Num a, KnownNat l, KnownNat n) => Matrix k l a -> Matrix m n a -> Matrix (k:+m) (l:+n) a
x⊕y = ((.+(first $ pure 0:-y)) <$> x) .+ (((first $ pure 0:-x).+) <$> y)
oplus :: (Num a, KnownNat l, KnownNat n) => List k (List l a) -> List m (List n a) -> List (k:+m) (List (l:+n) a)
oplus = (⊕)

-- Kronecker sum or tensor sum, x⊗1 + 1⊗y
-- Defined for any two square matrices
-- Satisfies the identity (x`kroneckerPlus`y) `lTimes` (u`tens`v) = (uncurry (+)) <$> fasten ((x`lTimes`u) `tens` v) (u `tens` (y`lTimes v))
kroneckerPlus :: (Num a, Num (Square m a), Num (Square n a), Num (Square (m:*n) a)) => Square m a -> Square n a -> Square (m:*n) a
x `kroneckerPlus` y = (x⊗(first $ 1:-y:-E)) + ((first $ 1:-x:-E)⊗y)

-- Matrix Hadamard product, aka entrywise multiplication
-- Sounds stupid, but is actually useful
-- Largest common submatrix of x⊗y and y⊗y
-- Unlike other matrix operations, not basis invariant
-- The identity for the Hadamard product is (pure $ pure 1)
-- Satisfies the identity (x⊗y)○(z⊗w) = (x○z)⊗(y○w)
(○) :: (Num a) => Matrix m n a -> Matrix m n a -> Matrix m n a
x○y = ((uncurry (*))<$>) . uncurry fasten <$> fasten x y
hadamardTimes :: (Num a) => Matrix m n a -> Matrix m n a -> Matrix m n a
hadamardTimes = (○)

type Matrix m n a = List m (List n a)
type Square n a = Matrix n n a

permanent :: (Num a, KnownNat n, Foldable (List n), Foldable (List (Power n))) => Square n a -> a
permanent x = sum $ (\(Set s,p) -> (if p == Even then id else negate) $ product $ sum . FinList <$> (transpose $ choose s x)) <$> (\n -> fasten (setList n) (pars n)) knownNat where
              pars :: SNat n -> List (Power n) Parity
              pars SZ = Even:-E
              pars (SS n) = ((Odd+) <$> pars n) .+ pars n
--permanent :: (Num a, KnownNat n, Foldable (List n), Foldable (List (Factorial n))) => Square n a -> a
--permanent x = sum $ product . (<*>x) . ((flip (!))<$>) . permToList <$> permList knownNat


choose :: Comb n k -> List n a -> List k a
choose EC E = E
choose (O c) (_:-xs) = choose c xs
choose (X c) (x:-xs) = x :- choose c xs

determinant :: (Num a, Num (Square n a), Foldable (List n)) => Square n a -> a
determinant E = 1
determinant (a@(_:-_)) = (if p a == Even then negate else id) $ first $ first $ foldr ($) a $ id :- ((\_ -> f a) <$> rest a) where
                                                    mu :: Num a => Square n a -> Square n a
                                                    mu E = E; mu ((x:-xx):-xs) = ((-(trace $ rest <$> xs)):-xx):-((0:-) <$> (mu $ rest <$> xs))
                                                    f a x = (mu x)*a
                                                    p :: List n a -> Parity
                                                    p E = Even
                                                    p (_:-x) = Odd + p x

-- This is the dumbest possible way to compute determinants.
--determinant :: (Num a, KnownNat n, Foldable (List n), Foldable (List (Factorial n))) => Square n a -> a
--determinant x = sum $ (\p -> (if parity p == Even then 1 else -1) * (product . (<*>x) . ((flip (!))<$>) $ permToList p)) <$> permList knownNat

trace :: Num a => Square n a -> a
trace E = 0
trace (x:-xs) = first x + (trace $ rest <$> xs)

instance Num a => Num (Square Z a) where{
    E+E           = E
;   E*E           = E
;   fromInteger _ = E
;   negate E      = E
;   abs E         = E
;   signum E      = E
}

instance (Num a, KnownNat (S n), Foldable (List (S n))) => Num (Square (S n) a) where{
    (+)           = matrixPlus
;   (*)           = matrixTimes
;   fromInteger k = (\x -> insert x (fromInteger k) $ rest $ pure 0) <$> finOrdList knownNat
;   negate        = ((negate<$>)<$>)
;   abs m          = (\x -> insert x (determinant m) $ rest $ pure 0) <$> finOrdList knownNat
}

one :: Num (Square n a) => SNat n -> Square n a
one _ = 1

instance Fractional a => Fractional (Square Z a) where{
    fromRational _ = E
;   recip E        = E
}

instance (Fractional a, KnownNat n, KnownNat (S n), Num (Square (S n) a), Num (Square n a), Foldable (List n)) => Fractional (Square (S n) a) where{
    fromRational k = (\x -> insert x (fromRational k) $ rest $ pure 0) <$> finOrdList knownNat
-- Very slow implementation of recip based on Cramer's rule.
;   recip x        = ((/(determinant x))<$>) <$> c where c = ((\(i,j) -> (f i j) * (determinant $ delete i <$> delete j x))<$>) <$> ((finOrdList knownNat) `cross` (finOrdList knownNat))
                                                         f :: Num a => FinOrd k -> FinOrd l -> a
                                                         f OZ     OZ     = 1
                                                         f (OS o) w      = -(f o w)
                                                         f o      (OS w) = -(f o w)
}

-- Exterior product of a list of k vectors
-- List of determinants of all k×k submatrices
-- Basis vectors of k-th exterior power are lists of k distinct basis vectors in lexicographic order
-- For example, the 2nd exterior power of a 3-dimensional vector space with ordered basis i,j,k has an ordered basis ij,ik,jk
-- The cross product in three dimensions is just the exterior product with i, j, and k identfied with jk, ki = -ik, and  ij respectively
exteriorProduct :: (Num a, Num (Square k a), KnownNat k, KnownNat n, Foldable (List k)) => List k (List n a) -> List (Choose n k) a
exteriorProduct l = determinant . (\os -> (\x -> (x!) <$> os) <$> l) . combToList <$> combList knownNat knownNat

-- k-th exterior power of a linear map
-- Satisfies the identity (exteriorPower m k) `lTimes` (exteriorProduct l) = exteriorProduct $ (m`lTimes`) <$> l whenever l has length k
exteriorPower :: (Num a, Num (Square k a), KnownNat k, KnownNat m, KnownNat n, Foldable (List k)) => Matrix m n a -> SNat k -> Matrix (Choose m k) (Choose n k) a
exteriorPower m k = (determinant<$>) . ((\(os,ws) -> (<$>ws) . (!) . (m!) <$> os)<$>) <$> (combToList <$> combList knownNat k) `cross` (combToList <$> combList knownNat k)

-- Symmetric product of a list of k vectors
-- Basis vectors of k-th symmetric power are lists of k basis vectors in lexicographic order
symmetricProduct :: (Num a, KnownNat k, KnownNat n, Foldable (List k), Foldable (List (Factorial k)), Ord (FinOrd k))
                 => List k (List n a) -> List (MultiChoose n k) a
symmetricProduct l = (\c -> semipermanent (f c) $ (\x -> (x!) <$> c) <$> l) . multiCombToList <$> multiCombList knownNat knownNat where
               f :: (KnownNat k, Eq a) => List k a -> FinList (FinList (FinOrd k))
               f l = (snd<$>) <$> (splitWith (\(x,_) (y,_) -> x==y) $ FinList $ fasten l $ finOrdList knownNat)
               semipermanent :: (Num a, KnownNat n, Foldable (List n), Foldable (List (Factorial n)), Ord (FinOrd n)) => FinList (FinList (FinOrd n)) -> Square n a -> a
               semipermanent q x = sum $ (\p -> if f q p then (product . (<*>x) . ((flip (!))<$>) $ permToList p) else 0) <$> permList knownNat where
                  f :: (Ord (FinOrd n), KnownNat n) => FinList (FinList (FinOrd n)) -> Permutation n -> Bool
                  f q p = foldl (&&) True $ g <$> q where l                        = permToList $ inverse p
                                                          g (FinList E)            = True
                                                          g (FinList (_:-E))       = True
                                                          g (FinList (x:-xx:-xs))  = l!x < l!xx && (g $ FinList $ xx:-xs)

-- k-th symmetric power of a linear map
-- Satisfies the identity (symmetricPower m k) `lTimes` (symmetricProduct l) = symmetricProduct $ (m`lTimes`) <$> l whenever l has length k
symmetricPower :: (Num a, KnownNat m, KnownNat n, KnownNat k, Foldable (List k), Foldable (List (Factorial k)), Ord (FinOrd k), KnownNat (MultiChoose m k))
               => Matrix m n a -> SNat k -> Matrix (MultiChoose m k) (MultiChoose n k) a
symmetricPower m k = transpose $ (\c -> symmetricProduct $ ((transpose m)!) <$> c) . multiCombToList <$> multiCombList knownNat k

data Set n where Set :: Comb n k -> Set n
deriving instance Show (Set n)
instance Eq (Set n) where
    (Set EC)    == (Set EC)    = True
    (Set (O s)) == (Set (O t)) = Set s == Set t
    (Set (X s)) == (Set (X t)) = Set s == Set t
    _           == _           = False

setList :: SNat n -> List (Power n) (Set n)
setList SZ = (Set EC):-E
setList (SS n) = ((\(Set s) -> Set $ O s) <$> setList n) .+ ((\(Set s) -> Set $ X s) <$> setList n)

type family MultiChoose (n :: Nat) (k :: Nat) :: Nat
type instance MultiChoose n     Z     = S Z
type instance MultiChoose Z     (S k) = Z
--type instance MultiChoose n (S k) = Choose (n:+k) k
type instance MultiChoose (S n) (S k) = MultiChoose (S n) k :+ MultiChoose n (S k)

data MultiComb n k where
    EM :: MultiComb Z Z
    XM :: MultiComb (S n) k -> MultiComb (S n) (S k)
    OM :: MultiComb n k -> MultiComb (S n) k
deriving instance Show (MultiComb n k)
deriving instance Eq (MultiComb n k)

multiCombList :: SNat n -> SNat k -> List (MultiChoose n k) (MultiComb n k)
multiCombList SZ     SZ     = EM:-E
multiCombList (SS n) SZ     = OM <$> multiCombList n SZ
multiCombList SZ     (SS _) = E
multiCombList (SS n) (SS k) = (XM <$> multiCombList (SS n) k).+(OM <$> multiCombList n (SS k))

multiCombToList :: MultiComb n k -> List k (FinOrd n)
multiCombToList EM     = E
multiCombToList (XM m) = OZ :- multiCombToList m
multiCombToList (OM m) = OS <$> multiCombToList m
