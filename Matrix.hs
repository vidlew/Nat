{-# LANGUAGE GADTs, DataKinds, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}

module Matrix where

import Nat

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
-- Satisfies the identity (x`kroneckerPlus`y) `lTimes` (u`tens`v) = ((x`lTimes`u) `tens` v) `matrixPlus` (u `tens` (y`lTimes v))
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

permanent :: (Num a, KnownNat n, Foldable (List n), Foldable (List (Factorial n))) => Square n a -> a
permanent x = sum $ product . (<*>x) . ((flip (!))<$>) . permToList <$> permList knownNat

determinant :: (Num a, KnownNat n, Foldable (List n), Foldable (List (Factorial n))) => Square n a -> a
determinant x = sum $ (\p -> (if parity p == Even then 1 else -1) * (product . (<*>x) . ((flip (!))<$>) $ permToList p)) <$> permList knownNat

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

instance (Num a, KnownNat (S n), Foldable (List (S n)){-, Foldable (List (Factorial (S n)))-}) => Num (Square (S n) a) where{
    (+)           = matrixPlus
;   (*)           = matrixTimes
;   fromInteger k = (\x -> insert x (fromInteger k) $ rest $ pure 0) <$> finOrdList knownNat
;   negate        = ((negate<$>)<$>)
--;   abs m          = (\x -> insert x (determinant m) $ rest $ pure 0) <$> finOrdList knownNat
}

instance Fractional a => Fractional (Square Z a) where{
    fromRational _ = E
;   recip E        = E
}

instance (Fractional a, KnownNat n, KnownNat (S n), Num (Square (S n) a), Foldable (List n), Foldable (List (Factorial n)), Foldable (List (Factorial (S n)))) => Fractional (Square (S n) a) where{
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
exteriorProduct :: (Num a, KnownNat k, KnownNat n, Foldable (List k), Foldable (List (Factorial k))) => List k (List n a) -> List (Choose n k) a
exteriorProduct l = determinant . (\os -> (\x -> (x!) <$> os) <$> l) . combToList <$> combList knownNat knownNat

-- k-th exterior power of a linear map
-- Satisfies the identity (exteriorPower m k) `lTimes` (exteriorProduct l) = exteriorProduct $ (m`lTimes`) <$> l whenever l has length k
exteriorPower :: (Num a, KnownNat k, KnownNat m, KnownNat n, Foldable (List k), Foldable (List (Factorial k))) => Matrix m n a -> SNat k -> Matrix (Choose m k) (Choose n k) a
exteriorPower m k = (determinant<$>) . ((\(os,ws) -> (<$>ws) . (!) . (m!) <$> os)<$>) <$> (combToList <$> combList knownNat k) `cross` (combToList <$> combList knownNat k)
