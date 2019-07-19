-- Finite fields of arbitrary prime power order and elliptic curves over them
-- It not done

{-# LANGUAGE GADTs, TypeInType, StandaloneDeriving, TypeFamilies, TypeOperators, UndecidableInstances #-}

module Elliptic where

import Nat
import Matrix

data SFinOrd (o :: FinOrd (n :: Nat)) where
    SOZ :: SFinOrd (OZ :: (FinOrd (S n)))
    SOS :: SFinOrd o -> SFinOrd (OS (o :: FinOrd n))
deriving instance Show (SFinOrd o)
deriving instance Eq (SFinOrd o)

sFinOrdVal :: SFinOrd (o :: FinOrd n) -> FinOrd n
sFinOrdVal SOZ = OZ
sFinOrdVal (SOS o) = OS $ sFinOrdVal o

class KnownFinOrd (o :: FinOrd n) where knownFinOrd :: SFinOrd o
instance KnownFinOrd OZ where knownFinOrd = SOZ
instance (KnownFinOrd o) => KnownFinOrd (OS o) where knownFinOrd = SOS knownFinOrd

type family ToNat (o :: FinOrd n) :: Nat
type instance ToNat OZ = Z
type instance ToNat (OS o) = S (ToNat o)

data PGPrimeField n a where
    Affine :: List n a -> PGPrimeField n a
    Infinity :: PGPrimeField n a -> PGPrimeField (S n) a

type family ToHomogeneousCoords (x :: PGPrimeField n (FinOrd p)) :: List (S n) (FinOrd p)
type instance ToHomogeneousCoords (Affine l) = (OS OZ) :- l
type instance ToHomogeneousCoords (Infinity p) = OZ :- (ToHomogeneousCoords p)

data WeierstrassEC n (a :: FinOrd n) (b :: FinOrd n)

type family ToFinOrd (n :: Nat) :: FinOrd (m :: Nat)
type instance ToFinOrd Z = OZ
type instance ToFinOrd (S n) = OS (ToFinOrd n)

type family ModPlus (a :: FinOrd n) (b :: FinOrd n) :: FinOrd n
type instance ModPlus (a :: FinOrd n) b = ToFinOrd (Mod ((ToNat a):+(ToNat b)) n)

type family ModTimes (a :: FinOrd n) (b :: FinOrd n) :: FinOrd n
type instance ModTimes (a :: FinOrd n) b = ToFinOrd (Mod ((ToNat a):*(ToNat b)) n)

type family Dec (o :: FinOrd m) :: FinOrd n
type instance Dec (OS o) = o

data FinL a where Fin :: List n a -> FinL a

type family ConsFinL (l :: a) (ls :: FinL a) :: FinL a
type instance ConsFinL l (Fin ls) = Fin (l:-ls)

type family AppendFinL (k :: FinL a) (l :: FinL a) :: FinL a
type instance AppendFinL (Fin E) l = l
type instance AppendFinL (Fin (k:-ks)) l = ConsFinL k (AppendFinL (Fin ks) l)

type family RevFinL (l :: FinL a) :: FinL a
type instance RevFinL (Fin E) = Fin E
type instance RevFinL (Fin (l:-ls)) = AppendFinL (Fin ls) (Fin (l:-E))

type family ScaleFinL (o :: FinOrd n) (f :: FinL (FinOrd n)) :: FinL (FinOrd n)
type instance ScaleFinL o (Fin E) = Fin E
type instance ScaleFinL o (Fin (f:-fs)) = ConsFinL (ModTimes o f) (ScaleFinL o (Fin fs))

type family AddFinL (f :: FinL (FinOrd n)) (g :: FinL (FinOrd n)) :: FinL (FinOrd n)
type instance AddFinL f (Fin E) = f
type instance AddFinL (Fin E) g = g
type instance AddFinL (Fin (f:-fs)) (Fin (g:-gs)) = ConsFinL (ModPlus f g) (AddFinL (Fin fs) (Fin gs))

type family MultFinL (f :: FinL (FinOrd n)) (g :: FinL (FinOrd n)) :: FinL (FinOrd n)
type instance MultFinL f (Fin E) = Fin E
type instance MultFinL (Fin E) g = Fin E
type instance MultFinL (Fin (f:-fs)) (Fin (g:-gs)) = ConsFinL (ModTimes f g) (AddFinL (AddFinL (ScaleFinL g (Fin fs)) (ScaleFinL f (Fin gs))) (ConsFinL OZ (MultFinL (Fin fs) (Fin gs))))

type family RemoveZeroes (l :: FinL (FinOrd (n :: Nat))) :: FinL (FinOrd (n :: Nat))
type instance RemoveZeroes (Fin E) = Fin E
type instance RemoveZeroes (Fin (OZ:-ls)) = Fin ls
type instance RemoveZeroes (Fin ((OS l):-ls)) = Fin ((OS l):-ls)

-- Polynomials mod n of degree d
data PolyDeg d n where
    ZP :: PolyDeg Z n
    PlusOne :: FinOrd n -> PolyDeg (S Z) (S n)
    TimesXPlus :: PolyDeg (S d) n -> FinOrd n -> PolyDeg (S (S d)) n

data SPolyDeg (f :: PolyDeg d n) where
    SZP :: SPolyDeg ZP
    SPlusOne :: SFinOrd o -> SPolyDeg (PlusOne o)
    STimesXPlus :: SPolyDeg f -> SFinOrd o -> SPolyDeg (TimesXPlus f o)
deriving instance Show (SPolyDeg f)

type family PolyDegToList (f :: PolyDeg d n) :: List d (FinOrd n)
type instance PolyDegToList ZP = E
type instance PolyDegToList (PlusOne o) = (OS o):-E
type instance PolyDegToList (TimesXPlus f o) = o:-(PolyDegToList f)

data Polynomial n where
    Poly :: PolyDeg d n -> Polynomial n

data SPolynomial (f :: Polynomial n) where
    SPoly :: SPolyDeg f -> SPolynomial (Poly f)

type family XPlus (f :: Polynomial n) (o :: FinOrd n) :: Polynomial n
type instance XPlus (Poly f) o = Poly (TimesXPlus f o)

type family PolynomialToFinL (f :: Polynomial n) :: FinL (FinOrd n)
type instance PolynomialToFinL (Poly f) = Fin (PolyDegToList f)

type family FinLToPolynomial (l :: FinL (FinOrd n)) :: Polynomial n
type instance FinLToPolynomial (Fin E) = Poly ZP
type instance FinLToPolynomial (Fin (o:-E)) = Poly (PlusOne (Dec o))
type instance FinLToPolynomial (Fin (o:-oo:-os)) = XPlus (FinLToPolynomial (Fin (oo:-os))) o
