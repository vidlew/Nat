-- Finite fields of arbitrary prime power order and elliptic curves over them
-- It not done

{-# LANGUAGE GADTs, TypeInType, StandaloneDeriving, TypeFamilies, TypeOperators, UndecidableInstances, FlexibleContexts, FlexibleInstances, ScopedTypeVariables #-}

module Elliptic where

import Nat
import Matrix

getNat :: SNat n -> Nat
getNat SZ = Z
getNat (SS n) = S $ getNat n

data SFinOrd (o :: FinOrd (n :: Nat)) where
    SOZ :: SFinOrd (OZ :: (FinOrd (S n)))
    SOS :: SFinOrd o -> SFinOrd (OS (o :: FinOrd n))
deriving instance Show (SFinOrd o)
deriving instance Eq (SFinOrd o)

getFinOrd :: SFinOrd (o :: FinOrd n) -> FinOrd n
getFinOrd SOZ = OZ
getFinOrd (SOS o) = OS $ getFinOrd o

class KnownFinOrd (o :: FinOrd n) where knownFinOrd :: SFinOrd o
instance KnownFinOrd OZ where knownFinOrd = SOZ
instance (KnownFinOrd o) => KnownFinOrd (OS o) where knownFinOrd = SOS knownFinOrd

type family ToNat (o :: FinOrd n) :: Nat
type instance ToNat OZ = Z
type instance ToNat (OS o) = S (ToNat o)

toNat :: FinOrd n -> Nat
toNat OZ = Z
toNat (OS o) = S $ toNat o

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

toFinOrd :: Num (FinOrd m) => Nat -> FinOrd (S m)
toFinOrd Z = OZ
toFinOrd (S n) = 1 + toFinOrd n

type family ModPlus (a :: FinOrd n) (b :: FinOrd n) :: FinOrd n
type instance ModPlus (a :: FinOrd n) b = ToFinOrd (Mod ((ToNat a):+(ToNat b)) n)

modPlus :: (KnownNat n, Num (FinOrd n)) => FinOrd (S n) -> FinOrd (S n) -> FinOrd (S n)
a `modPlus` b = toFinOrd $ (toNat a + toNat b) `mod` k where f :: SNat n -> FinOrd n -> SNat n
                                                             f n _ = n
                                                             k = getNat $ f knownNat a

type family ModTimes (a :: FinOrd n) (b :: FinOrd n) :: FinOrd n
type instance ModTimes (a :: FinOrd n) b = ToFinOrd (Mod ((ToNat a):*(ToNat b)) n)

modTimes :: (KnownNat n, Num (FinOrd n)) => FinOrd (S n) -> FinOrd (S n) -> FinOrd (S n)
a `modTimes` b = toFinOrd $ (toNat a * toNat b) `mod` k where f :: SNat n -> FinOrd n -> SNat n
                                                              f n _ = n
                                                              k = getNat $ f knownNat a

--sModTimes :: SFinOrd u -> SFinOrd v -> SFinOrd (ModTimes u v)
--u `sModTimes` v = undefined--toSFinOrd undefined

type family Dec (o :: FinOrd m) :: FinOrd n
type instance Dec (OS o) = o

-- Essentially the same as FinList, but the type constructor and data constructor have different names so GHC doesn't get confused
data FinL a where Fin :: List n a -> FinL a

{-
data SList (l :: List m (FinOrd n)) where
    SE :: SList E
    (:--) :: SFinOrd o -> SList l -> SList (o:-l)

data SFinL (l :: FinL (FinOrd n)) where
    SFin :: SList l -> SFinL (Fin l)
-}

type family ConsFinL (l :: a) (ls :: FinL a) :: FinL a
type instance ConsFinL l (Fin ls) = Fin (l:-ls)

--consSFinL :: SFinOrd o -> SFinL l -> SFinL (ConsFinL o l)
--consSFinL o (SFin l) = SFin $ o:--l

type family AppendFinL (k :: FinL a) (l :: FinL a) :: FinL a
type instance AppendFinL (Fin E) l = l
type instance AppendFinL (Fin (k:-ks)) l = ConsFinL k (AppendFinL (Fin ks) l)

--appendSFinL :: SFinL k -> SFinL l -> SFinL (AppendFinL k l)
--(SFin SE) `appendSFinL` l = l
--(SFin (k:--ks)) `appendSFinL` l = consSFinL k $ SFin ks `appendSFinL` l

type family RevFinL (l :: FinL a) :: FinL a
type instance RevFinL (Fin E) = Fin E
type instance RevFinL (Fin (l:-ls)) = AppendFinL (RevFinL (Fin ls)) (Fin (l:-E))

--revSFinL :: SFinL l -> SFinL (RevFinL l)
--revSFinL (SFin SE) = SFin SE
--revSFinL (SFin (l:--ls)) = appendSFinL (revSFinL $ SFin ls) $ SFin $ l:--SE

type family ScaleFinL (o :: FinOrd n) (f :: FinL (FinOrd n)) :: FinL (FinOrd n)
type instance ScaleFinL o (Fin E) = Fin E
type instance ScaleFinL o (Fin (f:-fs)) = ConsFinL (ModTimes o f) (ScaleFinL o (Fin fs))

--scaleSFinL :: SFinOrd o -> SFinL l -> SFinL (ScaleFinL o l)
--scaleSFinL o (SFin SE) = SFin SE
--scaleSFinL o (SFin (f:--fs)) = consSFinL (o `sModTimes` f) $ scaleSFinL o (SFin fs)

type family AddFinL (f :: FinL (FinOrd n)) (g :: FinL (FinOrd n)) :: FinL (FinOrd n)
type instance AddFinL f (Fin E) = f
type instance AddFinL (Fin E) g = g
type instance AddFinL (Fin (f:-fs)) (Fin (g:-gs)) = ConsFinL (ModPlus f g) (AddFinL (Fin fs) (Fin gs))

addFinList :: (KnownNat n, Num (FinOrd n)) => FinList (FinOrd (S n)) -> FinList (FinOrd (S n)) -> FinList (FinOrd (S n))
addFinList f (FinList E) = f
addFinList (FinList E) g = g
addFinList (FinList (f:-fs)) (FinList (g:-gs)) = (return $ f `modPlus` g) `mappend` (FinList fs `addFinList` FinList gs)

type family MultFinL (f :: FinL (FinOrd n)) (g :: FinL (FinOrd n)) :: FinL (FinOrd n)
type instance MultFinL f (Fin E) = Fin E
type instance MultFinL (Fin E) g = Fin E
type instance MultFinL (Fin (f:-fs)) (Fin (g:-gs)) = ConsFinL (ModTimes f g) (AddFinL (AddFinL (ScaleFinL g (Fin fs)) (ScaleFinL f (Fin gs))) (ConsFinL OZ (MultFinL (Fin fs) (Fin gs))))

multFinList :: (KnownNat n, Num (FinOrd n)) => FinList (FinOrd (S n)) -> FinList (FinOrd (S n)) -> FinList (FinOrd (S n))
multFinList f (FinList E) = FinList E
multFinList (FinList E) g = FinList E
multFinList (FinList (f:-fs)) (FinList (g:-gs)) = (return $ f `modTimes` g) `mappend` (((modTimes g <$> FinList fs) `addFinList` (modTimes f <$> FinList gs)) `addFinList` ((return OZ) `mappend` (FinList fs `multFinList` FinList gs)))

type family RemoveZeroes (l :: FinL (FinOrd (n :: Nat))) :: FinL (FinOrd (n :: Nat))
type instance RemoveZeroes (Fin E) = Fin E
type instance RemoveZeroes (Fin (OZ:-ls)) = RemoveZeroes (Fin ls)
type instance RemoveZeroes (Fin ((OS l):-ls)) = Fin ((OS l):-ls)

removeZeroes :: FinList (FinOrd n) -> FinList (FinOrd n)
removeZeroes (FinList E) = FinList E
removeZeroes (FinList (OZ:-ls)) = removeZeroes $ FinList ls
removeZeroes (FinList ((OS l):-ls)) = FinList $ (OS l):-ls

-- Polynomials mod n of degree d
data PolyDeg d n where
    ZP :: PolyDeg Z n
    PlusOne :: FinOrd n -> PolyDeg (S Z) (S n)
    TimesXPlus :: PolyDeg (S d) n -> FinOrd n -> PolyDeg (S (S d)) n
instance Show (PolyDeg d n) where
    show ZP = "0"
    show (PlusOne o) = show . finOrdVal $ OS o
    show (TimesXPlus (PlusOne o) u) = (show . finOrdVal $ OS o) ++ "X + " ++ (show $ finOrdVal u)
    show (TimesXPlus f o) = (unwords $ g <$> words s) ++ " + " ++ (show $ finOrdVal o)  where s = show f
                                                                                              g w = if w == "+" then w else if last w == 'X' then w++"^2" else if '^' `elem` w
                                                                                                    then let (a,b) = break (=='^') w in a ++ '^':(show . (+1) . (read :: String -> Int) $ tail b) else w ++ "X"

data SPolyDeg (f :: PolyDeg d n) where
    SZP :: SPolyDeg ZP
    SPlusOne :: SFinOrd o -> SPolyDeg (PlusOne o)
    STimesXPlus :: SPolyDeg f -> SFinOrd o -> SPolyDeg (TimesXPlus f o)
deriving instance Show (SPolyDeg f)

getPolyDeg :: SPolyDeg (f :: PolyDeg d n) -> PolyDeg d n
getPolyDeg SZP = ZP
getPolyDeg (SPlusOne o) = PlusOne $ getFinOrd o
getPolyDeg (STimesXPlus f o) = TimesXPlus (getPolyDeg f) $ getFinOrd o

class KnownPolyDeg f where knownPolyDeg :: SPolyDeg f
instance KnownPolyDeg ZP where knownPolyDeg = SZP
instance KnownFinOrd o => KnownPolyDeg (PlusOne o) where knownPolyDeg = SPlusOne knownFinOrd
instance (KnownPolyDeg f, KnownFinOrd o) => KnownPolyDeg (TimesXPlus f o) where knownPolyDeg = STimesXPlus knownPolyDeg knownFinOrd

type family PolyDegToList (f :: PolyDeg d n) :: List d (FinOrd n)
type instance PolyDegToList ZP = E
type instance PolyDegToList (PlusOne o) = (OS o):-E
type instance PolyDegToList (TimesXPlus f o) = o:-(PolyDegToList f)

polyDegToList :: PolyDeg d n -> List d (FinOrd n)
polyDegToList ZP = E
polyDegToList (PlusOne o) = (OS o):-E
polyDegToList (TimesXPlus f o) = o:-(polyDegToList f)

data Polynomial n where Poly :: PolyDeg d n -> Polynomial n
instance Show (Polynomial n) where show (Poly f) = show f

data SPolynomial (f :: Polynomial n) where SPoly :: SPolyDeg f -> SPolynomial (Poly f)
--deriving instance Show (SPolynomial f)
instance Show (SPolynomial f) where show = show . getPolynomial

getPolynomial :: SPolynomial (f :: Polynomial n) -> Polynomial n
getPolynomial (SPoly f) = Poly $ getPolyDeg f

class KnownPolynomial f where knownPolynomial :: SPolynomial f
instance KnownPolyDeg f => KnownPolynomial (Poly f) where knownPolynomial = SPoly knownPolyDeg

type family XPlus (f :: Polynomial n) (o :: FinOrd n) :: Polynomial n
type instance XPlus (Poly f) o = Poly (TimesXPlus f o)

xPlus :: Polynomial n -> FinOrd n -> Polynomial n
(Poly (f@(TimesXPlus _ _))) `xPlus` o = Poly (f `TimesXPlus` o)
(Poly (f@(PlusOne _))) `xPlus` o = Poly (f `TimesXPlus` o)

type family PolynomialToFinL (f :: Polynomial n) :: FinL (FinOrd n)
type instance PolynomialToFinL (Poly f) = Fin (PolyDegToList f)

polynomialToFinList :: Polynomial n -> FinList (FinOrd n)
polynomialToFinList (Poly f) = FinList $ polyDegToList f

type family FinLToPolynomial (l :: FinL (FinOrd n)) :: Polynomial n
type instance FinLToPolynomial (Fin E) = Poly ZP
type instance FinLToPolynomial (Fin ((OS o):-E)) = Poly (PlusOne o)
type instance FinLToPolynomial (Fin (o:-oo:-os)) = XPlus (FinLToPolynomial (Fin (oo:-os))) o

finListToPolynomial :: FinList (FinOrd n) -> Polynomial n
finListToPolynomial (FinList E) = Poly ZP
finListToPolynomial (FinList ((OS o):-E)) = Poly $ PlusOne o
finListToPolynomial (FinList (o:-oo:-os)) = (finListToPolynomial (FinList (oo:-os))) `xPlus` o

type family AddPolynomial (f :: Polynomial n) (g :: Polynomial n) :: Polynomial n
type instance AddPolynomial f g = FinLToPolynomial (RevFinL (RemoveZeroes (RevFinL (AddFinL (PolynomialToFinL f) (PolynomialToFinL g)))))

addPolynomial :: (KnownNat n, Num (FinOrd n)) => Polynomial (S n) -> Polynomial (S n) -> Polynomial (S n)
f `addPolynomial` g = finListToPolynomial . (\(FinList f) -> FinList $ rev f) . removeZeroes . (\(FinList f) -> FinList $ rev f) $ polynomialToFinList f `addFinList` polynomialToFinList g

type family MultPolynomial (f :: Polynomial n) (g :: Polynomial n) :: Polynomial n
type instance MultPolynomial f g = FinLToPolynomial (RevFinL (RemoveZeroes (RevFinL (MultFinL (PolynomialToFinL f) (PolynomialToFinL g)))))

multPolynomial :: (KnownNat n, Num (FinOrd n)) => Polynomial (S n) -> Polynomial (S n) -> Polynomial (S n)
f `multPolynomial` g = finListToPolynomial . (\(FinList f) -> FinList $ rev f) . removeZeroes . (\(FinList f) -> FinList $ rev f) $ polynomialToFinList f `multFinList` polynomialToFinList g

sPolynomialPlus :: KnownPolynomial (AddPolynomial f g) => SPolynomial f -> SPolynomial g -> SPolynomial (AddPolynomial f g)
sPolynomialPlus _ _ = knownPolynomial

sPolynomialTimes :: KnownPolynomial (MultPolynomial f g) => SPolynomial f -> SPolynomial g -> SPolynomial (MultPolynomial f g)
sPolynomialTimes _ _ = knownPolynomial

instance (KnownNat n, Num (FinOrd n)) => Num (Polynomial (S (S n))) where
    fromInteger c = case f k d of OZ     -> Poly ZP
                                  (OS o) -> Poly $ PlusOne o
                    where d = toFinOrd $ fromInteger c `mod` (getNat k)
                          k = knownNat
                          f :: SNat (S (S n)) -> FinOrd (S (S n)) -> FinOrd (S (S n))
                          f _ d = d
    (+) = addPolynomial
    (*) = multPolynomial
    negate f = finListToPolynomial $ toFinOrd . (\x -> case x of Z -> x; otherwise -> getNat k - x) . toNat <$> polynomialToFinList f
                        where k = knownNat
                              g :: SNat (S (S n)) -> Polynomial (S (S n)) -> ()
                              g _ _ = ()
                              t = g k f

data SomePolynomial n where SomePoly :: SPolynomial (f :: Polynomial n) -> SomePolynomial n
instance Show (SomePolynomial n) where show (SomePoly f) = show $ getPolynomial f

instance Num (SomePolynomial (S (S n))) where
    fromInteger 0 = SomePoly $ SPoly SZP
    fromInteger 1 = SomePoly . SPoly $ SPlusOne SOZ
    fromInteger c = (1+) $ fromInteger c
    --SomePoly (sf :: SPolynomial f) + SomePoly (sg :: SPolynomial g) = SomePoly $ sf `sPolynomialPlus` sg
