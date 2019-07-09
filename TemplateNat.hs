{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift, StandaloneDeriving, GADTs, DataKinds #-}

module TemplateNat where

import Language.Haskell.TH.Syntax
import Control.Monad
import Nat
import NonEmptyFinite

deriving instance Lift a => Lift (List n a)
deriving instance Lift a => Lift (FinList a)
deriving instance Lift a => Lift (NonEmptyFinite a)

mkList :: Lift a => [a] -> Q Exp
mkList [] = [| E |]
mkList (x:xs) = [| x :- $(mkList xs) |]

mkMatrix :: Lift a => [[a]] -> Q Exp
mkMatrix [] = [| E |]
mkMatrix (x:xs) = [| $(mkList x) :- $(mkMatrix xs)|]

mkTriangle :: Lift a => [[a]] -> Q Exp
mkTriangle [] = [| ET |]
mkTriangle (x:xs) = [| $(mkList x) :-: $(mkTriangle xs) |]

sNat :: Int -> Q Exp
sNat 0 = [| SZ |]
sNat n = [| SS $(sNat $ n-1) |]

nat :: Int -> Q Type
nat 0 = [t| Z |]
nat n = [t| S $(nat $ n-1) |]

genSNats :: Int -> Q [Dec]
genSNats n = forM [0..n] s where s i = do x <- sNat i; return $ FunD (mkName $ 's':show i) [Clause [] (NormalB x) []]

genNats :: Int -> Q [Dec]
genNats n = forM [0..n] s where s i = do x <- nat i; return $ TySynD (mkName $ 'N':show i) [] x

genOnes :: Int -> Q [Dec]
genOnes n = forM [0..n] s where s i = do x <- [| 1 :: Num a => List $(nat i) (List $(nat i) a) |]; return $ FunD (mkName $ 'i' : show i) [Clause [] (NormalB x) []]

genZeroes :: Int -> Q [Dec]
genZeroes n = forM [0..n] s where s i = do x <- [| 0 :: Num a => List $(nat i) (List $(nat i) a) |]; return $ FunD (mkName $ 'o' : show i) [Clause [] (NormalB x) []]
