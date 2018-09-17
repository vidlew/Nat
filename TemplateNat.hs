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

sNat :: Int -> Q Exp
sNat 0 = [| SZ |]
sNat n = [| SS $(sNat $ n-1) |]

nat :: Int -> Q Type
nat 0 = [t| Z |]
nat n = [t| S $(nat $ n-1) |]

genNats :: Int -> Q [Dec]
genNats n = forM [0..n] s where s i = do x <- sNat i; return $ FunD (mkName $ 's':show i) [Clause [] (NormalB x) []]

genOnes :: Int -> Q [Dec]
genOnes n = forM [0..n] s where s i = do x <- [| one $(sNat i) :: List $(nat i) (List $(nat i) Integer) |]; return $ FunD (mkName $ 'i' : show i) [Clause [] (NormalB x) []]
