{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Lib (typecheck
           , Node(..), Expr(..), TyF(..)
           , lam, app, var, number, text
           , lamTy', numTy', textTy')

import           Control.Unification (freeze)
import           Data.Functor.Fixedpoint (Fix(..))

import           Test.Tasty
import           Test.Tasty.HUnit

deriving instance Eq (TyF (Fix TyF))

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Whole Checker"
    [ testCase "add two ints" $ do
        Right ty <- pure . runTypecheck $ app (app (var "+") (number 1)) (number 2)
        freeze <$> ty @?= Just <$> Node numTy' (App 
                                     (Node (lamTy' numTy' numTy') (App 
                                        (Node (lamTy' numTy' (lamTy' numTy' numTy')) (Var "+"))
                                        (Node numTy' (Number 1)
                                     )))
                                     (Node numTy' (Number 2))
                                   )
    ]
            
