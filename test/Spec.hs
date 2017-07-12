{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Lib (typecheck, lam, app, var, number, text)
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Whole Checker"
    [ testCase "add two ints" $ do
        typecheck (app (app (var "+") (number 1)) (number 2))
            @?= (Node NumTy (App 
                  (Node (LamTy NumTy NumTy) (App 
                     (Node (LamTy NumTy (LamTy NumTy NumTy)) (Var "+"))
                     (Node NumTy (Number 1)
                  )))
                  (Node NumTy (Number 2))
                ))
    ]
            
