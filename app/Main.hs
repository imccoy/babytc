module Main where

import Lib

code0 = app (app (var "+") (number 1)) (number 2)
code1 = app (lam "id" (app (app (var "+") (app (var "id") (number 1))) (number 2))) (lam "x" (var "x"))

main :: IO ()
main = putStrLn . show . typecheck $ code0
