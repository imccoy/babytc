module Main where

import Lib

code0 = app (app (var "+") (number 1)) (number 2)
code1 = app (var "inc") (number 1)
code2 = app (lam "id" (app (app (var "+") (app (var "id") (number 1))) (number 2))) (lam "x" (var "x"))

main :: IO ()
main = putStrLn . show . evalTypecheck $ code0
