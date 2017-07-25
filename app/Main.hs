module Main where

import Lib

code0 = app (app (var "+") (number 1)) (number 2)
code1 = app (var "inc") (number 1)
code2 = lett [("id", lam "x" (var "x"))]
          $ app (app (var "+") (app (var "id") (number 1))) (number 2)
code3 = lett [("f", lam "n" (app (app (var "+") (app (var "f") (var "n"))) (number 2)))] (app (var "f") (number 2))
code4 = lett [("f", lam "n" (app (app (var "+") (app (var "f") (number 1))) (var "n")))] (app (var "f") (number 2))

main :: IO ()
main = putStrLn . show . evalTypecheck $ code0
