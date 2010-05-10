module Main where

import System.Environment
import Data.Char.Properties

usage = "Usage: prewreck <src-orig> <src> <out>"

main = getArgs >>= pre where
    pre [_,inf,outf] = readFile inf >>= writeFile outf . process
    pre _ = error usage
    process :: String -> String
    process [] = []
    process (c:cs) | c == 'ℓ' = "[$tls|" ++ tls cs
                   | otherwise = c : process cs
    tls (c:cs) | isIDStart c || isIDContinue c = c : tls cs
               | otherwise = "|]" ++ process (c:cs)
    tls [] = []