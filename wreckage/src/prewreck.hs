module Main where

import System.Environment
import System.IO
import Data.Char.Properties
import Debug.Trace
usage = "Usage: prewreck <src-orig> <src> <out>"

main = getArgs >>= pre where
    pre [_,inf,outf] = myReadFile inf >>= myWriteFile outf . process
    pre _ = error usage
    process [] = []
    process (c:cs) | c == 'ℓ' = "[$selQQ|" ++ tls cs
                   | otherwise = c : process cs
    tls (c:cs) | isIDStart c || isIDContinue c = c : tls cs
               | otherwise = "|]" ++ process (c:cs)
    tls [] = []

myReadFile f = do
    h <- openFile f ReadMode
    hSetEncoding h utf8
    hGetContents h

myWriteFile f s = do
    h <- openFile f WriteMode
    hSetEncoding h utf8
    hPutStr h s
    hFlush h