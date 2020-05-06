{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Exception (IOException, try)
import Control.Monad (mapM_, unless)
import qualified Data.Map as Map
import System.Environment (getArgs)
import System.IO (hFlush, stdout)

import Nitpick
import Normalize
import Parse
import Solver

evalStmt :: Context -> String -> IO Context
evalStmt ctxt input =
  case parseAction ctxt input of
    Left pe -> print pe >> return ctxt
    Right action -> execAction ctxt action

execAction :: Context -> Action -> IO Context
execAction ctxt (Def var f) = return $ Map.insert var f ctxt
execAction ctxt (Exec f) =
  case nitpick f of
    Left s -> putStrLn s >> return ctxt
    Right () -> (print $ decide $ qe f) >> return ctxt
execAction ctxt (Show var) =
  case Map.lookup var ctxt of
    Nothing -> putStrLn "Unknown expression variable"
    Just f -> print f
  >> return ctxt
execAction ctxt ShowAll =
  putStrLn (showContext ctxt) >> return ctxt
execAction ctxt (Read var filename) =
  readFileSafe filename ctxt $ \contents ->
  case parseFormula Map.empty contents of
    Left pe -> print pe >> return ctxt
    Right f -> return $ Map.insert var f ctxt
execAction ctxt (Write var filename) =
  case Map.lookup var ctxt of
    Nothing -> (putStrLn $ "Unknown variable " ++ show var)
    Just f -> writeFile filename (show f)
  >> return ctxt

repl :: Context -> IO ()
repl ctxt = do
  putStr "pres> "
  hFlush stdout
  input <- getLine
  unless (input == ":quit" || input == ":q") $
    if (input == ":help" || input == ":h")
    then readFileSafe "help.txt" () putStrLn >> repl ctxt
    else evalStmt ctxt input >>= repl

evalFile :: String -> IO ()
evalFile filename =
  putStrLn ("Evaluating " ++ filename) >>
  (readFileSafe filename () $ \contents ->
  case parseFormula Map.empty contents of
    Left pe -> print pe
    Right f -> print $ decide $ qe f)

readFileSafe :: FilePath -> a -> (String -> IO a) -> IO a
readFileSafe fp def f =
  try (readFile fp) >>= (\res ->
  case res of
    Left exc -> print (exc :: IOException) >> return def
    Right contents -> f contents)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> repl Map.empty
    _ -> mapM_ evalFile args
