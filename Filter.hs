#!/usr/bin/runhaskell

{-# LANGUAGE RecordWildCards #-}
import Text.Pandoc.JSON
import Text.Pandoc
import Tip.Core
import Tip.Parser
import Tip.Passes
import qualified Tip.Pretty.SMT as SMT
import qualified Tip.Pretty.Why3 as Why3
import Control.Monad

transform :: Block -> IO Block
transform (CodeBlock (name, ("tip":classes), attrs) expr) =
  return (tipBlock name classes attrs expr)
transform (CodeBlock (name, ("tip-include":classes), attrs) file) = do
  contents <- readFile file
  return (tipBlock name classes attrs contents)
transform (CodeBlock (name, ["include"], attrs) file) = do
  contents <- readFile file
  return (CodeBlock (name, [], attrs) contents)
transform block = return block

tipBlock name classes attrs expr =
  CodeBlock (name, [], attrs) (mode modes (foldr (.) id (map pass passes) thy))
  where
    Right thy = parse expr
    (modes, passes) = go classes [] []
    go [] modes passes = (reverse modes, reverse passes)
    go ("no-datatypes":xs) modes passes = go xs (NoData:modes) passes
    go ("no-check-sat":xs) modes passes = go xs (NoCheckSat:modes) passes
    go ("no-functions":xs) modes passes = go xs (NoFuns:modes) passes
    go ("no-properties":xs) modes passes = go xs (NoProp:modes) passes
    go ("why3":xs) modes passes = go xs (Why3:modes) passes
    go (x:xs) modes passes =
      case reads x of
        [(pass, "")] -> go xs modes (pass:passes)
        _ -> error ("Unknown pass " ++ x)

data Mode = NoData | NoProp | NoFuns | NoCheckSat | Why3 deriving (Show, Eq)

pass :: StandardPass -> Theory Id -> Theory Id
pass p = freshPass (runPass p)

mode :: [Mode] -> Theory Id -> String
mode ms thy@Theory{..}
  | Why3 `elem` ms       = show . Why3.ppTheory $ thy'
  | NoCheckSat `elem` ms = out' thy'
  | otherwise = out thy'
  where
    out  = show . SMT.ppTheory
    out' = dropRev (length "(check-sat)") . show . SMT.ppTheory
    dropRev n = reverse . drop n . reverse
    thy' =
      thy {
        thy_datatypes = checking NoData thy_datatypes,
        thy_funcs = checking NoFuns thy_funcs,
        thy_asserts = checking NoFuns thy_asserts }
    checking x xs
      | x `elem` ms = []
      | otherwise = xs

main = toJSONFilter (bottomUpM transform :: Pandoc -> IO Pandoc)
