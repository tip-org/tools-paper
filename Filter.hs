#!/usr/bin/runhaskell

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
import Text.Pandoc.JSON
import Text.Pandoc
import Tip.Core
import Tip.Parser
import Tip.Passes
import Tip.Lint
import qualified Tip.Pretty.SMT as SMT
import qualified Tip.Pretty.Why3 as Why3
import Control.Monad
import Text.PrettyPrint(Doc)


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
  case parse expr of
    Left err  -> CodeBlock (name, [], attrs) err
    Right thy ->
      case go classes [] [] of
        Right (modes, passes) ->
          CodeBlock (name, [], attrs) $
          case foldl (>>=) (fmap (:[]) (lintEither "parse" thy)) (map pass passes) of
            Left doc   -> show doc
            Right thy' -> unlines (pick $ map (mode modes) thy')
              where
                pick strs = case [ i | ThyNum i <- modes ] of
                         i:_ | i `elem` [0..length strs-1] -> [strs !! i]
                         _                                 -> strs
        Left err -> CodeBlock (name, [], attrs) err
  where
    go [] modes passes = Right (reverse modes, reverse passes)
    go ("no-datatypes":xs) modes passes = go xs (NoDatas:modes) passes
    go ("no-check-sat":xs) modes passes = go xs (NoCheckSat:modes) passes
    go ("no-functions":xs) modes passes = go xs (NoFuns:modes) passes
    go ("no-properties":xs) modes passes = go xs (NoProps:modes) passes
    go ("no-sigs":xs) modes passes = go xs (NoSigs:modes) passes
    go ("no-sorts":xs) modes passes = go xs (NoSorts:modes) passes
    go ("why3":xs) modes passes = go xs (Why3:modes) passes
    go (('t':n):xs) modes passes = go xs (ThyNum (read n):modes) passes
    go (x:xs) modes passes =
      let subst = [ case y of '-' -> ' '
                              '_' -> ','
                              'L' | prev == '-'            -> '['
                              'R' | prev `elem` ['0'..'9'] -> ']'
                              _         -> y
                  | (y,prev) <- x `zip` ('X':x)
                  ]
      in case reads subst of
           [(p, "")] -> go xs modes (p:passes)
           _ -> Left ("Unknown pass " ++ subst)

data Mode = NoDatas | NoProps | NoFuns | NoSigs | NoSorts | NoCheckSat | Why3 | ThyNum Int deriving (Show, Eq)

data FoldFold f g a = FoldFold { unFoldFold :: f (g a) }
  deriving (Functor,Traversable,Foldable)

pass :: StandardPass -> [Theory Id] -> Either Doc [Theory Id]
pass p = mapM (lintEither (show p)) . freshPass (continuePasses [p] . unFoldFold) . FoldFold
  where
  sfh []     = emptyTheory
  sfh (x:xs) = x

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
        thy_sorts = checking NoSorts thy_sorts,
        thy_sigs = checking NoSigs thy_sigs,
        thy_datatypes = checking NoDatas thy_datatypes,
        thy_funcs = checking NoFuns thy_funcs,
        thy_asserts = checking NoProps thy_asserts }
    checking x xs
      | x `elem` ms = []
      | otherwise = xs

main = toJSONFilter (bottomUpM transform :: Pandoc -> IO Pandoc)
