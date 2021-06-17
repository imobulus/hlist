{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
module Data.HList.TH (
  fromTuple,
  toTuple
) where

import Language.Haskell.TH
import Control.Monad
import Data.HList.HList hiding (Exp)

hlistE :: [Exp] -> ExpQ
hlistE = foldr (\e eq -> [e|$(return e) :|| $eq|]) [e|HEmpty|]

fromTuple :: Int -> ExpQ
fromTuple n = do
  when (n <= 1) $ error "a tuple must contain more than one element"
  names <- mapM (newName . ("a" <>) . show) [1..n]
  let arg = TupP $ map VarP names
  res <- hlistE $ map VarE names
  return $ LamE [arg] res

toTuple :: Int -> ExpQ
toTuple n = do
  names <- mapM (newName . ("a" <>) . show) [1..n]
  let arg = foldr (\n p -> ConP '(:||) [VarP n, p]) (ConP 'HEmpty []) names
      res = TupE $ map (Just . VarE) names
  return $ LamE [arg] res
