{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module Prop5 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop5 @-}
prop5 :: N -> N -> Bool
prop5 m n = subN n (addN n m) == Z

{-@ automatic-instances prop5_proof @-}
{-@ reflect prop5_proof @-}
[tactic|
prop5_proof :: N -> N -> Proof
prop5_proof m n =
  induction m;
  auto [] 2
|]