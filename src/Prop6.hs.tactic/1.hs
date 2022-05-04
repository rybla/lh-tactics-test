{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module Prop6 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop6 @-}
prop6 :: N -> N -> Bool
prop6 m n = subN n (addN n m) == Z

{-@ automatic-instances prop6_proof @-}
{-@ reflect prop6_proof @-}
[tactic|
prop6_proof :: N -> N -> Proof
prop6_proof m n =
  induction m;
  auto [] 2
|]
