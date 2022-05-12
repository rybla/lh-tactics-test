{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop7 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop7 @-}
prop7 :: N -> N -> Bool
prop7 n m = subN (addN n m) n == m

{-@ automatic-instances prop7_proof @-}
{-@ 
prop7_proof :: n:N -> m:N -> {prop7 n m}
@-}
-- %tactic:begin:prop7_proof
prop7_proof :: N -> N -> Proof
prop7_proof = \n -> \m -> case n of
                              Data.Z -> trivial
                              Data.S n_0 -> prop7_proof n_0 m
-- %tactic:end:prop7_proof

{-
[tactic|
prop7_proof :: N -> N -> Proof
prop7_proof n m =
  induct n
|]
-}