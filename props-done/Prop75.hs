{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop75 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n m xs = 
  countListN n xs `addN` countListN n (singletonListN m) ==
  countListN n (Cons m xs)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> m:N -> xs:ListN -> {prop n m xs}
@-}
-- [tactic|
-- proof :: N -> N -> ListN -> Proof
-- proof n m xs = induct xs
-- |]
-- %tactic:begin:proof
proof :: N -> N -> ListN -> Proof
proof = \n -> \m -> \xs -> case xs of
                               Data.Nil -> trivial
                               Data.Cons n_0
                                         listN_1 -> proof n_0 m listN_1 &&& (proof n n_0 listN_1 &&& proof n n listN_1)
-- %tactic:end:proof
