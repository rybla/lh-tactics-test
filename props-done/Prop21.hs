{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop21 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n m = leqN n (addN n m)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> m:N -> {prop n m}
@-}
-- [tactic|
-- proof :: N -> N -> Proof
-- proof n m = induct n
-- |]
-- %tactic:begin:proof
proof :: N -> N -> Proof
proof = \n -> \m -> case n of
                        Data.Z -> trivial
                        Data.S n_0 -> proof n_0 m
-- %tactic:end:proof
