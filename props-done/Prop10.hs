{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop10 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop m = subN m m == Z

{-@ automatic-instances proof @-}
{-@
proof :: m:N -> {prop m}
@-}
-- [tactic|
-- proof :: N -> Proof
-- proof m = induct m
-- |]
-- %tactic:begin:proof
proof :: N -> Proof
proof = \m -> case m of
                  Data.Z -> trivial
                  Data.S n_0 -> proof n_0
-- %tactic:end:proof
