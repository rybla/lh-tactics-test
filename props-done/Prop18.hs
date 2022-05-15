{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop18 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop i m = leN i (S (addN i m))

{-@ automatic-instances proof @-}
{-@
proof :: i:N -> m:N -> {prop i m}
@-}
-- [tactic|
-- proof :: N -> N -> Proof
-- proof i m = induct i
-- |]
-- %tactic:begin:proof
proof :: N -> N -> Proof
proof = \i -> \m -> case i of
                        Data.Z -> trivial
                        Data.S n_0 -> proof n_0 m
-- %tactic:end:proof
