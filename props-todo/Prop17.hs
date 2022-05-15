{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop17 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n = leqN n Z == (n == Z)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> {prop n}
@-}
-- [tactic|
-- proof :: N -> Proof
-- proof n = condition {leqN n Z}
-- |]
-- %tactic:begin:proof
proof :: N -> Proof
proof = \n -> if leqN n Z then trivial else trivial
-- %tactic:end:proof
