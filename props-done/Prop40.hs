{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop40 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop xs = takeListN Z xs == Nil

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> {prop xs}
@-}
-- [tactic|
-- proof :: ListN -> Proof
-- proof xs = trivial
-- |]
-- %tactic:begin:proof
proof :: ListN -> Proof
proof = \xs -> trivial
-- %tactic:end:proof
