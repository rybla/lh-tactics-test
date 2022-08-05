{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop36 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop xs = takeWhileListN (constant True) xs == xs

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> {prop xs}
@-}
-- [tactic|
-- proof :: ListN -> Proof
-- proof xs = 
--   induct xs as [/x' xs'];
--   [x']: condition {constant True x'}
-- |]
-- %tactic:begin:proof
proof :: ListN -> Proof
proof = \xs -> case xs of
                   Data.Nil -> trivial
                   Data.Cons x' xs' -> if constant True x' then proof xs' else trivial
-- %tactic:end:proof
