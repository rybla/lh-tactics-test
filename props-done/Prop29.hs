{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop29 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop x xs = elemListN x (ins1 x xs)

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> xs:ListN -> {prop x xs}
@-}
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof n xs = 
--   induct xs as [/x' xs'];
--   [x']: condition {n == x'}
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof = \n -> \xs -> case xs of
                         Data.Nil -> trivial
                         Data.Cons x' xs' -> if n == x' then trivial else proof n xs'
-- %tactic:end:proof
