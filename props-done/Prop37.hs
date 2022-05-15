{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop37 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop x xs = not (elemListN x (deleteListN x xs))

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> xs:ListN -> {prop x xs}
@-}
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof x xs = 
--   induct xs as [/x' xs'];
--   condition {x == x'} requires [x']
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof = \x -> \xs -> case xs of
                         Data.Nil -> trivial
                         Data.Cons x' xs' -> if x == x' then proof x' xs' else proof x xs'
-- %tactic:end:proof
