{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop38 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n xs =
  countListN n (concatListN xs (singletonListN n)) == 
  S (countListN n xs)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> xs:ListN -> {prop n xs}
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
                         Data.Cons x' xs' -> if n == x' then proof x' xs' else proof n xs'
-- %tactic:end:proof
