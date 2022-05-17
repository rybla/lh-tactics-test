{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop44 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop x xs ys = 
  zipListN (Cons x xs) ys ==
  zipConcatListN x xs ys

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> xs:ListN -> ys:ListN -> {prop x xs ys}
@-}
-- [tactic|
-- proof :: N -> ListN -> ListN -> Proof
-- proof x xs ys = trivial
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> ListN -> Proof
proof = \x -> \xs -> \ys -> trivial
-- %tactic:end:proof
