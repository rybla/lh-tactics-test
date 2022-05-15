{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop16 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop x xs = 
  if xs == Nil then 
    lastListN' (Cons x xs) == x 
  else 
    True

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> xs:ListN -> {prop x xs}
@-}
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof x xs = condition {xs == Nil}
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof = \x -> \xs -> if xs == Nil then trivial else trivial
-- %tactic:end:proof
