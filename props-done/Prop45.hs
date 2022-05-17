{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop45 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop x y xs ys =
  zipListN (Cons x xs) (Cons y ys) ==
  Cons2 x y (zipListN xs ys)

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> y:N -> xs:ListN -> ys:ListN -> {prop x y xs ys}
@-}
-- [tactic|
-- proof :: N -> N -> ListN -> ListN -> Proof
-- proof x y xs ys = trivial
-- |]
-- %tactic:begin:proof
proof :: N -> N -> ListN -> ListN -> Proof
proof = \x -> \y -> \xs -> \ys -> trivial
-- %tactic:end:proof
