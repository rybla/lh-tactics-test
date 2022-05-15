{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop77 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect lemma1_prop @-}
lemma1_prop Nil = True
lemma1_prop (Cons x xs) = if sortedListN (Cons x xs) then sortedListN xs else True

{-@
lemma1 :: xs:ListN -> {lemma1_prop xs}
@-}
lemma1 :: ListN -> Proof 
lemma1 xs = undefined

{-@ reflect lemma2_prop @-}
lemma2_prop n m = if leqN n m then True else leN m n && leqN m n

{-@
lemma2 :: n:N -> m:N -> {lemma2_prop n m}
@-}
lemma2 :: N -> N -> Proof
lemma2 = undefined

return []

{-@ reflect prop @-}
prop x xs = if sortedListN xs then sortedListN (insertListN x xs) else True

-- ! FAILS
{-@ automatic-instances proof @-}
{-@
proof :: x:N -> xs:ListN -> {prop x xs}
@-}
[tactic|
proof :: N -> ListN -> Proof
proof x ys =
  induct ys as [/y ys'];
  destruct ys' as [/y' ys''];
  condition {sortedListN ys};
  condition {leqN x y} requires [y];
  condition {leqN x y'} requires [y'];
  auto [lemma1, lemma2]
|]
-- use {lemma1 ys};
-- use {lemma2 n y'} requires [y'];
-- use {proof x ys'} requires [ys'];
-- use {lemma1 ys'} requires [ys']
-- auto [lemma1, lemma2]
