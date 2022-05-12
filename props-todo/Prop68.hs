{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop68 where

import Data
import Proof
import Tactic.Core.Quote

-- prop_68_lemma_trans is unsound in original
{-@
lemma :: a:N -> b:N -> c:N -> {(leN a b && leN b c) => leN a c}
@-}
lemma :: N -> N -> N -> Proof
lemma a b c = undefined 

return []

{-@ reflect prop @-}
prop x ys = lengthListN (deleteListN x ys) `leqN` lengthListN ys

-- ! FAILS
{-@ automatic-instances proof @-}
{-@
proof :: x:N -> ys:ListN -> {prop x ys}
@-}
[tactic|
proof :: N -> ListN -> Proof
proof x ys = 
  induct ys as [/y ys'];
  -- auto [lengthListN, deleteListN, lemma, S] 4
  -- use {proof x ys'} requires [ys'];
  -- use {lemma (lengthListN (deleteListN x ys')) (lengthListN ys') (S (lengthListN ys'))} requires [ys']
|]



