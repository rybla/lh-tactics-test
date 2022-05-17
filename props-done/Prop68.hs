{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop68 where

import Data
import Proof
import Tactic.Core.Quote

{-@
lemma1 :: a:N -> b:N -> c:N -> {(leqN a b && leqN b c) => leqN a c}
@-}
lemma1 :: N -> N -> N -> Proof
lemma1 a b c = undefined

{-@ lemma2 :: a:N -> {leqN a (S a)} @-}
lemma2 :: N -> Proof 
lemma2 = undefined

return []

{-@ reflect prop @-}
prop x ys = lengthListN (deleteListN x ys) `leqN` lengthListN ys

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> ys:ListN -> {prop x ys}
@-}
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof x ys =
--   induct ys as [/y ys'];
--   condition {x == y} requires [y];
--   use {lemma1 (lengthListN (deleteListN x ys')) (lengthListN ys') (lengthListN ys)} requires [y, ys'];
--   auto [lemma2, lengthListN]
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof = \x -> \ys -> case ys of
                         Data.Nil -> trivial
                         Data.Cons y ys' -> if x == y
                                             then lemma1 (lengthListN (deleteListN x ys')) (lengthListN ys') (lengthListN ys) &&& (proof y ys' &&& lemma2 (lengthListN ys'))
                                             else lemma1 (lengthListN (deleteListN x ys')) (lengthListN ys') (lengthListN ys) &&& proof x ys'
-- %tactic:end:proof
