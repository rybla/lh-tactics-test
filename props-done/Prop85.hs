{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop85 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect lemma1_prop @-}
lemma1_prop ls rs xs ys = 
  zipListN (concatListN ls xs) (concatListN rs ys) == 
  concatListN2 (zipListN ls rs) (zipListN xs ys)

{-@
lemma1 :: ls:ListN -> rs:ListN -> xs:ListN -> ys:ListN -> {lemma1_prop ls rs xs ys}
@-}
lemma1 :: ListN -> ListN -> ListN -> ListN -> Proof 
lemma1 ls rs xs ys = undefined

return []

{-@ reflect prop @-}
prop xs ys =
  if lengthListN xs == lengthListN ys then 
    zipListN (reverseListN xs) (reverseListN ys) ==
    reverseListN2 (zipListN xs ys)
  else 
    True

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> ys:ListN -> {prop xs ys}
@-}
-- [tactic|
-- proof :: ListN -> ListN -> Proof
-- proof xs ys =
--   assert {lengthListN xs == lengthListN ys};
--   induct xs as [/x xs'];
--   induct ys as [/y ys'];
--   [x, xs', y, ys']: use {lemma1 (reverseListN xs') (reverseListN ys') (singletonListN x) (singletonListN y)}
-- |]
-- %tactic:begin:proof
proof :: ListN -> ListN -> Proof
proof = \xs -> \ys -> if lengthListN xs == lengthListN ys
                       then case xs of
                                Data.Nil -> case ys of
                                                Data.Nil -> trivial
                                                Data.Cons y ys' -> trivial
                                Data.Cons x xs' -> case ys of
                                                       Data.Nil -> trivial
                                                       Data.Cons y
                                                                 ys' -> lemma1 (reverseListN xs') (reverseListN ys') (singletonListN x) (singletonListN y) &&& proof xs' ys'
                       else trivial
-- %tactic:end:proof


-- [tactic|
-- proof :: ListN -> ListN -> Proof
-- proof xs ys =
--   assert {lengthListN xs == lengthListN ys};
--   induct xs;
--   induct ys;
-- |]
-- auto [lemma1, reverseListN, singletonListN] -- ! there are just wayy to many