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
prop x xs = 
  if sortedListN xs 
    then sortedListN (insertListN x xs) 
    else True

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> xs:ListN -> {prop x xs}
@-}
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof x ys =
--   assert {sortedListN ys};
--   induct ys as [/y1 ys'];
--   induct ys' as [/y2 ys''];
--   dismiss {leqN x y1} requires [y1];
--   condition {leqN x y2} requires [y2];
--   auto [lemma1, lemma2] 2
-- |]
-- %tactic:begin:proof
-- * not pruned
proof :: N -> ListN -> Proof
proof = \x -> \ys -> if sortedListN ys
                      then case ys of
                               Data.Nil -> trivial
                               Data.Cons y1 ys' -> case ys' of
                                                       Data.Nil -> if leqN x y1
                                                                    then trivial
                                                                    else lemma2 x x &&& (lemma2 x y1 &&& (lemma2 y1 x &&& (lemma2 y1 y1 &&& (proof x ys' &&& proof y1 ys'))))
                                                       Data.Cons y2 ys'' -> if leqN x y1
                                                                             then trivial
                                                                             else if leqN x y2
                                                                                   then lemma1 ys'' &&& (lemma2 x x &&& (lemma2 x y1 &&& (lemma2 x y2 &&& (lemma2 y1 x &&& (lemma2 y1 y1 &&& (lemma2 y1 y2 &&& (lemma2 y2 x &&& (lemma2 y2 y1 &&& (lemma2 y2 y2 &&& (proof x ys' &&& (proof y1 ys' &&& proof y2 ys')))))))))))
                                                                                   else lemma1 ys'' &&& (lemma2 x x &&& (lemma2 x y1 &&& (lemma2 x y2 &&& (lemma2 y1 x &&& (lemma2 y1 y1 &&& (lemma2 y1 y2 &&& (lemma2 y2 x &&& (lemma2 y2 y1 &&& (lemma2 y2 y2 &&& (proof x ys' &&& (proof y1 ys' &&& proof y2 ys')))))))))))
                      else trivial

-- -- IH: if sortedListN ys then sortedListN (insertListN x ys)
-- if sortedListN (Cons y ys) then
--   sortedListN (insertListN x (Cons y ys))
--   if leN x y then 
--     sortedListN (Cons x (Cons y ys))
--     True `by` lemma1 (Cons y ys)
--   else
--     sortedListN (Cons y (insertListN x ys))
