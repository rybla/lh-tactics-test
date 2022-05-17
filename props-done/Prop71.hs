{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop71 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect lemma_prop @-}
lemma_prop x y ys = elemListN x ys == (x == y || elemListN x ys)

{-@
lemma :: x:N -> y:N -> ys:ListN -> {lemma_prop x y ys}
@-}
lemma :: N -> N -> ListN -> Proof
lemma x y ys = undefined

return []

{-@ reflect prop @-}
prop x y xs =
  if x == y
    then True
    else elemListN x (insertListN y xs) == elemListN x xs

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> y:N -> xs:ListN -> {prop x y xs}
@-}
-- [tactic|
-- proof :: N -> N -> ListN -> Proof 
-- proof x y ys = 
--   condition {x == y};
--   induct ys as [/y' ys'];
--   condition {x == y'} requires [y'];
--   auto [lemma]
-- |]
-- %tactic:begin:proof
-- TODO: not pruned
proof :: N -> N -> ListN -> Proof
proof = \x -> \y -> \ys -> if x == y
                            then case ys of
                                     Data.Nil -> trivial
                                     Data.Cons y' ys' -> if x == y'
                                                          then lemma x y ys' &&& (lemma x y' ys' &&& (lemma y x ys' &&& (lemma y y ys' &&& (lemma y y' ys' &&& (lemma y' x ys' &&& (lemma y' y ys' &&& (lemma y' y' ys' &&& (proof x x ys' &&& (proof x y ys' &&& (proof x y' ys' &&& (proof y x ys' &&& (proof y y ys' &&& (proof y y' ys' &&& (proof y' x ys' &&& (proof y' y ys' &&& proof y' y' ys')))))))))))))))
                                                          else lemma x x ys' &&& (lemma x y ys' &&& (lemma x y' ys' &&& (lemma y x ys' &&& (lemma y y ys' &&& (lemma y y' ys' &&& (lemma y' x ys' &&& (lemma y' y ys' &&& (lemma y' y' ys' &&& (proof x x ys' &&& (proof x y ys' &&& (proof x y' ys' &&& (proof y x ys' &&& (proof y y ys' &&& (proof y y' ys' &&& (proof y' x ys' &&& (proof y' y ys' &&& proof y' y' ys'))))))))))))))))
                            else case ys of
                                     Data.Nil -> trivial
                                     Data.Cons y' ys' -> if x == y'
                                                          then lemma x x ys' &&& (lemma x y ys' &&& (lemma x y' ys' &&& (lemma y x ys' &&& (lemma y y ys' &&& (lemma y y' ys' &&& (lemma y' x ys' &&& (lemma y' y ys' &&& (lemma y' y' ys' &&& (proof x x ys' &&& (proof x y ys' &&& (proof x y' ys' &&& (proof y x ys' &&& (proof y y ys' &&& (proof y y' ys' &&& (proof y' x ys' &&& (proof y' y ys' &&& proof y' y' ys'))))))))))))))))
                                                          else lemma x x ys' &&& (lemma x y ys' &&& (lemma x y' ys' &&& (lemma y x ys' &&& (lemma y y ys' &&& (lemma y y' ys' &&& (lemma y' x ys' &&& (lemma y' y ys' &&& (lemma y' y' ys' &&& (proof x x ys' &&& (proof x y ys' &&& (proof x y' ys' &&& (proof y x ys' &&& (proof y y ys' &&& (proof y y' ys' &&& (proof y' x ys' &&& (proof y' y ys' &&& proof y' y' ys'))))))))))))))))
-- %tactic:end:proof
