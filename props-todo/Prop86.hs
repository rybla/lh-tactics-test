{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop86 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect lemma_prop @-}
lemma_prop n m = 
  if leN n m then 
    leqN n m && not (n == m)
  else 
    True

{-@
lemma :: n:N -> m:N -> {lemma_prop n m}
@-}
lemma :: N -> N -> Proof 
lemma n m = undefined

return []

{-@ reflect prop @-}
prop x y zs =
  if leN x y then 
    elemListN x (insertListN y zs) == elemListN x zs
  else
    True 

-- ! FAILS
{-@ automatic-instances proof @-}
{-@
proof :: x:N -> y:N -> zs:ListN -> {prop x y zs}
@-}
-- [tactic|
-- proof :: N -> N -> ListN -> Proof
-- proof x y zs =
--   induct zs as [/z zs'];
--   condition {leN y z} requires [z];
--   use {lemma x y};
--   condition {x == z} requires [z];
--   use {proof x y zs'} requires [zs'];
--   trivial
-- |]
-- %tactic:begin:proof
proof :: N -> N -> ListN -> Proof
proof
  = \ x
      -> \ y
           -> \ zs
                -> case zs of
                     Nil -> (lemma x) y
                     Cons z zs'
                       -> if (leN y) z then
                              ((lemma x) y
                                 &&& (if x == z then ((proof x) y) zs' else ((proof x) y) zs'))
                          else
                              ((lemma x) y
                                 &&& (if x == z then ((proof x) y) zs' else ((proof x) y) zs'))
-- %tactic:end:proof
