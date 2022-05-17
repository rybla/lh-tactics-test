-- ! needs errata

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
  if leqN n m then 
    leqN n m
  else 
    not (n == m)

{-@
lemma :: n:N -> m:N -> {lemma_prop n m}
@-}
lemma :: N -> N -> Proof 
lemma n m = undefined


{-@ reflect lemma2_prop @-}
lemma2_prop x y ys = 
  if elemListN x (Cons y ys) && not (x == y) then 
    elemListN x ys
  else 
    True

{-@ lemma2 :: x:N -> y:N -> ys:ListN -> {lemma2_prop x y ys} @-}
lemma2 :: N -> N -> ListN -> Proof 
lemma2 x y ys = undefined

return []

{-@ reflect prop @-}
prop x y zs =
  if leqN x y && not (x == y) then 
    elemListN x (insertListN y zs) == elemListN x zs
  else
    True 

-- TODO: hangs for too long...
{-@ automatic-instances proof @-}
{-@
proof :: x:N -> y:N -> zs:ListN -> {prop x y zs}
@-}
-- [tactic|
-- proof :: N -> N -> ListN -> Proof
-- proof x y zs =
--   assert {leqN x y};
--   use {lemma x y};
--   induct zs as [/z zs'];
--   dismiss {leqN y z} requires [z];
--   use {lemma1 y z};
--   condition {x == z} requires [z];
--   use {proof x y zs'} requires [zs'];
--   trivial
-- |]
-- [tactic|
-- proof :: N -> N -> ListN -> Proof
-- proof x y zs =
--   assert {leqN x y};
--   induct zs as [/z zs'];
--   condition {leqN y z} requires [z];
--   dismiss {x == y};
--   dismiss {x == z} requires [z];
--   use {lemma2 x z (insertListN y zs)} requires [z];
--   use {proof x y zs'} requires [zs'];
--   trivial
-- |]
-- %tactic:begin:proof
proof :: N -> N -> ListN -> Proof
proof
  = \ x
      -> \ y
           -> \ zs
                -> if (leqN x) y then
                       case zs of
                         Nil -> if x == y then trivial else trivial
                         Cons z zs'
                           -> if (leqN y) z then
                                  if x == y then
                                      trivial
                                  else
                                      -- if x == z then
                                      --     trivial
                                      -- else
                                      --     (((lemma2 x) z) ((insertListN y) zs)
                                      --        &&& ((proof x) y) zs')
                                      trivial -- ! I need to specialize this because for some reason it takes a lot longer to verify otherwise
                              else
                                  if x == y then
                                      trivial
                                  else
                                      if x == z then
                                          trivial
                                      else
                                          (((lemma2 x) z) ((insertListN y) zs)
                                             &&& ((proof x) y) zs')
                   else
                       trivial
-- %tactic:end:proof
