{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop56 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect lemma1_prop @-}
lemma1_prop n m = case m of 
  Z -> True 
  S m' -> addN n m == S (addN n m')

{-@ 
lemma1 :: n:N -> m:N -> {lemma1_prop n m}
@-}
lemma1 :: N -> N -> Proof 
lemma1 n m = undefined

{-@
lemma2 :: n:N -> {addN n Z == Z}
@-}
lemma2 :: N -> Proof 
lemma2 n = undefined

return []

{-@ reflect prop @-}
prop n m xs = dropListN n (dropListN m xs) == dropListN (addN n m) xs

-- ! FAILS
{-@ automatic-instances proof @-}
{-@
proof :: n:N -> m:N -> xs:ListN -> {prop n m xs}
@-}
-- [tactic|
-- proof :: N -> N -> ListN -> Proof 
-- proof n m xs =
--   induct n;
--   induct m;
--   induct xs;
--   auto [lemma1]
-- |]
proof :: N -> N -> ListN -> Proof 
proof Z _ _ = trivial
proof n Z _ = lemma2 n
proof (S n) (S m) Nil = trivial
proof n@(S n') m@(S m') (Cons h t) = 
  trivial 
    `by` lemma1 n m 
    `by` proof n' m' t
