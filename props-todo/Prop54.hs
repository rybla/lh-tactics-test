{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop54 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect lemma1_prop @-}
lemma1_prop :: N -> N -> Bool
lemma1_prop n m = case m of
  Z -> True
  S m' -> addN n m == S (addN n m')

{-@
lemma1 :: n:N -> m:N -> {lemma1_prop n m}
@-}
lemma1 :: N -> N -> Proof
lemma1 n m = undefined -- ! ADMITTED

{-@
lemma2 :: n:N -> m:N -> {S (subN n m) == subN (S n) m}
@-}
lemma2 :: N -> N -> Proof 
lemma2 n m = undefined -- ! ADMITTED

return []

-- ! FAILS
{-@ automatic-instances proof @-}
{-@
proof :: n:N -> m:N -> {subN (addN m n) n == m}
@-}
proof = undefined -- TODO
-- [tactic|
-- proof :: N -> N -> Proof
-- proof n m =
--   induct n;
--   induct m;
--   auto [lemma1, lemma2, addN] 3
-- |]
