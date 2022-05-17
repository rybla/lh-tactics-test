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
lemma1 :: n:N -> m:N -> {addN n (S m) == S (addN n m)}
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
prop n m xs =
  dropListN n (dropListN m xs) == 
  dropListN (addN n m) xs

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> m:N -> xs:ListN -> {prop n m xs}
@-}
-- [tactic|
-- proof :: N -> N -> ListN -> Proof 
-- proof n m xs =
--   induct n;
--   induct xs;
--   auto [lemma2]
-- |]
-- %tactic:begin:proof
proof :: N -> N -> ListN -> Proof
proof = \n -> \m -> \xs -> case n of
                               Data.Z -> case xs of
                                             Data.Nil -> trivial
                                             Data.Cons n_0 listN_1 -> trivial
                               Data.S n_0 -> case xs of
                                                 Data.Nil -> trivial
                                                 Data.Cons n_1
                                                           listN_2 -> proof n_0 m listN_2 &&& lemma2 m
-- %tactic:end:proof
