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

{-@ idr_addN :: n:N -> {addN n Z == n} @-}
idr_addN :: N -> Proof 
idr_addN n = undefined

{-@ addN_m_Sn :: m:N -> n:N -> {addN m (S n) == S (addN m n)} @-}
addN_m_Sn :: N -> N -> Proof 
addN_m_Sn m n = undefined

{-@ addN_n_n :: n:N -> {subN n n == Z} @-}
addN_n_n :: N -> Proof 
addN_n_n n = undefined

return []

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> m:N -> {subN (addN m n) n == m}
@-}
-- [tactic|
-- proof :: N -> N -> Proof
-- proof n m =
--   induct n;
--   auto [idr_addN, addN_m_Sn, addN_n_n] 2
-- |]
-- %tactic:begin:proof
proof :: N -> N -> Proof
proof = \n -> \m -> case n of
                        Data.Z -> idr_addN m
                        Data.S n_0 -> proof n_0 m &&& addN_m_Sn m n_0
-- %tactic:end:proof
