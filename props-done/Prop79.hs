{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop79 where

import Data
import Proof
import Tactic.Core.Quote

{-@
lemma :: m:N -> n:N -> {subN m n == S (subN m (S n))}
@-}
lemma :: N -> N -> Proof 
lemma m n = undefined

return []

{-@ reflect prop @-}
prop m n k =
  subN (subN (S m) n) (S k) ==
  subN (subN m n) k

{-@ automatic-instances proof @-}
{-@
proof :: m:N -> n:N -> k:N -> {prop m n k}
@-}

-- proof :: N -> N -> N -> Proof
-- proof m Z k = trivial
-- proof m (S n) k = 
--   -- (S m - S n) - S k
--   -- (m - n) - S k
--   -- S (m - S n) - S k -- lemma
--   -- (m - S n) - S k
--   -- ----
--   -- GOAL: (m - S n) - k
--   -- IH: (S m - n) - S k == (m - n) - k
--   --
--   lemma m n
  

-- [tactic|
-- proof :: N -> N -> N -> Proof
-- proof m n k = 
--   destruct n as [/n'];
--   [n']: use {lemma m n'}
-- |]
-- %tactic:begin:proof
proof :: N -> N -> N -> Proof
proof = \m -> \n -> \k -> case n of
                              Data.Z -> trivial
                              Data.S n' -> lemma m n' &&& trivial
-- %tactic:end:proof

-- -- * eventually works, but takes annoyingly long
-- [tactic|
-- proof :: N -> N -> N -> Proof
-- proof m n k = 
--   destruct n;
--   auto [lemma] 2
-- |]
