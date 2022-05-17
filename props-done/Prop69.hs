{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop69 where

import Data
import Proof
import Tactic.Core.Quote

{-@
comm_addN :: m:N -> n:N -> {addN m n == addN n m}
@-}
comm_addN :: N -> N -> Proof 
comm_addN m n = undefined

return []

{-@ reflect prop @-}
prop m n = leqN m (addN n m)

{-@ automatic-instances proof @-}
{-@
proof :: m:N -> n:N -> {prop m n}
@-}
-- [tactic|
-- proof :: N -> N -> Proof
-- proof m n =
--   induct m;
--   auto [comm_addN, S]
-- |]
-- %tactic:begin:proof
proof :: N -> N -> Proof
proof = \m -> \n -> case m of
                        Data.Z -> trivial
                        Data.S n_0 -> proof n_0 n &&& (comm_addN (S n_0) (S n) &&& comm_addN (S n) n_0)
-- %tactic:end:proof

-- leqN (S m) (addN n (S m))
