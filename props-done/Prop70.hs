{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop70 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop m n = if leqN m n then leqN m (S n) else True

{-@ automatic-instances proof @-}
{-@
proof :: m:N -> n:N -> {prop m n}
@-}
-- [tactic|
-- proof :: N -> N -> Proof
-- proof m n =
--   assert {leqN m n};
--   induct m;
--   induct n
-- |]
-- %tactic:begin:proof
proof :: N -> N -> Proof
proof = \m -> \n -> if leqN m n
                     then case m of
                              Data.Z -> case n of
                                            Data.Z -> trivial
                                            Data.S n_0 -> trivial
                              Data.S n_0 -> case n of
                                                Data.Z -> trivial
                                                Data.S n_1 -> proof n_0 n_1
                     else trivial
