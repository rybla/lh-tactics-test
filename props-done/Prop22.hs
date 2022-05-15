{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop22 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop a b c = maxN (maxN a b) c == maxN a (maxN b c)

{-@ automatic-instances proof @-}
{-@
proof :: a:N -> b:N -> c:N -> {prop a b c}
@-}
-- [tactic|
-- proof :: N -> N -> N -> Proof
-- proof a b c = induct a; induct b; induct c
-- |]
-- %tactic:begin:proof
proof :: N -> N -> N -> Proof
proof = \a -> \b -> \c -> case a of
                              Data.Z -> case b of
                                            Data.Z -> case c of
                                                          Data.Z -> trivial
                                                          Data.S n_0 -> trivial
                                            Data.S n_0 -> case c of
                                                              Data.Z -> trivial
                                                              Data.S n_1 -> trivial
                              Data.S n_0 -> case b of
                                                Data.Z -> case c of
                                                              Data.Z -> trivial
                                                              Data.S n_1 -> trivial
                                                Data.S n_1 -> case c of
                                                                  Data.Z -> trivial
                                                                  Data.S n_2 -> proof n_0 n_1 n_2
-- %tactic:end:proof
