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

-- ! FAILS
{-@ automatic-instances proof @-}
{-@
proof :: m:N -> n:N -> {prop m n}
@-}
[tactic|
proof :: N -> N -> Proof
proof m n =
  induct n;
  auto [comm_addN]
|]

-- use {comm_addN n m};
-- induct n as [/n'];
-- use {comm_addN n' m} requires [n']
