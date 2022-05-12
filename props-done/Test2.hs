{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module Test2 where

import Proof
import Tactic.Core.Quote

{-@
data N = Z | S N
@-}
data N = Z | S N

{-@ reflect add @-}
add :: N -> N -> N
add Z n = n
add (S m) n = S (add m n)

return []

{-@ automatic-instances add_m_Sn @-}
{-@
add_m_Sn :: m:N -> n:N -> {add m (S n) == S (add m n)}
@-}
[tactic|
add_m_Sn :: N -> N -> Proof
add_m_Sn m n =
  induct m;
  auto [Z, S] 3
|]
-- add_m_Sn :: N -> N -> Proof
-- add_m_Sn = undefined

-- {-@ automatic-instances add_n_Z @-}
-- {-@
-- add_n_Z :: n:N -> {add n Z == n}
-- @-}
-- [tactic|
-- add_n_Z :: N -> Proof 
-- add_n_Z n =
--   induct n;
--   auto [Z, S, add] 2
-- |]
-- -- add_n_Z :: N -> Proof 
-- -- add_n_Z n = undefined

-- -- return [] -- since add_comm uses add_m_Sn, add_n_Z

-- {-@ automatic-instances add_comm @-}
-- {-@
-- add_comm :: m:N -> n:N -> {add m n == add n m}
-- @-}
-- [tactic|
-- add_comm :: N -> N -> Proof 
-- add_comm m n =
--   induct m;
--   auto [Z, S, add, add_n_Z, add_m_Sn] 2
-- |]
-- -- add_comm :: N -> N -> Proof 
-- -- add_comm m n = undefined
