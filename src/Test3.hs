{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module Test3 where

import Proof
import Tactic.Core.Quote
import Test2 (N (..), add, add_comm, add_m_Sn, add_n_Z)

-- {-@ automatic-instances add_assoc @-}
-- {-@
-- add_assoc :: l:N -> m:N -> n:N -> {add (add l m) n == add l (add m n)}
-- @-}
-- [tactic|
-- add_assoc :: N -> N -> N -> Proof
-- add_assoc l m n =
--   induct l;
--   induct m;
--   auto [Z, S, add, add_n_Z, add_m_Sn] 2;
-- |]
