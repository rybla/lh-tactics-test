{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop9 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop9 @-}
prop9 :: N -> N -> N -> Bool
prop9 i j k = subN (addN i j) k == subN i (addN j k)

-- [tactic|
-- prop9_proof :: N -> N -> N -> Proof
-- prop9_proof i j k =
--   induct j
-- |]
