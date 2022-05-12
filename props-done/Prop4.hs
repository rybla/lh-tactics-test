{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop4 where

import Data
import Proof
import Tactic.Core.Quote

-- {-@ reflect prop4 @-}
-- prop4 :: N -> ListN -> Bool
-- prop4 n xs = S (countListN n xs) == countListN n (Cons n xs)

-- {-@ automatic-instances prop4_proof @-}
-- {-@ reflect prop4_proof @-}
-- [tactic|
-- prop4_proof :: N -> ListN -> Proof
-- prop4_proof n xs =
--   trivial
-- |]