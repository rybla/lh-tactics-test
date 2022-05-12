{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop63 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n xs = 
  implies 
    (leN n (lengthListN xs))
    (lastListN' (dropListN n xs) == lastListN' xs)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> xs:ListN -> {prop n xs}
@-}
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof n xs =
--   induct xs;
--   destruct n
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof = \n -> \xs -> case xs of
                         Data.Nil -> case n of
                                         Data.Z -> trivial
                                         Data.S n_0 -> trivial
                         Data.Cons n_0 listN_1 -> case n of
                                                      Data.Z -> trivial
                                                      Data.S n_2 -> proof n_2 listN_1
-- %tactic:end:proof
