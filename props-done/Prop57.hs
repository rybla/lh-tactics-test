{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop57 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n m xs = dropListN n (takeListN m xs) == takeListN (subN m n) (dropListN n xs)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> m:N -> xs:ListN -> {prop n m xs}
@-}
-- %tactic:begin:proof
proof :: N -> N -> ListN -> Proof
proof = \n -> \m -> \xs -> case n of
                               Data.Z -> case m of
                                             Data.Z -> case xs of
                                                           Data.Nil -> trivial
                                                           Data.Cons n_0 listN_1 -> trivial
                                             Data.S n_0 -> case xs of
                                                               Data.Nil -> trivial
                                                               Data.Cons n_1 listN_2 -> trivial
                               Data.S n_0 -> case m of
                                                 Data.Z -> case xs of
                                                               Data.Nil -> trivial
                                                               Data.Cons n_1 listN_2 -> trivial
                                                 Data.S n_1 -> case xs of
                                                                   Data.Nil -> trivial
                                                                   Data.Cons n_2
                                                                             listN_3 -> proof n_0 n_1 listN_3
-- %tactic:end:proof

-- [tactic|
-- proof :: N -> N -> ListN -> Proof 
-- proof n m xs =
--   induct n;
--   induct m;
--   induct xs
-- |]
