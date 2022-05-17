{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop58 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n xs ys = 
  dropListN2 n (zipListN xs ys) ==
  zipListN (dropListN n xs) (dropListN n ys)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> xs:ListN -> ys:ListN -> {prop n xs ys}
@-}
-- [tactic|
-- proof :: N -> ListN -> ListN -> Proof
-- proof n xs ys =
--   induct n;
--   induct xs;
--   induct ys
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> ListN -> Proof
proof = \n -> \xs -> \ys -> case n of
                                Data.Z -> case xs of
                                              Data.Nil -> case ys of
                                                              Data.Nil -> trivial
                                                              Data.Cons n_0 listN_1 -> trivial
                                              Data.Cons n_0 listN_1 -> case ys of
                                                                           Data.Nil -> trivial
                                                                           Data.Cons n_2
                                                                                     listN_3 -> trivial
                                Data.S n_0 -> case xs of
                                                  Data.Nil -> case ys of
                                                                  Data.Nil -> trivial
                                                                  Data.Cons n_1 listN_2 -> trivial
                                                  Data.Cons n_1 listN_2 -> case ys of
                                                                               Data.Nil -> trivial
                                                                               Data.Cons n_3
                                                                                         listN_4 -> proof n_0 listN_2 listN_4
-- %tactic:end:proof
