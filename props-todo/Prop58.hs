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

-- ! FAILS
{-@ automatic-instances proof @-}
{-@
proof :: n:N -> xs:ListN -> ys:ListN -> {prop n xs ys}
@-}
-- %tactic:begin:proof
proof :: N -> ListN -> ListN -> Proof
proof
  = \ n
      -> \ xs
           -> \ ys
                -> case n of
                     Z -> case xs of
                            Nil
                              -> case ys of
                                   Nil -> trivial
                                   Cons n_0 listN_1 -> trivial
                            Cons n_0 listN_1
                              -> case ys of
                                   Nil -> trivial
                                   Cons n_2 listN_3 -> trivial
                     S n_0
                       -> case xs of
                            Nil
                              -> case ys of
                                   Nil -> trivial
                                   Cons n_1 listN_2 -> trivial
                            Cons n_1 listN_2
                              -> case ys of
                                   Nil -> trivial
                                   Cons n_3 listN_4 -> ((proof n_0) listN_2) listN_4
-- %tactic:end:proof

-- [tactic|
-- proof :: N -> ListN -> ListN -> Proof
-- proof n xs ys =
--   induct n;
--   induct xs;
--   induct ys
-- |]
