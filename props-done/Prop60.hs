{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop60 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop xs Nil = True
prop xs ys = lastListN' (concatListN xs ys) == lastListN' ys

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> ys:ListN -> {prop xs ys}
@-}
-- [tactic|
-- proof :: ListN -> ListN -> Proof
-- proof xs ys = induct xs; destruct ys; auto [Cons] 3
-- |]
-- %tactic:begin:proof
proof :: ListN -> ListN -> Proof
proof = \xs -> \ys -> case xs of
                          Data.Nil -> case ys of
                                          Data.Nil -> trivial
                                          Data.Cons n_0 listN_1 -> trivial
                          Data.Cons n_0 listN_1 -> case ys of
                                                       Data.Nil -> trivial
                                                       Data.Cons n_2
                                                                 listN_3 -> proof listN_1 (Cons n_2 listN_3)
-- %tactic:end:proof
