{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop83 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop xs ys zs = 
  zipListN (concatListN xs ys) zs ==
  concatListN2
    (zipListN xs (takeListN (lengthListN xs) zs))
    (zipListN ys (dropListN (lengthListN xs) zs))

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> ys:ListN -> zs:ListN -> {prop xs ys zs}
@-}
-- [tactic|
-- proof :: ListN -> ListN -> ListN -> Proof
-- proof xs ys zs =
--   induct xs;
--   induct zs
-- |]
-- %tactic:begin:proof
proof :: ListN -> ListN -> ListN -> Proof
proof = \xs -> \ys -> \zs -> case xs of
                                 Data.Nil -> case zs of
                                                 Data.Nil -> trivial
                                                 Data.Cons n_0 listN_1 -> trivial
                                 Data.Cons n_0 listN_1 -> case zs of
                                                              Data.Nil -> trivial
                                                              Data.Cons n_2
                                                                        listN_3 -> proof listN_1 ys listN_3
