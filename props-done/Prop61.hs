{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop61 where

import Data
import Proof
import Tactic.Core.Quote

{-@
lemma :: xs:ListN -> {concatListN xs Nil == xs}
@-}
lemma :: ListN -> Proof 
lemma xs = undefined

return []

{-@ reflect prop @-}
prop xs ys = 
  lastListN' (concatListN xs ys) == 
  lastOfTwo xs ys

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> ys:ListN -> {prop xs ys}
@-}
-- [tactic|
-- proof :: ListN -> ListN -> Proof 
-- proof xs ys = induct xs; auto [Cons]
-- |]
-- %tactic:begin:proof
proof :: ListN -> ListN -> Proof
proof = \xs -> \ys -> case xs of
                          Data.Nil -> trivial
                          Data.Cons n_0
                                    listN_1 -> proof listN_1 (Cons n_0 listN_1) &&& proof listN_1 ys
-- %tactic:end:proof
