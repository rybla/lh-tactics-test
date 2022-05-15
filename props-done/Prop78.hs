{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop78 where

import Data
import Proof
import Tactic.Core.Quote

{-@
lemma :: x:N -> ys:ListN -> {sortedListN (insertListN x ys) == sortedListN ys} 
@-}
lemma :: N -> ListN -> Proof 
lemma x ys = undefined

return []

{-@ reflect prop @-}
prop xs = sortedListN (sortListN xs)

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> {prop xs}
@-}
-- [tactic|
-- proof :: ListN -> Proof
-- proof xs =
--   induct xs;
--   auto [lemma, sortListN]
-- |]
-- %tactic:begin:proof
proof :: ListN -> Proof
proof = \xs -> case xs of
                   Data.Nil -> trivial
                   Data.Cons n_0
                             listN_1 -> proof listN_1 &&& lemma n_0 (sortListN listN_1)
-- %tactic:end:proof
