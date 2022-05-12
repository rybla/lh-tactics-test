{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop52 where

import Data
import Proof
import Tactic.Core.Quote

{-@ automatic-instances lemma @-}
{-@
lemma :: n:N -> xs:ListN -> ys:ListN -> {countListN n (concatListN xs ys) == countListN n (concatListN ys xs)}
@-}
lemma :: N -> ListN -> ListN -> Proof
lemma n xs ys = undefined

return []

-- * takes 3m47s to prune
{-@ automatic-instances proof @-}
{-@
proof :: n:N -> xs:ListN -> {countListN n xs == countListN n (reverseListN xs)}
@-}
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof = \n -> \xs -> case xs of
                         Data.Nil -> trivial
                         Data.Cons n_0
                                   listN_1 -> proof n listN_1 &&& lemma n (singletonListN n_0) (reverseListN listN_1)
-- %tactic:end:proof
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof n xs =
--   induct xs;
--   auto [lemma, reverseListN, singletonListN] 3
-- |]
