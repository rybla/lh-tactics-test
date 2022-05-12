{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop53 where

import Data
import Proof
import Tactic.Core.Quote

{-@ automatic-instances lemma @-}
{-@
lemma :: n:N -> x:N -> xs:ListN -> {countListN n (insertListN x xs) == countListN n (Cons x xs)}
@-}
lemma :: N -> N -> ListN -> Proof 
lemma n x xs = undefined

return []

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> xs:ListN -> {countListN n xs == countListN n (sortListN xs)}
@-}
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof = \n -> \xs -> case xs of
                         Data.Nil -> trivial
                         Data.Cons n_0
                                   listN_1 -> proof n listN_1 &&& lemma n n_0 (sortListN listN_1)
-- %tactic:end:proof
-- [tactic|
-- proof :: N -> ListN -> Proof 
-- proof n xs =
--   induct xs;
--   auto [lemma, sortListN]
-- |]
