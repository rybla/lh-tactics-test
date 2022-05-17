{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop59 where

import Data
import Proof
import Tactic.Core.Quote

{-@
idr_concat :: xs:ListN -> {concatListN xs Nil == xs}
@-}
idr_concat :: ListN -> Proof 
idr_concat xs = undefined

return []

{-@ reflect prop @-}
prop xs ys@Nil = lastListN' (concatListN xs ys) == lastListN' xs
prop xs ys = True

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> ys:ListN -> {prop xs ys}
@-}
-- [tactic|
-- proof :: ListN -> ListN -> Proof 
-- proof xs ys =
--   induct ys;
--   auto [idr_concat]
-- |]
-- %tactic:begin:proof
proof :: ListN -> ListN -> Proof
proof = \xs -> \ys -> case ys of
                          Data.Nil -> idr_concat xs
                          Data.Cons n_0 listN_1 -> trivial
-- %tactic:end:proof
