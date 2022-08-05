{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop39 where

import Data
import Proof
import Tactic.Core.Quote

{-@
lemma :: n:N -> {addN n Z == n}
@-}
lemma :: N -> Proof 
lemma = undefined

return []

{-@ reflect prop @-}
prop n x xs = 
  addN (countListN n (singletonListN x)) (countListN n xs) ==
  countListN n (Cons x xs)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> x:N -> xs:ListN -> {prop n x xs}
@-}
-- [tactic|
-- proof :: N -> N -> ListN -> Proof
-- proof n x xs =
--   destruct xs as [/x' xs'];
--   condition {n == x};
--   [x']: condition {n == x'};
--   trivial
-- |]
-- %tactic:begin:proof
proof :: N -> N -> ListN -> Proof
proof = \n -> \x -> \xs -> case xs of
                               Data.Nil -> if n == x then trivial else trivial
                               Data.Cons x' xs' -> if n == x
                                                    then if n == x' then trivial else trivial
                                                    else if n == x' then trivial else trivial
-- %tactic:end:proof
-- -- %tactic:begin:proof
-- proof :: N -> N -> ListN -> Proof
-- proof = \n -> \x -> \xs -> case xs of
--                                Data.Nil -> if n == x then trivial else trivial
--                                Data.Cons x' xs' -> if n == x
--                                                     then if n == x' then trivial else trivial
--                                                     else if n == x' then trivial else trivial
-- -- %tactic:end:proof
