{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop67 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop Nil = True
prop xs = lengthListN (initListN xs) == subN (lengthListN xs)  (S Z)

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> {prop xs}
@-}
-- [tactic|
-- proof :: ListN -> Proof
-- proof xs = 
--   induct xs as [/x xs'];
--   destruct xs'
-- |]
-- %tactic:begin:proof
proof :: ListN -> Proof
proof = \xs -> case xs of
                   Data.Nil -> trivial
                   Data.Cons x xs' -> case xs' of
                                          Data.Nil -> trivial
                                          Data.Cons n_0 listN_1 -> proof xs'
-- %tactic:end:proof

-- lengthListN (initListN (Cons x xs)) == subN (lengthListN (Cons x xs))  (S Z)
-- if xs == Nil
--   lengthListN (initListN (Cons x Nil)) == subN (lengthListN (Cons x Nil))  (S Z)
--   Z == subN (S Z) (S Z)
-- if xs == Cons x' xs'
--   lengthListN (initListN (Cons x (Cons x' xs'))) == subN (lengthListN (Cons x (Cons x' xs')))  (S Z)
--   lengthListN (Cons x (initListN xs')) == subN (S (S (lengthListN xs'))) (S Z)
--   S (lengthListN (initListN xs')) == S (lengthListN xs')
--   lengthListN (initListN xs') == lengthListN xs'
--   lengthListN xs' == lengthListN xs'
