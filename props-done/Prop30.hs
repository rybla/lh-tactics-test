{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop30 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop x xs = elemListN x (insertListN x xs)

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> xs:ListN -> {prop x xs}
@-}
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof n xs = 
--   induct xs as [/x' xs'];
--   dismiss {leN n x'} requires [x'];
--   dismiss {n == x'} requires [x']
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof = \n -> \xs -> case xs of
                         Data.Nil -> trivial
                         Data.Cons x' xs' -> if leN n x'
                                              then trivial
                                              else if n == x' then trivial else proof n xs'
-- %tactic:end:proof
-- -- %tactic:begin:proof
-- proof :: N -> ListN -> Proof
-- proof
--   = \ n
--       -> \ xs
--            -> case xs of
--                 Nil -> trivial
--                 Cons x' xs'
--                   -> if (leN n) x' then
--                       trivial
--                      else
--                          if n == x' then
--                              trivial
--                          else
--                              proof n xs'
-- -- %tactic:end:proof
