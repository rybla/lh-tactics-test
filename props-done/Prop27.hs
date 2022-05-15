{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop27 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop x xs ys = 
  if elemListN x ys then 
    elemListN x (concatListN xs ys)
  else 
    True

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> xs:ListN -> ys:ListN -> {prop x xs ys}
@-}
-- elemListN x1 (concatListN (Cons x2 xs) ys)
-- elemListN x1 (Cons x2 (concatListN xs ys))
-- if x1 == x2 then 
--   QED
-- else
--   elemListN x1 (concatListN xs ys)
-- [tactic|
-- proof :: N -> ListN -> ListN -> Proof
-- proof x xs ys =
--   induct xs;
--   condition {elemListN x ys}
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> ListN -> Proof
proof = \x -> \xs -> \ys -> case xs of
                                Data.Nil -> if elemListN x ys then trivial else trivial
                                Data.Cons n_0 listN_1 -> if elemListN x ys
                                                          then proof x listN_1 ys
                                                          else trivial
-- %tactic:end:proof
