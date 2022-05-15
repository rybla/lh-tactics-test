{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop28 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop x xs = elemListN x (concatListN xs (singletonListN x))

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> xs:ListN -> {prop x xs}
@-}
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof x xs = induct xs
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof = \x -> \xs -> case xs of
                         Data.Nil -> trivial
                         Data.Cons n_0 listN_1 -> proof x listN_1
-- %tactic:end:proof
