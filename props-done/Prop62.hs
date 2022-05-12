{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop62 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop Nil x = True
prop xs x = lastListN' (Cons x xs) == lastListN' xs

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> x:N -> {prop xs x}
@-}
-- %tactic:begin:proof
proof :: ListN -> N -> Proof
proof = \xs -> \x -> case xs of
                         Data.Nil -> trivial
                         Data.Cons n_0 listN_1 -> trivial
-- %tactic:end:proof

-- [tactic|
-- proof :: ListN -> N -> Proof
-- proof xs x = induct xs
-- |]