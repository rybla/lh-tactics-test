{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop51 where

import Data
import Proof
import Tactic.Core.Quote

{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> x:N -> {initListN (concatListN xs (singletonListN x)) == xs}
@-}
-- %tactic:begin:proof
proof :: ListN -> N -> Proof
proof = \xs -> \x -> case xs of
                         Data.Nil -> trivial
                         Data.Cons n_0 listN_1 -> proof listN_1 x
-- %tactic:end:proof

-- [tactic|
-- proof :: ListN -> N -> Proof
-- proof xs x = induct xs
-- |]