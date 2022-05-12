{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop48 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop :: ListN -> Bool 
prop Nil = True
prop (Cons h t) = concatListN (initListN (Cons h t)) (singletonListN (lastListN h t)) == Cons h t

return []

{-@ automatic-instances proof @-}
{-@
proof :: l:ListN -> {prop l}
@-}
-- %tactic:begin:proof
proof :: ListN -> Proof
proof = \l -> case l of
                  Data.Nil -> trivial
                  Data.Cons n_0 listN_1 -> proof listN_1
-- %tactic:end:proof

-- [tactic|
-- proof :: ListN -> Proof
-- proof l = induct l
-- |]
