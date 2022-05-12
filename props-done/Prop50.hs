{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop50 where

import Data
import Proof
import Tactic.Core.Quote

{-@ automatic-instances proof @-}
{-@
proof :: l:ListN -> {initListN l == takeListN (subN (lengthListN l) (S Z)) l}
@-}
-- %tactic:begin:proof
proof :: ListN -> Proof
proof = \l -> case l of
                  Data.Nil -> trivial
                  Data.Cons h t -> case t of
                                       Data.Nil -> trivial
                                       Data.Cons n_0 listN_1 -> proof t
-- %tactic:end:proof

-- [tactic|
-- proof :: ListN -> Proof
-- proof l = induct l as [|h t]; induct t
-- |]