{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop65 where

import Data
import Proof
import Tactic.Core.Quote

{-@
lemma :: m:N -> n:N -> {addN m (S n) == S (addN m n)}
@-}
lemma :: N -> N -> Proof 
lemma m n = undefined

return []

{-@ reflect prop @-}
prop i m = leN i (S (addN m i))

{-@ automatic-instances proof @-}
{-@
proof :: i:N -> m:N -> {prop i m}
@-}
-- [tactic|
-- proof :: N -> N -> Proof
-- proof i m = induct i; auto [lemma]
-- |]
-- %tactic:begin:proof
proof :: N -> N -> Proof
proof = \i -> \m -> case i of
                        Data.Z -> trivial
                        Data.S n_0 -> proof n_0 m &&& lemma m n_0
-- %tactic:end:proof

-- leN (S i) (S (addN m (S i)))
-- leN i (addN m (S i))
-- leN i (S (addN m i))
