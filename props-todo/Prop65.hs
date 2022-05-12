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
proof
  = \ i
      -> \ m
           -> case i of
                Z -> (lemma m) m
                S n_0
                  -> ((lemma m) m
                        &&&
                          ((lemma m) n_0
                             &&&
                               ((lemma n_0) m
                                  &&&
                                    ((lemma n_0) n_0 &&& ((proof n_0) m &&& (proof n_0) n_0)))))
-- %tactic:end:proof

-- i < S (m + i)
-- S i' < S (m + S i')
-- S i' < S (S (m + i')) `by` lemma m i'
-- i' < S (m + i') 
