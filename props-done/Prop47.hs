{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop47 where

import Data
import Proof
import Tactic.Core.Quote

-- prop47_lemma

{-@ reflect prop47_lemma @-}
prop47_lemma :: N -> N -> Bool
prop47_lemma m n = maxN m n == maxN n m

return []

{-@ automatic-instances prop47_lemma_proof @-}
{-@
prop47_lemma_proof :: m:N -> n:N -> {prop47_lemma m n}
@-}
prop47_lemma_proof :: N -> N -> Proof
prop47_lemma_proof m n = undefined

-- prop47

{-@ reflect prop47 @-}
prop47 :: TreeN -> Bool
prop47 t = heightTreeN t == heightTreeN (mirrorTreeN t)

return []

{-@ automatic-instances prop47_proof @-}
{-@
prop47_proof :: t:TreeN -> {prop47 t}
@-}
-- %tactic:begin:prop47_proof
prop47_proof :: TreeN -> Proof
prop47_proof = \t -> case t of
                         Data.Leaf -> trivial
                         Data.Node n_0
                                   treeN_1
                                   treeN_2 -> prop47_proof treeN_2 &&& (prop47_proof treeN_1 &&& prop47_lemma_proof (heightTreeN treeN_2) (heightTreeN treeN_1)) 
                                   -- * finds even more efficient proof than I thought of!
-- %tactic:end:prop47_proof

-- [tactic|
-- prop47_proof :: TreeN -> Proof
-- prop47_proof t = induct t; auto [prop47_lemma_proof, heightTreeN, mirrorTreeN] 3
-- |]