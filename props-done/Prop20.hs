{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop20 where

import Data
import Proof
import Tactic.Core.Quote

-- prop20_lemma

{-@ reflect prop20_lemma @-}
prop20_lemma :: N -> ListN -> Bool
prop20_lemma h t = lengthListN (insertListN h (sortListN t)) == S (lengthListN (sortListN t))

return []

{-@
prop20_lemma_proof :: h:N -> l:ListN -> {prop20_lemma h l}
@-}
prop20_lemma_proof :: N -> ListN -> Proof 
prop20_lemma_proof h l = undefined

-- prop20

{-@ reflect prop20 @-}
prop20 :: ListN -> Bool
prop20 l = lengthListN (sortListN l) == lengthListN l

return []

{-@ automatic-instances prop20_proof @-}
{-@
prop20_proof :: l:ListN -> {prop20 l}
@-}
-- %tactic:begin:prop20_proof
prop20_proof :: ListN -> Proof
prop20_proof = \l -> case l of
                         Data.Nil -> trivial
                         Data.Cons n_0
                                   listN_1 -> prop20_proof listN_1 &&& prop20_lemma_proof n_0 listN_1
-- %tactic:end:prop20_proof

-- [tactic|
-- prop20_proof :: ListN -> Proof
-- prop20_proof l =
--   induct l;
--   auto [prop20_lemma_proof]
-- |]
