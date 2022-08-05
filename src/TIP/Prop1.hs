{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop1 where

import Data
import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core.Quote

{-@ reflect prop1 @-}
prop1 :: N -> ListN -> Bool
prop1 n xs = concatListN (takeListN n xs) (dropListN n xs) == xs

return []

{-@ automatic-instances prop1_proof @-}
{-@
prop1_proof :: n:N -> l:ListN -> {prop1 n l}
@-}
[tactic|
prop1_proof :: N -> ListN -> Proof
prop1_proof n l =
  induct n;
  induct l as [/x y];
  auto [] 2
|]

-- -- %tactic:begin:prop1_proof
-- prop1_proof :: N -> ListN -> Proof
-- prop1_proof
--   = \ n
--       -> \ l
--            -> case n of
--                 Z -> case l of
--                        Nil -> trivial
--                        Cons n_0 listN_1 -> trivial
--                 S n_0
--                   -> case l of
--                        Nil -> trivial
--                        Cons n_1 listN_2 -> (prop1_proof n_0) listN_2
-- -- %tactic:end:prop1_proof
