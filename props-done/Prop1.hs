{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--compile-spec" @-}
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
  induct l;
  auto [] 2
|]

-- {-@ automatic-instances prop1_proof @-}
-- {-@
-- prop1_proof :: x:N -> l:ListN -> {prop1 x l}
-- @-}
-- prop1_proof :: N -> ListN -> Proof
-- -- prop1_proof x l = undefined
-- prop1_proof Z l = trivial
-- prop1_proof (S n) Nil = trivial
-- prop1_proof (S n) (Cons x l) = prop1_proof n l
--   -- -- HYP
--   -- concatListN (takeListN (S n) (Cons x l)) (dropListN (S n) (Cons x l))
--   -- concatListN (Cons x (takeListN n l)) (dropListN n l)
--   -- Cons x (concatListN (takeListN n l) (dropListN n l))
--   -- --
--   -- -- IH
--   -- concatListN n l

