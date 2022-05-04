{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module Prop2 where

import Data
import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core.Quote

{-@ reflect prop2 @-}
prop2 :: N -> NL -> NL -> Bool
prop2 n xs ys = addN (countNL n xs) (countNL n ys) == countNL n (concatNL xs ys)

return []

{-@ automatic-instances prop2_check @-}
{-@
prop2_check :: n:N -> xs:NL -> ys:NL -> {prop2 n xs ys}
@-}
[tactic|
prop2_check :: N -> NL -> NL -> Proof
prop2_check n xs ys =
  induct xs;
  auto [] 2
|]

-- prop2_check :: N -> NL -> NL -> Proof
-- prop2_check n xs ys =
--   case xs of
--     Cons x xs ->
--       -- addN (countNL n (Cons x xs)) (countNL n ys) == countNL n (concatNL (Cons x xs) ys)
--       -- addN (countNL n (Cons x xs)) (countNL n ys) == countNL n (Cons x (concatNL xs ys))
--       -- if n == x then
--       --   S (addN (countNL n xs) (countNL n ys)) == S (countNL n (concatNL xs ys))
--       --   addN (countNL n xs) (countNL n ys) == countNL n (concatNL xs ys) ***
--       -- else
--       --   addN (countNL n xs) (countNL n ys) ==  countNL n (concatNL xs ys) ***
--       prop2_check n xs ys
--     Nil ->
--       -- addN (countNL n Nil) (countNL n ys) == countNL n (concatNL Nil ys)
--       -- addN Z (countNL n ys) == countNL n ys ***
--       -- countNL n ys == countNL n ys
--       trivial
