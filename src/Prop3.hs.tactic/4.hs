{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module Prop3 where

import Data
import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core.Quote

{-@ reflect prop3 @-}
prop3 :: N -> NL -> NL -> Bool
prop3 n xs ys = leqN (countNL n xs) (countNL n (concatNL xs ys))

return []

{-@ automatic-instances prop3_proof @-}
{-@
prop3_proof :: n:N -> xs:NL -> ys:NL -> {prop3 n xs ys}
@-}
[tactic|
prop3_proof :: N -> NL -> NL -> Proof
prop3_proof n xs ys =
  use {leqN_addN (countNL n xs) (countNL n ys)}
  use {addN_countNL_concatNL n xs ys}
|]

{-@ automatic-instances leqN_addN @-}
{-@ 
assume leqN_addN :: m:N -> n:N -> {leqN m (addN m n)}
@-}
leqN_addN :: N -> N -> Proof
leqN_addN m n = trivial

{-@ automatic-instances addN_countNL_concatNL @-}
{-@
assume addN_countNL_concatNL :: n:N -> xs:NL -> ys:NL -> {countNL n (concatNL xs ys) == addN (countNL n xs) (countNL n ys)}
@-}
addN_countNL_concatNL :: N -> NL -> NL -> Proof
addN_countNL_concatNL n xs ys = trivial

