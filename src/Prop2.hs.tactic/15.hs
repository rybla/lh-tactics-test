{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module Prop2 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop2 @-}
prop2 :: N -> NL -> NL -> Bool
prop2 n xs ys = addN (countNL n xs) (countNL n ys) == countNL n (concatNL xs ys)

return []

{-@ automatic-instances prop2_proof @-}
{-@
prop2_proof :: n:N -> xs:NL -> ys:NL -> {prop2 n xs ys}
@-}
[tactic|
prop2_proof :: N -> NL -> NL -> Proof
prop2_proof n xs ys = induct xs
|]
