{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop42 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n x xs = takeListN (S n) (Cons x xs) == Cons x (takeListN n xs)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> x:N -> xs:ListN -> {prop n x xs}
@-}
-- [tactic|
-- proof :: N -> N -> ListN -> Proof
-- proof n x xs = trivial
-- |]
-- %tactic:begin:proof
proof :: N -> N -> ListN -> Proof
proof = \n -> \x -> \xs -> trivial
-- %tactic:end:proof
