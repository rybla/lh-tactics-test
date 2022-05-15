{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop13 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n x xs = dropListN (S n) (Cons x xs) == dropListN n xs

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
