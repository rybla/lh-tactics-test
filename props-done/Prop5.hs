{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop5 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n x xs =
  if n == x then 
    S (countListN n xs) == countListN n (Cons x xs)
  else 
    True

{-@ automatic-instances proof @-}
{-@
proof :: x:N -> n:N -> xs:ListN -> {prop x n xs}
@-}
-- [tactic|
-- proof :: N -> N -> ListN -> Proof
-- proof x n xs =
--   condition {n == x}
-- |]
-- %tactic:begin:proof
proof :: N -> N -> ListN -> Proof
proof = \x -> \n -> \xs -> if n == x then trivial else trivial
-- %tactic:end:proof
