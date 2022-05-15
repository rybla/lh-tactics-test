{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop76 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n m xs = 
  if n == m 
    then True 
    else countListN n (concatListN xs (singletonListN m)) == countListN n xs

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> m:N -> xs:ListN -> {prop n m xs}
@-}
-- [tactic|
-- proof :: N -> N -> ListN -> Proof
-- proof n m xs =
--   assert {not (n == m)};
--   induct xs
-- |]
-- %tactic:begin:proof
proof :: N -> N -> ListN -> Proof
proof = \n -> \m -> \xs -> if not (n == m)
                            then case xs of
                                     Data.Nil -> trivial
                                     Data.Cons n_0 listN_1 -> proof n m listN_1
                            else trivial
-- %tactic:end:proof
