{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop55 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n xs ys =
  dropListN n (concatListN xs ys)
    == concatListN (dropListN n xs) (dropListN (subN n (lengthListN xs)) ys)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> xs:ListN -> ys:ListN -> {prop n xs ys}
@-}
-- %tactic:begin:proof
proof :: N -> ListN -> ListN -> Proof
proof = \n -> \xs -> \ys -> case n of
                                Data.Z -> case xs of
                                              Data.Nil -> trivial
                                              Data.Cons n_0 listN_1 -> trivial
                                Data.S n_0 -> case xs of
                                                  Data.Nil -> trivial
                                                  Data.Cons n_1 listN_2 -> proof n_0 listN_2 ys
-- %tactic:end:proof

-- [tactic|
-- proof :: N -> ListN -> ListN -> Proof 
-- proof n xs ys = induct n; induct xs
-- |]
