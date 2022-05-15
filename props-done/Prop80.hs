{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop80 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop n xs ys =
  takeListN n (concatListN xs ys) ==
  concatListN (takeListN n xs) (takeListN (subN n (lengthListN xs)) ys)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> xs:ListN -> ys:ListN -> {prop n xs ys}
@-}

-- proof :: N -> ListN -> ListN -> Proof
-- proof n Nil ys = trivial
-- proof Z (Cons x xs) ys =
--   -- takeListN Z (concatListN (Cons x xs) ys)
--   -- Nil
--   -- concatListN Nil Nil
--   -- concatListN Nil (takeListN Z ys)
--   -- concatListN (takeListN Z (Cons x xs)) (takeListN (subN Z (lengthListN (Cons x xs))) ys)
--   trivial
-- proof (S n) (Cons x xs) ys =
--   -- takeListN (S n) (concatListN (Cons x xs) ys)
--   -- ...
--   -- concatListN (takeListN (S n) (Cons x xs)) (takeListN (subN (S n) (lengthListN (Cons x xs))) ys)
--   undefined


-- [tactic|
-- proof :: N -> ListN -> ListN -> Proof
-- proof n xs ys =
--   induct n;
--   induct xs
-- |]
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
