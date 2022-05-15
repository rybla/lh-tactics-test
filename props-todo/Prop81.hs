{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop81 where

import Data
import Proof
import Tactic.Core.Quote

{-@
comm_addN :: n:N -> m:N -> {addN n m == addN m n}
@-}
comm_addN :: N -> N -> Proof
comm_addN n m = undefined

return []

{-@ reflect prop @-}
prop n m xs =
  takeListN n (dropListN m xs) ==
  dropListN m (takeListN (addN n m) xs)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> m:N -> xs:ListN -> {prop n m xs}
@-}


-- -- * PASSES
-- proof :: N -> N -> ListN -> Proof
-- proof m n xs@Nil = trivial
-- proof Z Z (Cons x xs) = trivial
-- proof Z (S m) (Cons x xs) = proof Z m xs
-- proof (S n) Z (Cons x xs) = 
--   comm_addN (S n) Z
-- proof (S n) (S m) (Cons x xs) = 
--   comm_addN (S m) (S n) &&&
--   comm_addN m (S n) &&&
--   proof (S n) m xs

-- ! FAILS
[tactic|
proof :: N -> N -> ListN -> Proof
proof n m xs =
  destruct n as [/n'];
  induct m as [/m'];
  induct xs as [/x xs'];
  use {comm_addN n Z};
  use {comm_addN m n};
  use {proof n m' xs'} requires [m', xs']
|]

