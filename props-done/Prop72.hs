-- ! passes, but doesn't use auto

{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop72 where

import Data
import Proof
import Tactic.Core.Quote

{-@
lemma1 :: xs:ListN -> {lengthListN (reverseListN xs) == lengthListN xs}
@-}
lemma1 :: ListN -> Proof 
lemma1 xs = undefined

{-@
lemma2 :: xs:ListN -> ys:ListN -> {concatListN (takeListN (lengthListN xs) xs) ys == takeListN (addN (lengthListN ys) (lengthListN xs)) (concatListN xs ys)}
@-}
lemma2 :: ListN -> ListN -> Proof 
lemma2 xs ys = undefined

{-@ reflect lemma3_prop @-}
lemma3_prop n ls rs = 
  if leqN n (lengthListN ls)
    then takeListN n ls == takeListN n (concatListN ls rs)
    else True

-- more specialized, so I don't have to go to auto depth 4 in order to find it
{-@
lemma3 :: n:N -> x:N -> xs:ListN -> {lemma3_prop (subN (lengthListN xs) n) (reverseListN xs) (singletonListN x)}
@-}
lemma3 :: N -> N -> ListN -> Proof
lemma3 n x xs = undefined

{-@ reflect lemma3'_prop @-}
lemma3'_prop n xs ys =
  if leqN n (lengthListN xs) then
    takeListN n (concatListN xs ys) ==
    takeListN n xs
  else
    True

{-@ lemma3' :: i':N -> x:N -> xs':ListN -> {lemma3'_prop i' xs' (singletonListN x)} @-}
lemma3' :: N -> N -> ListN -> Proof
lemma3' i' x xs' = undefined

{-@ lemma3'' :: n:N -> xs:ListN -> ys:ListN -> {lemma3'_prop n xs ys} @-}
lemma3'' :: N -> ListN -> ListN -> Proof
lemma3'' n xs ys = undefined

-- {-@
-- lemma3 :: n:N -> ls:ListN -> rs:ListN -> {lemma3_prop n ls rs}
-- @-}
-- lemma3 :: N -> ListN -> ListN -> Proof 
-- lemma3 n ls rs = undefined

{-@
lemma4 :: xs:ListN -> {takeListN (lengthListN xs) xs == xs}
@-}
lemma4 :: ListN -> Proof 
lemma4 = undefined

{-@ automatic-instances lemma5 @-}
{-@ lemma5 :: x:N -> xs:ListN -> {takeListN (S (lengthListN xs)) (concatListN (reverseListN xs) (singletonListN x)) == concatListN (reverseListN xs) (singletonListN x)} @-}
lemma5 :: N -> ListN -> Proof 
lemma5 x xs = 
  -- lemma6 (S (lengthListN xs))
  undefined

{-@ lemma6 :: n:N -> {leqN n n} @-}
lemma6 :: N -> Proof
lemma6 n = undefined

{-@ lemma7 :: xs:ListN -> ys:ListN -> {leqN (lengthListN xs) (lengthListN (concatListN xs ys))} @-}
lemma7 :: ListN -> ListN -> Proof 
lemma7 xs ys = undefined

{-@ lemma8 :: m:N -> n:N -> {leqN (subN m n) m} @-}
lemma8 :: N -> N -> Proof 
lemma8 m n = undefined


return []

{-@ reflect prop @-}
prop i xs =
  reverseListN (dropListN i xs) == 
  takeListN (subN (lengthListN xs) i) (reverseListN xs)

{-@ automatic-instances proof @-}
{-@
proof :: i:N -> xs:ListN -> {prop i xs}
@-}
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof i xs = 
--   induct i as [/i'];
--   induct xs as [/x xs'];
-- 
--   use {lemma4 (concatListN (reverseListN xs') (singletonListN x))} requires [xs'];
--   use {lemma1 xs'} requires [xs'];
--   use {lemma5 x xs'} requires [x, xs'];
-- 
--   use {lemma3'' (subN (lengthListN xs') i') (reverseListN xs') (singletonListN x)} requires [i', x, xs'];
--   use {lemma8 ((lengthListN xs')) i'} requires [i', xs'];
--   use {lemma1 xs'} requires [xs'];
--   use {proof i' xs'} requires [i', xs'];
-- 
--   trivial
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof = \i -> \xs -> case i of
                         Data.Z -> case xs of
                                       Data.Nil -> trivial
                                       Data.Cons x
                                                 xs' -> lemma4 (concatListN (reverseListN xs') (singletonListN x)) &&& (lemma1 xs' &&& (lemma5 x xs' &&& lemma1 xs'))
                         Data.S i' -> case xs of
                                          Data.Nil -> trivial
                                          Data.Cons x
                                                    xs' -> lemma4 (concatListN (reverseListN xs') (singletonListN x)) &&& (lemma1 xs' &&& (lemma5 x xs' &&& (lemma3'' (subN (lengthListN xs') i') (reverseListN xs') (singletonListN x) &&& (lemma8 ((lengthListN xs')) i' &&& (lemma1 xs' &&& proof i' xs')))))
-- %tactic:end:proof


-- -- %tactic:begin:proof
-- proof :: N -> ListN -> Proof
-- proof
--   = \ i
--       -> \ xs
--            -> case i of
--                 Z -> case xs of
--                        Nil -> trivial
--                        Cons x xs' -> 
--                           lemma4 (concatListN (reverseListN xs') (singletonListN x)) &&&
--                           lemma1 xs' &&&
--                           lemma5 x xs'
--                           -- 
--                           -- posit (reverseListN (Cons x xs') == takeListN (lengthListN (Cons x xs')) (reverseListN (Cons x xs'))) &&&
--                           -- posit (concatListN (reverseListN xs') (singletonListN x) == takeListN (S (lengthListN xs')) (concatListN (reverseListN xs') (singletonListN x)))
--                           -- check (concatListN (reverseListN xs') (singletonListN x) == takeListN (S (lengthListN xs')) (concatListN (reverseListN xs') (singletonListN x)))
--                           --
--                           -- check (reverseListN (Cons x xs') == concatListN (reverseListN xs') (singletonListN x)) -- * PASS
--                           -- check (takeListN (lengthListN (Cons x xs')) (reverseListN (Cons x xs')) == takeListN (S (lengthListN xs')) (concatListN (reverseListN xs') (singletonListN x))) -- * PASS
--                           -- check (
--                           --   (concatListN (reverseListN xs') (singletonListN x) == takeListN (S (lengthListN xs')) (concatListN (reverseListN xs') (singletonListN x)))
--                           --   ==
--                           --   (concatListN (reverseListN xs') (singletonListN x) == takeListN (S (lengthListN xs')) (concatListN (reverseListN xs') (singletonListN x)))
--                           -- )

--                 S i'
--                   -> case xs of
--                        Nil -> trivial
--                        Cons x xs' -> 
--                           -- lemma3 (subN (lengthListN xs') i') x (reverseListN xs') &&&
--                           -- lemma1 xs' &&&
--                           -- lemma7 (reverseListN xs') (singletonListN x) &&&
--                           -- lemma8 (lengthListN xs') i' &&&
--                           (proof i') xs' &&&
--                           --
--                           -- posit (reverseListN (dropListN (S i') (Cons x xs')) == takeListN (subN (lengthListN (Cons x xs')) (S i')) (reverseListN (Cons x xs'))) -- * PASS
--                           -- posit (reverseListN (dropListN i' xs') == takeListN (subN (lengthListN xs') i') (concatListN (reverseListN xs') (singletonListN x))) -- * PASS
--                           -- posit (reverseListN (dropListN i' xs') == takeListN (subN (lengthListN xs') i') (concatListN (reverseListN xs') (singletonListN x))) -- * PASS
--                           --
--                           -- posit (reverseListN (dropListN i' xs') == takeListN (subN (lengthListN xs') i') (reverseListN xs')) -- ! FAIL
--                           --
--                           -- TODO sufficient to prove this:
--                           -- posit (
--                           --   takeListN (subN (lengthListN xs') i') (concatListN (reverseListN xs') (singletonListN x)) ==
--                           --   takeListN (subN (lengthListN xs') i') (reverseListN xs')
--                           -- )
--                           --
--                           -- lemma3' (subN (lengthListN xs') i') x (reverseListN xs') &&&
--                           lemma3'' (subN (lengthListN xs') i') (reverseListN xs') (singletonListN x) &&&
--                           lemma8 ((lengthListN xs')) i' &&& -- posit (leqN (subN (lengthListN xs') i') (lengthListN xs')) &&&
--                           lemma1 xs' -- posit (lengthListN xs' == lengthListN (reverseListN xs'))

--                           -- 
--                           -- GOAL: reverseListN (dropListN (S i') (Cons x xs')) == takeListN (subN (lengthListN (Cons x xs')) (S i')) (reverseListN (Cons x xs'))
--                           -- IH: reverseListN (dropListN i' xs') == takeListN (subN (lengthListN xs') i') (reverseListN xs')
--                           --
--                           -- reverseListN (dropListN i' xs') == takeListN (subN (S (lengthListN xs')) (S i')) (reverseListN (Cons x xs'))
--                           -- reverseListN (dropListN i' xs') == takeListN (subN (lengthListN xs') i') (concatListN (reverseListN xs') (singletonListN x))
--                           -- reverseListN (dropListN i' xs') == takeListN (subN (lengthListN xs') i') (concatListN (reverseListN xs') (singletonListN x)) 
--                           --   `by` lemma3 _ _ _ :: takeListN (subN (lengthListN xs') i') (concatListN (reverseListN xs') (singletonListN x)) == takeListN (subN (lengthListN xs') i') (reverseListN xs')
--                           --   `by` lemma7 (reverseListN xs') (singletonListN x) :: leqN (subN (lengthListN xs') i') (length (concatListN (reverseListN xs') (singletonListN x)))
--                           --   `by` lemma8 (lengthListN xs') i' :: leqN (subN (lengthListN xs') i') (lengthListN xs')
--                           -- reverseListN (dropListN i' xs') == takeListN (subN (lengthListN xs') i') (reverseListN xs')
--                           -- True `by` proof i' xs'
                         
-- -- %tactic:end:proof
