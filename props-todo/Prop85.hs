{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop85 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect lemma1_prop @-}
lemma1_prop ls rs xs ys = 
  zipListN (concatListN ls xs) (concatListN rs ys) == 
  concatListN2 (zipListN ls rs) (zipListN xs ys)

{-@
lemma1 :: ls:ListN -> rs:ListN -> xs:ListN -> ys:ListN -> {lemma1_prop ls rs xs ys}
@-}
lemma1 :: ListN -> ListN -> ListN -> ListN -> Proof 
lemma1 ls rs xs ys = undefined

return []

{-@ reflect prop @-}
prop xs ys =
  if lengthListN xs == lengthListN ys then 
    zipListN (reverseListN xs) (reverseListN ys) ==
    reverseListN2 (zipListN xs ys)
  else 
    True

-- ! FAILS, but should work
{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> ys:ListN -> {prop xs ys}
@-}
-- [tactic|
-- proof :: ListN -> ListN -> Proof
-- proof xs ys =
--   induct xs as [/x xs'];
--   induct ys as [/y ys'];
--   use {lemma1 (reverseListN xs') (reverseListN ys') (singletonListN x) (singletonListN y)} requires [x, xs', y, ys'];
--   auto [] 2
-- |]
-- %tactic:begin:proof
proof :: ListN -> ListN -> Proof
proof
  = \ xs
      -> \ ys
           -> case xs of
                Nil
                  -> case ys of
                       Nil -> trivial
                       Cons y ys' -> trivial
                Cons x xs'
                  -> case ys of
                       Nil -> trivial
                       Cons y ys'
                        --  -> ((((lemma1 (reverseListN xs')) (reverseListN ys'))
                        --         (singletonListN x))
                        --        (singletonListN y)
                        --        &&& (proof xs') ys')
                        {-
                        zipListN (reverseListN (Cons x xs)) (reverseListN (Cons y ys))
                        zip (rev (x:xs)) (rev (y:ys))
                        zip (rev xs ++ [x]) (rev ys ++ [y])
                        zip (rev xs) (rev ys) ++ zip [x] [y] `by` lemma (rev xs) (rev ys) [x] [y]
                        rev (zip xs ys) ++ zip [x] [y] `by` proof xs ys
                        rev (zip xs ys) ++ [(x,y)]
                        rev ((x,y):zip xs ys)
                        rev (zip (x:xs) (y:ys))
                        reverseListN2 (zipListN (Cons x xs) (Cons y ys))
                        -}
                        -> lemma1 (reverseListN xs') (reverseListN ys') (singletonListN x) (singletonListN y) &&&
                           proof xs' ys'
-- %tactic:end:proof
