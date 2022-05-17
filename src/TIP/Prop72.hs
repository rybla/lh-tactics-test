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

-- {-@
-- lemma3 :: n:N -> ls:ListN -> rs:ListN -> {lemma3_prop n ls rs}
-- @-}
-- lemma3 :: N -> ListN -> ListN -> Proof 
-- lemma3 n ls rs = undefined

-- more specialized, so I don't have to go to auto depth 4 in order to find it
{-@
lemma3 :: n:N -> x:N -> xs:ListN -> {lemma3_prop (subN (lengthListN xs) n) (reverseListN xs) (singletonListN x)}
@-}
lemma3 :: N -> N -> ListN -> Proof
lemma3 n x xs = undefined

{-@
lemma4 :: xs:ListN -> {takeListN (lengthListN xs) xs == xs}
@-}
lemma4 :: ListN -> Proof 
lemma4 = undefined

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
--   induct i;
--   induct xs
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof
  = \ i
      -> \ xs
           -> case i of
                Z -> case xs of
                       Nil -> trivial
                       Cons n_0 listN_1 -> trivial -- TODO
                S n_0
                  -> case xs of
                       Nil -> trivial
                       Cons n_1 listN_2 -> (proof n_0) listN_2 -- TODO
-- %tactic:end:proof

-- -- reverseListN (dropListN i xs) == 
-- -- takeListN (subN (lengthListN xs) i) (reverseListN xs)

-- -- IH: 
-- -- reverseListN (dropListN i xs)
-- -- takeListN (subN (lengthListN xs) i) (reverseListN xs)
-- reverseListN (dropListN Z (Cons x xs'))
-- reverseListN (Cons x xs')
-- concatListN (reverseListN xs') (singletonListN x)
-- takeListN (S (lengthListN xs')) (concatListN (reverseListN xs') (singletonListN x))
-- takeListN (lengthListN (Cons x xs')) (concatListN (reverseListN xs') (singletonListN x))
-- takeListN (subN (lengthListN (Cons x xs')) Z) (concatListN (reverseListN xs') (singletonListN x))


-- -- -- IH:
-- -- --   reverseListN (dropListN i xs) == 
-- -- --   takeListN (subN (lengthListN xs) i) (reverseListN xs)
-- -- reverseListN (dropListN (S i) (Cons x xs))
-- -- reverseListN (dropListN i xs)
-- -- takeListN (subN (lengthListN xs) i) (reverseListN xs) -- by IH
-- -- takeListN (subN (lengthListN xs) i) (concatListN (reverseListN xs) (singletonListN x)) -- by lemma3 i x xs
-- -- takeListN (subN (lengthListN xs) i) (reverseListN (Cons x xs))
-- -- takeListN (subN (S (lengthListN xs)) (S i)) (reverseListN (Cons x xs))
-- -- takeListN (subN (lengthListN (Cons x xs)) (S i)) (reverseListN (Cons x xs))
