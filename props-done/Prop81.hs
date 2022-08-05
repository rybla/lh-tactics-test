-- doesn't really use proper tactics, basically just a fancy way of writing 
-- the same proof since it provides all the applications. But, it could work 
-- really well as soon as I implement the Refine tactic (or even just the 
-- Generate tactic)

{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop81 where

import Data
import Proof
import Tactic.Core.Quote

{-@ comm_addN :: n:N -> m:N -> {addN n m == addN m n} @-}
comm_addN :: N -> N -> Proof
comm_addN n m = undefined

{-@ idr_addN :: n:N -> {addN n Z == n} @-}
idr_addN :: N -> Proof
idr_addN n = undefined

return []

{-@ reflect prop @-}
prop n m xs =
  takeListN n (dropListN m xs) ==
  dropListN m (takeListN (addN n m) xs)

{-@ automatic-instances proof @-}
{-@
proof :: n:N -> m:N -> xs:ListN -> {prop n m xs}
@-}

-- proof :: N -> N -> ListN -> Proof
-- proof _ _ Nil = trivial
-- proof Z (S m) (Cons x xs) = proof Z m xs
-- proof n Z (Cons x xs) = idr_addN n
-- proof n@(S n') m@(S m') (Cons x xs) = 
--   comm_addN m n &&&
--   comm_addN m' n &&&
--   proof n m' xs

-- [tactic|
-- proof :: N -> N -> ListN -> Proof
-- proof n m xs =
--   induct m as [/m'];
--   induct xs as [/x xs'];
--   destruct n #[remember];
--   use {comm_addN m n};
--   [m']: use {comm_addN m' n};
--   [m', xs']: use {proof n m' xs'};
--   trivial
-- |]
-- %tactic:begin:proof
proof :: N -> N -> ListN -> Proof
proof = \n -> \m -> \xs -> case m of
                               Data.Z -> case xs of
                                             Data.Nil -> case n of
                                                             Data.Z -> comm_addN m n
                                                             Data.S n_0 -> comm_addN m n
                                             Data.Cons x xs' -> case n of
                                                                    Data.Z -> comm_addN m n
                                                                    Data.S n_0 -> comm_addN m n
                               Data.S m' -> case xs of
                                                Data.Nil -> case n of
                                                                Data.Z -> comm_addN m n &&& comm_addN m' n
                                                                Data.S n_0 -> comm_addN m n &&& comm_addN m' n
                                                Data.Cons x xs' -> case n of
                                                                       Data.Z -> comm_addN m n &&& (comm_addN m' n &&& proof n m' xs')
                                                                       Data.S n_0 -> comm_addN m n &&& (comm_addN m' n &&& proof n m' xs')
-- %tactic:end:proof
-- auto [comm_addN, idr_addN] 2

-- -- %tactic:begin:proof
-- proof :: N -> N -> ListN -> Proof
-- proof
--   = \ n
--       -> \ m
--            -> \ xs
--                 -> case m of
--                      Z -> case xs of
--                             Nil
--                               -> case n of
--                                    Z -> (comm_addN n) n
--                                    S n_0
--                                      -> ((comm_addN n) n
--                                            &&&
--                                              ((comm_addN n) n_0
--                                                 &&&
--                                                   ((comm_addN n_0) n &&& (comm_addN n_0) n_0)))
--                             Cons n_0 listN_1
--                               -> case n of
--                                    Z -> ((comm_addN n) n
--                                            &&&
--                                              ((comm_addN n) n_0
--                                                 &&&
--                                                   ((comm_addN n_0) n &&& (comm_addN n_0) n_0)))
--                                    S n_2
--                                      -> ((comm_addN n) n
--                                            &&&
--                                              ((comm_addN n) n_0
--                                                 &&&
--                                                   ((comm_addN n) n_2
--                                                      &&&
--                                                        ((comm_addN n_0) n
--                                                           &&&
--                                                             ((comm_addN n_0) n_0
--                                                                &&&
--                                                                  ((comm_addN n_0) n_2
--                                                                     &&&
--                                                                       ((comm_addN n_2) n
--                                                                          &&&
--                                                                            ((comm_addN n_2) n_0
--                                                                               &&&
--                                                                                 (comm_addN n_2)
--                                                                                   n_2))))))))
--                      S n_0
--                        -> case xs of
--                             Nil
--                               -> case n of
--                                    Z -> ((comm_addN n) n
--                                            &&&
--                                              ((comm_addN n) n_0
--                                                 &&&
--                                                   ((comm_addN n_0) n &&& (comm_addN n_0) n_0)))
--                                    S n_1
--                                      -> ((comm_addN n) n
--                                            &&&
--                                              ((comm_addN n) n_0
--                                                 &&&
--                                                   ((comm_addN n) n_1
--                                                      &&&
--                                                        ((comm_addN n_0) n
--                                                           &&&
--                                                             ((comm_addN n_0) n_0
--                                                                &&&
--                                                                  ((comm_addN n_0) n_1
--                                                                     &&&
--                                                                       ((comm_addN n_1) n
--                                                                          &&&
--                                                                            ((comm_addN n_1) n_0
--                                                                               &&&
--                                                                                 (comm_addN n_1)
--                                                                                   n_1))))))))
--                             Cons n_1 listN_2
--                               -> case n of
--                                    Z -> ((comm_addN n) n
--                                            &&&
--                                              ((comm_addN n) n_0
--                                                 &&&
--                                                   ((comm_addN n) n_1
--                                                      &&&
--                                                        ((comm_addN n_0) n
--                                                           &&&
--                                                             ((comm_addN n_0) n_0
--                                                                &&&
--                                                                  ((comm_addN n_0) n_1
--                                                                     &&&
--                                                                       ((comm_addN n_1) n
--                                                                          &&&
--                                                                            ((comm_addN n_1) n_0
--                                                                               &&&
--                                                                                 ((comm_addN n_1)
--                                                                                    n_1
--                                                                                    &&&
--                                                                                      (((proof n)
--                                                                                          n_0)
--                                                                                         listN_2
--                                                                                         &&&
--                                                                                           (((proof
--                                                                                                n_0)
--                                                                                               n_0)
--                                                                                              listN_2
--                                                                                              &&&
--                                                                                                ((proof
--                                                                                                    n_1)
--                                                                                                   n_0)
--                                                                                                  listN_2)))))))))))
--                                    S n_3
--                                      -> ((comm_addN n) n
--                                            &&&
--                                              ((comm_addN n) n_0
--                                                 &&&
--                                                   ((comm_addN n) n_1
--                                                      &&&
--                                                        ((comm_addN n) n_3
--                                                           &&&
--                                                             ((comm_addN n_0) n
--                                                                &&&
--                                                                  ((comm_addN n_0) n_0
--                                                                     &&&
--                                                                       ((comm_addN n_0) n_1
--                                                                          &&&
--                                                                            ((comm_addN n_0) n_3
--                                                                               &&&
--                                                                                 ((comm_addN n_1)
--                                                                                    n
--                                                                                    &&&
--                                                                                      ((comm_addN
--                                                                                          n_1)
--                                                                                         n_0
--                                                                                         &&&
--                                                                                           ((comm_addN
--                                                                                               n_1)
--                                                                                              n_1
--                                                                                              &&&
--                                                                                                ((comm_addN
--                                                                                                    n_1)
--                                                                                                   n_3
--                                                                                                   &&&
--                                                                                                     ((comm_addN
--                                                                                                         n_3)
--                                                                                                        n
--                                                                                                        &&&
--                                                                                                          ((comm_addN
--                                                                                                              n_3)
--                                                                                                             n_0
--                                                                                                             &&&
--                                                                                                               ((comm_addN
--                                                                                                                   n_3)
--                                                                                                                  n_1
--                                                                                                                  &&&
--                                                                                                                    ((comm_addN
--                                                                                                                        n_3)
--                                                                                                                       n_3
--                                                                                                                       &&&
--                                                                                                                         (((proof
--                                                                                                                              n)
--                                                                                                                             n_0)
--                                                                                                                            listN_2
--                                                                                                                            &&&
--                                                                                                                              (((proof
--                                                                                                                                   n_0)
--                                                                                                                                  n_0)
--                                                                                                                                 listN_2
--                                                                                                                                 &&&
--                                                                                                                                   (((proof
--                                                                                                                                        n_1)
--                                                                                                                                       n_0)
--                                                                                                                                      listN_2
--                                                                                                                                      &&&
--                                                                                                                                        ((proof
--                                                                                                                                            n_3)
--                                                                                                                                           n_0)
--                                                                                                                                          listN_2)))))))))))))))))))
-- -- %tactic:end:proof

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

-- -- ! FAILS
-- [tactic|
-- proof :: N -> N -> ListN -> Proof
-- proof n m xs =
--   destruct n as [/n'];
--   induct m as [/m'];
--   induct xs as [/x xs'];
--   use {comm_addN n Z};
--   use {comm_addN m n};
--   [m', xs']: use {proof n m' xs'}
-- |]

