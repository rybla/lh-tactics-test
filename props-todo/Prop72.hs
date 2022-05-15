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

return []

{-@ reflect prop @-}
prop i xs =
  reverseListN (dropListN i xs) == 
  takeListN (subN (lengthListN xs) i) (reverseListN xs)

-- ! FAILS
{-@ automatic-instances proof @-}
{-@
proof :: i:N -> xs:ListN -> {prop i xs}
@-}
-- [tactic|
-- proof :: N -> ListN -> Proof
-- proof i xs = 
--   induct xs;
--   induct i;
--   auto [lemma1, lemma2, lemma3, lengthListN, reverseListN, singletonListN]
-- |]
-- %tactic:begin:proof
proof :: N -> ListN -> Proof
proof
  = \ i
      -> \ xs
           -> case xs of
                Nil
                  -> case i of
                       Z -> trivial
                       S n_0
                         -> (lemma1 (singletonListN n_0)
                               &&&
                                 ((lemma2 (singletonListN n_0)) (singletonListN n_0)
                                    &&& ((lemma3 n_0) n_0) (singletonListN n_0)))
                Cons n_0 listN_1
                  -> case i of
                       Z -> (lemma1 listN_1
                               &&&
                                 (lemma1 (reverseListN listN_1)
                                    &&&
                                      (lemma1 (singletonListN n_0)
                                         &&&
                                           ((lemma2 listN_1) listN_1
                                              &&&
                                                ((lemma2 listN_1) (reverseListN listN_1)
                                                   &&&
                                                     ((lemma2 listN_1) (singletonListN n_0)
                                                        &&&
                                                          ((lemma2 (reverseListN listN_1))
                                                             listN_1
                                                             &&&
                                                               ((lemma2 (reverseListN listN_1))
                                                                  (reverseListN listN_1)
                                                                  &&&
                                                                    ((lemma2
                                                                        (reverseListN listN_1))
                                                                       (singletonListN n_0)
                                                                       &&&
                                                                         ((lemma2
                                                                             (singletonListN
                                                                                n_0))
                                                                            listN_1
                                                                            &&&
                                                                              ((lemma2
                                                                                  (singletonListN
                                                                                     n_0))
                                                                                 (reverseListN
                                                                                    listN_1)
                                                                                 &&&
                                                                                   ((lemma2
                                                                                       (singletonListN
                                                                                          n_0))
                                                                                      (singletonListN
                                                                                         n_0)
                                                                                      &&&
                                                                                        (((lemma3
                                                                                             (lengthListN
                                                                                                listN_1))
                                                                                            (lengthListN
                                                                                               listN_1))
                                                                                           listN_1
                                                                                           &&&
                                                                                             (((lemma3
                                                                                                  (lengthListN
                                                                                                     listN_1))
                                                                                                 (lengthListN
                                                                                                    listN_1))
                                                                                                (reverseListN
                                                                                                   listN_1)
                                                                                                &&&
                                                                                                  (((lemma3
                                                                                                       (lengthListN
                                                                                                          listN_1))
                                                                                                      (lengthListN
                                                                                                         listN_1))
                                                                                                     (singletonListN
                                                                                                        n_0)
                                                                                                     &&&
                                                                                                       (((lemma3
                                                                                                            (lengthListN
                                                                                                               listN_1))
                                                                                                           n_0)
                                                                                                          listN_1
                                                                                                          &&&
                                                                                                            (((lemma3
                                                                                                                 (lengthListN
                                                                                                                    listN_1))
                                                                                                                n_0)
                                                                                                               (reverseListN
                                                                                                                  listN_1)
                                                                                                               &&&
                                                                                                                 (((lemma3
                                                                                                                      (lengthListN
                                                                                                                         listN_1))
                                                                                                                     n_0)
                                                                                                                    (singletonListN
                                                                                                                       n_0)
                                                                                                                    &&&
                                                                                                                      (((lemma3
                                                                                                                           n_0)
                                                                                                                          (lengthListN
                                                                                                                             listN_1))
                                                                                                                         listN_1
                                                                                                                         &&&
                                                                                                                           (((lemma3
                                                                                                                                n_0)
                                                                                                                               (lengthListN
                                                                                                                                  listN_1))
                                                                                                                              (reverseListN
                                                                                                                                 listN_1)
                                                                                                                              &&&
                                                                                                                                (((lemma3
                                                                                                                                     n_0)
                                                                                                                                    (lengthListN
                                                                                                                                       listN_1))
                                                                                                                                   (singletonListN
                                                                                                                                      n_0)
                                                                                                                                   &&&
                                                                                                                                     (((lemma3
                                                                                                                                          n_0)
                                                                                                                                         n_0)
                                                                                                                                        listN_1
                                                                                                                                        &&&
                                                                                                                                          (((lemma3
                                                                                                                                               n_0)
                                                                                                                                              n_0)
                                                                                                                                             (reverseListN
                                                                                                                                                listN_1)
                                                                                                                                             &&&
                                                                                                                                               ((lemma3
                                                                                                                                                   n_0)
                                                                                                                                                  n_0)
                                                                                                                                                 (singletonListN
                                                                                                                                                    n_0))))))))))))))))))))))))
                       S n_2
                         -> (lemma1 listN_1
                               &&&
                                 (lemma1 (reverseListN listN_1)
                                    &&&
                                      (lemma1 (singletonListN n_0)
                                         &&&
                                           (lemma1 (singletonListN n_2)
                                              &&&
                                                ((lemma2 listN_1) listN_1
                                                   &&&
                                                     ((lemma2 listN_1) (reverseListN listN_1)
                                                        &&&
                                                          ((lemma2 listN_1) (singletonListN n_0)
                                                             &&&
                                                               ((lemma2 listN_1)
                                                                  (singletonListN n_2)
                                                                  &&&
                                                                    ((lemma2
                                                                        (reverseListN listN_1))
                                                                       listN_1
                                                                       &&&
                                                                         ((lemma2
                                                                             (reverseListN
                                                                                listN_1))
                                                                            (reverseListN
                                                                               listN_1)
                                                                            &&&
                                                                              ((lemma2
                                                                                  (reverseListN
                                                                                     listN_1))
                                                                                 (singletonListN
                                                                                    n_0)
                                                                                 &&&
                                                                                   ((lemma2
                                                                                       (reverseListN
                                                                                          listN_1))
                                                                                      (singletonListN
                                                                                         n_2)
                                                                                      &&&
                                                                                        ((lemma2
                                                                                            (singletonListN
                                                                                               n_0))
                                                                                           listN_1
                                                                                           &&&
                                                                                             ((lemma2
                                                                                                 (singletonListN
                                                                                                    n_0))
                                                                                                (reverseListN
                                                                                                   listN_1)
                                                                                                &&&
                                                                                                  ((lemma2
                                                                                                      (singletonListN
                                                                                                         n_0))
                                                                                                     (singletonListN
                                                                                                        n_0)
                                                                                                     &&&
                                                                                                       ((lemma2
                                                                                                           (singletonListN
                                                                                                              n_0))
                                                                                                          (singletonListN
                                                                                                             n_2)
                                                                                                          &&&
                                                                                                            ((lemma2
                                                                                                                (singletonListN
                                                                                                                   n_2))
                                                                                                               listN_1
                                                                                                               &&&
                                                                                                                 ((lemma2
                                                                                                                     (singletonListN
                                                                                                                        n_2))
                                                                                                                    (reverseListN
                                                                                                                       listN_1)
                                                                                                                    &&&
                                                                                                                      ((lemma2
                                                                                                                          (singletonListN
                                                                                                                             n_2))
                                                                                                                         (singletonListN
                                                                                                                            n_0)
                                                                                                                         &&&
                                                                                                                           ((lemma2
                                                                                                                               (singletonListN
                                                                                                                                  n_2))
                                                                                                                              (singletonListN
                                                                                                                                 n_2)
                                                                                                                              &&&
                                                                                                                                (((lemma3
                                                                                                                                     (lengthListN
                                                                                                                                        listN_1))
                                                                                                                                    (lengthListN
                                                                                                                                       listN_1))
                                                                                                                                   listN_1
                                                                                                                                   &&&
                                                                                                                                     (((lemma3
                                                                                                                                          (lengthListN
                                                                                                                                             listN_1))
                                                                                                                                         (lengthListN
                                                                                                                                            listN_1))
                                                                                                                                        (reverseListN
                                                                                                                                           listN_1)
                                                                                                                                        &&&
                                                                                                                                          (((lemma3
                                                                                                                                               (lengthListN
                                                                                                                                                  listN_1))
                                                                                                                                              (lengthListN
                                                                                                                                                 listN_1))
                                                                                                                                             (singletonListN
                                                                                                                                                n_0)
                                                                                                                                             &&&
                                                                                                                                               (((lemma3
                                                                                                                                                    (lengthListN
                                                                                                                                                       listN_1))
                                                                                                                                                   (lengthListN
                                                                                                                                                      listN_1))
                                                                                                                                                  (singletonListN
                                                                                                                                                     n_2)
                                                                                                                                                  &&&
                                                                                                                                                    (((lemma3
                                                                                                                                                         (lengthListN
                                                                                                                                                            listN_1))
                                                                                                                                                        n_0)
                                                                                                                                                       listN_1
                                                                                                                                                       &&&
                                                                                                                                                         (((lemma3
                                                                                                                                                              (lengthListN
                                                                                                                                                                 listN_1))
                                                                                                                                                             n_0)
                                                                                                                                                            (reverseListN
                                                                                                                                                               listN_1)
                                                                                                                                                            &&&
                                                                                                                                                              (((lemma3
                                                                                                                                                                   (lengthListN
                                                                                                                                                                      listN_1))
                                                                                                                                                                  n_0)
                                                                                                                                                                 (singletonListN
                                                                                                                                                                    n_0)
                                                                                                                                                                 &&&
                                                                                                                                                                   (((lemma3
                                                                                                                                                                        (lengthListN
                                                                                                                                                                           listN_1))
                                                                                                                                                                       n_0)
                                                                                                                                                                      (singletonListN
                                                                                                                                                                         n_2)
                                                                                                                                                                      &&&
                                                                                                                                                                        (((lemma3
                                                                                                                                                                             (lengthListN
                                                                                                                                                                                listN_1))
                                                                                                                                                                            n_2)
                                                                                                                                                                           listN_1
                                                                                                                                                                           &&&
                                                                                                                                                                             (((lemma3
                                                                                                                                                                                  (lengthListN
                                                                                                                                                                                     listN_1))
                                                                                                                                                                                 n_2)
                                                                                                                                                                                (reverseListN
                                                                                                                                                                                   listN_1)
                                                                                                                                                                                &&&
                                                                                                                                                                                  (((lemma3
                                                                                                                                                                                       (lengthListN
                                                                                                                                                                                          listN_1))
                                                                                                                                                                                      n_2)
                                                                                                                                                                                     (singletonListN
                                                                                                                                                                                        n_0)
                                                                                                                                                                                     &&&
                                                                                                                                                                                       (((lemma3
                                                                                                                                                                                            (lengthListN
                                                                                                                                                                                               listN_1))
                                                                                                                                                                                           n_2)
                                                                                                                                                                                          (singletonListN
                                                                                                                                                                                             n_2)
                                                                                                                                                                                          &&&
                                                                                                                                                                                            (((lemma3
                                                                                                                                                                                                 n_0)
                                                                                                                                                                                                (lengthListN
                                                                                                                                                                                                   listN_1))
                                                                                                                                                                                               listN_1
                                                                                                                                                                                               &&&
                                                                                                                                                                                                 (((lemma3
                                                                                                                                                                                                      n_0)
                                                                                                                                                                                                     (lengthListN
                                                                                                                                                                                                        listN_1))
                                                                                                                                                                                                    (reverseListN
                                                                                                                                                                                                       listN_1)
                                                                                                                                                                                                    &&&
                                                                                                                                                                                                      (((lemma3
                                                                                                                                                                                                           n_0)
                                                                                                                                                                                                          (lengthListN
                                                                                                                                                                                                             listN_1))
                                                                                                                                                                                                         (singletonListN
                                                                                                                                                                                                            n_0)
                                                                                                                                                                                                         &&&
                                                                                                                                                                                                           (((lemma3
                                                                                                                                                                                                                n_0)
                                                                                                                                                                                                               (lengthListN
                                                                                                                                                                                                                  listN_1))
                                                                                                                                                                                                              (singletonListN
                                                                                                                                                                                                                 n_2)
                                                                                                                                                                                                              &&&
                                                                                                                                                                                                                (((lemma3
                                                                                                                                                                                                                     n_0)
                                                                                                                                                                                                                    n_0)
                                                                                                                                                                                                                   listN_1
                                                                                                                                                                                                                   &&&
                                                                                                                                                                                                                     (((lemma3
                                                                                                                                                                                                                          n_0)
                                                                                                                                                                                                                         n_0)
                                                                                                                                                                                                                        (reverseListN
                                                                                                                                                                                                                           listN_1)
                                                                                                                                                                                                                        &&&
                                                                                                                                                                                                                          (((lemma3
                                                                                                                                                                                                                               n_0)
                                                                                                                                                                                                                              n_0)
                                                                                                                                                                                                                             (singletonListN
                                                                                                                                                                                                                                n_0)
                                                                                                                                                                                                                             &&&
                                                                                                                                                                                                                               (((lemma3
                                                                                                                                                                                                                                    n_0)
                                                                                                                                                                                                                                   n_0)
                                                                                                                                                                                                                                  (singletonListN
                                                                                                                                                                                                                                     n_2)
                                                                                                                                                                                                                                  &&&
                                                                                                                                                                                                                                    (((lemma3
                                                                                                                                                                                                                                         n_0)
                                                                                                                                                                                                                                        n_2)
                                                                                                                                                                                                                                       listN_1
                                                                                                                                                                                                                                       &&&
                                                                                                                                                                                                                                         (((lemma3
                                                                                                                                                                                                                                              n_0)
                                                                                                                                                                                                                                             n_2)
                                                                                                                                                                                                                                            (reverseListN
                                                                                                                                                                                                                                               listN_1)
                                                                                                                                                                                                                                            &&&
                                                                                                                                                                                                                                              (((lemma3
                                                                                                                                                                                                                                                   n_0)
                                                                                                                                                                                                                                                  n_2)
                                                                                                                                                                                                                                                 (singletonListN
                                                                                                                                                                                                                                                    n_0)
                                                                                                                                                                                                                                                 &&&
                                                                                                                                                                                                                                                   (((lemma3
                                                                                                                                                                                                                                                        n_0)
                                                                                                                                                                                                                                                       n_2)
                                                                                                                                                                                                                                                      (singletonListN
                                                                                                                                                                                                                                                         n_2)
                                                                                                                                                                                                                                                      &&&
                                                                                                                                                                                                                                                        (((lemma3
                                                                                                                                                                                                                                                             n_2)
                                                                                                                                                                                                                                                            (lengthListN
                                                                                                                                                                                                                                                               listN_1))
                                                                                                                                                                                                                                                           listN_1
                                                                                                                                                                                                                                                           &&&
                                                                                                                                                                                                                                                             (((lemma3
                                                                                                                                                                                                                                                                  n_2)
                                                                                                                                                                                                                                                                 (lengthListN
                                                                                                                                                                                                                                                                    listN_1))
                                                                                                                                                                                                                                                                (reverseListN
                                                                                                                                                                                                                                                                   listN_1)
                                                                                                                                                                                                                                                                &&&
                                                                                                                                                                                                                                                                  (((lemma3
                                                                                                                                                                                                                                                                       n_2)
                                                                                                                                                                                                                                                                      (lengthListN
                                                                                                                                                                                                                                                                         listN_1))
                                                                                                                                                                                                                                                                     (singletonListN
                                                                                                                                                                                                                                                                        n_0)
                                                                                                                                                                                                                                                                     &&&
                                                                                                                                                                                                                                                                       (((lemma3
                                                                                                                                                                                                                                                                            n_2)
                                                                                                                                                                                                                                                                           (lengthListN
                                                                                                                                                                                                                                                                              listN_1))
                                                                                                                                                                                                                                                                          (singletonListN
                                                                                                                                                                                                                                                                             n_2)
                                                                                                                                                                                                                                                                          &&&
                                                                                                                                                                                                                                                                            (((lemma3
                                                                                                                                                                                                                                                                                 n_2)
                                                                                                                                                                                                                                                                                n_0)
                                                                                                                                                                                                                                                                               listN_1
                                                                                                                                                                                                                                                                               &&&
                                                                                                                                                                                                                                                                                 (((lemma3
                                                                                                                                                                                                                                                                                      n_2)
                                                                                                                                                                                                                                                                                     n_0)
                                                                                                                                                                                                                                                                                    (reverseListN
                                                                                                                                                                                                                                                                                       listN_1)
                                                                                                                                                                                                                                                                                    &&&
                                                                                                                                                                                                                                                                                      (((lemma3
                                                                                                                                                                                                                                                                                           n_2)
                                                                                                                                                                                                                                                                                          n_0)
                                                                                                                                                                                                                                                                                         (singletonListN
                                                                                                                                                                                                                                                                                            n_0)
                                                                                                                                                                                                                                                                                         &&&
                                                                                                                                                                                                                                                                                           (((lemma3
                                                                                                                                                                                                                                                                                                n_2)
                                                                                                                                                                                                                                                                                               n_0)
                                                                                                                                                                                                                                                                                              (singletonListN
                                                                                                                                                                                                                                                                                                 n_2)
                                                                                                                                                                                                                                                                                              &&&
                                                                                                                                                                                                                                                                                                (((lemma3
                                                                                                                                                                                                                                                                                                     n_2)
                                                                                                                                                                                                                                                                                                    n_2)
                                                                                                                                                                                                                                                                                                   listN_1
                                                                                                                                                                                                                                                                                                   &&&
                                                                                                                                                                                                                                                                                                     (((lemma3
                                                                                                                                                                                                                                                                                                          n_2)
                                                                                                                                                                                                                                                                                                         n_2)
                                                                                                                                                                                                                                                                                                        (reverseListN
                                                                                                                                                                                                                                                                                                           listN_1)
                                                                                                                                                                                                                                                                                                        &&&
                                                                                                                                                                                                                                                                                                          (((lemma3
                                                                                                                                                                                                                                                                                                               n_2)
                                                                                                                                                                                                                                                                                                              n_2)
                                                                                                                                                                                                                                                                                                             (singletonListN
                                                                                                                                                                                                                                                                                                                n_0)
                                                                                                                                                                                                                                                                                                             &&&
                                                                                                                                                                                                                                                                                                               (((lemma3
                                                                                                                                                                                                                                                                                                                    n_2)
                                                                                                                                                                                                                                                                                                                   n_2)
                                                                                                                                                                                                                                                                                                                  (singletonListN
                                                                                                                                                                                                                                                                                                                     n_2)
                                                                                                                                                                                                                                                                                                                  &&&
                                                                                                                                                                                                                                                                                                                    (proof
                                                                                                                                                                                                                                                                                                                       n_2)
                                                                                                                                                                                                                                                                                                                      listN_1))))))))))))))))))))))))))))))))))))))))))))))))))))))))
-- %tactic:end:proof
