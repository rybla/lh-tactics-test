{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop59 where

import Data
import Proof
import Tactic.Core.Quote

{-@
idR_concat :: xs:ListN -> {concatListN xs Nil == xs}
@-}
idR_concat :: ListN -> Proof 
idR_concat xs = undefined

return []

{-@ reflect prop @-}
-- prop xs ys =
--   if nullListN ys
--     then lastListN (concatListN xs ys) == lastListN xs
--     else True
prop xs Nil = True
prop xs ys = lastListN (concatListN xs ys) == lastListN xs

-- ! FAILS
{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> ys:ListN -> {prop xs ys}
@-}
-- %tactic:begin:proof
proof :: ListN -> ListN -> Proof
proof
  = \ xs
      -> \ ys
           -> case xs of
                Nil
                  -> case ys of
                       Nil -> trivial
                       Cons n_0 listN_1
                         -> (idR_concat listN_1 &&& idR_concat ((Cons n_0) listN_1))
                Cons n_0 listN_1
                  -> case ys of
                       Nil
                         -> (idR_concat listN_1
                               &&&
                                 (idR_concat ((Cons n_0) listN_1)
                                    &&&
                                      ((proof listN_1) listN_1
                                         &&& (proof listN_1) ((Cons n_0) listN_1))))
                       Cons n_2 listN_3
                         -> (idR_concat listN_1
                               &&&
                                 (idR_concat listN_3
                                    &&&
                                      (idR_concat ((Cons n_0) listN_1)
                                         &&&
                                           (idR_concat ((Cons n_0) listN_3)
                                              &&&
                                                (idR_concat ((Cons n_2) listN_1)
                                                   &&&
                                                     (idR_concat ((Cons n_2) listN_3)
                                                        &&&
                                                          ((proof listN_1) listN_1
                                                             &&&
                                                               ((proof listN_1) listN_3
                                                                  &&&
                                                                    ((proof listN_1)
                                                                       ((Cons n_0) listN_1)
                                                                       &&&
                                                                         ((proof listN_1)
                                                                            ((Cons n_0) listN_3)
                                                                            &&&
                                                                              ((proof listN_1)
                                                                                 ((Cons n_2)
                                                                                    listN_1)
                                                                                 &&&
                                                                                   (proof
                                                                                      listN_1)
                                                                                     ((Cons n_2)
                                                                                        listN_3))))))))))))
-- %tactic:end:proof
