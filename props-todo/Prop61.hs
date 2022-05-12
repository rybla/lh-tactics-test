{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop61 where

import Data
import Proof
import Tactic.Core.Quote

{-@
lemma :: xs:ListN -> {concatListN xs Nil == xs}
@-}
lemma :: ListN -> Proof 
lemma xs = undefined

return []

{-@ reflect prop @-}
prop xs ys = lastListN' (concatListN xs ys) == lastOfTwo xs ys

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
                       Cons n_0 listN_1 -> lemma listN_1
                Cons x1 xs'
                  -> case xs' of
                       Nil
                         -> case ys of
                              Nil -> trivial
                              Cons n_0 listN_1 -> (lemma listN_1 &&& (proof xs') listN_1)
                       Cons x2 xs''
                         -> ((proof ((Cons x2) xs'')) ys
                               &&&
                                 (case ys of
                                    Nil -> (lemma xs'' &&& (proof xs') xs'')
                                    Cons n_0 listN_1
                                      -> (lemma listN_1
                                            &&&
                                              (lemma xs''
                                                 &&&
                                                   ((proof xs') listN_1
                                                      &&& (proof xs') xs'')))))
-- %tactic:end:proof


-- [tactic|
-- proof :: ListN -> ListN -> Proof
-- proof xs ys =
--   induct xs as [/x xs'];
--   induct xs';
--   destruct ys;
--   auto [lemma]
-- |]
