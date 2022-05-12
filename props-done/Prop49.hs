{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop49 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop :: ListN -> ListN -> Bool 
prop xs ys = initListN (concatListN xs ys) == initConcatListN xs ys

{-@ 
idR_concatListN :: l:ListN -> {concatListN l Nil == l}
@-}
idR_concatListN :: ListN -> Proof
idR_concatListN = undefined

{-@
lem :: x1:N -> x2:N -> xs'':ListN -> {lengthListN_int (Cons x2 xs'') < lengthListN_int (Cons x1 (Cons x2 xs''))}
@-}
lem :: N -> N -> ListN -> Proof 
lem = undefined

return []

-- ! FAILS
-- TODO: why??
{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> ys:ListN -> {prop xs ys} / [lengthListN_int xs]
@-}
proof :: ListN -> ListN -> Proof 
proof xs ys = 
  case xs of 
    Cons x1 xs' ->
      case xs' of 
        Cons x2 xs'' ->
          case ys of 
            Cons y ys' -> 
              proof (Cons x2 xs'' `by` lem x1 x2 xs'') ys
            Nil ->
              idR_concatListN xs
        Nil ->
          case ys of 
            Cons y ys' -> 
              undefined
            Nil ->
              idR_concatListN xs
    Nil ->
      undefined
-- proof (Cons x1 (Cons x2 xs)) (Cons y ys) = undefined
-- proof (Cons x Nil) (Cons y ys) = undefined
-- proof xs Nil = idR_concatListN xs 
-- proof Nil ys = undefined
-- [tactic|
-- proof :: ListN -> ListN -> Proof 
-- proof xs ys =
--   induct xs as [|x xs'];
--   induct xs';
--   destruct ys;
--   auto [idR_concatListN] 2
-- |]
