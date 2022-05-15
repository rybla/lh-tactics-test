{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop71 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect lemma_prop @-}
lemma_prop x ys =
  case ys of
    Nil -> True
    Cons y ys' -> elemListN x ys == (x == y || elemListN x ys')

{-@
lemma :: x:N -> ys:ListN -> {lemma_prop x ys}
@-}
lemma :: N -> ListN -> Proof
lemma x ys = undefined

return []

{-@ reflect prop @-}
prop x y xs =
  if x == y
    then True
    else elemListN x (insertListN y xs) == elemListN x xs


-- ! HANGS
{-@ automatic-instances proof @-}
{-@
proof :: x:N -> y:N -> xs:ListN -> {prop x y xs}
@-}
proof :: N -> N -> ListN -> Proof
proof x y zs =
  if x == y then
    trivial
  else
    case zs of
      Nil -> trivial
      Cons z zs' -> 
        if leN y z then 
          trivial
        else 
          lemma x (insertListN y zs') &&&
          lemma x zs &&&
          proof x y zs'

-- [tactic|
-- proof :: N -> N -> ListN -> Proof
-- proof x y ys =
--   condition {x == y};
--   induct ys as [/y' ys'];
--   condition {leN y y'} requires [y'];
--   auto [lemma, insertListN] 3
-- |]
