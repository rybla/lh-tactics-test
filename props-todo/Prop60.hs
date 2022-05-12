{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop60 where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop xs Nil = True
prop xs ys = lastListN' (concatListN xs ys) == lastListN' ys

-- ! FAILS
{-@ automatic-instances proof @-}
{-@
proof :: xs:ListN -> ys:ListN -> {prop xs ys}
@-}
[tactic|
proof :: ListN -> ListN -> Proof
proof xs ys = 
  induct xs as [/x1 xs'];
  induct xs' as [/x2 xs''];
  induct ys as [/y ys'];
  use {proof (Cons x2 xs'') (Cons y ys')} requires [x2, xs'', y, ys']
|]
