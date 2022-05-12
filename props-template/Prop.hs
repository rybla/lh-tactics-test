{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module TIP.Prop# where

import Data
import Proof
import Tactic.Core.Quote

{-@ reflect prop @-}
prop = _

{-@ automatic-instances proof @-}
{-@
proof :: _ -> {prop _}
@-}
[tactic|
proof :: _ -> Proof
proof _ = _
|]