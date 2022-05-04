{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module Prop1 where

import Data
import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core.Quote

{-@ reflect prop1 @-}
prop1 :: N -> NL -> Bool
prop1 n xs = concatNL (takeNL n xs) (dropNL n xs) == xs

return []

{-@ automatic-instances prop1_proof @-}
{-@
prop1_proof :: n:N -> l:NL -> {prop1 n l}
@-}
[tactic|
prop1_proof :: N -> NL -> Proof
prop1_proof n l =
  induct n;
  induct l;
  auto [] 2
|]


{-
! problem
splices the following into the space above:

```
  -- %tactic:begin:prop1_proof
  prop1_proof :: N -> NL -> Proof
  prop1_proof = \n -> \l -> case n of
                                Data.Z -> case l of
                                              Data.Nil -> trivial
                                              Data.Cons n_0 nL_1 -> trivial
                                              Data.S n_0 -> case l of
                                                                Data.Nil -> trivial
                                                                Data.Cons n_0 nL_1 -> trivial
  -- %tactic:end:prop1_proof
```

the indentation is wrong! it doesn't indent the nested cases properly
-}

-- {-@ automatic-instances prop1_proof @-}
-- {-@
-- prop1_proof :: x:N -> l:NL -> {prop1 x l}
-- @-}
-- prop1_proof :: N -> NL -> Proof
-- -- prop1_proof x l = undefined
-- prop1_proof Z l = trivial
-- prop1_proof (S n) Nil = trivial
-- prop1_proof (S n) (Cons x l) = prop1_proof n l
--   -- -- HYP
--   -- concatNL (takeNL (S n) (Cons x l)) (dropNL (S n) (Cons x l))
--   -- concatNL (Cons x (takeNL n l)) (dropNL n l)
--   -- Cons x (concatNL (takeNL n l) (dropNL n l))
--   -- --
--   -- -- IH
--   -- concatNL n l

