{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

-- {-@ LIQUID "--compile-spec" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--short-names" @-}

module Test1 where

import Language.Haskell.TH.Syntax
import Proof
import Tactic.Core.Quote

{-@
data N = Z | S N
@-}
data N = Z | S N

{-@ reflect add @-}
add :: N -> N -> N
add Z n = n
add (S m) n = S (add m n)

return []

{-@ automatic-instances add_m_Sn @-}
{-@
add_m_Sn :: m:N -> n:N -> {add m (S n) == S (add m n)}
@-}
-- %tactic:begin:add_m_Sn
add_m_Sn :: N -> N -> Proof
add_m_Sn
  = \ m
      -> \ n
           -> case m of
                Z -> trivial
                S n_a4oV
                  -> ((add_m_Sn n_a4oV) n
                        &&&
                          ((add_m_Sn n_a4oV) n_a4oV
                             &&&
                               ((add_m_Sn n_a4oV) (S n)
                                  &&&
                                    ((add_m_Sn n_a4oV) (S n_a4oV)
                                       &&&
                                         ((add_m_Sn n_a4oV) (S Z)
                                            &&& ((add_m_Sn n_a4oV) Z &&& trivial))))))
-- %tactic:end:add_m_Sn
