{-@ LIQUID "--reflection" @-}

module Data where

-- N

{-@
data N = Z | S N
@-}
data N = Z | S N deriving (Eq, Show)

{-@ reflect addN @-}
addN :: N -> N -> N
addN Z n = n
addN (S m) n = S (addN m n)

{-@ reflect subN @-}
subN :: N -> N -> N
subN Z n = Z
subN m Z = m
subN (S m) (S n) = subN m n

{-@ reflect leqN @-}
leqN :: N -> N -> Bool
leqN Z n = True
leqN (S m) Z = False
leqN (S m) (S n) = leqN m n

-- NL

{-@
data NL = Nil | Cons N NL
@-}
data NL = Nil | Cons N NL deriving (Eq, Show)

{-@ reflect concatNL @-}
concatNL :: NL -> NL -> NL
concatNL Nil l2 = l2
concatNL (Cons h l1) l2 = Cons h (concatNL l1 l2)

{-@ reflect takeNL @-}
takeNL :: N -> NL -> NL
takeNL _ Nil = Nil
takeNL Z _ = Nil
takeNL (S n) (Cons h l) = Cons h (takeNL n l)

{-@ reflect dropNL @-}
dropNL :: N -> NL -> NL
dropNL _ Nil = Nil
dropNL Z (Cons h l) = Cons h l
dropNL (S n) (Cons h l) = dropNL n l

{-@ reflect countNL @-}
countNL :: N -> NL -> N
countNL n Nil = Z
countNL n (Cons h l) = if n == h then S (countNL n l) else countNL n l
