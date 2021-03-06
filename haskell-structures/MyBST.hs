{-# LANGUAGE DataKinds, GADTs, TypeOperators #-}
module MyBST where

{-@ data MyBST a where
      Empty :: MyBST a
      | Node :: v : a -> l : BSTL a v -> r : BSTR a v -> MyBST a @-}
{-@ type BSTL a X = MyBST {vl: a | vl < X} @-}
{-@ type BSTR a X = MyBST {vr: a | vr > X} @-}
data MyBST a where
  Empty :: Ord a => MyBST a
  Node :: Ord a => a -> MyBST a -> MyBST a -> MyBST a

validBST = Node 5 Empty (Node 11 Empty Empty)

--invalidBST = Node 5 (Node 11 Empty Empty) Empty
