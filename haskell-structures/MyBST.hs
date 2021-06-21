{-# LANGUAGE DataKinds, GADTs, TypeOperators #-}
module MyBST where

{-@ data MyBST a where
      Leaf :: MyBST a
      | Node :: key : a -> left : BSTL a key -> right : BSTR a key -> MyBST a @-}
{-@ type BSTL a X = MyBST {vl: a | vl < X} @-}
{-@ type BSTR a X = MyBST {vr: a | vr > X} @-}
data MyBST a where
  Leaf :: Ord a => MyBST a
  Node :: Ord a => a -> MyBST a -> MyBST a -> MyBST a

validBST = Node 5 Leaf (Node 11 Leaf Leaf)

--invalidBST = Node 5 (Node 11 Leaf Leaf) Leaf

insert :: Ord a => a -> MyBST a -> MyBST a
insert x Leaf = Node x Leaf Leaf
insert x (Node key left right)
  | x < key = Node key (insert x left) right
  | x > key = Node key left (insert x right)
  | otherwise = Node key left right

--invalidInsert :: Ord a => a -> MyBST a -> MyBST a
--invalidInsert x Leaf = Node x Leaf Leaf
--invalidInsert x (Node key l right)
--  | x < key = Node key left (insert x right)
--  | x > key = Node key left (insert x right)
--  | otherwise = Node key left right
