{-# LANGUAGE DataKinds, GADTs, TypeOperators #-}
module BST where

{-@ data BST a where
      Leaf :: BST a
      | Node :: key : a -> left : BSTL a key -> right : BSTR a key -> BST a @-}
{-@ type BSTL a X = BST {vl: a | vl < X} @-}
{-@ type BSTR a X = BST {vr: a | vr > X} @-}
data BST a where
  Leaf :: Ord a => BST a
  Node :: Ord a => a -> BST a -> BST a -> BST a

validBST = Node 5 Leaf (Node 11 Leaf Leaf)

--invalidBST = Node 5 (Node 11 Leaf Leaf) Leaf

insert :: Ord a => a -> BST a -> BST a
insert x Leaf = Node x Leaf Leaf
insert x (Node key left right)
  | x < key = Node key (insert x left) right
  | x > key = Node key left (insert x right)
  | otherwise = Node key left right

--invalidInsert :: Ord a => a -> BST a -> BST a
--invalidInsert x Leaf = Node x Leaf Leaf
--invalidInsert x (Node key l right)
--  | x < key = Node key left (insert x right)
--  | x > key = Node key left (insert x right)
--  | otherwise = Node key left right
