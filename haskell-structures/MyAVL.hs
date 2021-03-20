{-# LANGUAGE DataKinds, GADTs, TypeOperators #-}
module MyAVL where

{-@ data MyAVL a where
      Empty :: MyAVL a
      | Node :: v : a -> l : AVLL a v -> r : AVLR a v -> MyAVL a @-}
{-@ type AVLL a X = MyAVL {vl: a | vl < X} @-}
{-@ type AVLR a X = MyAVL {vr: a | vr > X} @-}
data MyAVL a where
  Empty :: Ord a => MyAVL a
  Node :: Ord a => a -> MyAVL a -> MyAVL a -> MyAVL a

-- https://arxiv.org/pdf/1701.03320.pdf
{-@ measure height @-}
{-@ height :: MyAVL a -> Nat @-}
height :: Ord a => MyAVL a -> Int
height Empty = 0
height (Node v l r) = 1 + max (height l) (height r)


validBST = Node 5 Empty (Node 11 Empty Empty)

--invalidBST = Node 5 (Node 11 Empty Empty) Empty

insert :: Ord a => a -> MyAVL a -> MyAVL a
insert x Empty = Node x Empty Empty
insert x (Node v l r)
  | x < v = Node v (insert x l) r
  | x > v = Node v l (insert x r)
  | otherwise = Node v l r

--invalidInsert :: Ord a => a -> MyAVL a -> MyAVL a
--invalidInsert x Empty = Node x Empty Empty
--invalidInsert x (Node v l r)
--  | x < v = Node v l (insert x r)
--  | x > v = Node v l (insert x r)
--  | otherwise = Node v l r
