{-# LANGUAGE GADTs, DataKinds #-}
module MyVector where

data Nat = Z | S Nat

data MyVector l a where
  Nil :: MyVector Z a
  Cons :: a -> MyVector x a -> MyVector (S x) a

insertVector :: a -> MyVector l a -> MyVector (S l) a
insertVector = Cons
