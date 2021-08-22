{-# LANGUAGE GADTs, DataKinds #-}
module Vector where

data Nat = Z | S Nat

data Vector l a where
  Nil :: Vector Z a
  Cons :: a -> Vector x a -> Vector (S x) a

insertVector :: a -> Vector l a -> Vector (S l) a
insertVector = Cons

a = Cons 1 Nil
