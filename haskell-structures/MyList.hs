module List where

data List a = Nil | Cons a (List a)

insert :: a -> List a -> List a
insert = Cons
