module MyList where

data MyList a = Nil | Cons a (MyList a)

insert :: a -> MyList a -> MyList a
insert = Cons
