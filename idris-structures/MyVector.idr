data Vect: Nat -> Type -> Type where
  Nil : Vect Z a
  Cons : a -> Vect x a -> Vect (S x) a

insert : a -> Vect x a -> Vect (S x) a
insert = Cons
