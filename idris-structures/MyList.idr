data MyList : (a: Type) -> Type where
  Nil: MyList a
  Cons: (x: a) -> MyList a -> MyList a

insertList: a -> MyList a -> MyList a
insertList = Cons

