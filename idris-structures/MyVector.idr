import Data.So

data Vect: Nat -> Type -> Type where
  Nil : Vect Z a
  Cons : a -> Vect x a -> Vect (S x) a

insert : a -> Vect x a -> Vect (S x) a
insert = Cons

data LEGN = L | E | G | N

Prelude.Interfaces.Eq LEGN where
  (==) L L = True
  (==) E E = True
  (==) G G = True
  (==) N N = True
  (==) _ _ = False
  (/=) x y = x == y

lessEqualGreater : Ord a => a -> a -> LEGN
lessEqualGreater x y = if (x > y) then G else if x < y then L else E

justLEGN: Ord a => Maybe a -> a -> LEGN
justLEGN Nothing _ = N
justLEGN (Just x) y = case lessEqualGreater x y of
                          L => L
                          E => E
                          G => G

isLMaybe: Ord a => Maybe a -> a -> Bool
isLMaybe Nothing _ = True
isLMaybe (Just x) y = x < y

isGMaybe: Ord a => Maybe a -> a -> Bool
isGMaybe Nothing _ = True
isGMaybe (Just x) y = x > y

data BST: (x: Type) -> Maybe x -> Type where
  EmptyBST: Ord a => BST a Nothing
  NodeBST: Ord a => (l: BST a b) -> (v: a) -> (r: BST a c) -> {auto leftValues: So (isLMaybe b v)} -> {auto rightValues: So (isGMaybe c v)} -> BST a (Just v)

insertTest : a -> BST a b -> BST a z
--insertTest x EmptyBST = NodeBST EmptyBST x EmptyBST
insertTest x (NodeBST l v r) = case lessEqualGreater x v of
                                     L => NodeBST (insertTest x l) v r
                                     E => NodeBST l v r
                                     G => NodeBST l v (insertTest x r)
                                     N => NodeBST l v r
