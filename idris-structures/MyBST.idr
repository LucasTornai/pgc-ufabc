import Data.So

data Tree : (a: Type) -> Type where
  Leaf  : Tree a
  Node  : (key: a) -> (left: Tree a) -> (right: Tree a) -> Tree a

minVal : Ord a => Tree a -> Maybe a
minVal Leaf                      = Nothing
minVal (Node key Leaf _)         = Just key
minVal (Node key left right)     = minVal left

maxVal : Ord a => Tree a -> Maybe a
maxVal Leaf                      = Nothing
maxVal (Node key _ Leaf)         = Just key
maxVal (Node left key right)     = maxVal right

data Comp = LT | EQ | GT

lessTree : Ord a => a -> Tree a -> Bool
lessTree x node = case minVal node of
                   Nothing => True
                   Just key  => x < key

moreTree : Ord a => a -> Tree a -> Bool
moreTree x node = case maxVal node of
                   Nothing => True
                   Just key  => x >= key

comp : Ord a => a -> a -> Comp
comp x y = if x > y then GT else if x < y then LT else EQ

IsLft : Ord a => (x: a) -> (left: Tree a) -> Type
IsLft x left = So (moreTree x left)

IsRgt : Ord a => (x: a) -> (right: Tree a) -> Type
IsRgt x right = So (lessTree x right)

mkIsLft : Ord a => (x: a) -> (l: Tree a) -> (IsLft x l)
mkIsLft x l =
  case (choose (moreTree x l)) of
       Left proofYes => proofYes

mkIsRgt : Ord a => (x: a) -> (r: Tree a) -> (IsRgt x r)
mkIsRgt x r =
  case (choose (lessTree x r)) of
       Left proofYes => proofYes

data IsBST : (t : Tree a) -> Type where
  IsBSTLeaf : IsBST Leaf
  IsBSTNode : Ord a => (x: a) -> (left: Tree a) -> (IsLft x left) -> (IsBST left) -> (right: Tree a) -> (IsRgt x right) -> (IsBST right) -> (IsBST (Node x left right))

BSTree : Type -> Type
BSTree a = (t' : (Tree a) ** (IsBST t'))

insert : Ord a => (x : a) -> (t : Tree a ** IsBST t) -> BSTree a
insert x (Leaf ** IsBSTLeaf)  = 
  let isLftPrf = mkIsLft x Leaf
      isRgtPrf = mkIsRgt x Leaf
  in  ((Node x Leaf Leaf) ** (IsBSTNode x Leaf isLftPrf IsBSTLeaf Leaf isRgtPrf IsBSTLeaf))
insert x ((Node y left right) ** (IsBSTNode y left isLftPrf lPrf right isRgtPrf rPrf)) =
  case comp y x of
       GT => 
       let (lTree ** pl) = insert x (left ** lPrf)
           isLft         = mkIsLft y lTree
       in  ((Node y lTree right) ** (IsBSTNode y lTree isLft pl right isRgtPrf rPrf))
       LT => 
       let (rTree ** pr) = insert x (right ** rPrf)
           isRgt         = mkIsRgt y rTree
       in  ((Node y left rTree) ** (IsBSTNode y left isLftPrf lPrf rTree isRgt pr))
       EQ => ((Node y left right) ** (IsBSTNode y left isLftPrf lPrf right isRgtPrf rPrf))
