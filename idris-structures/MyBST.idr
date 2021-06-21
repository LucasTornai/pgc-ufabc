import Data.So

data Tree : (a: Type) -> Type where
  Leaf : Tree a
  Node  : (left: Tree a) -> (key: a) -> (right: Tree a) -> Tree a

minVal : Ord a => Tree a -> Maybe a
minVal Leaf            = Nothing
minVal (Node Leaf key _) = Just key
minVal (Node left key right)     = minVal left

maxVal : Ord a => Tree a -> Maybe a
maxVal Leaf            = Nothing
maxVal (Node _ key Leaf) = Just key
maxVal (Node left key right)     = maxVal right

less : Ord a => a -> Tree a -> Bool
less x node = case minVal node of
                   Nothing => True
                   Just key  => x < key

more : Ord a => a -> Tree a -> Bool
more x node = case maxVal node of
                   Nothing => True
                   Just key  => x >= key

IsLft : Ord a => (x:a) -> (left:Tree a) -> Type
IsLft x left = So (more x left)

IsRgt : Ord a => (x:a) -> (right:Tree a) -> Type
IsRgt x right = So (less x right)

mkIsLft : Ord a => (x:a) -> (left:Tree a) -> Maybe (IsLft x left)
mkIsLft x left =
  case (choose (more x left)) of
       Left proofYes => Just proofYes
       Right proofNo => Nothing

mkIsRgt : Ord a => (x:a) -> (right:Tree a) -> Maybe (IsRgt x right)
mkIsRgt x right =
  case (choose (less x right)) of
       Left proofYes => Just proofYes
       Right proofNo => Nothing

t1 : Tree Int
t1 = Node Leaf 5 Leaf

t2 : Tree Int
t2 = Node Leaf 2 Leaf

t3 : Tree Int
t3 = Node t2 4 t1

data IsBST : (t : Tree a) -> Type where
  IsBSTZero : IsBST Leaf
  IsBSTOne  : Ord a => (x:a) -> IsBST (Node Leaf x Leaf)
  IsBSTLft  : Ord a => (x:a) -> (left:Tree a) -> (IsLft x left) -> (IsBST left) -> (IsBST (Node left x Leaf))
  IsBSTRgt  : Ord a => (x:a) -> (right:Tree a) -> (IsRgt x right) -> (IsBST right) -> (IsBST (Node Leaf x right))
  IsBSTMore : Ord a => (x:a) -> (left:Tree a) -> (right:Tree a) -> (IsLft x left) -> (IsRgt x right) -> (IsBST left) -> (IsBST right) -> (IsBST (Node left x right))

mkIsBST : Ord a => (t : Tree a) -> Maybe (IsBST t)
mkIsBST Leaf = Just IsBSTZero
mkIsBST (Node Leaf x Leaf) = Just (IsBSTOne x)
mkIsBST (Node left x Leaf) = do proofLeft <- mkIsLft x left
                              proofLBST <- mkIsBST left
                              Just (IsBSTLft x left proofLeft proofLBST)
mkIsBST (Node Leaf x right) = do proofRight <- mkIsRgt x right
                              proofRBST <- mkIsBST right
                              Just (IsBSTRgt x right proofRight proofRBST)
mkIsBST (Node left x right) = do proofLeft  <- mkIsLft x left
                          proofRight <- mkIsRgt x right
                          proofLBST  <- mkIsBST left
                          proofRBST  <- mkIsBST right
                          Just (IsBSTMore x left right proofLeft proofRight proofLBST proofRBST)

insert : Ord a => (x : a) -> (t : Tree a) -> (IsBST t) -> (t' : (Tree a) ** (IsBST t'))
insert x Leaf IsBSTZero  = ((Node Leaf x Leaf) ** (IsBSTOne x))
insert x (Node Leaf y Leaf) (IsBSTOne y) =
   let (tx ** px) = insert x Leaf IsBSTZero
   in  case choose (more y tx) of
           Left prfLft => (Node tx y Leaf ** (IsBSTLft y tx prfLft px))
           Right _     => case choose (less y tx) of
                               Left prfRgt => (Node Leaf y tx ** (IsBSTRgt y tx prfRgt px))
                               Right _     => (Node Leaf y Leaf ** (IsBSTOne y))
insert x (Node left y Leaf) (IsBSTLft y left isLftPrf lPrf) =
  let (tx ** px) = insert x Leaf IsBSTZero
      (tl ** pl) = insert x left lPrf
  in case choose (less y tx) of
          Left prfRgt => (Node left y tx ** IsBSTMore y left tx isLftPrf prfRgt lPrf px)
          Right _ => case choose (more y tl) of
                          Left prfLft => (Node tl y Leaf ** IsBSTLft y tl prfLft pl)
                          Right _ => (Node left y Leaf ** (IsBSTLft y left isLftPrf lPrf))
insert x (Node Leaf y right) (IsBSTRgt y right isRgtPrf rPrf) =
  let (tx ** px) = insert x Leaf IsBSTZero
      (tr ** pr) = insert x right rPrf
  in case choose (more y tx) of
          Left prfLft => (Node tx y right ** IsBSTMore y tx right prfLft isRgtPrf px rPrf)
          Right _ => case choose (less y tr) of
                          Left prfRgt => (Node Leaf y tr ** IsBSTRgt y tr prfRgt pr)
                          Right _ => (Node Leaf y right ** (IsBSTRgt y right isRgtPrf rPrf))
insert x (Node left y right) (IsBSTMore y left right isLftPrf isRgtPrf lPrf rPrf) =
  let (tx ** px) = insert x Leaf IsBSTZero
  in case choose (more y tx) of
          Left _ => insert x left lPrf
          Right _ => insert x right rPrf 
