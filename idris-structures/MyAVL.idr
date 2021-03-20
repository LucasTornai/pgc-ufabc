import Data.So

data Tree : (a: Type) -> Type where
  Empty : Tree a
  Node  : (l: Tree a) -> (v: a) -> (r: Tree a) -> Tree a

minVal : Ord a => Tree a -> Maybe a
minVal Empty            = Nothing
minVal (Node Empty v _) = Just v
minVal (Node l v r)     = minVal l

maxVal : Ord a => Tree a -> Maybe a
maxVal Empty            = Nothing
maxVal (Node _ v Empty) = Just v
maxVal (Node l v r)     = maxVal r

less : Ord a => a -> Tree a -> Bool
less x node = case minVal node of
                   Nothing => True
                   Just v  => x < v

more : Ord a => a -> Tree a -> Bool
more x node = case maxVal node of
                   Nothing => True
                   Just v  => x >= v

IsLft : Ord a => (x:a) -> (l:Tree a) -> Type
IsLft x l = So (more x l)

IsRgt : Ord a => (x:a) -> (r:Tree a) -> Type
IsRgt x r = So (less x r)

mkIsLft : Ord a => (x:a) -> (l:Tree a) -> Maybe (IsLft x l)
mkIsLft x l =
  case (choose (more x l)) of
       Left proofYes => Just proofYes
       Right proofNo => Nothing

mkIsRgt : Ord a => (x:a) -> (r:Tree a) -> Maybe (IsRgt x r)
mkIsRgt x r =
  case (choose (less x r)) of
       Left proofYes => Just proofYes
       Right proofNo => Nothing

t1 : Tree Int
t1 = Node Empty 5 Empty

t2 : Tree Int
t2 = Node Empty 2 Empty

t3 : Tree Int
t3 = Node t2 4 t1

data IsBST : (t : Tree a) -> Type where
  IsBSTZero : IsBST Empty
  IsBSTOne  : Ord a => (x:a) -> IsBST (Node Empty x Empty)
  IsBSTLft  : Ord a => (x:a) -> (l:Tree a) -> (IsLft x l) -> (IsBST l) -> (IsBST (Node l x Empty))
  IsBSTRgt  : Ord a => (x:a) -> (r:Tree a) -> (IsRgt x r) -> (IsBST r) -> (IsBST (Node Empty x r))
  IsBSTMore : Ord a => (x:a) -> (l:Tree a) -> (r:Tree a) -> (IsLft x l) -> (IsRgt x r) -> (IsBST l) -> (IsBST r) -> (IsBST (Node l x r))

mkIsBST : Ord a => (t : Tree a) -> Maybe (IsBST t)
mkIsBST Empty = Just IsBSTZero
mkIsBST (Node Empty x Empty) = Just (IsBSTOne x)
mkIsBST (Node l x Empty) = do proofLeft <- mkIsLft x l
                              proofLBST <- mkIsBST l
                              Just (IsBSTLft x l proofLeft proofLBST)
mkIsBST (Node Empty x r) = do proofRight <- mkIsRgt x r
                              proofRBST <- mkIsBST r
                              Just (IsBSTRgt x r proofRight proofRBST)
mkIsBST (Node l x r) = do proofLeft  <- mkIsLft x l
                          proofRight <- mkIsRgt x r
                          proofLBST  <- mkIsBST l
                          proofRBST  <- mkIsBST r
                          Just (IsBSTMore x l r proofLeft proofRight proofLBST proofRBST)

height: Ord a => Tree a -> Int
height Empty = 0
height (Node l v r) = 1 + (max (height l) (height r))

isImba: Int -> Int -> Bool
isImba x y = (x - 1) > y

isBal: Ord a => Tree a -> Type
isBal Empty = So True
isBal (Node l v r) =
  let hl = height l
      hr = height r
  in So (not (isImba hl hr) && not (isImba hr hl))

data Balance = ImbL | Bal | ImbR

checkBalance: Ord a => Tree a -> Balance
checkBalance Empty = Bal
checkBalance (Node l v r) =
  let hl = height l
      hr = height r
  in case isImba hl hr of
          True => ImbL
          False => case isImba hr hl of
                        True => ImbR
                        False => Bal



insert : Ord a => (x : a) -> (t : Tree a) -> (IsBST t) -> (t' : (Tree a) ** (IsBST t'))
insert x Empty IsBSTZero  = ((Node Empty x Empty) ** (IsBSTOne x))
insert x (Node Empty y Empty) (IsBSTOne y) =
   let (tx ** px) = insert x Empty IsBSTZero
   in  case choose (more y tx) of
           Left prfLft => (Node tx y Empty ** (IsBSTLft y tx prfLft px))
           Right _     => case choose (less y tx) of
                               Left prfRgt => (Node Empty y tx ** (IsBSTRgt y tx prfRgt px))
                               Right _     => (Node Empty y Empty ** (IsBSTOne y))
insert x (Node l y Empty) (IsBSTLft y l isLftPrf lPrf) =
  let (tx ** px) = insert x Empty IsBSTZero
      (tl  ** pl) = insert x l lPrf
  in case choose (less y tx) of
          Left prfRgt => (Node l y tx ** IsBSTMore y l tx isLftPrf prfRgt lPrf px)
          Right _ => case choose (more y tl) of
                          Left prfLft => (Node tl y Empty ** IsBSTLft y tl prfLft pl)
                          Right _ => (Node l y Empty ** (IsBSTLft y l isLftPrf lPrf))
insert x (Node Empty y r) (IsBSTRgt y r isRgtPrf rPrf) =
  let (tx ** px) = insert x Empty IsBSTZero
      (tr  ** pr) = insert x r rPrf
  in case choose (more y tx) of
          Left prfLft => (Node tx y r ** IsBSTMore y tx r prfLft isRgtPrf px rPrf)
          Right _ => case choose (less y tr) of
                          Left prfRgt => (Node Empty y tr ** IsBSTRgt y tr prfRgt pr)
                          Right _ => (Node Empty y r ** (IsBSTRgt y r isRgtPrf rPrf))
 
