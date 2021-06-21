{-# LANGUAGE DataKinds, GADTs, TypeOperators #-}
{-@ LIQUID "--no-termination" @-}

import Prelude hiding (max)

{-@ data AVL a =
  Leaf
  | Node {
    key    :: a,
    left   :: AVLL a key,
    right  :: {v:AVLR a key | isBalanced left v 1},
    height :: {v:Nat | isRealHeight v left right}
  }
@-}
data AVL a = Leaf | Node { key :: a, left :: AVL a, right :: AVL a, height :: Int } deriving (Show)

{-@ type AVLL a X = AVL {v:a | v < X} @-}
{-@ type AVLR a X = AVL {v:a | v > X} @-}

{-@ measure realHeight @-}
{-@ lazy realHeight @-}
{-@ realHeight                   :: AVL a -> Nat @-}
realHeight                       :: AVL a -> Int
realHeight Leaf                  =  0
realHeight (Node _ left right _) =  nodeHeight left right

{-@ inline nodeHeight @-}
{-@ nodeHeight        :: AVL a -> AVL a -> Nat @-}
nodeHeight            :: AVL a -> AVL a -> Int
nodeHeight left right =  1 + max (realHeight left) (realHeight right)

{-@ inline max @-}
{-@ max :: Nat -> Nat -> Nat @-}
max     :: Int -> Int -> Int
max x y =  if x > y then x else y

{-@ inline isRealHeight @-}
{-@ isRealHeight          :: h:Nat -> left:AVL a -> right:AVL a -> Bool @-}
isRealHeight              :: Int -> AVL a -> AVL a -> Bool
isRealHeight h left right =  h == nodeHeight left right

{-@ inline isBalanced @-}
{-@ isBalanced          :: left:AVL a -> right:AVL a -> n:Nat -> Bool @-}
isBalanced              :: AVL a -> AVL a -> Int -> Bool
isBalanced left right n =  (0 - n) <= d && d <= n
  where d               =  (getHeight left) - (getHeight right)

{-@ type AVLN a N = {v:AVL a | realHeight v = N} @-}

{-@ type AVLT a T = AVLN a {realHeight T} @-}

{-@ empty :: AVLN a 0 @-}
empty     :: AVL a
empty     =  Leaf

{-@ singleton :: a -> AVLN a 1 @-}
singleton     :: a -> AVL a
singleton x   =  Node x empty empty 1

{-@ mkNode          :: key:a -> left:AVLL a key -> {right:AVLR a key | isBalanced left right 1} -> {v:AVL a | realHeight v = nodeHeight left right} @-}
mkNode              :: a -> AVL a -> AVL a -> AVL a
mkNode x left right =  Node x left right h
  where h           =  nodeHeight left right

{-@ measure getHeight @-}
{-@ getHeight            :: t:AVL a -> {v:Nat | v = realHeight t} @-}
getHeight Leaf           =  0
getHeight (Node _ _ _ h) =  h

{-@ inline leftBig @-}
{-@ leftBig        :: left:AVL a -> right:AVL a -> Bool @-}
leftBig            :: AVL a -> AVL a -> Bool
leftBig left right =  getHeight left - getHeight right == 2

{-@ inline rightBig @-}
{-@ rightBig        :: left:AVL a -> right:AVL a -> Bool @-}
rightBig            :: AVL a -> AVL a -> Bool
rightBig left right =  getHeight right - getHeight left == 2

{-@ measure balanceFactor @-}
balanceFactor                       :: AVL a -> Int
balanceFactor Leaf                  =  0
balanceFactor (Node _ left right _) =  getHeight left - getHeight right

{-@ inline leftHeavy @-}
leftHeavy t = balanceFactor t > 0

{-@ inline rightHeavy @-}
rightHeavy t = balanceFactor t < 0

{-@ inline noHeavy @-}
noHeavy t = balanceFactor t == 0

{-@ inline diff @-}
diff s t = getHeight s - getHeight t

-- Ensure code is unreachable
{-@ die :: {s:String | false} -> a @-}
die :: String -> a
die = error

-- For use with Lemmas 
assert _ y = y

{-@ measure isNode @-}
isNode      :: AVL a -> Bool
isNode Leaf =  False
isNode _    =  True

{-@ balL0 :: x:a
          -> l:{AVLL a x | noHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLN a {realHeight l + 1}
  @-}
balL0 :: a -> AVL a -> AVL a -> AVL a -- Bool
balL0 v (Node lv ll lr _) r = mkNode lv ll (mkNode v lr r)

{-@ balLL :: x:a
          -> l:{AVLL a x | leftHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLT a l
  @-}
balLL v (Node lv ll lr _) r = mkNode lv ll (mkNode v lr r)

{-@ balLR :: x:a
          -> l:{AVLL a x | rightHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLT a l
  @-}
balLR v (Node lv ll (Node lrv lrl lrr _) _) r
  = mkNode lrv (mkNode lv ll lrl) (mkNode v lrr r)

{-@ balR0 :: x:a
          -> l: AVLL a x
          -> r: {AVLR a x | rightBig l r && noHeavy r}
          -> AVLN a {realHeight r + 1}
  @-}
balR0 v l (Node rv rl rr _) = mkNode rv (mkNode v l rl) rr

{-@ balRR :: x:a
          -> l: AVLL a x
          -> r:{AVLR a x | rightBig l r && rightHeavy r}
          -> AVLT a r
  @-}
balRR v l (Node rv rl rr _) = mkNode rv (mkNode v l rl) rr


{-@ balRL :: x:a
          -> l: AVLL a x
          -> r:{AVLR a x | rightBig l r && leftHeavy r}
          -> AVLT a r
  @-}
balRL v l (Node rv (Node rlv rll rlr _) rr _) = mkNode rlv (mkNode v l rll) (mkNode rv rlr rr)

{-@ insert :: a -> s:AVL a -> {t: AVL a | eqOrUp s t} @-}
insert y Leaf = singleton y
insert y t@(Node x _ _ _)
  | y < x     = insL y t
  | y > x     = insR y t
  | otherwise = t

{-@ inline eqOrUp @-}
eqOrUp s t = d == 0 || d == 1
  where
    d      = diff t s

{-@ insL :: x:a
         -> t:{AVL a | x < key t && 0 < realHeight t}
         -> {v: AVL a | eqOrUp t v}
  @-}
insL a (Node v l r _)
  | isLeftBig && leftHeavy l'  = balLL v l' r
  | isLeftBig && rightHeavy l' = balLR v l' r
  | isLeftBig                  = balL0 v l' r
  | otherwise                  = mkNode  v l' r
  where
    isLeftBig                  = leftBig l' r
    l'                         = insert a l

{-@ insR :: x:a
         -> t:{AVL a  | key t < x && 0 < realHeight t }
         -> {v: AVL a | eqOrUp t v}
  @-}
insR a (Node v l r _)
  | isRightBig && rightHeavy r' = balRR v l r'
  | isRightBig && leftHeavy r'  = balRL v l r'
  | isRightBig                  = balR0 v l r'
  | otherwise                   = mkNode v l r'
  where
    isRightBig                  = rightBig l r'
    r'                          = insert a r

-- This is probably a bug in Liquid Haskell, the tutorial doesn't have this invariant and breaks.
-- It should be computed from the other definitions we describe in the code.
{-@ invariant {v: AVL a | getHeight v == realHeight v} @-}

{-{-@ insertWrong :: a -> s:AVL a -> {t: AVL a | eqOrUp s t} @-}
insertWrong y Leaf = singleton y
insertWrong y t@(Node x _ _ _)
  | y < x     = insR y t
  | y > x     = insR y t
  | otherwise = t-}
