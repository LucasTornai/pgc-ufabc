{-# LANGUAGE DataKinds, GADTs, TypeOperators #-}
{-@ LIQUID "--no-termination" @-}
module MyAVL where
-- https://gist.github.com/timjb/8292342
-- https://ucsd-progsys.github.io/liquidhaskell-tutorial/Tutorial_12_Case_Study_AVL.html

{-@ data MyAVL a = Empty
               | Node { v :: a
                      , l :: AVLL a v
                      , r :: {k:AVLR a v | isBal l k 1}
                      , h :: {k:Nat        | isReal k l r}
                      }                                  @-}
{-@ type AVLL a X = MyAVL {v:a | v < X}  @-}
{-@ type AVLR a X = MyAVL {v:a | X < v}  @-}
data MyAVL a =
    Empty
  | Node { v :: a
         , l :: MyAVL a
         , r :: MyAVL a
         , h :: Int
         }

{-@ measure realHeight @-}
realHeight :: MyAVL a -> Int
realHeight Empty          = 0
realHeight (Node _ l r _) = nodeHeight l r

{-@ inline nodeHeight @-}
nodeHeight :: MyAVL a -> MyAVL a -> Int
nodeHeight l r = 1 + myMax hl hr
  where
    hl         = realHeight l
    hr         = realHeight r

{-@ inline myMax @-}
myMax :: Int -> Int -> Int
myMax x y = if x > y then x else y

{-@ inline isReal @-}
isReal :: Int -> MyAVL a -> MyAVL a -> Bool
isReal v l r = v == nodeHeight l r

{-@ inline isBal @-}
isBal :: MyAVL a -> MyAVL a -> Int -> Bool
isBal l r n = 0 - n <= d && d <= n
  where
    d       = realHeight l - realHeight r

{-@ type AVLN a N = {v: MyAVL a | realHeight v = N} @-}
{-@ type AVLT a T = AVLN a {realHeight T} @-}

{-@ empty :: AVLN a 0 @-}
empty = Empty

{-@ singleton :: a -> AVLN a 1 @-}
singleton x =  Node x empty empty 1

{-@ measure getHeight @-}
getHeight Empty          = 0
getHeight (Node _ _ _ n) = n

{-@ mkNode :: v:a -> l:AVLL a v -> r:{k:AVLR a v | isBal l k 1}
           -> AVLN a {nodeHeight l r}
  @-}
mkNode v l r = Node v l r (nodeHeight l r)

{-@ inline leftBig @-}
leftBig l r = diff l r == 2

{-@ inline rightBig @-}
rightBig l r = diff r l == 2

{-@ inline diff @-}
diff s t = getHeight s - getHeight t

{-@ measure balFac @-}
balFac Empty          = 0
balFac (Node _ l r _) = getHeight l - getHeight r

{-@ inline leftHeavy @-}
leftHeavy  t = balFac t > 0

{-@ inline rightHeavy @-}
rightHeavy t = balFac t < 0

{-@ inline noHeavy @-}
noHeavy    t = balFac t == 0

{-@ balL0 :: x:a
          -> l:{AVLL a x | noHeavy l}
          -> r:{AVLR a x | leftBig l r}
          -> AVLN a {realHeight l + 1 }
  @-}
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

{-@ insert :: a -> s:MyAVL a -> {t: MyAVL a | eqOrUp s t} @-}
insert y Empty = singleton y
insert y t@(Node x _ _ _)
  | y < x     = insL y t
  | y > x     = insR y t
  | otherwise = t

{-@ inline eqOrUp @-}
eqOrUp s t = d == 0 || d == 1
  where
    d      = diff t s

{-@ insL :: x:a
         -> t:{MyAVL a | x < v t && 0 < realHeight t}
         -> {v: MyAVL a | eqOrUp t v}
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
         -> t:{MyAVL a  | v t < x && 0 < realHeight t }
         -> {v: MyAVL a | eqOrUp t v}
  @-}
insR a (Node v l r _)
  | isRightBig && rightHeavy r' = balRR v l r'
  | isRightBig && leftHeavy r'  = balRL v l r'
  | isRightBig                  = balR0 v l r'
  | otherwise                   = mkNode v l r'
  where
    isRightBig                  = rightBig l r'
    r'                          = insert a r
