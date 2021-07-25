||| A key-value tree data structure.
|||
||| This structure doesn't encode the invariants of the tree and is
||| *simply* a container. This structure ideally shouldn't be exposed
||| to the user at all. This structure should be used to build other
||| data structures.  See the modules alongside this for appropriate
||| interfaces for using the tree.
|||
||| @keyTy The type associated with the key.
data Tree : (keyTy : Type)
         -> Type
  where
    ||| An empty Tree node.
    Empty : Tree k

    ||| A Key Value node in the Tree.
    |||
    ||| @key   The key.
    ||| @left  The left child of the Node
    ||| @right THe right child of the Node.
    Node : (key   : k)
        -> (left  : Tree k)
        -> (right : Tree k)
        -> Tree k

%name Tree t, tree

 -- ------------------------------------------------------------- [ Definitions ]
data Balance : Nat -> Nat -> Type where
  LHeavy   : Balance (S n) n
  RHeavy   : Balance n     (S n)
  Balanced : Balance n     n

%name Balance b, bal

||| Indirection ensures that it reduces to at least S n' without
||| needing to case split on balance.
|||
||| Should make proofs easier.
height : Balance n m -> Nat
height b = S (height' b)
  where
    height' : Balance n m -> Nat
    height' (LHeavy {n}) = S n
    height' (RHeavy {n}) = S n
    height' {n} (Balanced {n}) = n


||| Encoding of the AVL tree height invariants.
|||
||| @height The height of a Tree.
||| @tree   The tree whose height we are capturing.
data AVLInvariant : (height : Nat)
                 -> (tree   : Tree k)
                 -> Type
  where
    ||| A tree of height zero.
    AVLEmpty : AVLInvariant 0 Empty
    ||| A Balanced tree.
    |||
    ||| @left  The invariant of the left child.
    ||| @right The invariant of the right child.
    ||| @b     The encoding of the nodes' balance.
    AVLNode : (left  : AVLInvariant n l)
           -> (right :  AVLInvariant m r)
           -> (b : Balance n m)
           -> AVLInvariant (height b) (Node k l r)

%name AVLInvariant inv

||| An AVL Tree.
|||
||| Modelled using subset to separate the invariants from the tree
||| implementation itself.
|||
||| @height  The height of the Tree.
||| @keyTy   The type associated with the keys.
AVLTree : (height  : Nat)
       -> (keyTy   : Type)
       -> Type
AVLTree n k = Subset (Tree k) (AVLInvariant n)

-- --------------------------------------------------------------- [ Rotations ]
data InsertRes : Nat -> (k : Type) -> Type where
  Same : AVLTree n k     -> InsertRes n k
  Grew : AVLTree (S n) k -> InsertRes n k

%name InsertRes res, r

||| Process the result of an insertion of a new Key-Value pair into
||| the Tree, returning the new tree and proof of the new tree's
||| height.
|||
||| `InsertRes` is obtained from the result of running `Tree.insert`.
runInsertRes : InsertRes n k -> (n : Nat ** AVLTree n k)
runInsertRes (Same t) = (_ ** t)
runInsertRes (Grew t) = (_ ** t)

||| Perform a Left rotation.
rotLeft : k
       -> AVLTree n k
       -> AVLTree (S (S n)) k
       -> InsertRes (S (S n)) k
-- Impossible because Empty has depth 0 and we know the depth is at least 2 from the type
rotLeft key l (Element Empty AVLEmpty) impossible

rotLeft key (Element l invl) (Element (Node key' rl rr) (AVLNode invrl invrr Balanced)) =
    Grew $ Element (Node key' (Node key l rl) rr)
                        (AVLNode (AVLNode invl invrl RHeavy) invrr LHeavy)

rotLeft key (Element l invl) (Element (Node key' (Node key'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr LHeavy) invrr LHeavy)) =
    Same $ Element (Node key'' (Node key l rll) (Node key' rlr rr)) -- Needs Checking
                   (AVLNode (AVLNode invl invrll Balanced) (AVLNode invrlr invrr RHeavy) Balanced)

rotLeft key (Element l invl) (Element (Node key' (Node key'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr RHeavy) invrr LHeavy)) =
    Same $ Element (Node key'' (Node key l rll) (Node key' rlr rr))
                   (AVLNode (AVLNode invl invrll LHeavy) (AVLNode invrlr invrr Balanced) Balanced)

rotLeft key (Element l invl) (Element (Node key' (Node key'' rll rlr) rr) (AVLNode (AVLNode invrll invrlr Balanced) invrr LHeavy)) =
    Same $ Element (Node key'' (Node key l rll) (Node key' rlr rr))
                   (AVLNode (AVLNode invl invrll Balanced) (AVLNode invrlr invrr Balanced) Balanced) -- Needs Checking

rotLeft key (Element l invl) (Element (Node key' rl rr) (AVLNode invrl invrr RHeavy)) =
    Same $ Element (Node key' (Node key l rl) rr)
                   (AVLNode (AVLNode invl invrl Balanced) invrr Balanced)

||| Perform a Right rotation.
rotRight : k
        -> AVLTree (S (S n)) k
        -> AVLTree n k
        -> InsertRes (S (S n)) k
rotRight key (Element Empty AVLEmpty) r impossible

rotRight key'' (Element (Node key ll (Node key' lrl lrr))
             (AVLNode invll (AVLNode invlrl invlrr RHeavy) RHeavy)) (Element r invr) =
  Same $ Element (Node key' (Node key ll lrl) (Node key'' lrr r))
                 (AVLNode (AVLNode invll invlrl LHeavy) (AVLNode invlrr invr Balanced) Balanced)
rotRight key'' (Element (Node key ll (Node key' lrl lrr))
             (AVLNode invll (AVLNode invlrl invlrr LHeavy) RHeavy)) (Element r invr) =
  Same $ Element (Node key' (Node key ll lrl) (Node key'' lrr r))
                 (AVLNode (AVLNode invll invlrl Balanced) (AVLNode invlrr invr RHeavy) Balanced)
rotRight key (Element (Node key' ll lr) (AVLNode invll invlr Balanced)) (Element r invr) =
  Grew $ Element (Node key' ll (Node key lr r))
                 (AVLNode invll (AVLNode invlr invr LHeavy) RHeavy)

rotRight key (Element (Node key' ll lr) (AVLNode invll invlr LHeavy)) (Element r invr) =
  Same $ Element (Node key' ll (Node key lr r))
                 (AVLNode invll (AVLNode invlr invr Balanced) Balanced)

rotRight key (Element (Node key' ll (Node key'' lrl lrr))
             (AVLNode invll (AVLNode invlrl invlrr Balanced) RHeavy)) (Element r invr) =
  Same $ Element (Node key'' (Node key' ll lrl) (Node key lrr r))
                 (AVLNode (AVLNode invll invlrl Balanced) (AVLNode invlrr invr Balanced) Balanced)


 --------------------------------------------------------------- [ Insertion ]

||| Perform an insertion into the tree returning the new tree wrapped
||| in a description describing the height change.
doInsert : (Ord k)
         => k
         -> AVLTree n k
         -> InsertRes n k
doInsert newKey (Element Empty AVLEmpty) = Grew (Element (Node newKey Empty Empty)
                                                       (AVLNode AVLEmpty AVLEmpty Balanced))
doInsert newKey (Element (Node key l r) (AVLNode invl invr b)) with (compare newKey key)
  doInsert newKey (Element (Node key l r) (AVLNode invl invr b)) | EQ = Same (Element (Node newKey l r) (AVLNode invl invr b))

  doInsert newKey (Element (Node key l r) (AVLNode invl invr b)) | LT with (assert_total $ doInsert newKey (Element l invl))
    -- Totality checker not clever enough to see that this is smaller
    doInsert newKey (Element (Node key l r) (AVLNode invl invr b))        | LT | (Same (Element l' invl'))
                                                                               = Same $ Element (Node key l' r) (AVLNode invl' invr b)
    doInsert newKey (Element (Node key l r) (AVLNode invl invr LHeavy))   | LT | (Grew (Element l' invl'))
                                                                               = rotRight key (Element l' invl') (Element r invr)
    doInsert newKey (Element (Node key l r) (AVLNode invl invr Balanced)) | LT | (Grew (Element l' invl'))
                                                                               = Grew $ Element (Node key l' r) (AVLNode invl' invr LHeavy)
    doInsert newKey (Element (Node key l r) (AVLNode invl invr RHeavy))   | LT | (Grew (Element l' invl'))
                                                                               = Same $ Element (Node key l' r) (AVLNode invl' invr Balanced)

  doInsert newKey (Element (Node key l r) (AVLNode invl invr b)) | GT with (assert_total $ doInsert newKey (Element r invr))
  -- Totality checker not clever enough to see that this is smaller
    doInsert newKey (Element (Node key l r) (AVLNode invl invr b))        | GT | (Same (Element r' invr'))
                                                                               = Same $ Element (Node key l r') (AVLNode invl invr' b)
    doInsert newKey (Element (Node key l r) (AVLNode invl invr LHeavy))   | GT | (Grew (Element r' invr'))
                                                                               = Same $ Element (Node key l r') (AVLNode invl invr' Balanced)
    doInsert newKey (Element (Node key l r) (AVLNode invl invr Balanced)) | GT | (Grew (Element r' invr'))
                                                                               = Grew $ Element (Node key l r') (AVLNode invl invr' RHeavy)
    doInsert newKey (Element (Node key l r) (AVLNode invl invr RHeavy))   | GT | (Grew (Element r' invr'))
                                                                               = rotLeft key (Element l invl) (Element r' invr')

||| Insert a key value pair into the tree, returning a the new tree
||| and possibly its new height.
insert : Ord k => k -> AVLTree n k -> (n : Nat ** AVLTree n k)
insert k t = runInsertRes (doInsert k t)

