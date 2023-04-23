module Utils

import Data.Fin

public export
data AllEqual : List a -> Type where
    Empty     : AllEqual []
    Singleton : (x : a) -> AllEqual [x]
    Cons      : (y : a) -> AllEqual (x :: xs) -> x = y -> AllEqual (y :: x :: xs)


public export
data PairwiseEqual : List (a, a) -> Type where
    PairEqEmpty : PairwiseEqual []
    PairEqCons  : (x1 : a) -> (x2 : a) -> x1 = x2 
                -> PairwiseEqual xs 
                -> PairwiseEqual ((x1, x2) :: xs)


public export
getDistinct : {k : Nat} -> (x : Fin k) -> (y : Fin k) -> List (Fin k)
getDistinct x y = filter (\z => z /= x && z /= y) (allFins k) where
                                                allFins : (k : Nat) -> List (Fin k)
                                                allFins 0 = []
                                                allFins (S k) = FZ :: (FS <$> allFins k)


public export
findByIndex : Eq ix => (i : ix) -> List (ix, a) -> List a
findByIndex _ [] = []
findByIndex i ((j, x) :: xs) = if i == j then x :: (findByIndex i xs)
                              else findByIndex i xs


public export
innerJoin : Eq ix => List (ix, a) -> List (ix, a) -> List (a, a)
innerJoin [] _ = []
innerJoin ((i, x) :: xs) ys = ((\t => (x, t)) <$> (findByIndex i ys)) ++ (innerJoin xs ys)

public export
union : Eq ix => List (ix, a) -> List (ix, a) -> List (ix, a)
union [] ys = ys
union ((i, x) :: xs) ys = case findByIndex i ys of
                            []        => (i, x) :: (union xs ys)
                            (_ :: _)  => union xs ys



public export
data Joinable : Eq ix => List (ix, a) -> List (ix, a) -> Type where
    IsJoinable : Eq ix 
              => (l1 : List (ix, a)) 
              -> (l2 : List (ix, a)) 
              -> {prf : PairwiseEqual (innerJoin l1 l2)}
              -> Joinable l1 l2



l1 : List (Nat, String)
l1 = [(1, "gold"), (2, "black"), (3, "red")]

l2 : List (Nat, String)
l2 = [(1, "gold"), (3, "red"), (1, "beard")]

l3 : List (String, String)
l3 = innerJoin l2 l1