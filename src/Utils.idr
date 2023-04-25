module Utils

import Data.Fin
import Data.List.Elem
import Data.List
import Decidable.Equality

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
allFins : (k : Nat) -> List (Fin k)
allFins 0 = []
allFins (S k) = FZ :: (FS <$> allFins k)

public export
mapCong : (p : a -> b) -> (prf : Elem x xs) -> (Elem (p x) (p <$> xs))
mapCong p Here = Here
mapCong p (There prf1) = There (mapCong p prf1)

public export
pInAllFins : {k : Nat} -> (p : Fin k) -> (Elem p (allFins k))
pInAllFins FZ     = Here
pInAllFins (FS n) = There (mapCong FS $ pInAllFins n)


public export
equalToSo : {a : Fin n} -> {b : Fin n} -> (prf : a = b) -> (So (a == b))
equalToSo {a=FZ} {b=FZ} prf = Oh
equalToSo {a=(FS x)} {b=(FS y)} prf = equalToSo (injective prf)

public export
getDistinct : {k : Nat} -> (x : Fin k) -> (y : Fin k) -> List (Fin k)
getDistinct x y = filter (\z => z /= x && z /= y) (allFins k)

public export
filterPreservesMembership : (x : a)
                -> (xs : List a)
                -> (p : a -> Bool)
                -> (prf1 : Elem x xs)
                -> {auto prf2 : So (p x)}
                -> (Elem x (filter p xs))
filterPreservesMembership x (_ :: xs) p Here with (p x) proof eq
    _ | True = Here
filterPreservesMembership x (y :: ys) p (There prf) with (p y) proof eq
    _ | True = There (filterPreservesMembership x ys p prf)
    _ | False = filterPreservesMembership x ys p prf


public export
getDistinctContains : {k : Nat} 
                    -> (src : Fin k)
                    -> (dst : Fin k)
                    -> (p   : Fin k)
                    -> {auto prf : So (not (p == src) && Delay (p /= dst))}
                    -> Elem p (getDistinct src dst)
getDistinctContains src dst p {prf=prf} = 
    filterPreservesMembership p (allFins k) (\z => not (z == src) && Delay (z /= dst)) (pInAllFins p)


public export
findByIndex : Eq ix => (i : ix) -> List (ix, a) -> List a
findByIndex _ [] = []
findByIndex i ((j, x) :: xs) = if i == j then x :: (findByIndex i xs)
                              else findByIndex i xs


public export
innerJoin : Eq ix => List (ix, a) -> List (ix, a) -> List (a, a)
innerJoin [] _ = []
innerJoin ((i, x) :: xs) ys = ((\t => (x, t)) <$> (findByIndex i ys)) ++ (innerJoin xs ys)

innerJoinCommutes : Eq ix => {l1 : List (ix, a)} 
                          -> {l2 : List (ix, a)}
                          -> (innerJoin l1 l2) = (innerJoin l2 l1)



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


public export
sym : Eq ix => {l1 : List (ix, a)} 
            -> {l2 : List (ix, a)} 
            -> (Joinable l1 l2) 
            -> (Joinable l2 l1)
sym (IsJoinable l1 l2 {prf}) with (innerJoin l1 l2) proof prf1
    _ | ls with (sym $ innerJoinCommutes {l1} {l2})
        _ | prf2 with (sym $ trans prf2 prf1)
            _ | prf3 with (replace {p=PairwiseEqual} prf3 prf)
                _ | prf4 = IsJoinable l2 l1 {prf=prf4}



l1 : List (Nat, String)
l1 = [(1, "gold"), (2, "black"), (3, "red")]

l2 : List (Nat, String)
l2 = [(1, "gold"), (3, "red"), (1, "beard")]

l3 : List (String, String)
l3 = innerJoin l2 l1