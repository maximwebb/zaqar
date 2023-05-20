module Utils

import Data.Fin
import Data.List.Elem
import Data.List
import Data.List.Quantifiers
import Decidable.Equality
import Sorts

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
allFins (S k) = FZ :: (FS <$> Utils.allFins k)

public export
mapCong : (p : a -> b) -> (prf : Elem x xs) -> (Elem (p x) (p <$> xs))
mapCong p Here = Here
mapCong p (There prf1) = There (mapCong p prf1)


public export
mapPreservesNonEmpty : (xs : List a) -> (f : a -> b) -> (prf : NonEmpty xs) -> (NonEmpty (f <$> xs))
mapPreservesNonEmpty (h :: t) f prf = IsNonEmpty


public export
pInAllFins : {k : Nat} -> (p : Fin k) -> (Elem p (Utils.allFins k))
pInAllFins FZ     = Here
pInAllFins (FS n) = There (mapCong FS $ pInAllFins n)


public export
getUninvolved : {k : Nat} -> (x : Fin k) -> (y : Fin k) -> List (Fin k)
getUninvolved x y = filter (\z => z /= x && z /= y) (Utils.allFins k)

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
getUninvolvedElem : {k : Nat} 
                    -> (src : Fin k)
                    -> (dst : Fin k)
                    -> (p   : Fin k)
                    -> {auto prf : So (not (p == src) && Delay (p /= dst))}
                    -> Elem p (getUninvolved src dst)
getUninvolvedElem src dst p {prf=prf} = 
    filterPreservesMembership p (Utils.allFins k) (\z => not (z == src) && Delay (z /= dst)) (pInAllFins p)


public export
findByIndex : (i : Sort) -> List (Sort, a) -> List a
findByIndex _ [] = []
findByIndex i ((j, x) :: xs) = if i == j then x :: (findByIndex i xs)
                              else findByIndex i xs


public export
innerJoin : List (Sort, a) -> List (Sort, a) -> List (a, a)
innerJoin [] _ = []
innerJoin ((i, x) :: xs) ys = ((\t => (x, t)) <$> (findByIndex i ys)) ++ (innerJoin xs ys)

innerJoinCommutes : {l1 : List (Sort, a)} 
                 -> {l2 : List (Sort, a)}
                 -> (innerJoin l1 l2) = (innerJoin l2 l1)



public export
union : List (Sort, a) -> List (Sort, a) -> List (Sort, a)
union [] ys = ys
union ((i, x) :: xs) ys = case findByIndex i ys of
                            []        => (i, x) :: (union xs ys)
                            (_ :: _)  => union xs ys



public export
data Joinable : List (Sort, a) -> List (Sort, a) -> Type where
    IsJoinable : (l1 : List (Sort, a)) 
              -> (l2 : List (Sort, a)) 
              -> {auto prf : PairwiseEqual (innerJoin l1 l2)}
              -> Joinable l1 l2