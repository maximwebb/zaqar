module Mergeable

import Serialise

import Control.Linear.LIO
import Data.List.Quantifiers
import Data.List.Elem
import Data.List1
import Data.String
import Data.Vect

zero : Fin 3
zero = FZ

one : Fin 3
one = FS FZ

two : Fin 3
two = FS (FS FZ)

mutual
    data Actions : Type where
        Select  : (dst : Nat) -> (List (Nat, Type, Actions)) -> Actions
        Offer   : (src : Nat) -> (List (Nat, Type, Actions)) -> Actions
        Close   : Actions
    

data Channel : Actions -> Type where
    CloseChannel  : Channel Close
    CreateChannel : (actions : Actions) -> Channel actions


data AllEqual : List a -> Type where
    Empty     : AllEqual []
    Singleton : (x : a) -> AllEqual [x]
    Cons      : (y : a) -> AllEqual (x :: xs) -> x = y -> AllEqual (y :: x :: xs)

third : (a, b, c) -> c
third (x, y, z) = z


getValid : {k : Nat} -> (x : Fin k) -> (y : Fin k) -> List (Fin k)
getValid x y = filter (\z => z /= x && z /= y) (allFins k) where
                                                allFins : (k : Nat) -> List (Fin k)
                                                allFins 0 = []
                                                allFins (S k) = FZ :: (FS <$> allFins k)


mutual
    data Global : Nat -> Type where
        Done      : Global n
        Message   : (src : Fin n) -> (dst : Fin n)
                  -> (gs : List (Nat, Type, Global n))
                  -> (0 prf3 : All (\p => AllEqual ((\tup => project (third tup) p) <$> gs)) (getValid src dst))
                  => Global n


    project : (g : Global n) -> (p : Fin n) -> Actions
    project Done _ = Close
    project (Message src dst gs) p = if      p == src then Select (finToNat dst) (map (\(l,a,g) => (l,a, project g p)) gs)
                                     else if p == dst then Offer  (finToNat src) (map (\(l,a,g) => (l,a, project g p)) gs)
                                     else case gs of
                                            ((_, _, g) :: _) => project g p
                                            [] => Close



getChannel : Global n -> (p : Fin n) -> Type
getChannel g p = Channel (project g p)

