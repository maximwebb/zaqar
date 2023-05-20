module Sorts

public export
data IsSort : Type -> Type where
    MkNat : IsSort Nat
    MkStr : IsSort String
    MkBool : IsSort Bool


public export
data Sort : Type where
    Ty : (a : Type) -> {auto prf : IsSort a} -> Sort


public export
(==) : (a, b : Type) -> {auto prf1 : IsSort a} -> {auto prf2 : IsSort b} -> Bool
(==) .(_) .(_) {prf1=MkNat} {prf2=MkNat} = True
(==) .(_) .(_) {prf1=MkStr} {prf2=MkStr} = True
(==) .(_) .(_) {prf1=MkBool} {prf2=MkBool} = True
(==) _ _ = False


public export
Eq Sort where
    (==) (Ty a) (Ty b) = a == b