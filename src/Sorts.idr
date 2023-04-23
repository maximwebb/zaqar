module Sorts

public export
data Sort = NatTy | IntTy | StrTy | BoolTy

public export
Eq Sort where
    NatTy  == NatTy  = True
    IntTy  == IntTy  = True
    StrTy  == StrTy  = True
    BoolTy == BoolTy = True
    _      == _      = False

public export
SortToType : Sort -> Type
SortToType NatTy  = Nat
SortToType IntTy  = Int
SortToType StrTy  = String
SortToType BoolTy = Bool
