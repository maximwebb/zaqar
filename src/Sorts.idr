module Sorts

public export
data Sort = NatTy | IntTy | StrTy | BoolTy | Quote | Contrib | Acc | Rej

public export
Eq Sort where
    NatTy  == NatTy  = True
    IntTy  == IntTy  = True
    StrTy  == StrTy  = True
    BoolTy == BoolTy = True
    Quote == Quote = True
    Contrib == Contrib = True
    Acc == Acc = True
    Rej == Rej = True
    _      == _      = False

public export
SortToType : Sort -> Type
SortToType NatTy  = Nat
SortToType IntTy  = Int
SortToType StrTy  = String
SortToType BoolTy = Bool
SortToType Quote = Nat
SortToType Contrib = Nat
SortToType _ = Unit
