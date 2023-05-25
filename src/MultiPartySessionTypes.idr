module MultiPartySessionTypes

import public Serialise
import public Sorts
import public Utils

import public Control.Linear.LIO
import public Data.Fin
import public Data.List.Elem
import public Data.List
import public Data.List.Quantifiers
import public Decidable.Equality

data Peer : Nat -> Type where
    MkPeer : Fin k -> Peer k


public export
data Actions : Type where
    Select   : (dst : Nat) -> (List (Sort, Actions)) -> Actions
    Offer    : (src : Nat) -> (List (Sort, Actions)) -> Actions
    Close    : Actions
    

-- Predicate for testing if an Action is an Offer
public export
data IsOffer : Actions -> Type where
    MkOffer : IsOffer (Offer src choices)

public export
getSrc : (a : Actions) -> IsOffer a => Nat
getSrc (Offer src _) = src


public export
getChoices : (a : Actions) -> IsOffer a => List (Sort, Actions)
getChoices (Offer _ choices) = choices


-- Predicate for whether two actions are Mergeable - ie. if they are either equal,
-- or if they are both offering choices to the same participant, where any overlapping
-- choices agree on the type and continuation.
public export
data Mergeable : (a1 : Actions) -> (a2 : Actions) -> Type where
    EqActions    : (a1 : Actions) -> (a2 : Actions) -> {eq : a1 = a2} -> Mergeable a1 a2
    MergeActions : (a1 : Actions) -> (a2 : Actions)
                -> IsOffer a1
                => IsOffer a2
                => {auto eq: (getSrc a1) = (getSrc a2)}
                -> {auto join : Joinable (getChoices a1) (getChoices a2)}
                -> Mergeable a1 a2


public export
merge : (a1 : Actions) -> (a2 : Actions) -> {auto prf : Mergeable a1 a2} -> Actions
merge a1 a2 {prf=prf} = case prf of
                EqActions _ _ => a1
                MergeActions _ _ => Offer (getSrc a1) (union (getChoices a1) (getChoices a2))


mutual
    public export
    data AllMergeable : List Actions -> Type where
        AllMergeSingle : (a : Actions) -> AllMergeable [a]
        AllMergeCons   : (a : Actions)
                      -> NonEmpty as
                      => {mrgPrf : AllMergeable as}
                      -> {mrgRedPrf : Mergeable a (mergeReduce as)}
                      -> AllMergeable (a :: as)


    public export
    mergeReduce : (as : List Actions) -> {auto prf : AllMergeable as} -> NonEmpty as => Actions
    mergeReduce [a] = a
    mergeReduce (a :: a' :: as) {prf} = case prf of
        AllMergeCons _ => merge a (mergeReduce (a' :: as))


mutual
    public export
    data Global : Nat -> Type where
        Done      : Global n
        Message   : (src : Fin n) -> (dst : Fin n)
                 -> (gs : List (Sort, Global n))
                 -> {auto nonEmp : NonEmpty gs}
                 -> {auto prf : All (\p => AllMergeable ((\choice => project (snd choice) p) <$> gs)) (getUninvolved src dst)}
                 -> Global n

    public export
    project : {n : Nat} -> (g : Global n) -> (p : Fin n) -> Actions
    project Done _ = Close
    project {n=n} (Message src dst gs {prf=prf} {nonEmp = nonEmp}) p with (p /= src) proof neq1
        _ | False = Select (finToNat dst) (map (\(s,g) => (s, project g p)) gs)
        _ | True with (p /= dst) proof neq2
            _ | False = Offer  (finToNat src) (map (\(s,g) => (s, project g p)) gs)
            _ | True = let neqPrf = andSo (eqToSo neq1, eqToSo neq2) in
                       let elem = getUninvolvedElem src dst p in
                       let mergePrf = indexAll elem prf in
                       let nonEmpPrf = mapPreservesNonEmpty gs (\choice => project (snd choice) p) nonEmp in
                           mergeReduce ((\choice => project (snd choice) p) <$> gs)


public export
data Channel : Actions -> Type where
    MkChannel : (actions : Actions) -> Channel actions


public export
getChannel : {n : Nat} -> Global n -> (p : Fin n) -> Type
getChannel g p = Channel (project g p)


public export
pushMessage : (1 _ : Channel (Select dst choices)) 
            -> (v : Sort)
            -> {next : Actions}
            -> {prf : Elem (v, next) choices}
            -> Channel next


public export
popMessage : (1 _ : Channel (Offer src choices))
           -> {next : Actions}
           -> Channel next


public export
send : (1 chan : Channel (Select dst choices)) 
     -> (val : t)
     -> IsSort t
     => ElemSort (Ty t) choices
     => L IO {use=1} (Channel (findBySort (Ty t) choices))


public export
close : (1 chan : Channel Close) -> L IO ()
close (MkChannel Close) = pure ()