module MultiPartySessionTypes

import public Serialise
import public Sorts
import public Utils

import public Control.Linear.LIO
import public Data.Fin
import public Data.List.Elem
import public Data.List.Quantifiers


public export
data Actions : Type where
    Select  : (dst : Nat) -> (List (Sort, Actions)) -> Actions
    Offer   : (src : Nat) -> (List (Sort, Actions)) -> Actions
    Close   : Actions
    

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
    EqActions    : (a1 : Actions) -> (a2 : Actions) -> a1 = a2 => Mergeable a1 a2
    MergeActions : (a1 : Actions) -> (a2 : Actions)
                -> IsOffer a1
                => IsOffer a2
                => (getSrc a1) = (getSrc a2)
                => Joinable (getChoices a1) (getChoices a2)
                => Mergeable a1 a2

public export
merge : (a1 : Actions) -> (a2 : Actions) -> {auto prf : Mergeable a1 a2} -> Actions
merge a1 a2 {prf=prf} = case prf of
                EqActions a1 a2 => a1
                MergeActions a1 a2 => Offer (getSrc a1) (union (getChoices a1) (getChoices a2))


mutual
    public export
    data Global : Nat -> Type where
        Done      : Global n
        Message   : (src : Fin n) -> (dst : Fin n)
                 -> (gs : List (Sort, Global n))
                 -> All (\p => AllEqual ((\choice => project (snd choice) p) <$> gs)) (getDistinct src dst)
                 => Global n

    public export
    project : (g : Global n) -> (p : Fin n) -> Actions
    project Done _ = Close
    project (Message src dst gs) p = if      p == src then Select (finToNat dst) (map (\(s,g) => (s, project g p)) gs)
                                     else if p == dst then Offer  (finToNat src) (map (\(s,g) => (s, project g p)) gs)
                                     else case gs of
                                            -- ((_, g') :: gs') => foldr (merge) (project g' p) ((\g => project g p) <$> gs')
                                            ((_, g) :: _) => project g p
                                            [] => Close

public export
data Channel : Actions -> Type where
    MkChannel : (actions : Actions) -> Channel actions


public export
getChannel : Global n -> (p : Fin n) -> Type
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
close : (1 chan : Channel Close) -> L IO ()
close (MkChannel Close) = pure ()


