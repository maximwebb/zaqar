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
    EqActions    : (a1 : Actions) -> (a2 : Actions) -> {eq : a1 = a2} -> Mergeable a1 a2
    MergeActions : (a1 : Actions) -> (a2 : Actions)
                -> IsOffer a1
                => IsOffer a2
                => {eq: (getSrc a1) = (getSrc a2)}
                -> {join : Joinable (getChoices a1) (getChoices a2)}
                -> Mergeable a1 a2


public export
sym : Mergeable a1 a2 -> Mergeable a2 a1
sym (EqActions a1 a2 {eq}) = EqActions a2 a1 {eq=(sym eq)}
sym (MergeActions a1 a2 {eq} {join}) = MergeActions a2 a1 {eq=(sym eq)} {join=(sym join)}


public export
data AllMergeable : List Actions -> Type where
    AllMergeEmpty  : AllMergeable []
    AllMergeCons   : (a : Actions) 
                  -> AllMergeable as
                  -> (All (\v => Mergeable a v) as)
                  -> AllMergeable (a :: as)


public export
merge : (a1 : Actions) -> (a2 : Actions) -> {auto prf : Mergeable a1 a2} -> Actions
merge a1 a2 {prf=prf} = case prf of
                EqActions a1 a2 => a1
                MergeActions a1 a2 => Offer (getSrc a1) (union (getChoices a1) (getChoices a2))


mergeId : (a : Actions) -> a = merge a a
mergeId a with (merge a a)
    _ | x = Refl


%hint
mergePreserves : {0 a1 : Actions} -> {0 a2 : Actions} -> {0 a3 : Actions}
              -> (m12 : Mergeable a1 a2)
              -> (m13 : Mergeable a1 a3)
              -> (m23 : Mergeable a2 a3)
              -> Mergeable (merge a1 a2) a3
mergePreserves _ _ = believe_me


public export
allTail : (All p (x :: xs)) -> All p xs
allTail (_ :: t) = t


public export
mergeAll : (as : List Actions) -> {auto prf : AllMergeable as} -> Actions
mergeAll [] = Close
mergeAll [a] = a
mergeAll (a1 :: a2 :: as) {prf} with (prf)
  _ | AllMergeCons _ prf1 all_prf1 with (prf1)
    _ | AllMergeCons _ prf3 all_prf2 with (indexAll Here all_prf1)
      _ | m12 with (merge a1 a2) proof m_lab
        _ | m with (allTail all_prf1)
          _ | all_prf3 with (zipPropertyWith (mergePreserves m12) all_prf3 all_prf2)
            _ | all_prf4 with (replace {p=(\r => All (\v => Mergeable r v) as)} (m_lab) all_prf4)
              _ | all_prf5 = mergeAll (m::as) {prf=(AllMergeCons m prf3 all_prf5)}

mutual
    public export
    data Global : Nat -> Type where
        Done      : Global n
        Message   : (src : Fin n) -> (dst : Fin n)
                 -> (gs : List (Sort, Global n))
                 -> NonEmpty gs
                 => {auto prf : All (\p => AllMergeable ((\choice => project (snd choice) p) <$> gs)) (getDistinct src dst)}
                 -> Global n

    public export
    project : {n : Nat} -> (g : Global n) -> (p : Fin n) -> Actions
    project Done _ = Close
    project {n=n} (Message src dst gs {prf=prf}) p with (p /= src) proof eq1
        _ | False = Select (finToNat dst) (map (\(s,g) => (s, project g p)) gs)
        _ | True with (p /= dst) proof eq2
            _ | False = Offer  (finToNat src) (map (\(s,g) => (s, project g p)) gs)
            _ | True = let ne_prf = andSo (eqToSo eq1, eqToSo eq2) in
                       let prf1 = getDistinctContains src dst p in
                       let merge_prf = indexAll prf1 prf in
                           mergeAll ((\choice => project (snd choice) p) <$> gs) {prf=merge_prf}


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
close : (1 chan : Channel Close) -> L IO ()
close (MkChannel Close) = pure ()


