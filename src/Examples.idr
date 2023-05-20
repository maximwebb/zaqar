import MultiPartySessionTypes


-- Fails without merging
MergeExample : Global 3
MergeExample = Message 0 1 [
                      (Ty Nat,  Message 1 2 [
                        (Ty Bool, Done), 
                        (Ty Nat, Done)
                      ]),
                      (Ty Bool, Message 1 2 [
                        (Ty Nat, Done), 
                        (Ty Bool, Done)
                      ])
                    ]


a1 : Actions
a1 = Offer 5 [(Ty Nat, Close), (Ty Bool, Close)]

a2 : Actions
a2 = Offer 5 [(Ty Nat, Close)]

as : List Actions
as = [a1, a2]