import MultiPartySessionTypes


Example : Global 3
Example = Message 0 1 [(Quote,
            Message 0 2 [(Quote,
              Message 1 2 [(Contrib,
                Message 2 0 [(Acc, Done), (Rej, Done)]
              )]
            )]
          )]

-- Fails without merging
MergeExample : Global 3
MergeExample = Message 0 1 [(NatTy,  Message 1 2 [
                                              (BoolTy, Done), 
                                              (NatTy, Done)
                                              ]),
                       (BoolTy, Message 1 2 [
                                              (NatTy, Done), 
                                              (NatTy, Done)
                                             ])
                    ]

a1 : Actions
a1 = Offer 5 [(NatTy, Close)]

a2 : Actions
a2 = Offer 5 [(NatTy, Close)]

as : List Actions
as = [a1, a2]