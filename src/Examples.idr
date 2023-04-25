import MultiPartySessionTypes


Example : Global 3
Example = Message 0 1 [(NatTy,  Message 1 2 [
                                              (NatTy, Done), 
                                              (NatTy, Done)
                                              ]),
                       (BoolTy, Message 1 2 [
                                              (NatTy, Done), 
                                              (NatTy, Done)
                                             ])
                    ]

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
a2 = Offer 5 [(NatTy, Close), (StrTy, Offer 5 [(NatTy, Close)])]

a12 : Actions
a12 = merge a1 a2