module MultiPartySessionTypes

import Serialise

import Control.Linear.LIO
import Data.List.Quantifiers
import Data.List1
import Data.String

data Actions : Type where
    Send  : (dst : Nat) -> (a : Type) -> (a -> Actions) -> Actions
    Recv  : (src : Nat) -> (a : Type) -> (a -> Actions) -> Actions
    Close : Actions


data Channel : Actions -> Type where
    CloseChannel  : Channel Close
    CreateChannel : (actions : Actions) -> Channel actions


PushMessage : Serialise ty => (1 _ : Channel (Send dst ty next)) -> (v : ty) -> Channel (next v)
PushMessage (CreateChannel (Send dst ty next)) v = CreateChannel (next v)

PopMessage : Serialise ty => (1 _ : Channel (Recv src ty next)) -> (v : ty) -> Channel (next v)
PopMessage (CreateChannel (Recv src ty next)) v = CreateChannel (next v)


namespace Global
    public export
    data Global : Type -> Type where
        Message : (src : Nat) -> (dst : Nat) -> (a : Type) -> Global b -> Global b
        Done    : Global ()


Project : Global a -> (p : Nat) -> Actions
Project (Message src dst a next) p = if p == src then Send dst a (\c => Project next p)
                                     else if p == dst then Recv src a (\c => Project next p)
                                     else Project next p
Project Done _ = Close


ProjectToChannel : Global a -> (p : Nat) -> Type
ProjectToChannel g p = Channel (Project g p)


send : Serialise ty => (1 chan : Channel (Send dst ty next)) -> (val : ty) -> L IO {use=1} (Channel (next val))
send chan val = do _ <- putStrLn "Sending value"
                   _ <- putStrLn $ show val
                   pure1 (PushMessage chan val)


recv : Serialise ty => (1 chan : Channel (Recv src ty next)) -> L IO {use=1} (Res ty (\val => Channel (next val)))
recv chan = do _ <- putStrLn "Receiving value"
               v <- getLine
               Just v' <- pure $ parse {a=ty} v | Nothing => recv chan
               x <- pure1 (PopMessage chan v')
               pure1 (v' # x)


close : (1 chan : Channel Close) -> L IO ()
close CloseChannel = pure ()
close (CreateChannel Close) = pure ()


Example : Global ()
Example = Message 1 2 Int $
          Message 2 3 Int $
          Message 3 1 Int $
          Done


example1 : (1 chan : ProjectToChannel Example 1) -> L IO ()
example1 chan = do chan <- send chan 5
                   res # chan <- recv chan
                   close chan

init : L IO ()
init = example1 (CreateChannel $ Project Example 1)