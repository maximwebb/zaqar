module BinarySessionTypes

import Serialise

import Control.Linear.LIO
import Data.List.Quantifiers
import Data.List1
import Data.String



data Actions : Type where
    Send  : (a : Type) -> (a -> Actions) -> Actions
    Recv  : (a : Type) -> (a -> Actions) -> Actions
    Close : Actions


data Channel : Actions -> Type where
    CloseChannel  : Channel Close
    CreateChannel : (actions : Actions) -> Channel actions


PushMessage : Serialise ty => (1 _ : Channel (Send ty next)) -> (v : ty) -> Channel (next v)
PushMessage (CreateChannel (Send ty next)) v = CreateChannel (next v)

PopMessage : Serialise ty => (1 _ : Channel (Recv ty next)) -> (v : ty) -> Channel (next v)
PopMessage (CreateChannel (Recv ty next)) v = CreateChannel (next v)


namespace Proto
    public export
    data Protocol : Type -> Type where
        Request : (a : Type) -> Protocol a
        Respond : (a : Type) -> Protocol a
        (>>=)   : Protocol a -> (a -> Protocol b) -> Protocol b
        Done    : Protocol ()



ClientCont : Protocol a -> (a -> Actions) -> Actions
ClientCont (Request a) k = Send a k
ClientCont (Respond a) k = Recv a k
ClientCont (x >>= f)   k = ClientCont x ((\c => ClientCont c k) . f)
ClientCont Done        k = k ()


ServerCont : Protocol a -> (a -> Actions) -> Actions
ServerCont (Request a) k = Recv a k
ServerCont (Respond a) k = Send a k
ServerCont (x >>= f)   k = ServerCont x ((\c => ServerCont c k) . f)
ServerCont Done        k = k ()


AsClient, AsServer: Protocol a -> Actions
AsClient p = ClientCont p (\x => Close)
AsServer p = ServerCont p (\x => Close)


Client, Server : Protocol a -> Type
Client p = Channel ( AsClient p )
Server p = Channel ( AsServer p )


send : Serialise ty => (1 chan : Channel (Send ty next)) -> (val : ty) -> L IO {use=1} (Channel (next val))
send chan val = do _ <- putStrLn $ show val
                   pure1 (PushMessage chan val)



recv : Serialise ty => (1 chan : Channel (Recv ty next)) -> L IO {use=1} (Res ty (\val => Channel (next val)))
recv chan = do _ <- putStrLn "Receiving value"
               v <- getLine
               Just v' <- pure $ parse {a=ty} v | Nothing => recv chan
               x <- pure1 (PopMessage chan v')
               pure1 (v' # x)


close : (1 chan : Channel Close) -> L IO ()
close CloseChannel = pure ()
close (CreateChannel Close) = pure ()


fork : ((1 chan : Server p) -> L IO ()) -> L IO {use=1} (Client p)


data Command = Add | Reverse

Show Command where
    show c = case c of 
                Add => "Add"
                Reverse => "Reverse"

Serialise Command where
    parse s = case s of
                "Add"     => Just Add
                "Reverse" => Just Reverse
                _         => Nothing


Utils : Protocol ()
Utils = Proto.do cmd <- Request Command
                 case cmd of
                    Add     => Proto.do _ <- Request (Int, Int)
                                        _ <- Respond Int
                                        Done
                    Reverse => Proto.do _ <- Request String
                                        _ <- Respond String
                                        Done

utilServer : (1 chan : Server Utils) -> L IO ()
utilServer chan = do cmd # chan <- recv chan
                     case cmd of
                          Add     => do (x, y) # chan <- recv chan
                                        chan <- send chan (x + y)
                                        close chan
                          Reverse => do str # chan <- recv chan
                                        chan <- send chan (reverse str)
                                        close chan



init : L IO ()
init = utilServer (CreateChannel $ AsServer Utils)