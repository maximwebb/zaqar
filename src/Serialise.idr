module Serialise

import Data.List1
import Data.String

public export
interface Show a => Serialise a where
    parse : String -> Maybe a

public export
Serialise Nat where
    parse x = let y = stringToNatOrZ x in
                if y == 0 && x /= "0" then Nothing
                else Just y

public export
Serialise Int where
    parse = parseInteger


public export
Serialise String where
    parse = Just

public export
(Serialise a, Serialise b) => Serialise (a, b) where
    parse s = case (forget $ split (\c => c == ',') s) of
                [x, y] => do Just (!(parse {a=a} x), !(parse {a=b} y))
                _      => Nothing



public export
Serialise a => Serialise (List a) where
    parse x = let xs = (forget $ split isSpace x) in
               sequence $ map (parse {a}) xs
                


-- Usage

foo : Serialise a => a -> IO (Maybe a)
foo x = do
        putStrLn $ show x
        Just x <- map Just getLine | Nothing => pure Nothing
        pure $ parse x
           
l : List Nat
l = [1, 4, 6, 9]



bar : IO ()
bar = do Just x <- foo l | Nothing => putStrLn "nothing"
         putStrLn $ show x
