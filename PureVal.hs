module PureVal where

import AbsGrammar
import Data.List(intersperse)
import Data.Char(toLower)

data PureVal = Int Integer | Str String | Boolean Bool | Array [PureVal] | Tuple [PureVal]
    deriving(Eq, Ord)

showPureValsType :: PureVal -> String
showPureValsType (Int _) = "int"
showPureValsType (Str _) = "string"
showPureValsType (Boolean _) = "bool"
showPureValsType (Array vals) = if null vals then "[]" else showPureValsType (head vals) ++ " []"
showPureValsType (Tuple vals) = "Tuple<" ++ concat (intersperse ", " (map showPureValsType vals)) ++ ">"

showsPrecPureVals :: String -> Int -> [PureVal] -> ShowS
showsPrecPureVals terminal prec [] = showString ""
showsPrecPureVals terminal prec (val:vals) = case vals of
    [] -> showsPrec prec val . showString terminal
    other -> showsPrec prec val . showString ", " . showsPrecPureVals terminal prec other

instance Show PureVal where
    showsPrec prec (Int i) = showString $ show i
    showsPrec prec (Str string) = if prec >= 200000
        then showString string
        else \s -> string ++ s
    showsPrec prec (Boolean b) = showString $ map toLower $ show b
    showsPrec prec (Array vals) = showString "[" . showsPrecPureVals "" 200000 vals . showString "]"
    showsPrec prec (Tuple vals) = showString "((" . showsPrecPureVals "," 200000 vals . showString "))"