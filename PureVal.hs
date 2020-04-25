module PureVal where
import AbsGrammar
import Data.List(intersperse)
import Data.Char(toLower)

data PureType = TInt | TStr | TBoolean | TArray PureType | TTuple [PureType] | TEmptyArray

isOrderable :: PureType -> Bool
isOrderable x = case x of
    TInt -> True
    TStr -> True
    TBoolean -> True
    _ -> False

instance Eq PureType where
    ptype1 == ptype2 = case (ptype1, ptype2) of
        (TInt, TInt) -> True
        (TStr, TStr) -> True
        (TBoolean, TBoolean) -> True
        (TArray pt1, TArray pt2) -> pt1 == pt2
        (TArray pt1, TEmptyArray) -> True
        (TEmptyArray, TArray pt2) -> True
        (TEmptyArray, TEmptyArray) -> True
        (TTuple pts1, TTuple pts2) -> pts1 == pts2
        (_, _) -> False

instance Show PureType where
    show ptype = case ptype of
        TInt -> "int"
        TStr -> "string"
        TBoolean -> "bool"
        TArray ptype -> "[" ++ show ptype ++ "]"
        TTuple ptypes -> "Tuple<" ++ concat (intersperse ", " $ map show ptypes) ++ ">"
        TEmptyArray -> "[]"

type2PureType :: Type a -> PureType
type2PureType type_ = case type_ of
    BaseT _ (IntT _) -> TInt
    BaseT _ (BooleanT _) -> TBoolean
    BaseT _ (StrT _) -> TStr
    ArrayT _ type_ -> TArray (type2PureType type_)
    TupleT _ types -> TTuple (map type2PureType types)

compTypeWithPureTypes :: [Type a] -> [PureType] -> Bool
compTypeWithPureTypes [] [] = True
compTypeWithPureTypes (t:ts) (pt:pts) = if not (compTypeWithPureType t pt) then False else compTypeWithPureTypes ts pts
compTypeWithPureTypes _ _ = False

compTypeWithPureType :: Type a -> PureType -> Bool
compTypeWithPureType ptype type_ = case (ptype, type_) of
    (BaseT _ (IntT _), TInt) -> True
    (BaseT _ (BooleanT _), TBoolean) -> True
    (BaseT _ (StrT _), TStr) -> True
    (ArrayT _ type_, TArray ptype) -> compTypeWithPureType type_ ptype
    (ArrayT _ type_, TEmptyArray) -> True
    (TupleT _ types, TTuple ptypes) -> compTypeWithPureTypes types ptypes
    (_, _) -> False

data PureVal = Int Integer | Str String | Boolean Bool | Array [PureVal] | Tuple [PureVal]
    deriving(Eq, Ord)

showPureValsType :: PureVal -> String
showPureValsType (Int _) = "int"
showPureValsType (Str _) = "string"
showPureValsType (Boolean _) = "bool"
showPureValsType (Array vals) = if null vals then "[]" else showPureValsType (head vals) ++ " []"
showPureValsType (Tuple vals) = "Tuple<" ++ concat (intersperse ", " (map showPureValsType vals)) ++ ">"

showsPrecPureVals :: Int -> [PureVal] -> ShowS
showsPrecPureVals prec [] = showString ""
showsPrecPureVals prec (val:vals) = case vals of
    [] -> showsPrec prec val
    other -> showsPrec prec val . showString ", " . showsPrecPureVals prec other

instance Show (PureVal) where
    showsPrec prec (Int i) = showString $ show i
    showsPrec prec (Str string) = if prec >= 200000
        then showString string
        else \s -> string ++ s
    showsPrec prec (Boolean b) = showString $ map toLower $ show b
    showsPrec prec (Array vals) = showString "[" . showsPrecPureVals 200000 vals . showString "]"
    showsPrec prec (Tuple vals) = showString "(" . showsPrecPureVals 200000 vals . showString ")"

ident2String :: Ident -> String
ident2String (Ident str) = str