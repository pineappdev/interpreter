module PureType where
import AbsGrammar
import Data.List(intersperse)
import Data.Char(toLower)

-- TODO: add NoInit, correct string printing,
-- TODO: separate to more modules
-- alter printing error places
-- remove all unneeded stuff
-- improve style (use liftM and mapM wherever possible, ...)
-- make some usage examples

data PureType = TInt | TStr | TBoolean | TArray PureType | TTuple [PureType] | TEmptyArray

isOrderable :: PureType -> Bool
isOrderable x = case x of
    TInt -> True
    TStr -> True
    TBoolean -> True
    _ -> False

-- use with caution, this relation is not transitive
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

compTypesWithPureTypes :: [Type a] -> [PureType] -> Bool
compTypesWithPureTypes [] [] = True
compTypesWithPureTypes (t:ts) (pt:pts) = if not (compTypeWithPureType t pt) then False else compTypesWithPureTypes ts pts
compTypesWithPureTypes _ _ = False

compTypeWithPureType :: Type a -> PureType -> Bool
compTypeWithPureType ptype type_ = case (ptype, type_) of
    (BaseT _ (IntT _), TInt) -> True
    (BaseT _ (BooleanT _), TBoolean) -> True
    (BaseT _ (StrT _), TStr) -> True
    (ArrayT _ type_, TArray ptype) -> compTypeWithPureType type_ ptype
    (ArrayT _ type_, TEmptyArray) -> True
    (TupleT _ types, TTuple ptypes) -> compTypesWithPureTypes types ptypes
    (_, _) -> False