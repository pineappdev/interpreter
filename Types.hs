module Types where
import AbsGrammar
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Maybe(fromJust)
import Data.List(intersperse)
import Data.Char(toLower)

type ErrorType a = (String, Val a) -- Error, value to return (if return was called, then that string == "RETURN")

keywords = ["print", "get", "set"]

-- TODO: that PlaceHolder is really, really unelegant...
string2error :: String -> ErrorType a
string2error msg = (msg, NULL)

type Loc = Int
type Env loc_type = Map.Map Ident (Loc, loc_type) -- loc_type stores the location of ident's definition
type Store loc_type = (Map.Map Loc (Val loc_type), Loc) -- (Map loc -> value, first free loc)

type ERSIO res_type loc_type = ExceptT (ErrorType loc_type) (ReaderT (Env loc_type) (StateT (Store loc_type) IO)) res_type

data Val a = Int a Integer | Str a String | Boolean a Bool | ArrayInt a [Int] | ArrayBoolean a [Bool]
         | ArrayStr a [String] | EmptyArray a | Tuple a [Val a] | Fun (Block a) (Type a) (Env a) [Arg a] | NULL

changeAVal :: a -> Val a -> Val a
changeAVal a' val = case val of
    Int a i -> Int a' i
    Str a str -> Str a' str
    Boolean a b -> Boolean a' b
    ArrayInt a arr -> ArrayInt a' arr
    ArrayBoolean a arr -> ArrayBoolean a' arr
    ArrayStr a arr -> ArrayStr a' arr
    EmptyArray a -> EmptyArray a'
    Tuple a vals -> Tuple a' vals

showsPrecVals :: Int -> [Val a] -> ShowS
showsPrecVals prec [] = showString ""
showsPrecVals prec (val:vals) = case vals of
    [] -> showsPrec prec val
    other -> showsPrec prec val . showString ", " . showsPrecVals prec other

instance Show (Val a) where
    showsPrec prec (Int _ i) = showString $ show i
    showsPrec prec (Str _ string) = if prec >= 200000
        then showString string
        else \s -> string ++ s
    showsPrec prec (Boolean _ b) = showString $ map toLower $ show b
    showsPrec prec (ArrayInt _ arr) = showString $ show arr
    showsPrec prec (ArrayBoolean _ arr) = showString $ show arr
    showsPrec prec (ArrayStr _ arr) = showString $ show arr
    showsPrec prec (EmptyArray _) = showString $ show ([] :: [Int])
    showsPrec prec (Tuple _ vals) = showString "(" . showsPrecVals 200000 vals . showString ")"

getLoc :: Show a => a -> Ident -> ERSIO (Loc, a) a
getLoc a x = do
    env <- ask
    case Map.lookup x env of
        Nothing -> throwError $ string2error  $ show a ++ ": error: " ++ show x ++ " was not defined"
        Just x -> return x

getVal :: Loc -> ERSIO (Val a) a
getVal loc = do
    (store, loc') <- get
    return $ fromJust $ Map.lookup loc store


compTypeLists :: [Val a] -> [Val a] -> Bool
compTypeLists [] [] = True
compTypeLists (t1:t1s) (t2:t2s) = if compValTypes t1 t2 then compTypeLists t1s t2s else False
compTypeLists _ _ = False

compValTypes :: Val a -> Val a -> Bool
compValTypes t1 t2 =
    case (t1, t2) of
        (Int _ _, Int _ _) -> True
        (Str _ _, Str _ _) -> True
        (Boolean _ _, Boolean _ _) -> True
        (ArrayInt _ _, ArrayInt _ _) -> True
        (ArrayBoolean _ _, ArrayBoolean _ _) -> True
        (ArrayStr _ _, ArrayStr _ _) -> True
        (EmptyArray _, ArrayInt _ _) -> True
        (EmptyArray _, ArrayBoolean _ _) -> True
        (EmptyArray _, ArrayStr _ _) -> True
        (ArrayInt _ _, EmptyArray _) -> True
        (ArrayBoolean _ _, EmptyArray _) -> True
        (ArrayStr _ _, EmptyArray _) -> True
        (Tuple _ x1, Tuple _ x2) -> compTypeLists x1 x2
        (_, _) -> False 

compTypesWithVals :: [Type a] -> [Val a] -> Bool
compTypesWithVals [] [] = True
compTypesWithVals (type_:types) (val:vals) = if compTypeWithVal type_ val then compTypesWithVals types vals else False
compTypesWithVals _ _ = False

compTypeWithVal :: Type a -> Val a -> Bool
compTypeWithVal type_ val = case (type_, val) of 
    (BaseT _ (IntT _), Int _ _) -> True
    (BaseT _ (BooleanT _), Boolean _ _) -> True
    (BaseT _ (StrT _), Str _ _) -> True
    (ArrayT _ (IntT _), ArrayInt _ _) -> True
    (ArrayT _ (BooleanT _), ArrayBoolean _ _) -> True
    (ArrayT _ (StrT _), ArrayStr _ _) -> True
    (ArrayT _ (IntT _), EmptyArray _) -> True
    (ArrayT _ (BooleanT _), EmptyArray _) -> True
    (ArrayT _ (StrT _), EmptyArray _) -> True
    (TupleT _ types, Tuple _ vals) -> compTypesWithVals types vals
    _ -> False


-- allocates a new loc with input value and returns this new loc
alloc :: Val a -> ERSIO Loc a
alloc val = do
    loc <- getNewLoc
    modify (\(store, _) -> (Map.insert loc val store, loc + 1))
    return loc

getNewLoc :: ERSIO Loc a
getNewLoc = do
    (store, loc) <- get
    return loc

getAFromType :: Type a -> a
getAFromType type_ = case type_ of
    BaseT a _ -> a
    ArrayT a _ -> a
    TupleT a _ -> a

getAFromVal :: Val a -> a
getAFromVal val = case val of
    Int a _ -> a
    Str a _ -> a
    Boolean a _ -> a
    ArrayInt a _ -> a
    ArrayBoolean a _ -> a
    ArrayStr a _ -> a
    EmptyArray a -> a
    Tuple a _ -> a

getAFromMulOp :: MulOp a -> a
getAFromMulOp mulop = case mulop of
    Times a -> a
    Div a -> a
    Mod a -> a

-- getAt :: Val a -> Int -> Val a
-- getAt (Tuple t) pos = t !! pos

ident2String :: Ident -> String
ident2String (Ident str) = str
