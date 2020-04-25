module Types where
import AbsGrammar
import PureVal
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Maybe(fromJust)
import Data.List(intersperse)
import Data.Char(toLower)

type ErrorType = String

keywords = ["print", "set", "return", "break", "continue", "if", "then", "else", "while", "int", "string", "boolean"]

string2error :: String -> ErrorType
string2error msg = msg

type Loc = Int
type Env a = Map.Map Ident (Loc, a) -- a stores the location of ident's definition
-- (Map loc -> value, first free loc, break/continue/return flag, (value of return, place where return was called))
-- flag : 0 - nothing, 1 - break, 2 - continue, 3 - return
type Store a = (Map.Map Loc (Val a), Loc, Int, (PureVal, a))

setPureVal :: Loc -> PureVal -> ERSIO () a
setPureVal loc val = modify (\(store, loc', flag, val') -> (Map.insert loc (PureVal val) store, loc', flag, val'))

setVal :: Loc -> Val a -> ERSIO () a
setVal loc val = modify (\(store, loc', flag, val') -> (Map.insert loc val store, loc', flag, val'))

getVal :: Loc -> ERSIO (Val a) a
getVal loc = do
    (store, loc', flag, val') <- get
    return $ fromJust $ Map.lookup loc store  

getPureVal :: Loc -> ERSIO PureVal a
getPureVal loc = do
    val <- getVal loc
    return $ toPureVal val

type ERSIO res_type a = ExceptT ErrorType (ReaderT (Env a) (StateT (Store a) IO)) res_type

data Val a = PureVal PureVal | Fun (Block a) (Type a) (Env a) [Arg a]
    deriving(Eq)

isPureVal :: Val a -> Bool
isPureVal (PureVal pv) = True
isPureVal _ = False 

toPureVal :: Val a -> PureVal
toPureVal (PureVal pv) = pv

instance Show (Val a) where
    show = show . toPureVal

showValsType :: Val a -> String
showValsType = showPureValsType . toPureVal

val2Bool :: Show a => a -> Val a -> ERSIO Bool a
val2Bool place val = case val of
    PureVal (Boolean b) -> return b
    _ -> throwError $ string2error $ show place ++ ": type error, expected bool, but got " ++ showValsType val

val2Int :: Show a => a -> Val a -> ERSIO Integer a
val2Int place val = case val of
    PureVal (Int i) -> return i
    _ -> throwError $ string2error $ show place ++ ": type error, expected int, but got " ++ showValsType val

val2Str :: Show a => a -> Val a -> ERSIO String a
val2Str place val = case val of
    PureVal (Str s) -> return s
    _ -> throwError $ string2error $ show place ++ ": type error, expected string, but got " ++ showValsType val

-- given a place and an ident, computes loc of this ident
-- or throws an error "undefined..." at given place
getLoc :: Show a => Ident -> ERSIO Loc a
getLoc x = do
    env <- ask
    return $ fst $ fromJust $ Map.lookup x env

-- allocates a new loc with input value and returns this new loc
alloc :: Val a -> ERSIO Loc a
alloc val = do
    loc <- getNewLoc
    modify (\(store, loc, flag, val') -> (Map.insert loc val store, loc + 1, flag, val'))
    return loc

allocPure :: PureVal -> ERSIO Loc a
allocPure = alloc . PureVal

getNewLoc :: ERSIO Loc a
getNewLoc = do
    (_, loc, _, _) <- get
    return loc

getPlaceFromType :: Type a -> a
getPlaceFromType type_ = case type_ of
    BaseT a _ -> a
    ArrayT a _ -> a
    TupleT a _ -> a

getPlaceFromMulOp :: MulOp a -> a
getPlaceFromMulOp mulop = case mulop of
    Times a -> a
    Div a -> a
    Mod a -> a
