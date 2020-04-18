module Types where
import AbsNewGrammar
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Maybe(fromJust)

type ErrorType = (String, Val) -- Error, value to return (if return was called, then that string == "RETURN")

string2error :: String -> ErrorType
string2error msg = (msg, Int 0)

type Loc = Int
type Env = Map.Map Ident Loc
type Store = (Map.Map Loc Val, Loc) -- Map, first free loc
-- type Fun a = [Loc] -> Store -> Stmt ?

type ERSIO a = ExceptT ErrorType (ReaderT Env (StateT Store IO)) a

data Val = Int Integer | Str String | Boolean Bool | ArrayInt [Int] | ArrayBoolean [Bool]
         | ArrayStr [String] | EmptyArray | Tuple [Val] | Fun Block Type Env [Arg] deriving (Show)


getLoc :: Ident -> ERSIO Loc
getLoc x = do
    env <- ask
    case Map.lookup x env of
        Nothing -> throwError $ string2error  $ show x ++ " was not defined"
        Just loc -> return loc

getVal :: Loc -> ERSIO Val
getVal loc = do
    (store, loc') <- get
    return $ fromJust $ Map.lookup loc store -- TODO: we ignore the fact that x can not have a value yet... (it shouldn't happen, grammar forbids this)



compTypeLists :: [Val] -> [Val] -> Bool
compTypeLists [] [] = True
compTypeLists (t1:t1s) (t2:t2s) = if compTypes t1 t2 then compTypeLists t1s t2s else False
compTypeLists _ _ = False

compTypes :: Val -> Val -> Bool
compTypes t1 t2 =
    case (t1, t2) of
        (Int _, Int _) -> True
        (Str _, Str _) -> True
        (Boolean _, Boolean _) -> True
        (ArrayInt _, ArrayInt _) -> True
        (ArrayBoolean _, ArrayBoolean _) -> True
        (ArrayStr _, ArrayStr _) -> True
        (EmptyArray, ArrayInt _) -> True
        (EmptyArray, ArrayBoolean _) -> True
        (EmptyArray, ArrayStr _) -> True
        (ArrayInt _, EmptyArray) -> True
        (ArrayBoolean _, EmptyArray) -> True
        (ArrayStr _, EmptyArray) -> True
        (Tuple x1, Tuple x2) -> compTypeLists x1 x2
        (_, _) -> False 


-- TODO: do we need this at all? Can't we incorporate data Type into data Val?
type2Val :: Type -> Val
type2Val t =
    case t of
        BaseT IntT -> Int 0
        BaseT StrT -> Str ""
        BaseT BooleanT -> Boolean False
        ArrayT IntT -> ArrayInt []
        ArrayT StrT -> ArrayStr []
        ArrayT BooleanT -> ArrayBoolean []
        TupleT types -> Tuple (map type2Val types)

compTypeWithVal :: Type -> Val -> Bool
compTypeWithVal type_ val = compTypes (type2Val type_) val

-- allocates a new loc with input value and returns this new loc
alloc :: Val -> ERSIO Loc
alloc val = do
    (store, loc) <- get
    modify (\_ -> (Map.insert loc val store, loc + 1))
    return loc

getNewLoc :: ERSIO Loc
getNewLoc = do
    (store, loc) <- get
    return loc

getAt :: Val -> Int -> Val
getAt (Tuple t) pos = t !! pos
