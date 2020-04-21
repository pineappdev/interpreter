module Stmt where

import AbsGrammar
import Types

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import Data.List(intersperse)

transStmt :: Show a => Stmt a -> ERSIO () a

transStmt (Break a) = do throwError $ ("BREAK", NULL)

transStmt (Continue a) = do throwError $ ("CONTINUE", NULL)

transStmt (Ret a expr) = do
    val <- transExpr expr
    throwError $ ("RETURN", changeAVal a val)

transStmt (Empty a) = do return ()

transStmt (Ass a x expr) = do
    val <- transExpr expr
    (loc_x, a_x) <- getLoc a x
    val_x <- getVal loc_x
    if not (compValTypes val val_x)
        then throwError $ string2error $ show a ++ ": type error - expected" ++ showValsType val_x ++ ", but got " ++ showValsType val
        else modify (\(store, loc) -> (Map.insert loc_x val store, loc))

transStmt (Cond _ expr stmt) = do
    b <- evalToBool expr
    if b
        then transStmt stmt
        else return ()    

transStmt (CondElse _ expr stmt1 stmt2) = do
    b <- evalToBool expr
    if b
        then transStmt stmt1
        else transStmt stmt2

transStmt (While a expr stmt) = do
    b <- evalToBool expr
    if b
        then catchError (transStmt stmt >> transStmt (While a expr stmt)) fun
        else return ()
        where
            fun error = case error of
                ("BREAK", _) -> return ()
                ("CONTINUE", _) -> transStmt (While a expr stmt)
                other -> throwError other

transStmt (SExp _ expr) = do
    transExpr expr
    return ()

transStmt (BStmt _ (Block _ [])) = do
    return ()

transStmt (BStmt a (Block a' (stmt:stmts))) = do
    case stmt of
        Decl a'' type_ items -> do
            env <- transDecl (Decl a'' type_ items)
            local (\env' -> env) (transStmt (BStmt a (Block a' stmts)))
        FunDef a topdef -> do
            env <- transFnDef (FunDef a topdef)
            local (\env' -> env) (transStmt (BStmt a (Block a' stmts)))
        other -> transStmt stmt >> transStmt (BStmt a (Block a' stmts))

transFnDef :: Show a => Stmt a -> ERSIO (Env a) a
transFnDef (FunDef a topdef) = do
    env <- registerFun topdef
    local (\env' -> env) (transTopDef topdef)
    return env

-- assumes that func already lives in the env, saves it to store
transTopDef :: Show a => TopDef a -> ERSIO () a
transTopDef (FnDef a type_ ident args block) = do
    env <- ask
    (loc, _) <- getLoc a ident
    let fun_val = Fun block type_ env args
    modify (\(store, loc') -> (Map.insert loc fun_val store, loc'))
    return ()

-- reserve loc for func and change the env, but don't define function (in store loc for that func points to nothing)
registerFun :: Show a => TopDef a -> ERSIO (Env a) a
registerFun (FnDef a type_ f args block) = let x = ident2String f in
    if elem x keywords
    then do
        throwError $ string2error $ show a ++ ": illegal function definition: " ++ show f ++ " is a restricted keyword"
    else do
        env <- ask
    -- TODO: name overriding, but not in scope of the same block... TODO
    -- case Map.lookup f env of
        -- Just _ -> throwError $ string2error $ "Function " ++ show f ++ " is already defined"
        -- Nothing -> do
        loc <- getNewLoc
        modify (\(store, loc') -> (store, loc' + 1))
        return $ Map.insert f (loc, a) env

transDecl :: Show a => Stmt a -> ERSIO (Env a) a
transDecl (Decl a type_ []) = do ask
transDecl (Decl a type_ ((Init a' x expr):items)) = do
    val <- transExpr expr
    if not (compTypeWithVal type_ val)
        then do throwError $ string2error $ show a ++ ": type error: expected " ++ show type_  ++ ", but got " ++ showValsType val
        else do
            loc <- alloc val
            local (\env -> Map.insert x (loc, a) env) (transDecl (Decl a type_ items))






------------------------------------------------- EXPRS -------------------------------------------------------------------------
-- TODO: separate this as a distinct module
-- TODO: showType val function??

insertVal :: Loc -> Val a -> ERSIO () a
insertVal loc val = do
    modify (\(store, loc') -> (Map.insert loc val store, loc'))

getAFromExpr :: Show a => Expr a -> a
getAFromExpr expr = case expr of
    EVar a _ -> a
    ELitInt a _ -> a
    ELitTrue a -> a
    ELitFalse a -> a
    EApp a _ _ -> a
    EString a _ -> a
    ETuple a _ -> a
    EArray a -> a
    Neg a _ -> a
    Not a _ -> a
    EMul a _ _ _ -> a
    EAdd a _ _ _ -> a
    ERel a _ _ _ -> a
    EAnd a _ _ -> a
    EOr a _ _ -> a

getAFromEArg :: Show a => EArg a -> a
getAFromEArg (EArgE a _) = a
getAFromEArg (EArgName a _) = a

evalToInt :: Show a => Expr a -> ERSIO Integer a
evalToInt expr = do
    val <- transExpr expr
    case val of
        Int _ x -> return x
        _ -> throwError $ string2error  $ show (getAFromExpr expr) ++ ": type error: expected int, but got " ++ showValsType val

evalToBool :: Show a => Expr a -> ERSIO Bool a
evalToBool expr = do
    val <- transExpr expr
    case val of
        Boolean _ x -> return x
        _ -> throwError $ string2error  $ show (getAFromExpr expr) ++ ": type error: expected bool, but got " ++ showValsType val

-- adjusts store and env to args
-- first a is the place of the function call
resolveArgs :: Show a => a -> [EArg a] -> [Arg a] -> ERSIO (Env a) a
resolveArgs _ [] [] = do ask
resolveArgs a (earg:eargs) (arg:args) =
    case (earg, arg) of
        (EArgE ea expr, Arg aa type_ x) -> do
            val <- transExpr expr
            -- I need a function to compare type with val and throwError w.r.t. to place of the earg and arg
            -- the problem is, val a doesn't really have info of places
            if not $ compTypeWithVal type_ val
                then throwError $ string2error $ show ea ++ ": type error: expected "
                    ++ show type_ ++ " as declared at: " ++ show aa ++ ", but got " ++ showValsType val
                else do
                    loc <- alloc val
                    local (\env -> Map.insert x (loc, aa) env) (resolveArgs a eargs args)
        (EArgName ea name, Arg aa type_ x) -> do
            (loc, a') <- getLoc ea name
            val <- getVal loc
            if not $ compTypeWithVal type_ val
                then throwError $ string2error  $ show ea ++ ": type error: expected " ++ show type_ ++ " as declared at: " ++ show aa
                    ++ ", but got " ++ showValsType val
                else do
                    local (\env -> Map.insert x (loc, aa) env) (resolveArgs a eargs args)

resolveArgs _ eargs [] = case head eargs of
    earg -> throwError $ string2error $ show (getAFromEArg earg) ++ ": too many arguments in function call"

resolveArgs a [] args = throwError $ string2error $ show a ++ ": not enough arguments provided"

execFun :: Show a => Ident -> Env a -> Stmt a -> ERSIO (Val a) a
execFun fun env stmt = do
    local (\env' -> env) (transStmt stmt)
    throwError $ string2error $ "No return in function: " ++ show fun

-- a is the place where the function was called
printArgs :: Show a => a -> [EArg a] -> ERSIO (Val a) a
printArgs a [] = return (Int a 0)
printArgs a (earg:eargs) = do
    val <- case earg of
        EArgE a expr -> transExpr expr
        EArgName a x -> throwError $ string2error $ show a ++ ": print only accepts passing by value"
    let str = if not $ null eargs then show val ++ " " else show val ++ "\n" 
    liftIO (putStr str) >> printArgs a eargs

computeIndex :: Show a => EArg a -> ERSIO Integer a
computeIndex earg = do
    let a' = getAFromEArg earg
    let un_val = case earg of
            EArgE _ expr -> transExpr expr
            EArgName b x -> do
                (loc, _) <- getLoc b x
                getVal loc
    val <- un_val
    case val of
        Int a i -> if i < 0 then
            throwError $ string2error $ show a' ++ ": negative index"
            else return i
        _ -> throwError $ string2error $ show a' ++ ": index can be only int, got " ++ showValsType val

checkRange :: Show a => Foldable t => a -> Integer -> t b -> ERSIO () a
checkRange a idx arr = if idx >= toInteger (length arr)
    then throwError $ string2error $ show a ++ ": index out of range"
    else return ()

eargToValue :: Show a => EArg a -> ERSIO (Val a) a
eargToValue earg = case earg of
    EArgE _ expr -> transExpr expr
    EArgName b x -> do
        (loc, _) <- getLoc b x
        getVal loc

transGet :: Show a => a -> [EArg a] -> ERSIO (Val a) a
transGet a eargs = if length eargs > 2 then throwError $ string2error $ show a ++ ": in get: too many args provided (get accepts index and tuple/array as args)" else
    if length eargs < 2 then throwError $ string2error $ show a ++ ": in get: not enough arguments (get accepts index and tuple/array as args)" else do
        let a' = getAFromEArg $ head eargs
        idx <- computeIndex $ head eargs
        let a'' = getAFromEArg $ eargs !! 1
        li <- eargToValue (eargs !! 1)
        case li of
            Tuple _ vals -> checkRange a' idx vals >> return (vals !! fromInteger(idx))
            ArrayInt _ arr -> checkRange a' idx arr >> return (Int a (arr !! fromInteger(idx)))
            ArrayBoolean _ arr -> checkRange a' idx arr >> return (Boolean a (arr !! fromInteger(idx))) 
            ArrayStr _ arr -> checkRange a' idx arr >> return (Str a (arr !! fromInteger(idx)))
            EmptyArray _ -> throwError $ string2error $ show a' ++ ": array index out of range"
            _ -> throwError $ string2error $ show a' ++ ": get only accepts tuples or arrays, got " ++ showValsType li

insertToArr :: Int -> a -> [a] -> [a]
insertToArr idx val vals = case splitAt idx vals of
    (left, right) -> left ++ [val] ++ right' where
        right' = case splitAt 1 right of
            (l, r) -> r

transSet :: Show a => a -> [EArg a] -> ERSIO (Val a) a
--          array index value
transSet a (earg1:earg2:earg3:[]) = do
    let a3 = getAFromEArg earg3
    let a2 = getAFromEArg earg2
    idx <- computeIndex earg2
    to_set <- eargToValue earg3
    case earg1 of
        EArgE a' expr -> throwError $ string2error $ show a' ++ ": first argument of set must be passed by name"
        EArgName b x -> do
            (loc, _) <- getLoc b x
            val <- getVal loc
            case val of
                Tuple z vals -> do
                    checkRange a2 idx vals
                    let val_cur = (vals !! fromInteger(idx))
                    if not (compValTypes to_set val_cur) then
                        throwError $ string2error $ show a3 ++ ": type error: expected " ++ showValsType val_cur ++ ", but got " ++ showValsType to_set
                        else insertVal loc (Tuple z (insertToArr (fromInteger idx) to_set vals))
                ArrayInt z arr -> do
                    checkRange a2 idx arr
                    i <- val2Int a3 to_set
                    insertVal loc (ArrayInt z (insertToArr (fromInteger idx) i arr))
                ArrayBoolean z arr -> do
                    checkRange a2 idx arr
                    b <- val2Bool a3 to_set
                    insertVal loc (ArrayBoolean z (insertToArr (fromInteger idx) b arr))
                ArrayStr z arr -> do
                    checkRange a2 idx arr
                    s <- val2Str a3 to_set
                    insertVal loc (ArrayStr z (insertToArr (fromInteger idx) s arr))
                EmptyArray _ -> throwError $ string2error $ show a2 ++ ": array index out of range"
                _ -> throwError $ string2error $ show a2 ++ ": set only accepts tuples or arrays, got " ++ showValsType val
    return $ Int a 0

transSet a _ = throwError $ string2error $ show a ++ ": set function accepts 3 args: array/tuple, index (int), and a new value"


transExpr :: Show a => Expr a -> ERSIO (Val a) a

transExpr (EVar a x) = do
    (loc, a') <- getLoc a x
    val <- getVal loc
    return $ changeAVal a val

transExpr (ELitInt a i) = do return (Int a i)

transExpr (ELitTrue a) = do return (Boolean a True)

transExpr (ELitFalse a) = do return (Boolean a False)

transExpr (EApp a ident eargs) = let x = ident2String ident in
    if elem x keywords
    then do
        case x of
            "print" -> printArgs a eargs
            "get" -> transGet a eargs
            "set" -> transSet a eargs
    else do
        (loc, a') <- getLoc a ident
        (store, loc') <- get
        fun <- getVal loc
        case fun of
            Fun block type_ env args -> do
                let a'' = case block of Block a _ -> a
                env <- resolveArgs a eargs args
                catchError (execFun ident env (BStmt a'' block)) (\error -> case error of
                    -- handle_error :: Show a => ErrorType a -> ERSIO (Val a) a
                    (msg, val) -> case msg of
                        "RETURN" -> if not (compTypeWithVal type_ val)
                            then
                                throwError $ string2error $ show (getAFromVal val) ++ ": type error: expected "
                                ++ show type_ ++ ", but got " ++ showValsType val
                            else return (changeAVal a val)
                        "BREAK" -> throwError $ string2error $ show (getAFromVal val) ++ ": break coutside of loop"
                        "CONTINUE" -> throwError $ string2error $ show (getAFromVal val) ++ ": continue outside of loop"
                        other -> throwError $ string2error other)

transExpr (EString a string) = do
    return (Str a string)

transExpr (ETuple a exprs) = liftM (Tuple a) (mapM transExpr exprs)
    -- tup_content <- mapM transExpr exprs
    -- return (Tuple tup_content)

transExpr (EArray a) = do
    return (EmptyArray a)

transExpr (Neg a expr) = do
    x <- evalToInt expr
    return $ Int a ((-1) * x)

transExpr (Not a expr) = do
    x <- evalToBool expr
    return $ Boolean a $ not x

transExpr (EMul a expr1 mulop expr2) = do
    x <- evalToInt expr1
    y <- evalToInt expr2
    case mulop of
        Times _ -> return $ Int a $ x * y
        op -> if y == 0
            then throwError $ string2error $ show (getAFromMulOp op) ++ ": division by 0"
            else case op of
                Div _ -> return $ Int a $ x `div` y
                Mod _ -> return $ Int a $ x `mod` y

transExpr (EAdd a expr1 addop expr2) = do
    x <- evalToInt expr1
    y <- evalToInt expr2
    case addop of
        Plus a -> return $ Int a $ x + y
        Minus a -> return $ Int a $ x - y

transExpr (ERel a expr1 relop expr2) = do
    val1 <- transExpr expr1
    val2 <- transExpr expr2

    case (val1, val2) of
        (Str _ s1, Str _ s2) -> return $ Boolean a $ transOrdRelOp relop s1 s2
        (Boolean _ b1, Boolean _ b2) -> return $ Boolean a $ transOrdRelOp relop b1 b2
        (Int _ i1, Int _ i2) ->  return $ Boolean a $ transOrdRelOp relop i1 i2
        x -> if isOrdOp relop
            then
                throwError $ string2error $ show a ++ ": comparison error - provided types "
                ++ showValsType val1 ++ ", " ++ showValsType val2 ++ " are not in Order"
            else case x of
                (ArrayInt _ arr1, ArrayInt _ arr2) -> return $ Boolean a $ transEqRelOp relop arr1 arr2  
                (ArrayBoolean _ arr1, ArrayBoolean _ arr2) -> return $ Boolean a $ transEqRelOp relop arr1 arr2
                (ArrayStr _ arr1, ArrayStr _ arr2) -> return $ Boolean a $ transEqRelOp relop arr1 arr2
                (EmptyArray _, ArrayInt _ arr2) -> return $ Boolean a $ transEqRelOp relop [] arr2
                (EmptyArray _, ArrayBoolean _ arr2) -> return $ Boolean a $ transEqRelOp relop [] arr2
                (EmptyArray _, ArrayStr _ arr2) -> return $ Boolean a $ transEqRelOp relop [] arr2
                (EmptyArray _, EmptyArray _) -> return $ Boolean a $ transEqRelOp relop ([] :: [Int]) []
                (ArrayInt _ arr1, EmptyArray _) -> return $ Boolean a $ transEqRelOp relop arr1 []
                (ArrayBoolean _ arr1, EmptyArray _) -> return $ Boolean a $ transEqRelOp relop arr1 []
                (ArrayStr _ arr1, EmptyArray _) -> return $ Boolean a $ transEqRelOp relop arr1 []
                (Tuple _ t1, Tuple _ t2) -> if k == 1 then f True else if k == 0 then f False else throwError $ string2error $ show a
                    ++ ": comparison error - provided types " ++ showValsType val1 ++ ", " ++ showValsType val2 ++ " are not comparable" where
                    k = compValLists t1 t2
                    f = \b -> return $ Boolean a b
                _ -> throwError $ string2error $ show a ++ ": comparison error - provided types "
                    ++ showValsType val1 ++ ", " ++ showValsType val2 ++ " are not comparable"

transExpr (EAnd a expr1 expr2) = do
    val1 <- evalToBool expr1
    val2 <- evalToBool expr2
    return $ Boolean a (val1 && val2)

transExpr (EOr a expr1 expr2) = do
    val1 <- evalToBool expr1
    val2 <- evalToBool expr2
    return $ Boolean a (val1 || val2)

isOrdOp :: RelOp a -> Bool
isOrdOp x = case x of
    EQU a -> False
    NE a -> False
    _ -> True

transOrdRelOp :: (Ord a) => RelOp b -> a -> a -> Bool
transOrdRelOp x = case x of
    LTH b -> (<)
    LE b -> (<=)
    GTH b -> (>)
    GE b -> (>=)
    EQU b -> (==)
    NE b -> (/=)


transEqRelOp :: (Eq a) => RelOp b -> a -> a -> Bool
transEqRelOp x = case x of
    EQU b -> (==)
    NE b -> (/=)





-- runExp :: Expr -> IO (Either ErrorType Val, Store)
-- runExp exp = runStateT (runReaderT (runExceptT (transExpr exp)) Map.empty) (Map.empty, 0)

-- exp1 = ERel (EArray) EQU (EArray)
-- exp2 = EMul (ELitInt 3) Div (ELitInt 0)
-- | Some Exp tests
-- >>> runExp exp1
-- qweqwe(Right (Boolean True),fromList [])
-- 