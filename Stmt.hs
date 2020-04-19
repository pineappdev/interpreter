module Stmt where

import AbsNewGrammar
import Types

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import Data.List(intersperse)

transStmt :: Stmt -> ERSIO ()


-- TODO: break && continue (important!)
transStmt Break = do throwError $ string2error "BREAK"

transStmt Continue = do throwError $ string2error "CONTINUE"

transStmt (Ret expr) = do
    val <- transExpr expr
    throwError $ ("RETURN", val)

transStmt Empty = do return ()

transStmt (Ass x expr) = do
    val <- transExpr expr
    loc_x <- getLoc x
    val_x <- getVal loc_x
    if not (compTypes val val_x)
        then throwError $ string2error $ "Type error: in " ++ show x ++ " = " ++ show expr
        else modify (\(store, loc) -> (Map.insert loc_x val store, loc))

transStmt (Cond expr stmt) = do
    b <- evalToBool expr
    if b
        then transStmt stmt
        else return ()    

transStmt (CondElse expr stmt1 stmt2) = do
    b <- evalToBool expr
    if b
        then transStmt stmt1
        else transStmt stmt2

transStmt (While expr stmt) = do
    b <- evalToBool expr
    if b
        then catchError (transStmt stmt >> transStmt (While expr stmt)) fun
        else return ()
        where
            fun error = case error of
                ("BREAK", _) -> return ()
                ("CONTINUE", _) -> transStmt (While expr stmt)
                other -> throwError other

transStmt (SExp expr) = do
    transExpr expr
    return ()

transStmt (BStmt (Block [])) = do
    return ()

transStmt (BStmt (Block (stmt:stmts))) = do
    case stmt of
        Decl type_ items -> do
            env <- transDecl (Decl type_ items)
            local (\env' -> env) (transStmt (BStmt (Block stmts)))
        FunDef topdef -> do
            env <- transFnDef (FunDef topdef)
            local (\env' -> env) (transStmt (BStmt (Block stmts)))
        other -> transStmt stmt >> transStmt (BStmt (Block stmts))

transFnDef :: Stmt -> ERSIO Env
transFnDef (FunDef topdef) = do
    env <- registerFun topdef
    local (\env' -> env) (transTopDef topdef)
    return env

-- assumes that func already lives in the env, saves it to store
transTopDef :: TopDef -> ERSIO ()
transTopDef (FnDef type_ ident args block) = do
    env <- ask
    loc <- getLoc ident
    let fun_val = Fun block type_ env args
    modify (\(store, loc') -> (Map.insert loc fun_val store, loc'))
    return ()

-- reserve loc for func and change the env, but don't define function (in store loc for that func points to nothing)
registerFun :: TopDef -> ERSIO Env
registerFun (FnDef type_ f args block) = let x = ident2String f in
    if elem x keywords
    then do
        throwError $ string2error $ show f ++ " is a restricted keyword"
    else do
        env <- ask
    -- TODO: name overriding, but not in scope of the same block... TODO
    -- case Map.lookup f env of
        -- Just _ -> throwError $ string2error $ "Function " ++ show f ++ " is already defined"
        -- Nothing -> do
        loc <- getNewLoc
        modify (\(store, loc') -> (store, loc' + 1))
        return $ Map.insert f loc env

transDecl :: Stmt -> ERSIO Env
transDecl (Decl type_ []) = do ask
transDecl (Decl type_ ((Init x expr):items)) = do
    val <- transExpr expr
    if not (compTypeWithVal type_ val)
        then do throwError $ string2error  $ "Type error: in " ++ show type_ ++ " " ++ show x ++ " = " ++ show expr
        else do
            loc <- alloc val
            local (\env -> Map.insert x loc env) (transDecl (Decl type_ items))






------------------------------------------------- EXPRS -------------------------------------------------------------------------
-- TODO: separate this as a distinct module

evalToInt :: Expr -> ERSIO Integer
evalToInt expr = do
    val <- transExpr expr
    case val of
        Int x -> return x
        _ -> throwError $ string2error  $ "Type error: " ++ show expr ++ " is not an int"

evalToBool :: Expr -> ERSIO Bool
evalToBool expr = do
    val <- transExpr expr
    case val of
        Boolean x -> return x
        _ -> throwError $ string2error  $ "Type error: " ++ show expr ++ " is not a bool"

-- adjusts store and env to args
resolveArgs :: [EArg] -> [Arg] -> ERSIO Env
resolveArgs [] [] = do ask
resolveArgs (earg:eargs) (arg:args) =
    case (earg, arg) of
        (EArgE expr, Arg type_ x) -> do
            val <- transExpr expr
            if not $ compTypeWithVal type_ val
                then throwError $ string2error  $ "Function argument " ++ show expr ++ " is not of type " ++ show type_
                else do
                    loc <- alloc val
                    local (\env -> Map.insert x loc env) (resolveArgs eargs args)
        (EArgName name, Arg type_ x) -> do
            loc <- getLoc name
            val <- getVal loc
            if not $ compTypeWithVal type_ val
                then throwError $ string2error  $ "Function argument " ++ show name ++ " is not of type " ++ show type_
                else do
                    local (\env -> Map.insert x loc env) (resolveArgs eargs args)

resolveArgs eargs [] = throwError $ string2error  $ "Function was called with too many arguments"
resolveArgs [] args = throwError $ string2error  $ "Function was called with not enough arguments"

execFun :: Ident -> Env -> Stmt -> ERSIO Val
execFun fun env stmt = do
    local (\env' -> env) (transStmt stmt)
    throwError $ string2error  $ "No return in the function " ++ show fun

-- TODO: mapM...?
printArgs :: [EArg] -> ERSIO Val
printArgs [] = return (Int 0)
printArgs (earg:eargs) = do
    val <- case earg of
        EArgE expr -> transExpr expr
        EArgName x -> throwError $ string2error "print only accepts passing by value"
    let str = if not $ null eargs then show val ++ " " else show val ++ "\n" 
    liftIO (putStr str) >> printArgs eargs

transExpr :: Expr -> ERSIO Val

transExpr (EVar x) = getLoc x >>= getVal

transExpr (ELitInt i) = do return (Int i)

transExpr ELitTrue = do return (Boolean True)

transExpr ELitFalse = do return (Boolean False)

transExpr (EApp ident eargs) = let x = ident2String ident in
    if elem x keywords
    then do
        case x of
            "print" -> printArgs eargs
            "get" -> throwError $ string2error $ "get not implemented yet"
            "set" -> throwError $ string2error $ "set not implemented yet"
    else do
        loc <- getLoc ident
        (store, loc') <- get
        fun <- getVal loc
        case fun of
            Fun block type_ env args -> do
                env <- resolveArgs eargs args
                catchError (execFun ident env (BStmt block)) handle_error where
                    handle_error :: ErrorType -> ERSIO Val
                    handle_error (msg, val) = case msg of
                        "RETURN" -> if not $ compTypeWithVal type_ val
                            then throwError $ string2error $ "Function " ++ show ident ++ " returned a different type than declared"
                            else return val
                        "BREAK" -> throwError $ string2error $ "Error: break coutside of loop"
                        "CONTINUE" -> throwError $ string2error $ "Error: continue outside of loop"
                        other -> throwError $ string2error other

transExpr (EString string) = do
    return (Str string)

-- TODO: can we really use mapM here?
-- Because we might want to evaluate exprs iteratively
-- as they might change the store
transExpr (ETuple exprs) = liftM Tuple (mapM transExpr exprs)
    -- tup_content <- mapM transExpr exprs
    -- return (Tuple tup_content)

-- TODO: make sure this works
-- TODO: what's the type of this? !!!!!!!!!! IMPORTANT !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!1
transExpr EArray = do
    return EmptyArray

transExpr (Neg expr) = do
    x <- evalToInt expr
    return $ Int ((-1) * x)

transExpr (Not expr) = do
    x <- evalToBool expr
    return $ Boolean $ not x

transExpr (EMul expr1 mulop expr2) = do
    x <- evalToInt expr1
    y <- evalToInt expr2
    case mulop of
        Times -> return $ Int $ x * y
        op -> if y == 0
            then throwError $ string2error  $ "Error: the divider " ++ show expr2 ++ " is equal to 0"
            else case op of
                Div -> return $ Int $ x `div` y
                Mod -> return $ Int $ x `mod` y

transExpr (EAdd expr1 addop expr2) = do
    x <- evalToInt expr1
    y <- evalToInt expr2
    case addop of
        Plus -> return $ Int $ x + y
        Minus -> return $ Int $ x - y

transExpr (ERel expr1 relop expr2) = do
    val1 <- transExpr expr1
    val2 <- transExpr expr2

    case (val1, val2) of
        (Str s1, Str s2) -> return $ Boolean $ transOrdRelOp relop s1 s2
        (Boolean b1, Boolean b2) -> return $ Boolean $ transOrdRelOp relop b1 b2
        (Int i1, Int i2) ->  return $ Boolean $ transOrdRelOp relop i1 i2
        x -> if isOrdOp relop
            then throwError $ string2error  $ "Comparison error: " ++ show expr1 ++ " and " ++ show expr2 ++ " are not orderable types"
            else case x of
                (ArrayInt arr1, ArrayInt arr2) -> return $ Boolean $ transEqRelOp relop arr1 arr2  
                (ArrayBoolean arr1, ArrayBoolean arr2) -> return $ Boolean $ transEqRelOp relop arr1 arr2
                (ArrayStr arr1, ArrayStr arr2) -> return $ Boolean $ transEqRelOp relop arr1 arr2
                (EmptyArray, ArrayInt arr2) -> return $ Boolean $ transEqRelOp relop [] arr2
                (EmptyArray, ArrayBoolean arr2) -> return $ Boolean $ transEqRelOp relop [] arr2
                (EmptyArray, ArrayStr arr2) -> return $ Boolean $ transEqRelOp relop [] arr2
                (EmptyArray, EmptyArray) -> return $ Boolean $ transEqRelOp relop ([] :: [Int]) []
                (ArrayInt arr1, EmptyArray) -> return $ Boolean $ transEqRelOp relop arr1 []
                (ArrayBoolean arr1, EmptyArray) -> return $ Boolean $ transEqRelOp relop arr1 []
                (ArrayStr arr1, EmptyArray) -> return $ Boolean $ transEqRelOp relop arr1 []
                (Tuple t1, Tuple t2) -> throwError $ string2error  $ "Tuple comparison not implemented yet"
                _ -> throwError $ string2error  $ "Comparison error: " ++ show expr1 ++ " is not comparable with " ++ show expr1

transExpr (EAnd expr1 expr2) = do
    val1 <- evalToBool expr1
    val2 <- evalToBool expr2
    return $ Boolean (val1 && val2)

transExpr (EOr expr1 expr2) = do
    val1 <- evalToBool expr1
    val2 <- evalToBool expr2
    return $ Boolean (val1 || val2)

isOrdOp :: RelOp -> Bool
isOrdOp x = case x of
    EQU -> False
    NE -> False
    _ -> True

transOrdRelOp :: (Ord a) => RelOp -> a -> a -> Bool
transOrdRelOp x = case x of
    LTH -> (<)
    LE -> (<=)
    GTH -> (>)
    GE -> (>=)
    EQU -> (==)
    NE -> (/=)


transEqRelOp :: (Eq a) => RelOp -> a -> a -> Bool
transEqRelOp x = case x of
    EQU -> (==)
    NE -> (/=)





runExp :: Expr -> IO (Either ErrorType Val, Store)
runExp exp = runStateT (runReaderT (runExceptT (transExpr exp)) Map.empty) (Map.empty, 0)

exp1 = ERel (EArray) EQU (EArray)
exp2 = EMul (ELitInt 3) Div (ELitInt 0)
-- | Some Exp tests
-- >>> runExp exp1
-- qweqwe(Right (Boolean True),fromList [])
-- 