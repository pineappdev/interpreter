module Stmt where

import AbsNewGrammar
import Types

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map

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
        then throwError $ string2error $ show x ++ " is of different type than " ++ show expr
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
        then transStmt stmt >> transStmt (While expr stmt)
        else return () 

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
        other -> transStmt stmt >> transStmt (BStmt (Block stmts))

transDecl :: Stmt -> ERSIO Env
transDecl (Decl type_ []) = do ask
transDecl (Decl type_ ((Init x expr):items)) = do
    val <- transExpr expr
    if not (compTypeWithVal type_ val)
        then do throwError $ string2error  $ "Type error: " ++ show expr ++ " is not of type " ++ show type_
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


transExpr :: Expr -> ERSIO Val

transExpr (EVar x) = getLoc x >>= getVal

transExpr (ELitInt i) = do return (Int i)

transExpr ELitTrue = do return (Boolean True)

transExpr ELitFalse = do return (Boolean False)

transExpr (EApp ident eargs) = do
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