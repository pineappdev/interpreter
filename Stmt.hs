module Stmt where

import AbsGrammar
import PureVal
import Types

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as Map
import Data.List(intersperse)

assign :: Show a => (Ident, PureVal) -> ERSIO () a
assign (x, val) = do
    loc_x <- getLoc x
    val_x <- getPureVal loc_x
    setPureVal loc_x val

evalFinal :: Show a => Final a -> ERSIO (Ident, [(Integer, a)]) a
evalFinal final = case final of
    Final1 a ident -> return (ident, [])
    Final2 a f expr -> do
        idx <- evalToInt expr
        (ident, idxs) <- evalFinal f
        return (ident, idxs ++ [(idx, getAFromExpr expr)])


checkRange :: Show a => Foldable t => a -> Integer -> t b -> ERSIO () a
checkRange a idx arr = if idx >= toInteger (length arr)
    then throwError $ string2error $ show a ++ ": index out of range: " ++ show idx
    else if idx < 0
        then throwError $ string2error $ show a ++ ": negative index: " ++ show idx
        else return ()

insertAt :: Show a => PureVal -> PureVal -> [(Integer, a)] -> ERSIO PureVal a
insertAt to_insert original ([]) = return to_insert
insertAt to_insert (Array vals) ((idx, a):idxs) = do
    checkRange a idx vals
    case splitAt (fromInteger idx) vals of
        (left, right) -> case splitAt 1 right of
            (to_modify:[], right') -> do
                modified <- insertAt to_insert to_modify idxs
                return $ Array $ left ++ (modified:right')

assignAt :: Show a => Ident -> PureVal -> [(Integer, a)] -> ERSIO () a
assignAt x val [] = assign (x, val)
assignAt x val idxs = do
    loc_x <- getLoc x
    val_x <- getPureVal loc_x
    new_val_x <- insertAt val val_x idxs
    setPureVal loc_x new_val_x

assignFinal :: Show a => Final a -> PureVal -> ERSIO () a
assignFinal final val = do
    (x, idxs) <- evalFinal final
    assignAt x val idxs

unpackVal :: Show a => PureVal -> ItemQ a -> ERSIO () a
unpackVal val itemq = case itemq of
    ItemQTuple a itemqs -> do
        case val of
            Tuple tvals -> do
                mapM (\(val, itemq) -> unpackVal val itemq) (zip tvals itemqs)
                return ()
    ItemQFinal a final -> assignFinal final val
        

transStmt :: Show a => Stmt a -> ERSIO () a

transStmt (Break a) = do 
    modify (\(store, loc, flag, val) -> (store, loc, 1, val))

transStmt (Continue a) = do
    modify (\(store, loc, flag, val) -> (store, loc, 2, val))

transStmt (Ret a expr) = do
    val <- transExpr expr
    modify (\(store, loc, _, _) -> (store, loc, 3, (val, a)))

transStmt (Empty a) = do return ()

transStmt (Ass a final expr) = do
    val <- transExpr expr
    assignFinal final val
    
    
transStmt (Unpack a itemq expr) = do
    val <- transExpr expr
    unpackVal val itemq

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
    if b then do
        transStmt stmt
        (store, loc, flag, val) <- get
        case flag of
            1 -> put (store, loc, 0, val) -- break
            2 -> put (store, loc, 0, val) >> transStmt(While a expr stmt) -- continue
            3 -> return () -- return
            0 -> transStmt (While a expr stmt) -- normal case
        else
            return ()

transStmt (SExp _ expr) = do
    transExpr expr
    return ()

transStmt (BStmt a (Block a' [])) = return ()

transStmt (BStmt a (Block a' (stmt:stmts))) = do
    case stmt of
        Decl a'' type_ items -> do
            env <- transDecl (Decl a'' type_ items)
            local (\env' -> env) (transStmt (BStmt a (Block a' stmts)))
        FunDef a'' topdef -> do
            env <- transFnDef (FunDef a topdef)
            local (\env' -> env) (transStmt (BStmt a (Block a' stmts)))
        other -> do
            transStmt stmt
            (_, _, flag, _) <- get
            if flag /= 0
                then return ()
                else transStmt (BStmt a (Block a' stmts))

transFnDef :: Show a => Stmt a -> ERSIO (Env a) a
transFnDef (FunDef a topdef) = do
    env <- registerFun topdef
    local (\env' -> env) (transTopDef topdef)
    return env

-- assumes that func already lives in the env, saves it to store
transTopDef :: Show a => TopDef a -> ERSIO () a
transTopDef (FnDef a type_ ident args block) = do
    env <- ask
    loc <- getLoc ident
    let fun_val = Fun block type_ env args
    setVal loc fun_val
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
        modify (\(store, loc', x, y) -> (store, loc' + 1, x, y))
        return $ Map.insert f (loc, a) env

transDecl :: Show a => Stmt a -> ERSIO (Env a) a
transDecl (Decl a type_ []) = do ask
transDecl (Decl a type_ ((Init a' x expr):items)) = do
    val <- transExpr expr
    loc <- allocPure val
    local (\env -> Map.insert x (loc, a) env) (transDecl (Decl a type_ items))



------------------------------------------------- EXPRS -------------------------------------------------------------------------
-- TODO: separate this as a distinct module
-- TODO: showType val function??

getAFromExpr :: Show a => Expr a -> a
getAFromExpr expr = case expr of
    EVar a _ -> a
    ELitInt a _ -> a
    ELitTrue a -> a
    ELitFalse a -> a
    EApp a _ _ -> a
    EString a _ -> a
    ETuple a _ _ -> a
    EArray a _ -> a
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
        Int x -> return x

evalToBool :: Show a => Expr a -> ERSIO Bool a
evalToBool expr = do
    val <- transExpr expr
    case val of
        Boolean x -> return x

-- adjusts store and env to args
-- first a is the place of the function call
resolveArgs :: Show a => a -> [EArg a] -> [Arg a] -> ERSIO (Env a) a
resolveArgs _ [] [] = do ask
resolveArgs a (earg:eargs) (arg:args) =
    case (earg, arg) of
        (EArgE ea expr, Arg aa type_ x) -> do
            val <- transExpr expr
            loc <- allocPure val
            local (\env -> Map.insert x (loc, aa) env) (resolveArgs a eargs args)
        (EArgName ea name, Arg aa type_ x) -> do
            loc <- getLoc name
            val <- getPureVal loc
            local (\env -> Map.insert x (loc, aa) env) (resolveArgs a eargs args)

-- TODO: check this, static typing should take care...
resolveArgs _ eargs [] = case head eargs of
    earg -> throwError $ string2error $ show (getAFromEArg earg) ++ ": too many arguments in function call"

resolveArgs a [] args = throwError $ string2error $ show a ++ ": not enough arguments provided"

-- TODO: provide place...
execFun :: Show a => Type a -> Ident -> Env a -> Stmt a -> ERSIO PureVal a
execFun type_ fun env stmt = do
    local (\env' -> env) (transStmt stmt)
    (store, loc, flag, (pval, a)) <- get
    case flag of
        -- static typing should take care of this...
        -- 0 -> throwError $ string2error $ "No return in function " ++ show fun
        -- 1 -> throwError $ string2error $ "Break outside of while"
        -- 2 -> throwError $ string2error $ "Continue outside of while"
        3 -> put (store, loc, 0, (pval, a)) >> return pval
            -- else throwError $ string2error $ show a ++ ": expected " ++ show type_ ++ " as declared at " ++ show (getPlaceFromType type_) ++ ", but got " ++ showPureValsType pval

-- a is the place where the function was called
printArgs :: Show a => a -> [EArg a] -> ERSIO (PureVal) a
printArgs a [] = return (Int 0)
printArgs a (earg:eargs) = do
    val <- case earg of
        EArgE a expr -> transExpr expr
        EArgName a x -> throwError $ string2error $ show a ++ ": print only accepts passing by value" -- TODO: check this during static typing
    let str = if not (null eargs) then show val ++ " " else show val ++ "\n" 
    liftIO (putStr str) >> printArgs a eargs

eargToValue :: Show a => EArg a -> ERSIO PureVal a
eargToValue earg = case earg of
    EArgE _ expr -> transExpr expr
    EArgName b x -> do
        loc <- getLoc x
        getPureVal loc

insertToArr :: Int -> a -> [a] -> [a]
insertToArr idx val vals = case splitAt idx vals of
    (left, right) -> left ++ [val] ++ right' where
        right' = case splitAt 1 right of
            (l, r) -> r

transExpr :: Show a => Expr a -> ERSIO PureVal a

transExpr (EGet a expr1 expr2) = do
    idx <- evalToInt expr2
    val1 <- transExpr expr1
    let pvals = case val1 of Array pvals -> pvals
    checkRange a idx pvals
    return $ pvals !! (fromInteger idx)

transExpr (EArray a exprs) = liftM Array (mapM transExpr exprs)

transExpr (EVar a x) = do
    loc <- getLoc x
    val <- getVal loc
    -- if not (isPureVal val) then throwError $ string2error $ show a ++ ": " ++ show x ++ " is a function"
    return $ toPureVal val

transExpr (ELitInt a i) = do return (Int i)

transExpr (ELitTrue a) = do return (Boolean True)

transExpr (ELitFalse a) = do return (Boolean False)

transExpr (EApp a ident eargs) = let x = ident2String ident in
    if elem x keywords
    then do
        case x of
            "print" -> printArgs a eargs
            -- "set" -> transSet a eargs
    else do
        loc <- getLoc ident
        (store, loc', _, _) <- get
        fun <- getVal loc
        case fun of
            Fun block type_ env args -> do
                let a'' = case block of Block a _ -> a
                env <- resolveArgs a eargs args
                execFun type_ ident env (BStmt a'' block)

transExpr (EString a string) = return (Str string)

transExpr (ETuple a expr exprs) = liftM Tuple (mapM transExpr (expr:exprs))

transExpr (Neg a expr) = do
    x <- evalToInt expr
    return $ Int ((-1) * x)

transExpr (Not a expr) = do
    x <- evalToBool expr
    return $ Boolean $ not x

transExpr (EMul a expr1 mulop expr2) = do
    x <- evalToInt expr1
    y <- evalToInt expr2
    case mulop of
        Times _ -> return $ Int $ x * y
        op -> if y == 0
            then throwError $ string2error $ show (getPlaceFromMulOp op) ++ ": division by 0"
            else case op of
                Div _ -> return $ Int $ x `div` y
                Mod _ -> return $ Int $ x `mod` y

transExpr (EAdd a expr1 addop expr2) = do
    x <- evalToInt expr1
    y <- evalToInt expr2
    case addop of
        Plus _ -> return $ Int $ x + y
        Minus _ -> return $ Int $ x - y

transExpr (ERel a expr1 relop expr2) = liftM2 (\x -> \y -> Boolean (transRelOp relop x y)) (transExpr expr1) (transExpr expr2) 

transExpr (EAnd a expr1 expr2) = liftM2 (\x -> \y -> Boolean ((&&) x y)) (evalToBool expr1) (evalToBool expr2)

transExpr (EOr a expr1 expr2) = liftM2 (\x -> \y -> Boolean ((||) x y)) (evalToBool expr1) (evalToBool expr2)

transRelOp :: (Ord b, Eq b) => RelOp a -> b -> b -> Bool
transRelOp x = case x of
    LTH _ -> (<)
    LE _ -> (<=)
    GTH _ -> (>)
    GE _ -> (>=)
    EQU _ -> (==)
    NE _ -> (/=)


------------------------------------------------- Program ---------------------------------------------

getAFromProgram :: Program a -> a
getAFromProgram (Program a _) = a

transProgram :: Show a => Program a -> IO ()
transProgram program = do
    let a = getAFromProgram program
    outcome <- runStateT (runReaderT (runExceptT (transProgram_ program)) Map.empty) (Map.empty, 0, 0, (Int 0, a))
    case fst outcome of
        Left error -> putStrLn error
        Right () -> return ()

-- TODO: move checking main type to static type checking phase
transProgram_ :: Show a => Program a -> ERSIO () a
transProgram_ (Program a topdefs) = do
    env <- registerFuns topdefs
    local (\env' -> env) (transTopDefs topdefs)
    val <- local (\env' -> env) (transExpr (EApp a (Ident "main") []))
    case val of
        Int i -> do
            liftIO $ putStrLn $ "Main returned " ++ show i
        _ -> throwError $ string2error $ show a ++ ": main return value should be int"


-- TODO: wrap it in foldM maybe?
-- adds function names to the env (reserving locations), but doesn't change the store
registerFuns :: Show a => [TopDef a] -> ERSIO (Env a) a
registerFuns [] = ask
registerFuns (topdef:topdefs) = do
    env <- registerFun topdef
    local (\env' -> env) (registerFuns topdefs)

transTopDefs :: Show a => [TopDef a] -> ERSIO () a
transTopDefs [] = return ()
transTopDefs (topdef:topdefs) = transTopDef topdef >> transTopDefs topdefs
