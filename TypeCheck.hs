module TypeCheck where
import PureVal
import AbsGrammar
import qualified Data.Map as Map
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Set as Set -- From the 'containers' library

hasDuplicates :: (Ord a) => [a] -> Bool
hasDuplicates list = length list /= length set
    where set = Set.fromList list


keyfuns = ["print"]

data FunType a = Fun PureType a [(PureType, a)]

data Typee a = PureType a PureType | FunType (FunType a)

type TEnv a = Map.Map Ident (Typee a)

-- first flag - whether we're in a loop
-- second flag - return type of the function we are currently in
-- and the place where it was defined
type Flags a = (Bool, (PureType, a))

type Env a = (TEnv a, Flags a)

type ER res_type a = ExceptT ErrorType (Reader (Env a)) res_type

insertFunRetTypeToEnv :: PureType -> a -> ER (Env a) a
insertFunRetTypeToEnv ptype a = do
    (env, (b, (ptype', a'))) <- ask
    return (env, (b, (ptype, a)))

insertPureTypeToEnv :: Ident -> a -> PureType -> ER (Env a) a
insertPureTypeToEnv x a ptype = do
    (env, flags) <- ask
    return (Map.insert x (PureType a ptype) env, flags)

insertFunTypeToEnv :: Ident -> FunType a -> ER (Env a) a
insertFunTypeToEnv x ftype = do
    (env, flags) <- ask
    return (Map.insert x (FunType ftype) env, flags)

-- type ERS res_type a = ExceptT ErrorType (ReaderT (Env a) (State (Bool))) res_type

-- TODO: shouldn't we store flags in State?
loopFlag :: ER (Env a) a
loopFlag = do
    (tenv, (flag, x)) <- ask
    return (tenv, (True, x))

whetherInLoop :: ER Bool a
whetherInLoop = do
    (_, (flag, _)) <- ask
    return flag

getCurFuncType :: ER (PureType, a) a
getCurFuncType = do
    (_, (_, x)) <- ask
    return x

getPureType :: Show a => a -> Ident -> ER (PureType, a) a
getPureType a x = do
    (env, _) <- ask
    case Map.lookup x env of
        Nothing -> throwError $ show a ++ ": " ++ show x ++ " is undefined" 
        Just y -> case y of
            PureType a ptype -> return (ptype, a)
            other -> throwError $ show a ++ ": " ++ show x ++ " is a function"

getFunType :: Show a => a -> Ident -> ER (FunType a) a
getFunType a x = do
    (env, _) <- ask
    case Map.lookup x env of
        Nothing -> throwError $ show a ++ ": " ++ show x ++ " is undefined"
        Just y -> case y of
            FunType f -> return f
            other -> throwError $ show a ++ ": " ++ show x ++ " is not a function"

type ErrorType = String

string2error :: String -> ErrorType
string2error = id

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
    EGet a _ _ -> a

getAFromEArg :: Show a => EArg a -> a
getAFromEArg (EArgE a _) = a
getAFromEArg (EArgName a _) = a

typeCheckTo :: Show a => PureType -> Expr a -> ER PureType a
typeCheckTo ptype expr = do
    type_ <- typeCheckExpr expr
    if type_ /= ptype
        then throwError $ string2error $ show (getAFromExpr expr) ++ ": expected " ++ show ptype ++
            ", but got " ++ show type_
        else return ptype

-- provided list must have length >= 1
-- compares all types in given list
-- if not equal, returns Nothing
-- otherwise returns the best representative of them (the least polymorphic type)
compAndGetBestPType :: [PureType] -> Maybe PureType
compAndGetBestPType (ptype:[]) = Just ptype
compAndGetBestPType (ptype1:ptype2:ptypes) =
    if ptype1 /= ptype2
        then Nothing
        else compAndGetBestPType (best:ptypes)
            where best = chooseBestRepresentative (ptype1, ptype2)

-- assumes, that given types are already equal
-- chooses the type with most information gain
-- e.g. choosemostRepresentative (TArray Int, TEmptyArray) will return TArray Int, as TEmptyArray is more polymorphic
-- no guarantee, that return type will not be polymorphic - e.g. TEmptyArray, TEmptyArray -> TEmptyArray
chooseBestRepresentative :: (PureType, PureType) -> PureType
chooseBestRepresentative x = case x of
    (TInt, _) -> TInt
    (TStr, _) -> TStr
    (TBoolean, _) -> TBoolean
    (TArray pt1, TArray pt2) -> TArray (chooseBestRepresentative (pt1, pt2))
    (x, TEmptyArray) -> x
    (TEmptyArray, x) -> x
    (TTuple pts1, TTuple pts2) -> TTuple (map chooseBestRepresentative (zip pts1 pts2))


typeCheckEArg :: Show a => EArg a -> ER PureType a
typeCheckEArg earg = case earg of
    EArgE a expr -> typeCheckExpr expr
    EArgName a name -> do
        (ptype, _) <- getPureType a name
        return ptype


getAFromFinal :: Final a -> a
getAFromFinal f = case f of
    Final1 a _ -> a
    Final2 a _ _ -> a

-- data Final a = Final1 a Ident | Final2 a (Final a) (Expr a)
-- evaluates Final to PureType
-- e.g. evalFinal (x {2} {3} {4}) -> type of x[2][3][4] (or error)
evalFinal :: Show a => Final a -> ER PureType a
evalFinal f = case f of
    Final1 a x -> do
        (ptype, _) <- getPureType a x
        return ptype
    Final2 a f expr -> do
        ptype <- evalFinal f
        typeCheckTo TInt expr
        case ptype of
            TArray ptype -> return ptype
            other -> throwError $ string2error $ show (getAFromFinal f) ++ ": " ++ show other
                ++ " is not an array, cannot be indexed\n"
                ++ "\tdid you overuse nested array indexing? (e.g. int [] x = [0]; x{0}{1}{2}{3}{4} = 3;"

typeCheckExpr :: Show a => Expr a -> ER PureType a

typeCheckExpr (EGet a expr1 expr2) = do
    typeCheckTo TInt expr2
    type1 <- typeCheckExpr expr1
    case type1 of
        TArray ptype -> return ptype
        TTuple _ -> throwError $ string2error $ show (getAFromExpr expr1) ++ ": tuple indexing is against static typing, please don't do this" 
        other -> throwError $ string2error $ show (getAFromExpr expr1) ++ ": indexing works only on arrays, got " ++ show type1

typeCheckExpr (EArray a exprs) = do
    if null exprs
        then return TEmptyArray
        else do
            types <- mapM typeCheckExpr exprs
            case compAndGetBestPType types of
                Nothing -> throwError $ string2error $ show a ++ ": all values in an array must have the same type"
                Just type_ -> return $ TArray type_


typeCheckExpr (EVar a x) = do
    (type_, a_def) <- getPureType a x
    return type_

typeCheckExpr (ELitInt _ i) = return TInt

typeCheckExpr (ELitTrue _) = return TBoolean

typeCheckExpr (ELitFalse _) = return TBoolean

typeCheckExpr (EApp a ident eargs) = let x = ident2String ident in do
    earg_types_ <- mapM typeCheckEArg eargs
    -- TODO: check if Haskell laziness doesn't prevent us from checking earg types
    let earg_types = zip earg_types_ (map getAFromEArg eargs)
    if elem x keyfuns
        then do
            case x of
                -- TODO: check types of eargs!!!!
                "print" -> return TInt
                -- "set" -> transSet a eargs
        else do
            fun <- getFunType a ident
            case fun of
                -- (PureType [(PureType, a)], a')
                Fun ret_type a' arg_types -> do
                    _ <- mapM (\(a, b) -> compare a b) (zip arg_types earg_types)
                    return ret_type
                where
                    compare :: Show a => (PureType, a) -> (PureType, a) -> ER () a
                    compare (ptype1, aa) (ptype2, ea) =
                        if ptype1 /= ptype2
                            then throwError $ string2error $ show ea ++ ": expected " ++ show ptype1
                                ++ " as declared in " ++ show aa ++ ", but got " ++ show ptype2
                            else return ()


typeCheckExpr (EString a string) = return TStr

typeCheckExpr (ETuple a expr exprs) = liftM TTuple (mapM typeCheckExpr (expr:exprs))

-- typeCheckTo :: Show a => PureType -> Expr a -> ER () a
typeCheckExpr (Neg a expr) = typeCheckTo TInt expr

typeCheckExpr (Not a expr) = typeCheckTo TBoolean expr

typeCheckExpr (EMul a expr1 mulop expr2) = do
    typeCheckTo TInt expr1
    typeCheckTo TInt expr2

typeCheckExpr (EAdd a expr1 addop expr2) = do
    typeCheckTo TInt expr1
    typeCheckTo TInt expr2

typeCheckExpr (ERel a expr1 relop expr2) = do
    type1 <- typeCheckExpr expr1
    typeCheckTo type1 expr2
    if isOrdOp relop
        then
            if isOrderable type1
                then return TBoolean
                else throwError $ string2error $ show a
                    ++ ": type " ++ show type1 ++ " is not orderable"
        else
            return TBoolean


typeCheckExpr (EAnd a expr1 expr2) = do
    typeCheckTo TBoolean expr1
    typeCheckTo TBoolean expr2

typeCheckExpr (EOr a expr1 expr2) = do
    typeCheckTo TBoolean expr1
    typeCheckTo TBoolean expr2


isOrdOp :: RelOp a -> Bool
isOrdOp x = case x of
    EQU a -> False
    NE a -> False
    _ -> True











typeCheckItemQ :: Show a => ItemQ a -> ER PureType a
typeCheckItemQ (ItemQFinal a final) = evalFinal final
typeCheckItemQ (ItemQTuple _ itemqs) = liftM TTuple (mapM typeCheckItemQ itemqs)

-- flag - if stmt will return under any circumstances
typeCheckStmt :: Show a => Stmt a -> ER Bool a

typeCheckStmt (Ass a final expr) = do
    type_expr <- typeCheckExpr expr
    type_left <- evalFinal final
    if type_left /= type_expr
        then throwError $ string2error $ show (getAFromExpr expr) ++ ": type error: expected " ++ show type_left ++ ", but got " ++ show type_expr
        else return False

typeCheckStmt (Break a) = do
    in_loop <- whetherInLoop
    if not in_loop
        then throwError $ string2error $ show a ++ ": error: break outside of a loop"
        else return False

typeCheckStmt (Continue a) = do
    in_loop <- whetherInLoop
    if not in_loop
        then throwError $ string2error $ show a ++ ": error: continue outside of a loop"
        else return False

typeCheckStmt (Ret a expr) = do
    type_expr <- typeCheckExpr expr
    (ret_type, fun_place) <- getCurFuncType
    if type_expr /= ret_type
        then throwError $ string2error $ show a ++ ": type error: expected "
            ++ show ret_type ++ " as declared at " ++ show fun_place ++ "but got " ++ show type_expr
        else
            return True

typeCheckStmt (Empty a) = return False

-- data ItemQ a = ItemQIdent a Ident | ItemQTuple a [ItemQ a]

-- TODO: we could show exact location when the error happens...
typeCheckStmt (Unpack a itemq expr) = do
    type_expr <- typeCheckExpr expr
    type_itemqs <- typeCheckItemQ itemq
    if type_expr /= type_itemqs
        then throwError $ string2error $ show a ++ ": type error: r-expr is of type "
            ++ show type_expr ++ ", but unpack template has type: " ++ show type_itemqs
        else return False


typeCheckStmt (Cond _ expr stmt) = do
    typeCheckTo TBoolean expr
    typeCheckStmt stmt

typeCheckStmt (CondElse _ expr stmt1 stmt2) = do
    typeCheckTo TBoolean expr
    liftM2 (&&) (typeCheckStmt stmt1) (typeCheckStmt stmt2)

typeCheckStmt (While _ expr stmt) = do
    typeCheckTo TBoolean expr
    env' <- loopFlag
    local (\env -> env') (typeCheckStmt stmt)

typeCheckStmt (SExp _ expr) = typeCheckExpr expr >> return False

typeCheckStmt (BStmt a (Block a' [])) = return False

typeCheckStmt (BStmt a (Block a' (stmt:stmts))) = do
    case stmt of
        Decl a'' type_ items -> do
            env <- typeCheckDecl (Decl a'' type_ items)
            local (\env' -> env) (typeCheckStmt (BStmt a (Block a' stmts)))
        FunDef a'' topdef -> do
            env <- typeCheckTopDef (topdef)
            local (\env' -> env) (typeCheckStmt (BStmt a (Block a' stmts)))
        -- TODO: Haskell's laziness can cause him to avoid evaluating stmts entirely, right?
        -- return 2; "qwe" + 2
        other -> liftM2 (||) (typeCheckStmt stmt) (typeCheckStmt (BStmt a (Block a' stmts)))


typeCheckItem :: Show a => PureType -> Item a -> ER (Env a) a
typeCheckItem ptype (Init a x expr) = do
    typeCheckTo ptype expr
    insertPureTypeToEnv x a ptype

typeCheckItems :: Show a => PureType -> [Item a] -> ER (Env a) a
typeCheckItems ptype [] = ask
typeCheckItems ptype (item:items) = do
    env <- typeCheckItem ptype item
    local (\env' -> env) (typeCheckItems ptype items)

typeCheckDecl :: Show a => Stmt a -> ER (Env a) a
typeCheckDecl (Decl a'' type_ items) = do
    let ptype = type2PureType type_
    typeCheckItems ptype items

getAFromArg :: Arg a -> a
getAFromArg (Arg a _ _) = a

arg2Ident :: Arg a -> Ident
arg2Ident (Arg _ _ x) = x

arg2Type :: Arg a -> Type a
arg2Type (Arg _ type_ _) = type_

checkForDuplicateIdents :: Show a => a -> [Arg a] -> ER () a
checkForDuplicateIdents a args = do
    if hasDuplicates $ map arg2Ident args
        then throwError $ string2error $ show a ++ ": function arguments must have different names"
        else return ()

evalArg :: Show a => Arg a -> ER (Env a) a
evalArg (Arg a type_ x) = do
    let ptype = type2PureType type_
    env <- insertPureTypeToEnv x a ptype
    return env

evalArgs :: Show a => [Arg a] -> ER (Env a) a
evalArgs [] = ask
evalArgs (arg:args) = do
    env <- evalArg arg
    local (\env' -> env) (evalArgs args)

-- TODO: register all functions before type checking
typeCheckTopDef :: Show a => TopDef a -> ER (Env a) a
typeCheckTopDef (FnDef a type_ f args block) = do
    if elem (ident2String f) keyfuns
        then do
            throwError $ string2error $ show a ++ ": illegal function definition: " ++ show f ++ " is a restricted keyword"
        else do
            checkForDuplicateIdents a args
            let ptypes = zip (map (type2PureType . arg2Type) args) (map getAFromArg args)
            let fun = Fun (type2PureType type_) a ptypes
            env <- insertFunTypeToEnv f fun
            env' <- local (\_ -> env) (evalArgs args)
            env_block <- local (\_ -> env') (insertFunRetTypeToEnv (type2PureType type_) a)
            does_ret <- local (\_ -> env_block) (typeCheckStmt (BStmt a block))
            if not does_ret
                then do
                    throwError $ string2error $ show a ++ ": no return in function " ++ show f
                else
                    return env


-- change the env (adding function ident and type to it)
-- but don't type check the function's body
registerFun :: Show a => TopDef a -> ER (Env a) a
registerFun (FnDef a type_ f args block) = let x = ident2String f in do
    let ptypes = zip (map (type2PureType . arg2Type) args) (map getAFromArg args)
    let fun = Fun (type2PureType type_) a ptypes
    env <- insertFunTypeToEnv f fun
    return env

registerFuns :: Show a => [TopDef a] -> ER (Env a) a
registerFuns [] = ask
registerFuns (topdef:topdefs) = do
    env <- registerFun topdef
    local (\env' -> env) (registerFuns topdefs)

typeCheckProgram :: Show a => Program a -> ER () a
typeCheckProgram (Program a topdefs) = do
    env <- registerFuns topdefs
    local (\_ -> env) (mapM typeCheckTopDef topdefs)
    return ()

-- transStmt (BStmt a (Block a' stmts)) = do
    -- liftM (null . (filter id)) (mapM transStmt stmts)

checkType :: Show a => Program a -> IO Bool
checkType (Program a topdefs) =
    let outcome = runReader (runExceptT (typeCheckProgram (Program a topdefs))) (Map.empty, (False, (TInt, a))) in
    case outcome of
        Left error -> putStrLn error >> return False
        Right () -> return True

