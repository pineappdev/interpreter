module AbsGrammar where
import Data.List(intersperse)
-- Haskell module generated by the BNF converter




newtype Ident = Ident String deriving (Eq, Ord, Read)
data Program a = Program a [TopDef a]
    deriving (Eq, Ord, Show, Read)

instance Show Ident where
    show (Ident str) = str

instance Functor Program where
    fmap f x = case x of
        Program a topdefs -> Program (f a) (map (fmap f) topdefs)

data TopDef a = FnDef a (Type a) Ident [Arg a] (Block a)
    deriving (Eq, Ord, Show, Read)

instance Functor TopDef where
    fmap f x = case x of
        FnDef a type_ ident args block -> FnDef (f a) (fmap f type_) ident (map (fmap f) args) (fmap f block)

data Arg a = Arg a (Type a) Ident
    deriving (Eq, Ord, Read, Show)

instance Functor Arg where
    fmap f x = case x of
        Arg a type_ ident -> Arg (f a) (fmap f type_) ident

data Block a = Block a [Stmt a]
    deriving (Eq, Ord, Show, Read)

instance Functor Block where
    fmap f x = case x of
        Block a stmts -> Block (f a) (map (fmap f) stmts)

data Stmt a
    = Empty a
    | BStmt a (Block a)
    | Break a
    | Continue a
    | Decl a (Type a) [Item a]
    | FunDef a (TopDef a)
    | Ass a Ident (Expr a)
    | Ret a (Expr a)
    | Cond a (Expr a) (Stmt a)
    | CondElse a (Expr a) (Stmt a) (Stmt a)
    | While a (Expr a) (Stmt a)
    | SExp a (Expr a)
    deriving (Eq, Ord, Show, Read)

instance Functor Stmt where
    fmap f x = case x of
        Empty a -> Empty (f a)
        BStmt a block -> BStmt (f a) (fmap f block)
        Break a -> Break (f a)
        Continue a -> Continue (f a)
        Decl a type_ items -> Decl (f a) (fmap f type_) (map (fmap f) items)
        FunDef a topdef -> FunDef (f a) (fmap f topdef)
        Ass a ident expr -> Ass (f a) ident (fmap f expr)
        Ret a expr -> Ret (f a) (fmap f expr)
        Cond a expr stmt -> Cond (f a) (fmap f expr) (fmap f stmt)
        CondElse a expr stmt1 stmt2 -> CondElse (f a) (fmap f expr) (fmap f stmt1) (fmap f stmt2)
        While a expr stmt -> While (f a) (fmap f expr) (fmap f stmt)
        SExp a expr -> SExp (f a) (fmap f expr)

data Item a = Init a Ident (Expr a)
    deriving (Eq, Ord, Show, Read)

instance Functor Item where
    fmap f x = case x of
        Init a ident expr -> Init (f a) ident (fmap f expr)

data BaseType a = IntT a | StrT a | BooleanT a
    deriving (Eq, Ord, Show, Read)

instance Functor BaseType where
    fmap f x = case x of
        IntT a -> IntT (f a)
        StrT a -> StrT (f a)
        BooleanT a -> BooleanT (f a)

data Type a
    = BaseT a (BaseType a) | ArrayT a (BaseType a) | TupleT a [Type a]
  deriving (Eq, Ord, Show, Read)

instance Functor Type where
    fmap f x = case x of
        BaseT a basetype -> BaseT (f a) (fmap f basetype)
        ArrayT a basetype -> ArrayT (f a) (fmap f basetype)
        TupleT a types -> TupleT (f a) (map (fmap f) types)
data EArg a = EArgE a (Expr a) | EArgName a Ident
    deriving (Eq, Ord, Show, Read)

instance Functor EArg where
    fmap f x = case x of
        EArgE a expr -> EArgE (f a) (fmap f expr)
        EArgName a ident -> EArgName (f a) ident

data Expr a
    = EVar a Ident
    | ELitInt a Integer
    | ELitTrue a
    | ELitFalse a
    | EApp a Ident [EArg a]
    | EString a String
    | ETuple a [Expr a]
    | EArray a
    | Neg a (Expr a)
    | Not a (Expr a)
    | EMul a (Expr a) (MulOp a) (Expr a)
    | EAdd a (Expr a) (AddOp a) (Expr a)
    | ERel a (Expr a) (RelOp a) (Expr a)
    | EAnd a (Expr a) (Expr a)
    | EOr a (Expr a) (Expr a)
  deriving (Eq, Ord, Show, Read)

instance Functor Expr where
    fmap f x = case x of
        EVar a ident -> EVar (f a) ident
        ELitInt a integer -> ELitInt (f a) integer
        ELitTrue a -> ELitTrue (f a)
        ELitFalse a -> ELitFalse (f a)
        EApp a ident eargs -> EApp (f a) ident (map (fmap f) eargs)
        EString a string -> EString (f a) string
        ETuple a exprs -> ETuple (f a) (map (fmap f) exprs)
        EArray a -> EArray (f a)
        Neg a expr -> Neg (f a) (fmap f expr)
        Not a expr -> Not (f a) (fmap f expr)
        EMul a expr1 mulop expr2 -> EMul (f a) (fmap f expr1) (fmap f mulop) (fmap f expr2)
        EAdd a expr1 addop expr2 -> EAdd (f a) (fmap f expr1) (fmap f addop) (fmap f expr2)
        ERel a expr1 relop expr2 -> ERel (f a) (fmap f expr1) (fmap f relop) (fmap f expr2)
        EAnd a expr1 expr2 -> EAnd (f a) (fmap f expr1) (fmap f expr2)
        EOr a expr1 expr2 -> EOr (f a) (fmap f expr1) (fmap f expr2)

data AddOp a = Plus a | Minus a
  deriving (Eq, Ord, Show, Read)

instance Functor AddOp where
    fmap f x = case x of
        Plus a -> Plus (f a)
        Minus a -> Minus (f a)

data MulOp a = Times a | Div a | Mod a
  deriving (Eq, Ord, Show, Read)

instance Functor MulOp where
    fmap f x = case x of
        Times a -> Times (f a)
        Div a -> Div (f a)
        Mod a -> Mod (f a)

data RelOp a = LTH a | LE a | GTH a | GE a | EQU a | NE a
    deriving (Eq, Ord, Show, Read)

instance Functor RelOp where
    fmap f x = case x of
        LTH a -> LTH (f a)
        LE a -> LE (f a)
        GTH a -> GTH (f a)
        GE a -> GE (f a)
        EQU a -> EQU (f a)
        NE a -> NE (f a)