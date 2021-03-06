-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParGrammar where
import AbsGrammar
import LexGrammar
import ErrM

}

-- no lexer declaration
%monad { Err } { thenM } { returnM }
%tokentype {Token}
%name pProgram_internal Program
%token
  '!' { PT _ (TS _ 1) }
  '!=' { PT _ (TS _ 2) }
  '%' { PT _ (TS _ 3) }
  '&' { PT _ (TS _ 4) }
  '&&' { PT _ (TS _ 5) }
  '(' { PT _ (TS _ 6) }
  ')' { PT _ (TS _ 7) }
  '*' { PT _ (TS _ 8) }
  '+' { PT _ (TS _ 9) }
  ',' { PT _ (TS _ 10) }
  '-' { PT _ (TS _ 11) }
  '/' { PT _ (TS _ 12) }
  ';' { PT _ (TS _ 13) }
  '<' { PT _ (TS _ 14) }
  '<=' { PT _ (TS _ 15) }
  '=' { PT _ (TS _ 16) }
  '==' { PT _ (TS _ 17) }
  '>' { PT _ (TS _ 18) }
  '>=' { PT _ (TS _ 19) }
  'Tuple' { PT _ (TS _ 20) }
  '[' { PT _ (TS _ 21) }
  ']' { PT _ (TS _ 22) }
  'bool' { PT _ (TS _ 23) }
  'break' { PT _ (TS _ 24) }
  'continue' { PT _ (TS _ 25) }
  'else' { PT _ (TS _ 26) }
  'false' { PT _ (TS _ 27) }
  'if' { PT _ (TS _ 28) }
  'int' { PT _ (TS _ 29) }
  'return' { PT _ (TS _ 30) }
  'string' { PT _ (TS _ 31) }
  'true' { PT _ (TS _ 32) }
  'while' { PT _ (TS _ 33) }
  '{' { PT _ (TS _ 34) }
  '||' { PT _ (TS _ 35) }
  '}' { PT _ (TS _ 36) }

  L_ident {PT _ (TV _)}
  L_integ {PT _ (TI _)}
  L_quoted {PT _ (TL _)}

%%

Ident :: {
  (Maybe (Int, Int), Ident)
}
: L_ident {
  (Just (tokenLineCol $1), Ident (prToken $1)) 
}

Integer :: {
  (Maybe (Int, Int), Integer)
}
: L_integ {
  (Just (tokenLineCol $1), read (prToken $1)) 
}

String :: {
  (Maybe (Int, Int), String)
}
: L_quoted {
  (Just (tokenLineCol $1), prToken $1)
}

Program :: {
  (Maybe (Int, Int), Program (Maybe (Int, Int)))
}
: ListTopDef {
  (fst $1, AbsGrammar.Program (fst $1)(snd $1)) 
}

ListTopDef :: {
  (Maybe (Int, Int), [TopDef (Maybe (Int, Int))]) 
}
: TopDef {
  (fst $1, (:[]) (snd $1)) 
}
| TopDef ListTopDef {
  (fst $1, (:) (snd $1)(snd $2)) 
}

TopDef :: {
  (Maybe (Int, Int), TopDef (Maybe (Int, Int)))
}
: Type Ident '(' ListArg ')' Block {
  (fst $1, AbsGrammar.FnDef (fst $1)(snd $1)(snd $2)(snd $4)(snd $6)) 
}

ListArg :: {
  (Maybe (Int, Int), [Arg (Maybe (Int, Int))]) 
}
: {
  (Nothing, [])
}
| Arg {
  (fst $1, (:[]) (snd $1)) 
}
| Arg ',' ListArg {
  (fst $1, (:) (snd $1)(snd $3)) 
}

Arg :: {
  (Maybe (Int, Int), Arg (Maybe (Int, Int)))
}
: Type Ident {
  (fst $1, AbsGrammar.Arg (fst $1)(snd $1)(snd $2)) 
}

Block :: {
  (Maybe (Int, Int), Block (Maybe (Int, Int)))
}
: '{' ListStmt '}' {
  (Just (tokenLineCol $1), AbsGrammar.Block (Just (tokenLineCol $1)) (reverse (snd $2)))
}

ListStmt :: {
  (Maybe (Int, Int), [Stmt (Maybe (Int, Int))]) 
}
: {
  (Nothing, [])
}
| ListStmt Stmt {
  (fst $1, flip (:) (snd $1)(snd $2)) 
}

Stmt :: {
  (Maybe (Int, Int), Stmt (Maybe (Int, Int)))
}
: ';' {
  (Just (tokenLineCol $1), AbsGrammar.Empty (Just (tokenLineCol $1)))
}
| Block {
  (fst $1, AbsGrammar.BStmt (fst $1)(snd $1)) 
}
| 'break' ';' {
  (Just (tokenLineCol $1), AbsGrammar.Break (Just (tokenLineCol $1)))
}
| 'continue' ';' {
  (Just (tokenLineCol $1), AbsGrammar.Continue (Just (tokenLineCol $1)))
}
| Type ListItem ';' {
  (fst $1, AbsGrammar.Decl (fst $1)(snd $1)(snd $2)) 
}
| '<' ItemQ '>' '=' Expr ';' {
  (Just (tokenLineCol $1), AbsGrammar.Unpack (Just (tokenLineCol $1)) (snd $2)(snd $5)) 
}
| Final '=' Expr ';' {
  (fst $1, AbsGrammar.Ass (fst $1)(snd $1)(snd $3)) 
}
| TopDef {
  (fst $1, AbsGrammar.FunDef (fst $1)(snd $1)) 
}
| 'return' Expr ';' {
  (Just (tokenLineCol $1), AbsGrammar.Ret (Just (tokenLineCol $1)) (snd $2)) 
}
| 'if' '(' Expr ')' Stmt {
  (Just (tokenLineCol $1), AbsGrammar.Cond (Just (tokenLineCol $1)) (snd $3)(snd $5)) 
}
| 'if' '(' Expr ')' Stmt 'else' Stmt {
  (Just (tokenLineCol $1), AbsGrammar.CondElse (Just (tokenLineCol $1)) (snd $3)(snd $5)(snd $7)) 
}
| 'while' '(' Expr ')' Stmt {
  (Just (tokenLineCol $1), AbsGrammar.While (Just (tokenLineCol $1)) (snd $3)(snd $5)) 
}
| Expr ';' {
  (fst $1, AbsGrammar.SExp (fst $1)(snd $1)) 
}

Item :: {
  (Maybe (Int, Int), Item (Maybe (Int, Int)))
}
: Ident '=' Expr {
  (fst $1, AbsGrammar.Init (fst $1)(snd $1)(snd $3)) 
}

Final :: {
  (Maybe (Int, Int), Final (Maybe (Int, Int)))
}
: Ident {
  (fst $1, AbsGrammar.Final1 (fst $1)(snd $1)) 
}
| Final '{' Expr '}' {
  (fst $1, AbsGrammar.Final2 (fst $1)(snd $1)(snd $3)) 
}

ItemQ :: {
  (Maybe (Int, Int), ItemQ (Maybe (Int, Int)))
}
: Final {
  (fst $1, AbsGrammar.ItemQFinal (fst $1)(snd $1)) 
}
| '(' ListItemQ ')' {
  (Just (tokenLineCol $1), AbsGrammar.ItemQTuple (Just (tokenLineCol $1)) (snd $2)) 
}

ListItemQ :: {
  (Maybe (Int, Int), [ItemQ (Maybe (Int, Int))]) 
}
: ItemQ {
  (fst $1, (:[]) (snd $1)) 
}
| ItemQ ',' ListItemQ {
  (fst $1, (:) (snd $1)(snd $3)) 
}

ListItem :: {
  (Maybe (Int, Int), [Item (Maybe (Int, Int))]) 
}
: Item {
  (fst $1, (:[]) (snd $1)) 
}
| Item ',' ListItem {
  (fst $1, (:) (snd $1)(snd $3)) 
}

BaseType :: {
  (Maybe (Int, Int), BaseType (Maybe (Int, Int)))
}
: 'int' {
  (Just (tokenLineCol $1), AbsGrammar.IntT (Just (tokenLineCol $1)))
}
| 'string' {
  (Just (tokenLineCol $1), AbsGrammar.StrT (Just (tokenLineCol $1)))
}
| 'bool' {
  (Just (tokenLineCol $1), AbsGrammar.BooleanT (Just (tokenLineCol $1)))
}

Type :: {
  (Maybe (Int, Int), Type (Maybe (Int, Int)))
}
: BaseType {
  (fst $1, AbsGrammar.BaseT (fst $1)(snd $1)) 
}
| Type '[' ']' {
  (fst $1, AbsGrammar.ArrayT (fst $1)(snd $1)) 
}
| 'Tuple' '<' ListType '>' {
  (Just (tokenLineCol $1), AbsGrammar.TupleT (Just (tokenLineCol $1)) (snd $3)) 
}

ListType :: {
  (Maybe (Int, Int), [Type (Maybe (Int, Int))]) 
}
: Type {
  (fst $1, (:[]) (snd $1)) 
}
| Type ',' ListType {
  (fst $1, (:) (snd $1)(snd $3)) 
}

Expr6 :: {
  (Maybe (Int, Int), Expr (Maybe (Int, Int)))
}
: Ident {
  (fst $1, AbsGrammar.EVar (fst $1)(snd $1)) 
}
| Integer {
  (fst $1, AbsGrammar.ELitInt (fst $1)(snd $1)) 
}
| 'true' {
  (Just (tokenLineCol $1), AbsGrammar.ELitTrue (Just (tokenLineCol $1)))
}
| 'false' {
  (Just (tokenLineCol $1), AbsGrammar.ELitFalse (Just (tokenLineCol $1)))
}
| Ident '(' ListEArg ')' {
  (fst $1, AbsGrammar.EApp (fst $1)(snd $1)(snd $3)) 
}
| String {
  (fst $1, AbsGrammar.EString (fst $1)(snd $1)) 
}
| '(' Expr ',' ListExpr ')' {
  (Just (tokenLineCol $1), AbsGrammar.ETuple (Just (tokenLineCol $1)) (snd $2)(snd $4)) 
}
| '[' ListExpr ']' {
  (Just (tokenLineCol $1), AbsGrammar.EArray (Just (tokenLineCol $1)) (snd $2)) 
}
| Expr6 '[' Expr6 ']' {
  (fst $1, AbsGrammar.EGet (fst $1)(snd $1)(snd $3)) 
}
| '(' Expr ')' {
  (Just (tokenLineCol $1), snd $2)
}

ListEArg :: {
  (Maybe (Int, Int), [EArg (Maybe (Int, Int))]) 
}
: {
  (Nothing, [])
}
| EArg {
  (fst $1, (:[]) (snd $1)) 
}
| EArg ',' ListEArg {
  (fst $1, (:) (snd $1)(snd $3)) 
}

EArg :: {
  (Maybe (Int, Int), EArg (Maybe (Int, Int)))
}
: Expr {
  (fst $1, AbsGrammar.EArgE (fst $1)(snd $1)) 
}
| '&' Ident {
  (Just (tokenLineCol $1), AbsGrammar.EArgName (Just (tokenLineCol $1)) (snd $2)) 
}

ListExpr :: {
  (Maybe (Int, Int), [Expr (Maybe (Int, Int))]) 
}
: {
  (Nothing, [])
}
| Expr {
  (fst $1, (:[]) (snd $1)) 
}
| Expr ',' ListExpr {
  (fst $1, (:) (snd $1)(snd $3)) 
}

Expr5 :: {
  (Maybe (Int, Int), Expr (Maybe (Int, Int)))
}
: '-' Expr6 {
  (Just (tokenLineCol $1), AbsGrammar.Neg (Just (tokenLineCol $1)) (snd $2)) 
}
| '!' Expr6 {
  (Just (tokenLineCol $1), AbsGrammar.Not (Just (tokenLineCol $1)) (snd $2)) 
}
| Expr6 {
  (fst $1, snd $1)
}

Expr4 :: {
  (Maybe (Int, Int), Expr (Maybe (Int, Int)))
}
: Expr4 MulOp Expr5 {
  (fst $1, AbsGrammar.EMul (fst $1)(snd $1)(snd $2)(snd $3)) 
}
| Expr5 {
  (fst $1, snd $1)
}

Expr3 :: {
  (Maybe (Int, Int), Expr (Maybe (Int, Int)))
}
: Expr3 AddOp Expr4 {
  (fst $1, AbsGrammar.EAdd (fst $1)(snd $1)(snd $2)(snd $3)) 
}
| Expr4 {
  (fst $1, snd $1)
}

Expr2 :: {
  (Maybe (Int, Int), Expr (Maybe (Int, Int)))
}
: Expr2 RelOp Expr3 {
  (fst $1, AbsGrammar.ERel (fst $1)(snd $1)(snd $2)(snd $3)) 
}
| Expr3 {
  (fst $1, snd $1)
}

Expr1 :: {
  (Maybe (Int, Int), Expr (Maybe (Int, Int)))
}
: Expr2 '&&' Expr1 {
  (fst $1, AbsGrammar.EAnd (fst $1)(snd $1)(snd $3)) 
}
| Expr2 {
  (fst $1, snd $1)
}

Expr :: {
  (Maybe (Int, Int), Expr (Maybe (Int, Int)))
}
: Expr1 '||' Expr {
  (fst $1, AbsGrammar.EOr (fst $1)(snd $1)(snd $3)) 
}
| Expr1 {
  (fst $1, snd $1)
}

AddOp :: {
  (Maybe (Int, Int), AddOp (Maybe (Int, Int)))
}
: '+' {
  (Just (tokenLineCol $1), AbsGrammar.Plus (Just (tokenLineCol $1)))
}
| '-' {
  (Just (tokenLineCol $1), AbsGrammar.Minus (Just (tokenLineCol $1)))
}

MulOp :: {
  (Maybe (Int, Int), MulOp (Maybe (Int, Int)))
}
: '*' {
  (Just (tokenLineCol $1), AbsGrammar.Times (Just (tokenLineCol $1)))
}
| '/' {
  (Just (tokenLineCol $1), AbsGrammar.Div (Just (tokenLineCol $1)))
}
| '%' {
  (Just (tokenLineCol $1), AbsGrammar.Mod (Just (tokenLineCol $1)))
}

RelOp :: {
  (Maybe (Int, Int), RelOp (Maybe (Int, Int)))
}
: '<' {
  (Just (tokenLineCol $1), AbsGrammar.LTH (Just (tokenLineCol $1)))
}
| '<=' {
  (Just (tokenLineCol $1), AbsGrammar.LE (Just (tokenLineCol $1)))
}
| '>' {
  (Just (tokenLineCol $1), AbsGrammar.GTH (Just (tokenLineCol $1)))
}
| '>=' {
  (Just (tokenLineCol $1), AbsGrammar.GE (Just (tokenLineCol $1)))
}
| '==' {
  (Just (tokenLineCol $1), AbsGrammar.EQU (Just (tokenLineCol $1)))
}
| '!=' {
  (Just (tokenLineCol $1), AbsGrammar.NE (Just (tokenLineCol $1)))
}

{

returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    t:_ -> " before `" ++ id(prToken t) ++ "'"

myLexer = tokens

pProgram = (>>= return . snd) . pProgram_internal
}

