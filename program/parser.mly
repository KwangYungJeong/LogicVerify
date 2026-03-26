%{
  open Utils.Lib 
%}

(* Token - Value *)
%token <string> IDENT
%token <int> NUMBER
%token <bool> BOOLEAN

(* Token - System and Keyboard Symbol *)
%token LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK 
%token SEMICOLON COLON COMMA 
%token EOF

(* Token - Other Symbol *)
%token FNOT IMPLY IFF AND OR EAND EOR
%token NEQ ENOT
%token LE GE LT GT EQ 
%token PLUS MINUS STAR SLASH MOD
%token ASSIGN DOT LENGTH

(* Token - Keyword *)
%token REQUIRES ENSURES RETURNS METHOD PREDICATE FUNCTION NEW
%token FORALL EXISTS
%token INT BOOL ARRAY VAR
%token INVARIANT DECREASE 
%token IF THEN ELSE WHILE RETURN BREAK SKIP

(* Priority *)
%right  IMPLY IFF
%left   OR 
%left   AND
%left   EAND EOR 
%right  FNOT 
%left   EQ NEQ 
%left   LT GT LE GE
%left   PLUS MINUS
%left   ENOT 
%left   STAR SLASH MOD
%right  UMINUS

(* Type of Pattern *)
%type   <Syntax.typ>          typ atyp
%type   <Syntax.exp>          exp
%type   <Syntax.lv>           lv
%type   <Syntax.fmla>         fmla
%type   <Syntax.inv>          inv
%type   <Syntax.rank option>  rank
%type   <Syntax.stmt>         stmt
%type   <Syntax.decl>         decl arg_decl
%type   <Syntax.decl list>    args
%type   <Syntax.mthd>         mthd_def 
%type   <Syntax.pred>         pred_def 
%type   <Syntax.pgm>          pgm

(* Entrancy of Pattern *)
%start  <Syntax.pgm>         start

%%

start:
  | p=pgm EOF                             { p }

typ:
  | ty=atyp                               { ty }
  | ARRAY LT ty=atyp GT                   { Syntax.T_arr ty }

atyp:
  | INT                                   { Syntax.T_int }
  | BOOL                                  { Syntax.T_bool }

exp:
  | LPAREN e1=exp RPAREN                  { e1 }
  | n1=NUMBER                             { Syntax.E_int n1 }
  | b1=BOOLEAN                            { Syntax.E_bool b1 }
  | l1=lv                                 { Syntax.E_lv l1 }
  | e1=exp PLUS e2=exp                    { Syntax.E_add (e1, e2) }
  | e1=exp MINUS e2=exp                   { Syntax.E_sub (e1, e2) }
  | e1=exp STAR e2=exp                    { Syntax.E_mul (e1, e2) }
  | e1=exp SLASH e2=exp                   { Syntax.E_div (e1, e2) }
  | e1=exp MOD e2=exp                     { Syntax.E_mod (e1, e2) }
  | e1=exp EAND e2=exp                    { Syntax.E_and (e1, e2) }
  | e1=exp EOR e2=exp                     { Syntax.E_or (e1, e2) }
  | MINUS e1=exp %prec UMINUS             { Syntax.E_neg e1 }
  | id1=IDENT DOT LENGTH                  { Syntax.E_len id1 }
  | ENOT e1=exp                           { Syntax.E_not e1 }
  | e1=exp EQ e2=exp                      { Syntax.E_cmp (Syntax.Eq, e1, e2) }
  | e1=exp NEQ e2=exp                     { Syntax.E_cmp (Syntax.Neq, e1, e2) }
  | e1=exp LT e2=exp                      { Syntax.E_cmp (Syntax.Lt, e1, e2) }
  | e1=exp GT e2=exp                      { Syntax.E_cmp (Syntax.Gt, e1, e2) }
  | e1=exp LE e2=exp                      { Syntax.E_cmp (Syntax.Le, e1, e2) }
  | e1=exp GE e2=exp                      { Syntax.E_cmp (Syntax.Ge, e1, e2) }
  | IF LPAREN e1=exp RPAREN THEN e2=exp ELSE e3=exp { Syntax.E_if (e1, e2, e3) }
  | fid=IDENT LPAREN args=separated_list(COMMA, exp) RPAREN
    {
      E_call (fid, args)
    }
  | NEW LBRACK e=exp RBRACK
    { Syntax.E_new e }
  
lv:
  | id=IDENT                              { Syntax.V_var id }
  | id=IDENT LBRACK e=exp RBRACK          { Syntax.V_arr (id, e) }

fmla:
  | LPAREN f=fmla RPAREN                  { f }
  | e=exp                                 { Syntax.F_exp e }
  | FNOT f=fmla                           { Syntax.F_not f }
  | f1=fmla AND f2=fmla                   { Syntax.F_and [f1; f2] }
  | f1=fmla OR f2=fmla                    { Syntax.F_or [f1; f2] }
  | f1=fmla IMPLY f2=fmla                 { Syntax.F_imply (f1, f2) }
  | f1=fmla IFF f2=fmla                   { Syntax.F_iff (f1, f2) }
  | FORALL xs=separated_nonempty_list(COMMA, IDENT) COLON COLON body=fmla   
    { 
      List.fold_right (fun x f ->
        Syntax.F_forall (x, None, f)
      ) xs body
    }
  | EXISTS xs=separated_nonempty_list(COMMA, IDENT) COLON COLON body=fmla   
    { 
      List.fold_right (fun x f ->
        Syntax.F_exists (x, None, f)
      ) xs body
    }

inv:
  | INVARIANT f=fmla                  
    { f }

rank:
  | DECREASE el1=separated_nonempty_list (COMMA, exp) 
    { Some el1 }
  |                                       
    { None }
    
stmt:
  | LBRACE RBRACE                         
    { Syntax.S_skip }

  | LBRACE sl1=nonempty_list (stmt) RBRACE 
    { Syntax.S_seq sl1 }

  | SKIP SEMICOLON                        
    { Syntax.S_skip }

  | v1=separated_nonempty_list(COMMA, lv) ASSIGN e2=separated_nonempty_list(COMMA, exp) SEMICOLON         
    { Syntax.S_assign (v1, e2) }

  | IF LPAREN e1=exp RPAREN s2=stmt ELSE s3=stmt 
    { Syntax.S_if (e1, s2, s3) }

  | IF LPAREN e1=exp RPAREN s2=stmt       
    { Syntax.S_if (e1, s2, Syntax.S_skip) }

  | WHILE LPAREN cond=exp RPAREN invs=list(inv) rank=rank body=stmt 
    { Syntax.S_while (invs, rank, cond, body) }

  | RETURN exps=separated_list(COMMA, exp) SEMICOLON               
    { Syntax.S_return exps }

  | BREAK SEMICOLON                       
    { Syntax.S_break }

args:
  | al1=separated_nonempty_list (COMMA, arg_decl) { al1 }

arg_decl:
  | id=IDENT COLON ty=typ                 { (ty, id, None) }

ensures:
  | ENSURES f=fmla  { f }

requires:
  | REQUIRES f=fmla  { f }

returns:
  | RETURNS LPAREN rvars=args RPAREN  { rvars }
  |                                   { [] }

mthd_def:
  | METHOD fid=IDENT LPAREN args=args RPAREN rvars=returns
      pre=list(requires) post=list(ensures) rank=rank 
      body=mbody
    { 
      Syntax.create_method (body |> snd)
          pre
          post
          rank
          rvars
          fid 
          args
          (body |> fst) 
    }

mbody:
  | LBRACE dl1=list(decl) sl1=list(stmt) RBRACE 
    { (dl1, Syntax.S_seq sl1) }

decl:
  | VAR id=IDENT COLON ty=typ SEMICOLON          { (ty, id, None) }
  | VAR id=IDENT COLON ty=typ ASSIGN e=exp SEMICOLON       { (ty, id, Some e) }

pred_def:
  | PREDICATE pid=IDENT LPAREN args=args RPAREN
    LBRACE
      fmla=fmla
    RBRACE 
    {
      Syntax.create_predicate pid args fmla 
    }

func_def:
  | FUNCTION fid=IDENT LPAREN args=args RPAREN COLON ret_ty=typ
  LBRACE
    body=exp
  RBRACE
  {
    Syntax.create_function fid args ret_ty body 
  }

global:
  | m=mthd_def { Syntax.Mthd m }
  | p=pred_def { Syntax.Pred p }
  | f=func_def { Syntax.Func f }

pgm:
  | globals=list(global) 
    { 
      Syntax.create_program (List.rev globals)
    }