(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open Ostap
let intToBool i = if (i = 0) then false else true
let boolToInt b = if b then 1 else 0
let performBinop op left right = match op with
  | "+"   -> left + right
  | "-"   -> left - right
  | "*"   -> left * right
  | "/"   -> left / right
  | "%"   -> left mod right
  | "=="  -> boolToInt (left == right)
  | "!="  -> boolToInt (left != right)
  | ">"   -> boolToInt (left >  right)
  | ">="  -> boolToInt (left >= right)
  | "<"   -> boolToInt (left <  right)
  | "<="  -> boolToInt (left <= right)
  | "&&"  -> boolToInt ((intToBool left) && (intToBool right))
  | "!!"  -> boolToInt ((intToBool left) || (intToBool right))
  | _     -> failwith ("Unknown operation " ^ op)

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
     *)                                                       
    let rec eval s e =
      match e with
        | Const value -> value
        | Var name -> s name
        | Binop (op, l, r) -> performBinop op (eval s l) (eval s r)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)

    let makeBinop op l r = Binop (op, l, r)

    ostap (                                      
      expr:
        !(Util.expr
        (fun x -> x)
        [|
          `Lefta, [ostap ("!!"), makeBinop "!!"];
          `Lefta, [ostap ("&&"), makeBinop "&&"];
          `Nona, [ostap ("<="), makeBinop "<="; ostap ("<"), makeBinop "<"; ostap (">="), makeBinop ">="; ostap (">"), makeBinop ">"];
          `Nona, [ostap ("=="), makeBinop "=="; ostap ("!="), makeBinop "!="];
          `Lefta, [ ostap("+"), makeBinop "+"; ostap("-"), makeBinop "-"; ];
          `Lefta , [ostap ("*"), makeBinop "*"; ostap ("/"), makeBinop "/"; ostap ("%"), makeBinop "%"];
        |]
        primary
        );

      primary: x:IDENT { Var x } | x:DECIMAL { Const x } | -"(" expr -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (state, input, output) s =
      match s with
        | Read name -> ((Expr.update name (List.hd input) state), (List.tl input), output)
        | Write expr -> (state, input, output @ [Expr.eval state expr])
        | Assign(name, expr) -> ((Expr.update name (Expr.eval state expr) state), input, output)
        | Seq(l, r) -> eval (eval (state, input, output) l) r
        | Skip -> (state, input, output) 
        | If(c, t, e) -> let branch = if intToBool (Expr.eval state c) then t else e
          in eval (state, input, output) branch
        | While(c, b) -> 
          let toEval = if intToBool (Expr.eval state c) then Seq(b, While(c, b)) else Skip in 
          eval (state, input, output) toEval
        | Repeat(b, c) -> 
          let (state, input, output) as config = eval (state, input, output) b in
          let toEval = if intToBool (Expr.eval state c) then Repeat(b, c) else Skip in
          eval config toEval

    (* Statement parser *)
    ostap (
      assign: x:IDENT ":=" e:!(Expr.expr) { Assign (x, e) } ;
      read: "read" "(" x:IDENT ")" { Read x } ;
      write: "write" "(" e:!(Expr.expr) ")" { Write e } ;
      
      elseBlock: 
        "elif" e:!(Expr.expr) "then" b:parse next:elseBlock { If(e, b, next) }
      | "else" b:parse { b }
      | "elif" e:!(Expr.expr) "then" b:parse { If (e, b, Skip) };
      
      ifBlock: 
        "if" e:!(Expr.expr) "then" b:parse el:elseBlock "fi" { If (e, b, el) }
      | "if" e:!(Expr.expr) "then" b:parse "fi" { If (e, b, Skip )} ;

      whileBlock: 
        "while" e:!(Expr.expr) b:parse "od" { While (e, b) };

      repeatBlock:
        "repeat" b:parse "until" e:!(Expr.expr) { Repeat (b, e) }; 
        
      simple_stmt: assign | read | write | ifBlock | whileBlock | repeatBlock;
      parse: <s::ss> :
        !(Util.listBy)
        [ostap (";")]
        [simple_stmt]
        { List.fold_left (fun s ss -> Seq (s, ss)) s ss}
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
