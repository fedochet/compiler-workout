open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
*)                         
let rec oneStep cfg i =
  match cfg, i with
    | (l, (s, i::input, output)), READ -> (i::l, (s, input, output))
    | _, READ -> failwith "Input is empty, cannot read from it"
    | (i::l, (s, input, output)), WRITE -> (l, (s, input, output @ [i]))
    | _, WRITE -> failwith "Stack is empty, cannot write from it"
    | (l, (s, i, o)), LD name -> ((s name)::l, (s, i, o))
    | (i::l, (s, input, output)), ST name -> (l, (Expr.update name (i) s, input, output))
    | _, ST name -> failwith ("Cannot store variable " ^ name ^ ", stack is empty")
    | (l, cfg), CONST v -> (v::l, cfg)
    | (right::left::l, cfg), BINOP op -> ((performBinop op left right)::l, cfg)
    | _, BINOP op -> failwith ("Cannot perform " ^ op ^ "; not enough values on stack")

let rec eval cfg ins = List.fold_left oneStep cfg ins

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
