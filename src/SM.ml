open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval _ = failwith "Not Implemented Yet"
let rec eval'' env cfg ins =
  let rec eval' cfg ins = match cfg, ins with
    | _, [] -> cfg
    | (l, (s, i::input, output)), READ::ins -> eval' (i::l, (s, input, output)) ins
    | _, READ::_ -> failwith "Input is empty, cannot read from it"
    | (i::l, (s, input, output)), WRITE::ins -> eval' (l, (s, input, output @ [i])) ins
    | _, WRITE::_ -> failwith "Stack is empty, cannot write from it"
    | (l, (s, i, o)), (LD name)::ins -> eval' ((s name)::l, (s, i, o)) ins
    | (i::l, (s, input, output)), (ST name)::ins -> eval' (l, (Expr.update name (i) s, input, output)) ins
    | _, (ST name)::_ -> failwith ("Cannot store variable " ^ name ^ ", stack is empty")
    | (l, cfg), (CONST v)::ins -> eval' (v::l, cfg) ins
    | (right::left::l, cfg), (BINOP op)::ins -> eval' ((performBinop op left right)::l, cfg) ins
    | _, (BINOP op)::ins -> failwith ("Cannot perform " ^ op ^ "; not enough values on stack")
    | cfg, (LABEL name)::ins -> eval' cfg ins
    | cfg, (JMP name)::ins -> eval' cfg (env#labeled name)
    | (c::l, (s, input, output)), (CJMP (cond, name))::ins -> 
      let op = match cond with "z" -> (=) | "nz" -> (<>) | _ -> failwith ("Unknown condition " ^ cond) in
      let nextIns = if (op c 0) then (env#labeled name) else ins in
      eval' cfg nextIns
    | _, (CJMP (cond, name))::_ -> failwith ("Cannot perform " ^ cond ^ " conditional jump; no condition value on stack")
  in eval' cfg ins


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
class labelGenerator =
 object (self)
   val counter = ref 0
   method nextLabel = let current = !counter in
     incr counter; Printf.sprintf "L%d" current
 end

let generator = new labelGenerator
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | e, Stmt.Seq (s1, s2)  -> compile (e, s1) @ compile (e, s2)
  | _, Stmt.Read x        -> [READ; ST x]
  | _, Stmt.Write e       -> expr e @ [WRITE]
  | _, Stmt.Assign (x, e) -> expr e @ [ST x]
  | _, Stmt.Skip          -> []
  | e, Stmt.If (c, t, e')  -> 
    let elseL = generator#nextLabel in 
    let exitL = generator#nextLabel in
    expr c 
    @ [CJMP ("z", elseL) ] 
    @ compile (e, t) 
    @ [JMP exitL; LABEL elseL]
    @ compile (e, e')
    @ [LABEL exitL]
  | e, Stmt.While (c, b) -> 
    let startL = generator#nextLabel in
    let exitL = generator#nextLabel in 
    [LABEL startL]
    @ expr c
    @ [CJMP ("z", exitL)]
    @ compile (e, b)
    @ [JMP startL; LABEL exitL]
  | e, Stmt.Repeat (b, c) -> 
    let startL = generator#nextLabel in
    [LABEL startL]
    @ compile (e, b)
    @ expr c
    @ [CJMP ("z", startL)]

