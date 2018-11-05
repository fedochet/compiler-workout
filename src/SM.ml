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
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
(* let rec eval env ((cstack, stack, ((st, i, o, r) as c)) as conf) prg = failwith "Not implemented" *)
let rec eval env cfg ins =
   let rec eval' cfg ins = begin 
    (* (match cfg with 
      | (_, (_::_ as l), _) -> begin List.iter (Printf.printf "%d\n") l end 
      | _ -> Printf.printf "%s\n" "empty") ; 
      Printf.printf "%s\n" "";  *)
    match cfg, ins with
    | _, [] -> cfg
    | (progs, l, (s, i::input, output, r)), READ::ins -> eval' (progs, i::l, (s, input, output, r)) ins
    | _, READ::_ -> failwith "Input is empty, cannot read from it"
    | (progs, i::l, (s, input, output, r)), WRITE::ins -> eval' (progs, l, (s, input, output @ [i], r)) ins
    | _, WRITE::_ -> failwith "Stack is empty, cannot write from it"
    | (progs, l, (s, i, o, r)), (LD name)::ins -> eval' (progs, (State.eval s name)::l, (s, i, o, r)) ins
    | (progs, i::l, (s, input, output, r)), (ST name)::ins -> eval' (progs, l, (State.update name (i) s, input, output, r)) ins
    | _, (ST name)::_ -> failwith ("Cannot store variable " ^ name ^ ", stack is empty")
    | (progs, l, cfg), (CONST v)::ins -> eval' (progs, v::l, cfg) ins
    | (progs, right::left::l, cfg), (BINOP op)::ins -> eval' (progs, (Expr.to_func op left right)::l, cfg) ins
    | _, (BINOP op)::ins -> failwith ("Cannot perform " ^ op ^ "; not enough values on stack")
    | cfg, (LABEL name)::ins -> eval' cfg ins
    | cfg, (JMP name)::ins -> eval' cfg (env#labeled name)
    | (progs, c::l, (s, input, output, r)), (CJMP (cond, name))::ins -> 
      let op = match cond with "z" -> (=) | "nz" -> (<>) | _ -> failwith ("Unknown condition " ^ cond) in
      let nextIns = if (op c 0) then (env#labeled name) else ins in
      eval' (progs, l, (s, input, output, r)) nextIns
    | _, (CJMP (cond, name))::_ -> failwith ("Cannot perform " ^ cond ^ " conditional jump; no condition value on stack")
    | (progs, l, (s, input, output, r)), (CALL name)::ins -> eval' ((ins, s)::progs, l, (s, input, output, r)) (env#labeled name)
    | (progs, l, (s, input, output, r)), (BEGIN (params, locals))::ins -> 
      let s' = State.enter s (params @ locals) in
      let (s'', l') = List.fold_left (fun (s, v::l) n -> (State.update n v s, l)) (s', l) params in 
      eval' (progs, l', (s'', input, output, r)) ins
    | cfg, END::[] -> cfg
    | ((ins, s)::progs, l, (s', input, output, r)), END::_ -> eval' (progs, l, (State.leave s' s, input, output, r)) ins 
    | _, END::_ -> failwith "Not last instruction with no previous stack frame!" 
  end 
  in eval' cfg ins

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o, _)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [], None)) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
(* let compile (defs, p) = failwith "Not implemented" *)
class labelGenerator =
 object (self)
   val counter = ref 0
   method nextLabel = let current = !counter in
     incr counter; Printf.sprintf "L%d" current
 end

 let generator = new labelGenerator
 let rec compile (functions, prog) =
   let rec compileExpr = function
    | Expr.Var   x          -> [LD x]
    | Expr.Const n          -> [CONST n]
    | Expr.Binop (op, x, y) -> compileExpr x @ compileExpr y @ [BINOP op]
    | Expr.Call (name, args) -> 
      List.concat (List.map compileExpr (List.rev args))
      @ [CALL name]
   in
   let rec compile' expr = match expr with
   | Stmt.Seq (s1, s2)  -> compile' s1 @ compile' s2
   | Stmt.Read x        -> [READ; ST x]
   | Stmt.Write e       -> compileExpr e @ [WRITE]
   | Stmt.Assign (x, e) -> compileExpr e @ [ST x]
   | Stmt.Skip          -> []
   | Stmt.If (c, t, e)  -> 
     let elseL = generator#nextLabel in 
     let exitL = generator#nextLabel in
     compileExpr c 
     @ [CJMP ("z", elseL) ] 
     @ compile' t 
     @ [JMP exitL; LABEL elseL]
     @ compile' e
     @ [LABEL exitL]
   | Stmt.While (c, b) -> 
     let startL = generator#nextLabel in
     let exitL = generator#nextLabel in 
     [LABEL startL]
     @ compileExpr c
     @ [CJMP ("z", exitL)]
     @ compile' b
     @ [JMP startL; LABEL exitL]
    | Stmt.Repeat (b, c) -> 
      let startL = generator#nextLabel in
      [LABEL startL]
      @ compile' b
      @ compileExpr c
      @ [CJMP ("z", startL)]
    | Stmt.Call (name, args) -> 
      (List.concat (List.map compileExpr args))
      @ [CALL name]
    | Stmt.Return (Some expr) ->
      compileExpr expr 
      @ [END]
    | Stmt.Return None -> [END]
  in 
  let compileFunction (name, (params, locals, body)) = 
    [LABEL name; BEGIN (params, locals)]
    @ compile' body 
    @ [END]
  in
  let mainLabel = generator#nextLabel in
  [JMP mainLabel]
  @ List.concat (List.map compileFunction functions) 
  @ [LABEL mainLabel]
  @ (compile' prog)
