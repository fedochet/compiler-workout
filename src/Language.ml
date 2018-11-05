(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
let intToBool i = if (i = 0) then false else true
let boolToInt b = if b then 1 else 0


(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                  
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)            
    let rec eval env ((st, i, o, r) as conf) expr = 
      match expr with
        | Const n -> (st, i, o, Some n)
        | Var x -> (st, i, o, Some (State.eval st x))
        | Binop (op, x, y) -> 
          let ((_, _ ,_ , Some x') as conf') = eval env conf x in
          let ((st'', i'', o'', Some y') as conf) = eval env conf' y in
          (st'', i'', o'', Some (to_func op x' y'))
        | Call (name, args) -> 
          let folder (conf, acc) e = let ((_, _, _, Some v) as conf') = eval env conf e in (conf', v::acc) in
          let (conf', args') = List.fold_left folder (conf, []) args 
          in 
          env#definition env name (List.rev args') conf
          (* let st' = State.enter st (params @ locals) in  *)
          (* let st'' = List.fold_left2 (fun s n v -> State.update n (Expr.eval st v) s) state' params args in  *)
          (* let (state''', input', output') = eval env (state'', input, output) body in  *)
          (* (State.drop_scope state''' state, input', output') *)

         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse:
      !(Ostap.Util.expr 
               (fun x -> x)
         (Array.map (fun (a, s) -> a, 
                             List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                          ) 
                [|                
      `Lefta, ["!!"];
      `Lefta, ["&&"];
      `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
      `Lefta, ["+" ; "-"];
      `Lefta, ["*" ; "/"; "%"];
                |] 
         )
         primary);
        
        call: 
         fn:IDENT "(" args:(!(Util.list0By) [ostap (",")] [parse]) ")" { Call (fn, args) };
         
        primary:
          n:DECIMAL {Const n}
        | fn:IDENT "(" args:(!(Util.list0By) [ostap (",")] [parse]) ")" { Call (fn, args) }
        | x:IDENT   {Var x}
        | -"(" parse -")"
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt = 
      let seq x y = match (x, y) with 
        | Skip, y -> y
        | x, Skip -> x
        | x, y -> Seq (x, y)
      in 
      match stmt with
        | Read name -> 
          let conf' = match i with 
            | z::i' -> (State.update name z st, i', o, None)
            | _ -> failwith "Input is empty, cannot read!" 
          in
          eval env conf' Skip k
        | Write expr -> 
          let st', i', o', Some v = Expr.eval env conf expr in
          eval env (st', i', o' @ [v], None) Skip k
        | Assign (name, expr) -> 
          let st', i', o', Some(v) = Expr.eval env conf expr in
          eval env (State.update name v st', i', o', None) Skip k
        | Seq (l, r) -> eval env conf (seq r k) l  (*TODO see if needs fixing*)
        | Skip -> (match k with | Skip -> conf | _ -> eval env conf Skip k)
        | If (c, t, e) -> 
          let (st', i', o', Some v) = Expr.eval env conf c in
          let branch = if v <> 0 then t else e in
          eval env (st', i', o', None) k branch
        | While(c, b) -> 
          let (st', i', o', Some v) = Expr.eval env conf c in
          let cfg' = (st', i', o', None) in
          if v <> 0 
          then eval env cfg' (seq stmt k) b
          else eval env cfg' Skip k
        | Repeat (b, c) -> eval env conf (seq (While (Expr.Binop ("==", c, Expr.Const 0), b)) k) b
        | Call (name, args) -> eval env (Expr.eval env conf (Expr.Call (name, args))) k Skip
        | Return (Some e) -> Expr.eval env conf e
        | Return None -> (st, i, o, None)
         
    (* Statement parser *)
    ostap (
      assign: x:IDENT ":=" e:!(Expr.parse) { Assign (x, e) } ;
      read: "read" "(" x:IDENT ")" { Read x } ;
      write: "write" "(" e:!(Expr.parse) ")" { Write e } ;
      skip: "skip" { Skip };
      
      elseBlock: 
        "elif" e:!(Expr.parse) "then" b:parse next:elseBlock { If(e, b, next) }
      | "else" b:parse { b }
      | "elif" e:!(Expr.parse) "then" b:parse { If (e, b, Skip) };
      
      ifBlock: 
        "if" e:!(Expr.parse) "then" b:parse el:elseBlock "fi" { If (e, b, el) }
      | "if" e:!(Expr.parse) "then" b:parse "fi" { If (e, b, Skip )} ;

      whileBlock: 
        "while" e:!(Expr.parse) "do" b:parse "od" { While (e, b) };

      repeatBlock:
        "repeat" b:parse "until" e:!(Expr.parse) { Repeat (b, e) }; 

      forBlock: 
        "for " init:simple_stmt "," cond:!(Expr.parse) "," upd:simple_stmt "do" b:parse "od" { Seq(init, While(cond, Seq(b, upd))) };

      return:
        "return " value:(!(Expr.parse))? { Return value };
      (* | "return" { Return None }; *)

      call: 
        fn:IDENT "(" args:(!(Util.list0By) [ostap (",")] [Expr.parse]) ")" { Call (fn, args)};
        
      simple_stmt: assign | read | write | skip | call | return;
      stmt: simple_stmt | ifBlock | whileBlock | repeatBlock | forBlock;
      parse: <s::ss> :
        !(Util.listBy)
        [ostap (";")]
        [stmt]
        { List.fold_left (fun s ss -> Seq (s, ss)) s ss}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
