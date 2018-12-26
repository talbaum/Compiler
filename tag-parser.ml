(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
  
                       
exception X_syntax_error;;
exception X_tmp;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list


end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* ------------------------ work on the tag parser starts here --------------------------------------*)


(* ------------------------------ Helper functions ---------------------------------------------------*) 

let is_in_reserved_list = function
  | Symbol(check_me)->   List.mem check_me reserved_word_list 
  | _-> raise X_syntax_error;;

let rec is_improper_list list  = match list with
|Nil -> false
|Pair(car,cdr) -> is_improper_list cdr
| _ -> true;;

let rec find_last_element = function
  | _::xs -> List.hd(List.rev( xs))
  | [] -> raise X_syntax_error;;

let rec convert_to_sexpr_list list = match list with
| Nil -> []
| Pair(car, Nil)->[car]
| Symbol(car) -> [Symbol(car)]
| Pair(car,cdr) ->  car :: (convert_to_sexpr_list cdr)
| _ -> raise X_syntax_error;;

let string_converter_function car dif =
let reservedWord=  is_in_reserved_list (Symbol(car)) in
      match reservedWord with 
        |true -> raise X_syntax_error
        |false ->dif;;

let rec convert_to_string_list list = match list with
| Nil -> []
| Pair(Symbol(car), Nil)-> string_converter_function car [car]
| Symbol(car) -> string_converter_function car [car]
| Pair(Symbol(car),cdr) -> string_converter_function car (car :: (convert_to_string_list cdr))
| _ -> raise X_syntax_error;;


let is_not_duplicated_args args = 
let unique_number_of_args = (List.sort_uniq String.compare args) in
if (List.compare_lengths args  unique_number_of_args == 0) then true else false;;


let without_last_arg list = 
  let reversedList= List.rev list in
  let no_first_arg = List.tl reversedList in
  List.rev no_first_arg
	

(* ------------------------------ tag parse ---------------------------------------------------*) 

let rec tag_parse sexpr =  match sexpr with
| Number (Int(a)) -> Const(Sexpr(Number(Int(a))))
| Number (Float(a)) -> Const(Sexpr(Number(Float(a))))
| Bool (a) ->  Const(Sexpr(Bool (a)))
| Char(a)-> Const(Sexpr(Char(a)))
| String(a)-> Const (Sexpr(String(a)))
(* | Vector(exprs) -> Const(Sexpr(Vector((exprs)))) *)
| Pair(Symbol("quote"), Pair(a, Nil)) -> Const(Sexpr(a))
| Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parse test, tag_parse dit, tag_parse dif)
| Pair(Symbol("if"), Pair(test, Pair(dit, Nil)))-> If(tag_parse test, tag_parse dit, Const (Void))
| Pair(Symbol("define"),(Pair(Symbol(name) ,(Pair(expr, Nil)))))-> define_tag_parser (Symbol(name)) expr
| Pair(Symbol("set!"),(Pair(Symbol(name) ,(Pair(expr, Nil)))))->set_tag_parser name expr
| Pair(Symbol("begin"), exprs)-> seq_tag_parser exprs
| Pair(Symbol("or"),exprs)->or_tag_parser exprs
| Pair(Symbol("lambda"), Pair(args, body)) -> lambda_tag_parser args body
| Pair (Symbol "let",Pair (Nil, body)) -> handle_let_no_args body
| Pair (Symbol "let",Pair (args, body)) -> handle_let args body 0
| Pair (Pair((Symbol "let"),Number(Int(is_star))),Pair (args, body)) -> handle_let args body is_star
| Pair (Symbol "let*",Pair (args, body)) -> handle_let_star args body 
| Pair (Symbol "letrec",Pair (args, body)) -> handle_letrec args body 
| Pair(Symbol("quasiquote"),Pair(exprs,Nil))-> quasiquote_tag_parser exprs
| Pair(Symbol("cond"),Pair(rib, otherRibs))-> cond_tag_parser  rib otherRibs
| Pair(Symbol "and", exprs) -> and_macro_extension exprs
| Pair(Symbol "define", Pair(Pair(varname, arglist), body))-> define_mit_macro_extension varname arglist body
| Symbol(a)-> symbol_tag_parser a 
| Pair (functionName, args)->applic_tag_parser functionName args
| _-> raise X_syntax_error 


(* ------------------------------- let rec-------------------------------------*)
and handle_letrec args body = match args with
|Nil -> tag_parse (Pair (Symbol "let",Pair (Nil, body)))
|Pair(Pair(car,cdr),other_pairs) -> 
let whatever_values = create_whateverlist args in  
let set_args = create_set_args args body in
tag_parse(Pair (Symbol "let",Pair (whatever_values, set_args)))
|_ -> raise X_syntax_error 


and create_set_args args body= match args with
|Nil -> body
|Pair(Pair(arg,value),next_ribs)  -> 
    let one_set = (Pair(Symbol("set!"),Pair(arg,value))) in
    Pair(one_set,(create_set_args next_ribs body))
|Pair(arg, value) ->  Pair(Pair(Symbol("set!"),(Pair(arg ,value))),body)
|_ -> raise X_syntax_error

and create_whateverlist args = 
let whatever = Pair(Symbol("quote"),(Pair(Symbol("whatever"),Nil))) in
match args with
|Pair(Pair(arg,Pair(value,Nil)),Nil) -> (Pair(arg,whatever))   
|Pair(Pair(arg,Pair(value,Nil)),next_ribs)  -> Pair(Pair(arg,Pair(whatever,Nil)), create_whateverlist next_ribs) 
|Pair(arg, value) -> Pair(arg,Pair(whatever, Nil))
|_ -> raise X_syntax_error

(* ------------------------------- let star-------------------------------------*)

and handle_let_star args body  = match args with
|Nil -> tag_parse (Pair (Symbol "let",Pair (Nil, body)))
|Pair(single ,Nil) ->
            let parse_let_star = Pair (Pair((Symbol "let"),Number(Int(1))),Pair (single, body)) in
            tag_parse (parse_let_star)
|Pair(args,other_pairs) ->  
            let parse_let_star = Pair (Pair((Symbol "let"),Number(Int(1))),Pair (args, Pair(Pair((Symbol "let*",Pair (other_pairs, body))),Nil))) in
            tag_parse (parse_let_star)
| _ -> raise X_syntax_error


(* ------------------------------- let -------------------------------------*)

and create_arglist ribs = match ribs with
|Pair(Pair (arg,value),Nil) ->  Pair(arg,Nil)
|Pair(Pair(arg,value),next_ribs) -> (Pair(arg, (create_arglist next_ribs))) 
|Pair(arg, value) ->Pair(arg, Nil)
|_ -> raise X_syntax_error

and create_valueslist ribs = match ribs with
|Pair(Pair(arg,Pair(value,Nil)),Nil) -> Pair(value,Nil)
|Pair(Pair(arg,Pair(value,Nil)),next_ribs)  ->  Pair(value , create_valueslist next_ribs)
|Pair(arg, value) -> Pair(value,Nil)
|_ -> raise X_syntax_error

and create_letstar_valueslist ribs = 
 match ribs with
|Pair(Pair(arg,Pair(value,Nil)),Nil) -> value
|Pair(Pair(arg,Pair(value,Nil)),next_ribs)  ->  Pair(value , create_letstar_valueslist next_ribs)
|Pair(arg, value) -> value
|_ -> raise X_syntax_error 


and handle_let args body is_star = match is_star with
|1 ->  macro_extension_let body (create_arglist  args) (create_letstar_valueslist args ) 
|_->  macro_extension_let body (create_arglist  args) (create_valueslist args )


and handle_let_no_args body  = 
macro_extension_let body Nil Nil


and macro_extension_let body arglist valuesList = 
let parsed_lambda = tag_parse (Pair(Symbol("lambda"),Pair(arglist,body)))  in
        Applic(parsed_lambda, map_tag_parse valuesList) 



(* -------------------------------------- cond ----------------------------------------------------------*)

and rib1_cond_tag_parser test seq otherRibs = 
let dit = Pair(Symbol("begin"), seq) in
let dif = (Pair(Symbol("cond"),otherRibs)) in
(match otherRibs with 
|Nil -> tag_parse(Pair(Symbol("if"), Pair(test, Pair(dit, Nil))))
|_-> tag_parse (Pair(Symbol("if"), Pair(test, Pair(dit, (Pair(dif,  Nil)))))))


and rib2_nil_cond_tag_parser exp_k exp_f=
let test=Symbol("value") in
let dit =Pair((Pair(Symbol("f"),Nil)),Symbol("value")) in
let ifAndApplic=( Pair(Symbol("if"), Pair(test, (Pair(dit ,Nil))))) in
 let k= Pair(Symbol("value"),Pair(exp_k,Nil)) in
let f= Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(exp_f,Nil))),Nil))  in
let args = (Pair(Symbol("let"),Pair( (Pair(k,Pair(f,Nil)) ),Pair(ifAndApplic,Nil))))  in
tag_parse (args)


and rib2_cond_tag_parser exp_k exp_f rest=
let test=Symbol("value") in
let dit =Pair((Pair(Symbol("f"),Nil)),Symbol("value")) in
let dif =Pair(Symbol("rest"),Nil) in
let ifAndApplic=( Pair(Symbol("if"), Pair(test, (Pair(dit ,Pair(dif,Nil)))))) in
let k= Pair(Symbol("value"),Pair(exp_k,Nil)) in
let f= Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(exp_f,Nil))),Nil))  in
let restCond = Pair(Symbol("cond"),rest) in
let rest1 = Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(restCond,Nil))),Nil))  in
let args = (Pair(Symbol("let"),Pair( (Pair(k,Pair(f,Pair(rest1,Nil))) ),Pair(ifAndApplic,Nil))))  in
tag_parse (args)

and  cond_tag_parser rib otherRibs=
(match rib with
|Pair(exp_k,Pair(Symbol("=>"),Pair(exp_f,Nil)))->(match otherRibs with
        |Nil->rib2_nil_cond_tag_parser exp_k exp_f
        |_->rib2_cond_tag_parser exp_k exp_f otherRibs)
|Pair(Symbol("else"),seq)->tag_parse (Pair(Symbol("begin"),seq)) 
|Pair(test,seq)-> rib1_cond_tag_parser test seq otherRibs
|_->raise X_syntax_error)



(*---------------------------------- lambda ---------------------------------------------------------*)

and lambda_tag_parser args body= 
(match args with 
    | Nil -> LambdaSimple ([],(needBegin body))
    |Symbol(vs) -> LambdaOpt([], vs ,( needBegin body))
    | Pair(car,Nil) -> let converted_args = convert_to_string_list args in 
                           LambdaSimple(converted_args,( needBegin body))
    | Pair(car,cdr) -> let converted_args = convert_to_string_list args in 
                      if (is_not_duplicated_args converted_args) then
                              if(is_improper_list args)
                              then 
                                  let last_element = find_last_element(converted_args) in
                                  let almost_all_args = without_last_arg(converted_args) in
                                  LambdaOpt(almost_all_args, last_element,( needBegin body))
                              else LambdaSimple(converted_args,( needBegin body))
                      else raise  X_syntax_error
|_ -> raise X_syntax_error)



(*---------------------------- needBegin -----------------------------------*)
and needBegin body=
(match body with
|Nil ->tag_parse Nil
|Pair (Pair (Symbol "begin", x), Nil)->seq_tag_parser x
|Pair (Symbol "begin", x)->seq_tag_parser x

|_->tag_parse (Pair(Symbol("begin"), body)))


(* ------------------------------- define -------------------------------------*)



and define_mit_macro_extension var arglist body = 
match arglist with
|Nil ->(match body with
    |Pair(_, Nil)->let parsed_lambda =  (Pair (Symbol("lambda"),(Pair(arglist,body)))) in
          tag_parse (Pair(Symbol("define"),(Pair(var ,(Pair(parsed_lambda, Nil))))))
    |_->raise X_syntax_error ) 
|_->
let parsed_lambda =  (Pair (Symbol("lambda"),(Pair(arglist,body)))) in
tag_parse (Pair(Symbol("define"),(Pair(var ,(Pair(parsed_lambda, Nil))))))

(* ------------------------------- and -------------------------------------*)

and and_macro_extension sexpr= match sexpr with
|Nil -> tag_parse (Bool (true))
|Pair(last_element,Nil) -> tag_parse last_element
|Pair(car,cdr) -> 
    let dit = Pair(((Symbol ("and")), cdr)) in
    let test =car in
    let  dif = (Bool (false)) in
    tag_parse(Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil))))) 
|_ -> raise X_syntax_error

(*---------------------------------- quasiquote ---------------------------------------------------------*)
and quasiquote_tag_parser exprs= 
(match exprs with
|Nil -> tag_parse (Pair(Symbol("quote"), Pair(Nil, Nil)))
|Symbol(exprs) ->tag_parse (Pair(Symbol("quote"), Pair(Symbol(exprs), Nil)))
|String(exprs) ->tag_parse (Pair(Symbol("quote"), Pair(String(exprs), Nil)))
|Number(exprs) ->tag_parse (Pair(Symbol("quote"), Pair(Number(exprs), Nil)))
|Bool(exprs) ->tag_parse (Pair(Symbol("quote"), Pair(Bool(exprs), Nil)))
|Char(exprs) ->tag_parse (Pair(Symbol("quote"), Pair(Char(exprs), Nil)))
|Pair(Symbol("quote"),rest)-> let tmp = Pair(Symbol("quote"),rest) in
tag_parse (Pair(Symbol("quote"), Pair(tmp, Nil)))
|Pair(Symbol("unquote"), Pair(rest,Nil))-> tag_parse rest
|Pair(Symbol("unquote-splicing"), rest)->raise X_syntax_error
|Pair(Pair(Symbol("unquote-splicing"),Pair(spliced,Nil)),after)-> tag_parse (unquote_splicing_builder spliced Nil after 1)
|Pair(before,Pair(Symbol("unquote-splicing"),Pair(spliced,Nil)))-> tag_parse (unquote_splicing_builder spliced before Nil 2)
|Pair(before,after)-> tag_parse (unquote_splicing_builder Nil before after 3)
|Vector(args)-> tag_parse(Pair(Symbol( "vector"),(list_to_nested_pairs(quasi_map_tag_parse args))))
) 


(*--------------------------------- unquote-splicing -----------------------------------------*)
and unquote_splicing_builder spliced before after option=
(match option with
|1 ->(Pair(Symbol( "append"), (Pair(spliced,(Pair(Pair(Symbol("quasiquote"),Pair( after,Nil)),Nil))))))
|2-> (Pair(Symbol( "cons"), (Pair( Pair(Symbol("quasiquote"),Pair(before,Nil)), Pair(spliced,Nil)))))
|3-> (Pair(Symbol( "cons"), (Pair( (Pair(Symbol("quasiquote"),Pair(before,Nil))),(Pair(Pair(Symbol("quasiquote"),Pair(after,Nil)),Nil))))))
|_-> raise X_syntax_error)


(* ------------------------------- list_to_nested_pairs -------------------------------------*)

and list_to_nested_pairs args = 
(match args with 
|[] -> Nil
|_ -> Pair( (List.hd args), (list_to_nested_pairs (List.tl args) )))

(* ------------------------------- quasi map -------------------------------------*)

and quasi_map_tag_parse args = 
List.map (fun(element)->(Pair(Symbol("quasiquote"),Pair(element,Nil)))) (args)


(* ------------------------------- map -------------------------------------*)

and map_tag_parse args = 
List.map tag_parse (convert_to_sexpr_list args)


(*---------------------------- or  ----------------------------------------*)
and or_tag_parser exprs= 
let tagParsedExprs = map_tag_parse exprs in
let lengthOfsequence = (List.length tagParsedExprs) in
(match (lengthOfsequence) with
    |0->Const(Sexpr(Bool(false)))
    |1->(List.hd tagParsedExprs) 
    (* |1-> Or(tagParsedExprs)    PASS GILAD*)
    |_->Or(tagParsedExprs))

(*--------------------------- seq --------------------------------------------- *)
and seq_tag_parser exprs = 
let tagParsedExprs = map_tag_parse exprs in
let lengthOfsequence = (List.length tagParsedExprs) in
(match (lengthOfsequence) with
    |0-> Const(Void)
    |1->  (match exprs with
        |Symbol(exprs) -> raise X_syntax_error
        | _ ->   List.hd tagParsedExprs)
    |_->Seq(tagParsedExprs))

(*--------------------------- Applic ------------------------------------------- *)

and applic_tag_parser functionName args = 
let tag_parsed_functionName = tag_parse functionName in
let tag_parsed_args = map_tag_parse args in
Applic(tag_parsed_functionName ,tag_parsed_args) 


(*------------------------------ Define ----------------------------------------*)
and define_tag_parser name expr =
let tag_parsed_name = tag_parse(name) in
 let tag_parsed_expr = tag_parse expr in
 (match tag_parsed_name with
 |Var(x)->Def(tag_parsed_name,tag_parsed_expr)
 |_->raise X_syntax_error)
 
(*------------------------------ Set! ----------------------------------------*)

and set_tag_parser name expr = 
let tag_parsed_name = tag_parse(Symbol(name)) in
let tag_parsed_expr = tag_parse expr in
Set(tag_parsed_name,tag_parsed_expr)
(*------------------------------------ Symbol ------------------------------------------------------------*)

and symbol_tag_parser a=
let reservedWord=  is_in_reserved_list (Symbol(a)) in
(match reservedWord with 
|true -> raise X_syntax_error
|false ->Var(a));;

(*------------------------ Main Functions ----------------------------------*)
let tag_parse_expression sexpr = tag_parse sexpr;;
let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr;;



end;; (* struct Tag_Parser *)



