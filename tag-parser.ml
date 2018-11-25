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

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
  val test : string -> expr
  val test_reader : string -> sexpr

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
| _ -> raise  X_syntax_error

(*   
Pair(Symbol "quasiquote", Pair(, Nil)))) (execute_expected(Const(Sexpr(Pair(Symbol "quote", Pair(Symbol "h", Nil)))))));
*)


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
|Pair (Pair (Symbol "begin", x), Nil)->seq_tag_parser x
|_->tag_parse (Pair(Symbol("begin"), body)))


(* ------------------------------- define -------------------------------------*)


and define_mit_macro_extension var arglist body = 
let parsed_lambda =  (Pair (Symbol("lambda"),(Pair(arglist,body)))) in
tag_parse (Pair(Symbol("define"),(Pair(var ,(Pair(parsed_lambda, Nil))))))
(* Def(tag_parse var, parsed_lambda) *)

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



(* 

test_Lambda_Expressions number 17 Failed with got LambdaSimple([ a ],Const(Void)) while expected Var("test failed with X_syntax_error") !!!
test_Applications number 9 Failed with got Applic(Var("+"),[ Var("+") ]) while expected Var("test failed with X_syntax_error") !!!
test_Definitions number 33 Failed with got Def(Var("func"),LambdaSimple([  ],Const(Void))) while expected Var("test failed with X_syntax_error") !!!
test_Definitions number 34 Failed with got Def(Var("func"),LambdaSimple([  ],Seq([ Var("x"); Var("y") ]))) while expected Var("test failed with X_syntax_error") !!!
test_Sequences number 14 Failed with got Var("g") while expected Var("test failed with X_syntax_error") !!!
test_Quasiquoted_Macro_Expansion number 2 Failed with Pair(Symbol("quasiquote"),Pair(String("string"),Nil)) as X_syntax_error !!!
test_Quasiquoted_Macro_Expansion number 3 Failed with Pair(Symbol("quasiquote"),Pair(Char(),Nil)) as X_syntax_error !!!
test_Quasiquoted_Macro_Expansion number 5 Failed with got Applic(Var("cons"),[ Const(Sexpr(Symbol("quote"))); Applic(Var("cons"),[ Const(Sexpr(Symbol("h"))); Const(Sexpr(Nil)) ]) ]) while expected Const(Sexpr(Pair(Symbol("quote"),Pair(Symbol("h"),Nil)))) !!!
test_Quasiquoted_Macro_Expansion number 12 Failed with Pair(Symbol("quasiquote"),Pair(Number(Int(5)),Nil)) as X_syntax_error !!!
test_Quasiquoted_Macro_Expansion number 13 Failed with Pair(Symbol("quasiquote"),Pair(String("string"),Nil)) as X_syntax_error !!!
test_Quasiquoted_Macro_Expansion number 14 Failed with Pair(Symbol("quasiquote"),Pair(Char(
),Nil)) as X_syntax_error !!!
test_Quasiquoted_Macro_Expansion number 16 Failed with got Applic(Var("cons"),[ Const(Sexpr(Symbol("quote"))); Applic(Var("cons"),[ Const(Sexpr(Symbol("h"))); Const(Sexpr(Nil)) ]) ]) while expected Const(Sexpr(Pair(Symbol("quote"),Pair(Symbol("h"),Nil)))) !!!


test_Lambda_Expressions number 17 Failed with got LambdaSimple([ a ],Const(Void)) while expected Var("test failed with X_syntax_error") !!!
test_Applications number 9 Failed with got Applic(Var("+"),[ Var("+") ]) while expected Var("test failed with X_syntax_error") !!!
test_Definitions number 33 Failed with got Def(Var("func"),LambdaSimple([  ],Const(Void))) while expected Var("test failed with X_syntax_error") !!!
test_Definitions number 34 Failed with got Def(Var("func"),LambdaSimple([  ],Seq([ Var("x"); Var("y") ]))) while expected Var("test failed with X_syntax_error") !!!
test_Sequences number 14 Failed with got Var("g") while expected Var("test failed with X_syntax_error") !!!
test_Quasiquoted_Macro_Expansion number 5 Failed with got Applic(Var("cons"),[ Const(Sexpr(Symbol("quote"))); Applic(Var("cons"),[ Const(Sexpr(Symbol("h"))); Const(Sexpr(Nil)) ]) ]) while expected Const(Sexpr(Pair(Symbol("quote"),Pair(Symbol("h"),Nil)))) !!!
test_Quasiquoted_Macro_Expansion number 16 Failed with got Applic(Var("cons"),[ Const(Sexpr(Symbol("quote"))); Applic(Var("cons"),[ Const(Sexpr(Symbol("h"))); Const(Sexpr(Nil)) ]) ]) while expectedConst(Sexpr(Pair(Symbol("quote"),Pair(Symbol("h"),Nil)))) !!!
*)

 

(*
 Pair(Symbol "quote", Pair(Symbol "h", Nil))
*)
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
(* |_-> raise X_syntax_error *) ) 


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
    (* |1->(List.hd tagParsedExprs)  pass jonathan*)
    (* |1-> Or(tagParsedExprs)    PASS GILAD*)
    |_->Or(tagParsedExprs))

(*--------------------------- seq --------------------------------------------- *)
and seq_tag_parser exprs = 
let tagParsedExprs = map_tag_parse exprs in
let lengthOfsequence = (List.length tagParsedExprs) in
(match (lengthOfsequence) with
    |0-> Const(Void)
    |1->  List.hd tagParsedExprs
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


let test string = 
tag_parse (Reader.read_sexpr string);;

let test_reader string = 
Reader.read_sexpr string;;



    (**********TESTING**********)
open Reader;;
open PC;;

let _tag_string str =
  let sexp = (read_sexpr str) in
  tag_parse_expression sexp;;

exception X_test_mismatch;;

(*Test will fail if no X_syntax_error is raised with input str*)
let _assertX num str =
  try let sexpr = (tag_parse_expression (read_sexpr str)) in
      match sexpr with
      |_ ->
        (failwith
	(Printf.sprintf
	   "Failed %.1f: Expected syntax error with string '%s'"num str))
   with
  |X_no_match ->
     (failwith
	(Printf.sprintf
	   "Failed %.1f with X_no_match: Reader couldn't parse the string '%s'"num str))
  |X_syntax_error -> num
     
(*Test will fail if an exception is raised,
or the output of parsing str is different than the expression out*)
let _assert num str out =
  try let sexpr = (read_sexpr str) in
      (if not (expr_eq (tag_parse_expression sexpr) out)
       then raise X_test_mismatch
       else num)
  with
  |X_no_match ->
     (failwith
	(Printf.sprintf
	   "Failed %.2f with X_no_match: Reader couldn't parse the string '%s'"num str))
  |X_test_mismatch ->
    (failwith
       (Printf.sprintf
	  "Failed %.2f with mismatch: The input -- %s -- produced unexpected expression"num str))
  |X_syntax_error ->
     (failwith
	(Printf.sprintf
	   "Failed %.2f with X_syntax_error: Tag parser failed to resolve expression '%s'"num str));;

(*Boolean*)
_assert 1.0 "#t" ( Const (Sexpr (Bool true)));;
_assert 1.1 "#f" ( Const (Sexpr (Bool false)));;

(*Number*)
_assert 2.0 "123" ( Const (Sexpr (Number (Int 123))));;
_assert 2.1 "-123" ( Const (Sexpr (Number (Int (-123)))));;
_assert 2.2 "12.3" ( Const (Sexpr (Number (Float (12.3)))));;
_assert 2.3 "-12.3" ( Const (Sexpr (Number (Float (-12.3)))));;


(*Char*)
_assert 3.0 "#\\A" ( Const (Sexpr (Char 'A')));;
_assert 3.1 "#\\nul" ( Const (Sexpr (Char '\000')));;


(*String*)
_assert 4.0 "\"String\"" (Const (Sexpr (String "String")));;


(*Quote*)
_assert 5.0 "'quoting" (Const (Sexpr (Symbol "quoting")));;
(*_assert 5.1 ",unquoting" (Const (Sexpr (Symbol "unquoting")));; removed - invalid syntax*)

(*Symbol*)
_assert 6.0 "symbol" (Var "symbol");;

(*If*)
_assert 7.0 "(if #t 2 \"abc\")"
  (If (Const (Sexpr (Bool true)), Const (Sexpr (Number (Int 2))),
       Const (Sexpr (String "abc"))));;
  
_assert 7.1 "(if #t 2)"
  (If (Const (Sexpr (Bool true)), Const (Sexpr (Number (Int 2))),
       (Const Void)));;
  
(*SimpleLambda*)
_assert 8.0 "(lambda (a b c) d)" (LambdaSimple (["a"; "b"; "c"], Var "d"));;
_assert 8.1 "(lambda (a b c) (begin d))" (LambdaSimple (["a"; "b"; "c"], Var "d"));;
_assert 8.2 "(lambda (a b c) a b)" (LambdaSimple (["a"; "b"; "c"], Seq [Var "a"; Var "b"]));;
_assert 8.3 "(lambda (a b c) (begin a b))" (LambdaSimple (["a"; "b"; "c"], Seq [Var "a"; Var "b"]));;
_assert 8.4 "(lambda (a b c) (begin))" (LambdaSimple (["a"; "b"; "c"], Const Void));;
_assertX 8.5 "(lambda (a b c d d) e f)";;
_assert 8.6 "(lambda () e f)" (LambdaSimple( [], Seq [Var "e"; Var "f"])) ;;

(*LambdaOpt*)
_assert 9.0 "(lambda (a b . c) d)" ( LambdaOpt (["a"; "b"], "c", Var "d"));;
_assert 9.1 "(lambda (a b . c) (begin d))" ( LambdaOpt (["a"; "b"], "c", Var "d"));;
_assert 9.2 "(lambda (a b . c) d e)" ( LambdaOpt (["a"; "b"], "c",  Seq [Var "d"; Var "e"]));;
_assert 9.3 "(lambda (a b . c) (begin d e))" ( LambdaOpt (["a"; "b"], "c",  Seq [Var "d"; Var "e"]));;
_assert 9.4 "(lambda (a b . c) (begin) )" ( LambdaOpt (["a"; "b"], "c",  Const Void));;
_assertX 9.5 "(lambda (a b c d .a) e f)";;



(*Lambda Variadic*)
_assert 10.0 "(lambda a d)" ( LambdaOpt ([], "a", Var "d"));;
_assert 10.1 "(lambda a (begin d))" ( LambdaOpt ([], "a", Var "d"));;
_assert 10.2 "(lambda a d e)" ( LambdaOpt ([], "a", Seq [Var "d"; Var "e"] ));;
_assert 10.3 "(lambda a (begin d e))" ( LambdaOpt ([], "a",  Seq [Var "d"; Var "e"]));;
_assert 10.4 "(lambda a (begin) )" ( LambdaOpt ([], "a",  Const Void));;

(*Application*)
_assert 11.0 "(+ 1 2 3)"
  (Applic (Var "+", [Const (Sexpr (Number (Int 1)));
		     Const (Sexpr (Number (Int 2)));
		     Const (Sexpr (Number (Int 3)))]));;
_assert 11.1 "((lambda (v1 v2) c1 c2 c3) b1 b2)"
  (Applic
     (LambdaSimple (["v1"; "v2"],
		    Seq [Var "c1"; Var "c2"; Var "c3"]),
      [Var "b1"; Var "b2"]));;


(* Or*)
_assert 12.0 "(or #t #f #\\a)"
  (Or
     [Const (Sexpr (Bool true)); Const (Sexpr (Bool false));
      Const (Sexpr (Char 'a'))]);;

_assert 12.1 "(or 'a)"  (Or [Const (Sexpr (Symbol "a"))]);;
  
(* based on forum answers, the case with one expression is only *evaluated* to that expression,
but its still parsed as an Or expression at this point
(Const (Sexpr (Symbol "a")));;*)

_assert 12.2 "(or)"
  (Const (Sexpr (Bool false)));;
 
(*Define*)
_assert 13.0 "(define a b)" (Def (Var "a", Var "b"));;
_assertX 13.1 "(define 5 b)";;
_assertX 13.2 "(define if b)";;

(*Set*)
_assert 14.0 "(set! a 5)" (Set (Var "a", Const (Sexpr (Number (Int 5)))));;
_assertX 14.1 "(set! define 5)";;
_assertX 14.2 "(set! \"string\" 5)";;


(*Let*)
_assert 15.0 "(let ((v1 b1)(v2 b2)) c1 c2 c3)"
  (Applic (LambdaSimple (["v1"; "v2"], Seq [Var "c1"; Var "c2"; Var "c3"]), [Var "b1"; Var "b2"]));;
_assert 15.1 "(let () c1 c2)" (Applic (LambdaSimple ([], Seq [Var "c1"; Var "c2"]), []));;

(*And*)
_assert 16.0 "(and)" (Const (Sexpr (Bool true)));;
_assert 16.1 "(and e1)" (Var "e1");;
_assert 16.2 "(and e1 e2 e3 e4)"
  (If (Var "e1",
       If (Var "e2", If (Var "e3", Var "e4", Const (Sexpr (Bool false))),
	   Const (Sexpr (Bool false))),
       Const (Sexpr (Bool false))));;

(*Let* *)
_assert 17.0 "(let* () body)" (Applic (LambdaSimple ([], Var "body"), []));;
_assert 17.1 "(let* ((e1 v1)) body)" (Applic (LambdaSimple (["e1"], Var "body"), [Var "v1"]));;
_assert 17.2 "(let* ((e1 v1)(e2 v2)(e3 v3)) body)"
  (Applic (LambdaSimple (["e1"], Applic (LambdaSimple (["e2"], Applic (LambdaSimple (["e3"], Var "body"),
   [Var "v3"])), [Var "v2"])), [Var "v1"]));;


(*MIT define*)
(*
The body shouldn't be used in an applic expression.
_assert 18.0 "(define (var . arglst) . (body))" (Def (Var "var", LambdaOpt ([],"arglst", Applic (Var "body", []))));;*)

_assert 18.0 "(define (var . arglst) . (body))" (_tag_string "(define var (lambda arglst body))");;

(* equivalent to (define (var . arglst) body)  *)


(*Letrec
_assert 19.0 "(letrec ((f1 e1)(f2 e2)(f3 e3)) body)"
  (_tag_string
     "(let ((f1 'whatever)(f2 'whatever)(f3 'whatever))
(set! f1 e1) (set! f2 e2) (set! f3 e3)
(let () body))");;


    (*
This output is wrong as the 'body' of the letrec needs to be enclosed in a let expr according to the lectures
(Applic
 (LambdaSimple (["f1"; "f2"; "f3"],
   Seq
    [Set (Var "f1", Var "e1"); Set (Var "f2", Var "e2");
     Set (Var "f3", Var "e3"); Var "body"]),
 [Const (Sexpr (Symbol "whatever")); Const (Sexpr (Symbol "whatever"));
      Const (Sexpr (Symbol "whatever"))]));;*)
*)

(*Quasiquote*)
_assert 20.0 "`,x" (_tag_string "x");;
_assertX 20.01 "`,@x";;
_assert 20.02 "`(a b)" (_tag_string "(cons 'a (cons 'b '()))");;
_assert 20.03 "`(,a b)" (_tag_string "(cons a (cons 'b '()))");;
_assert 20.04 "`(a ,b)" (_tag_string "(cons 'a (cons b '()))");;
_assert 20.05 "`(,@a b)" (_tag_string "(append a (cons 'b '()))");;
_assert 20.06 "`(a ,@b)" (_tag_string "(cons 'a (append b '()))");;
_assert 20.07 "`(,a ,@b)" (_tag_string "(cons a (append b '()))");;
_assert 20.08 "`(,@a ,@b)" (_tag_string "(append a (append b '()))");;
_assert 20.09 "`(,@a . ,b)" (_tag_string "(append a b)");;
_assert 20.10 "`(,a . ,@b)" (_tag_string "(cons a b)");;
_assert 20.11 "`(((,@a)))" (_tag_string "(cons (cons (append a '()) '()) '())");;
_assert 20.12 "`#(a ,b c ,d)" (_tag_string "(vector 'a b 'c d)");;
(*
_assert 20.15 "`" (_tag_string "");;
_assert 20.16 "`" (_tag_string "");;
  _assert 20.17 "`" (_tag_string "");;*)


(*Cond*)

(*
Before the fucking change that the rest of the ribs had to be enclosed in a lambda

_assert 21.0 "(cond (a => b)(c => d))"
  (_tag_string
     "(let ((value a)(f (lambda () b)))
        (if value
          ((f) value)
          (let ((value c)(f (lambda () d)))
            (if value
  ((f) value)))))");; *)

_assert 21.0 "(cond (e1 => f1) (e2 => f2))"
  (_tag_string
     "
(let
((value e1)
(f (lambda () f1))
(rest (lambda ()
 
(let ((value e2)(f (lambda () f2))) (if value ((f) value)))

)))
(if value ((f) value) (rest)))");;

(* Note: the separated line is the expansion of the second cond rib *)


_assert 21.1 "(cond (p1 e1 e2) (p2 e3 e4) (p3 e4 e5))"
  (_tag_string
     "(if p1
        (begin e1 e2)
        (if p2
          (begin e3 e4)
          (if p3
            (begin e4 e5))))");;

_assert 21.2 "(cond (p1 e1 e2) (p2 e3 e4) (else e5 e6) (BAD BAD BAD))"
  (_tag_string
     "(if p1
        (begin e1 e2)
        (if p2
          (begin e3 e4)
          (begin e5 e6)))");;

end;; (* struct Tag_Parser *)

