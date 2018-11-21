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


let is_in_reserved_list = function
  | Symbol(check_me)->   List.mem check_me reserved_word_list 
  | _-> raise X_not_yet_implemented;;

let rec is_improper_list list  = match list with
|Pair(_ , Nil)->  false
|Pair(car,cdr)  ->  is_improper_list cdr
|vs -> true;;

let rec find_last_element = function
  | x::[] -> x
  | _::xs -> find_last_element xs
  | [] -> raise X_syntax_error;;


let rec convert_to_sexpr_list list = match list with
| Nil -> []
| Pair(car, Nil)->[car]
(*| car -> [car]*)
| Pair(car,cdr) ->  car :: (convert_to_sexpr_list cdr)
| _ -> raise X_not_yet_implemented;;


let rec convert_to_string_list list = match list with
| Nil -> []
| Pair(Symbol(car), Nil)-> if (is_in_reserved_list(Symbol(car)))  then raise X_not_yet_implemented else [car]
| Symbol(car) -> if (is_in_reserved_list(Symbol(car))) then raise X_not_yet_implemented else [car]
| Pair(Symbol(car),cdr) -> if (is_in_reserved_list(Symbol(car))) then raise X_not_yet_implemented else car :: (convert_to_string_list cdr)
| _ -> raise X_not_yet_implemented;;



let is_not_duplicated_args args = 
let unique_number_of_args = (List.sort_uniq String.compare args) in
if (List.length unique_number_of_args == List.length args) then true else false;;

let rec tag_parse sexpr =  match sexpr with
| Number (Int(a)) -> Const(Sexpr(Number(Int(a))))
| Number (Float(a)) -> Const(Sexpr(Number(Float(a))))
| Bool (a) ->  Const(Sexpr(Bool (a)))
| Char(a)-> Const(Sexpr(Char(a)))
| String(a)-> Const (Sexpr(String(a)))
| Pair(Symbol("quote"), Pair(a, Nil)) -> Const(Sexpr(a))
| Symbol(a)-> if( List.mem a reserved_word_list)  then raise X_not_yet_implemented else Var(a)
| Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) ->
  If(tag_parse test, tag_parse dit, tag_parse dif)
| Pair(Symbol("if"), Pair(test, Pair(dit, Nil)))->
  If(tag_parse test, tag_parse dit, Const (Void))
|Pair(Symbol("define"),(Pair(Symbol(name) ,(Pair(expr, Nil)))))-> define_tag_parser name expr
|Pair(Symbol("set!"),(Pair(Symbol(name) ,(Pair(expr, Nil)))))->set_tag_parser name expr
|Pair(Symbol("begin"), Pair(exprs,Nil))-> seq_tag_parser exprs
|Pair(Symbol("or"),Pair(exprs,Nil))->or_tag_parser exprs
|Pair(Symbol("lambda"), Pair(args, body)) -> lambda_tag_parser args body
|Pair(Symbol "let",Pair(Pair(rib, ribs), Pair(body, Nil))) ->raise X_not_yet_implemented
|Pair (Symbol (functionName), args)->applic_tag_parser functionName args
(*|Pair(Symbol "and", Pair(sexpr, Nil)) -> and_macro_extension sexpr*)
| _ -> raise X_syntax_error 

(* ------------------------------- and -------------------------------------*)

(*
and and_macro_extension sexpr= 
match  
*)

(* ------------------------------- lambda -------------------------------------*)

and lambda_tag_parser args body= 
(match args with 
    |Symbol(vs) -> LambdaOpt([], vs ,seq_tag_parser body)
    | Pair(car,cdr) -> let converted_args = convert_to_string_list args in 
                      if (is_not_duplicated_args converted_args) then
                              if(is_improper_list args)
                              then LambdaOpt(converted_args, find_last_element(converted_args), seq_tag_parser body)
                              else LambdaSimple(converted_args, seq_tag_parser body)
                      else raise X_not_yet_implemented
|_ -> raise X_not_yet_implemented) 
(* ------------------------------- map -------------------------------------*)

and map_tag_parse args = 
List.map tag_parse (convert_to_sexpr_list args)

(*---------------------------- or  ----------------------------------------*)
and or_tag_parser exprs= 
let tagParsedExprs = map_tag_parse exprs in
(match tagParsedExprs with
    |[]->Const(Sexpr(Bool(false)))
    |[tagParsedExprs]-> tagParsedExprs
    |_->Or(tagParsedExprs))

(*--------------------------- seq --------------------------------------------- *)
and seq_tag_parser exprs = 
let tagParsedExprs = map_tag_parse exprs in
(match tagParsedExprs with
    |[]->Const(Void)
    |[tagParsedExprs]-> tagParsedExprs
    |_->Seq(tagParsedExprs))

(*--------------------------- Applic ------------------------------------------- *)

and applic_tag_parser functionName args = 
let tag_parsed_functionName = tag_parse (Symbol(functionName)) in
let tag_parsed_args = map_tag_parse args in
Applic(tag_parsed_functionName ,tag_parsed_args) 

(*------------------------------ Define ----------------------------------------*)
and define_tag_parser name expr =
let tag_parsed_name = tag_parse(Symbol(name)) in
 let tag_parsed_expr = tag_parse expr in
 Def(tag_parsed_name,tag_parsed_expr)
(*------------------------------ Set ----------------------------------------*)

and set_tag_parser name expr = 
let tag_parsed_name = tag_parse(Symbol(name)) in
let tag_parsed_expr = tag_parse expr in
Set(tag_parsed_name,tag_parsed_expr);;


let tag_parse_expression sexpr = tag_parse sexpr;;
let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr;;


let test string = 
tag_parse (Reader.read_sexpr string);;

let test_reader string = 
Reader.read_sexpr string;;

end;; (* struct Tag_Parser *)

