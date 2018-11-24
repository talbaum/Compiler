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
exception X_unquote_splicing_error;;
exception X of sexpr;;
exception X_split_to_twoLists of sexpr;;
exception X_lambda of sexpr;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

(* work on the tag parser starts here *)

let tag_parse_expression sexpr = raise X_not_yet_implemented;;

let tag_parse_expressions sexpr = raise X_not_yet_implemented;;

end;; (* struct Tag_Parser *)
let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

let not_reserved_word s = andmap (fun x-> (compare x s !=0 )) reserved_word_list ;;
let rec not_dup s = 
  match s with
  | [] -> true
  | [a] -> true
  | _ -> (let first = List.hd s in 
  let newlist= List.tl s in 
  let dup =  andmap (fun x-> (compare x first !=0)) newlist in
  if(dup =false )
            then false 
            else not_dup newlist);;
 

let rec to_list s = 
  match s with 
  | Pair(a,b)-> a::to_list b
  | Nil -> []
  | y -> raise (X y) ;;

let rec to_list_string s = 
  match s with 
  | Pair(Symbol(a),b) -> a::to_list_string b
  | Pair (Nil ,Symbol(b))-> [b]
  | Nil -> []
  | Symbol(a) -> [a]
  | y -> raise (X y) ;;

let rec last_elem s = 
  match s with
  | Pair (Symbol (a),b) -> last_elem b
  | Pair(Nil, Symbol(b))-> b
  | Symbol (c) -> c
  | y -> raise (X y) ;;

let rec to_list_string_no_last s =
  match s with 
  | Pair(Symbol(a),b) -> a::to_list_string_no_last b
  | Pair (Nil ,Symbol(b))-> []
  | Symbol (c) -> []
  | y -> raise (X y) ;;

let rec is_proper s = 
  match s with 
  | Pair(a,b) -> if b = Nil
                  then true 
                  else is_proper b
  | Nil -> true
  | _ -> false;;

let rec pair_from_list s = 
    match s with
    | [] -> Nil
    | hd::tl -> Pair (hd, pair_from_list tl);;
  
let split_to_twoLists pair =
      let rec split pair (vars, vals) =
        match pair with
        | Pair ((Symbol _) as l, Pair(r, Nil))-> (Pair (l, vars),Pair(r, vals))
        | Pair (Pair ((Symbol _) as l, Pair (r, Nil)), tl) -> split tl (Pair (l, vars), Pair (r, vals))
        | Nil -> (pair_from_list (List.rev (to_list vars)), pair_from_list (List.rev (to_list vals)))
        | y ->raise (X_split_to_twoLists y)   in
  split pair (Nil, Nil);;
  
  
let rec tag_parser_qq sexpr =
    match sexpr with
    | (Pair((Symbol("unquote")), (Pair(sexpr, Nil)))) -> sexpr
    | (Pair((Symbol("unquote-splicing")), (Pair(sexpr, Nil)))) -> raise X_unquote_splicing_error
    | (Vector(expr))-> raise X_not_yet_implemented
    | (Pair(a, b)) ->
        (match (a, b) with
        | ((Pair((Symbol("unquote-splicing")), (Pair(a, Nil)))), b) ->
	        let exp = tag_parser_qq b in
	        (Pair((Symbol("append")), (Pair(a, (Pair(exp, Nil))))))
        | (a, (Pair((Symbol("unquote-splicing")), (Pair(b, Nil))))) ->
	        let exp = tag_parser_qq a in
	        (Pair((Symbol("cons")), (Pair(exp, (Pair(b, Nil))))))
        | (a, b) ->
	        let a = tag_parser_qq a in
	        let b = tag_parser_qq b in
          (Pair((Symbol("cons")), (Pair(a, (Pair(b, Nil)))))))
    | expr -> expr;;

let tag_parse_letStar sexpr =
  match sexpr with 
  | Pair (args,body) -> (
    match args with 
    | Nil -> Pair(Symbol "let", sexpr)
    | Pair(Pair(Symbol _, Pair(_, Nil)), Nil) -> Pair(Symbol "let", sexpr)
    | _ -> (
      let ar= to_list args in
      let firstarg = List.hd ar in 
      let newlist = List.tl ar in
      let newargs =pair_from_list newlist in
      let body= Pair(Symbol "let*", Pair(newargs, body))in 
      Pair (Symbol "let",Pair(firstarg,Pair(body,Nil)) )))
  | _ -> raise  X_not_yet_implemented;;

let tag_parse_letrec sexpr=
  match sexpr with 
  | Pair (args,body) -> (
    match args with 
    | Nil -> Pair(Symbol "let", sexpr)
    | _-> (
      let (vars,vals) = split_to_twoLists args in
      let arg =to_list vars in 
      let arg =List.map(fun x -> Pair(x, Pair(Symbol("whatever"), Nil)) )arg in
      let arg =pair_from_list arg in 
      let list_args = to_list args in
      let start_body =List.map (fun x -> Pair (Symbol ("set!"), x)) list_args in 
      let body =to_list body in
      let body = pair_from_list( List.append start_body body )in 
      Pair (Symbol "let", Pair (arg,body))
    )
  )| _ -> raise  X_not_yet_implemented;;

let rec tag_parse_cond sexpr = 
  match sexpr with
     | Pair (Pair (predicate, Pair (dit, Nil)), Pair (Pair (Symbol "else", Pair (dif, Nil)), Nil)) -> Pair (Symbol("if"), Pair (predicate, Pair (dit, Pair (dif, Nil))))
	   | Pair (Pair (predicate, Pair (dit, Nil)), Pair (Pair (Symbol "else", Pair (dif, Nil)), _)) -> raise X_syntax_error
	   | Pair (Pair (predicate, Pair (dit, Nil)), Nil) -> Pair (Symbol("if"), Pair (predicate, Pair (dit, Pair (Void, Nil))))
	   | Pair (Pair (predicate, Pair (dit, Nil)), rest) -> Pair (Symbol("if"), Pair (predicate, Pair (dit, Pair (tag_parse_cond rest, Nil))))
	   | Pair (Pair (predicate, Nil), Pair (Pair (Symbol "else", Pair (dif, Nil)), Nil)) -> Pair (Symbol("if"), Pair (predicate, Pair (Nil, Pair (dif, Nil))))
	   | Pair (Pair (predicate, Nil), Pair (Pair (Symbol "else", Pair (dif, Nil)), _)) -> raise X_syntax_error
	   | Pair (Pair (predicate, Nil), Nil) -> Pair (Symbol("if"), Pair (predicate, Pair (Void, Pair (Void, Nil))))
	   | Pair (Pair (predicate, Nil),rest) -> Pair (Symbol("if"), Pair (predicate, Pair (Void, Pair (tag_parse_cond rest, Nil))))
	   | Pair (Pair (predicate, beginbody), Nil) -> Pair (Symbol("if"), Pair (predicate, Pair (Pair (Symbol ("begin"), beginbody), Pair (Void, Nil))))
	   | Pair (Pair (predicate, beginbody), Pair (Pair (Symbol("else"), Pair(dif, Nil)), Nil)) -> Pair (Symbol("if"), Pair (predicate, Pair (Pair (Symbol ("begin"), beginbody), Pair (dif, Nil))))
	   | Pair (Pair (predicate, beginbody), rest) -> Pair (Symbol("if"), Pair (predicate, Pair (Pair (Symbol ("begin"), beginbody), Pair (tag_parse_cond rest, Nil))))
     | _ -> let () = print_string "cond_error" in raise X_syntax_error in

let rec tag_parse sexpr =
  match sexpr with
  | Number(_) -> Const(Sexpr(sexpr))
  | Bool(_) -> Const(Sexpr(sexpr))
  | Char(_) -> Const(Sexpr(sexpr))
  | Nil -> Const(Sexpr(sexpr))
  | String(_) -> Const(Sexpr(sexpr))
  | Pair (Symbol "quote", (Pair (sexpr, Nil))) -> Const(Sexpr(sexpr))
  | Pair (Symbol "quasiquote",(Pair(sexpr, Nil))) -> tag_parse (tag_parser_qq sexpr)
  | Symbol(word) -> if(not_reserved_word word) then Var (word) else raise (X sexpr)
  | Pair (Symbol ("if"),(Pair (cond , (Pair (then_exp ,(Pair (else_exp,Nil))))))) -> If ((tag_parse cond), (tag_parse then_exp), (tag_parse else_exp))
  | Pair (Symbol ("if"),(Pair (cond , (Pair (then_exp , Nil))))) -> If ((tag_parse cond) ,(tag_parse then_exp), Const (Void))
  | Pair (Symbol ("or"),t) -> tag_parse_or t
  | Pair (Symbol ("and"),t) -> (match t with 
    | Nil -> Const( Sexpr(Bool true))
    | Pair (op, Nil) -> tag_parse op
    | _ -> let rec tag_parse_and =(function 
          | Pair (car, Pair (cadr, Nil)) -> Pair (Symbol("if"), Pair (car, Pair (cadr, Pair (Bool false, Nil))))
          | Pair (car, cdr) -> Pair (Symbol("if"), Pair (car, Pair(tag_parse_and cdr, Pair (Bool false, Nil))))
          | _ -> raise X_syntax_error) in
          tag_parse (tag_parse_and t))
  | Pair (Symbol "begin" , sexprs) ->
    let sexprs = List.map tag_parse (to_list sexprs) in
    (match sexprs with
      | [] -> Const (Void) 
      | [sexpr] -> sexpr
      | _ -> Seq sexprs)
  | Pair (Symbol ("lambda"), Pair (args, body))->(
    let sexprs = List.map tag_parse (to_list body)in
    let expr = (match sexprs with
      | [] -> Const (Void) 
      | [sexpr] -> sexpr
      | _ -> Seq sexprs) in
    let list_string = to_list_string args in
    if not_dup list_string
    then if( is_proper args)
      then LambdaSimple (list_string , expr)
      else
        let last = last_elem args in 
        let list_string = to_list_string_no_last args in 
        LambdaOpt (list_string ,last, expr)
    else raise (X_lambda sexpr))
  | Pair(Symbol "lambda", Pair(Symbol s, body)) -> ( 
    let sexprs = List.map tag_parse (to_list body)in
    let expr = (match sexprs with
      | [] -> Const (Void) 
      | [sexpr] -> sexpr
      | _ -> Seq sexprs) in
      LambdaOpt([], s, expr))
  | Pair (Symbol ("define"), Pair(Symbol var, Pair(value, Nil))) -> Def(tag_parse (Symbol(var)), tag_parse value)
  | Pair (Symbol "define", Pair (Pair (name, args), sexpr)) -> tag_parse (
    Pair (Symbol "define", Pair (name, Pair (Pair (Symbol "lambda", Pair (args, sexpr)), Nil))))
  | Pair (Symbol ("set!"), Pair(Symbol var, Pair(value, Nil))) -> Def(tag_parse (Symbol(var)), tag_parse value)
  | Pair (Symbol ("let"), Pair (args, body)) ->(
    let (vars,vals) = split_to_twoLists args in 
    tag_parse (Pair (Pair (Symbol "lambda", Pair (vars, body)), vals)))
  | Pair (Symbol ("let*"),s) -> tag_parse (tag_parse_letStar s)
  | Pair (Symbol ("letrec"),s) -> tag_parse (tag_parse_letrec s)
  | Pair (Symbol "cond", sexpr) -> 
      (match sexpr with
       | Nil -> Const Void
       | Pair (Nil, Nil) -> let () = print_string "cond_error " in raise X_syntax_error
       | Pair (Pair (Symbol "else", Pair (expr, Nil)), Nil) -> tag_parse expr
       | pair -> tag_parse (tag_parse_cond sexpr)
  | Pair (app , args) -> Applic ((tag_parse app), (List.map tag_parse (to_list args)))
  | y -> raise (X y)

  and tag_parse_or sexpr =  
    let list = to_list sexpr in 
    let len= List.length list in 
    if(len = 0)
    then Const(Sexpr(Bool false))
    else Or(List.map (fun (a)->tag_parse a) (list)) ;;
(*
(*constans*)
tag_parse (Bool true);;
tag_parse (Number (Int 5));;
tag_parse (Number (Float 5.3));;
tag_parse (Nil);;
tag_parse (Char 'a');;
tag_parse (String "this is a string");;
tag_parse (Symbol "x");;
tag_parse (Pair(Symbol "quote", Pair(Bool true, Nil)) );;
tag_parse (Pair(Symbol "+", Pair(Number (Int 1), Pair(Number (Int 2), Nil))));;
tag_parse (Pair(Number (Int 1), Pair(Number (Int 2), Pair(Number (Int 3), Nil))));;
(*is*)
tag_parse (Pair(Symbol("if"), Pair(Bool true, Pair(Char 'a', Pair(Char 'b', Nil)))) );;
tag_parse (Pair(Symbol "if", Pair(Bool true, Pair(Number (Int 5), Nil))) );;
(*begin*)
tag_parse (Pair(Symbol "begin", Nil));;
tag_parse  (Pair(Symbol "begin", Pair(Number (Int 5), Pair(Number (Int 1), Pair(Number (Int 2), Nil)))) );;
tag_parse  (Pair(Symbol "begin", Pair(Number (Int 5), Nil)) );;
tag_parse  (Pair(Symbol "begin", Pair(Symbol"a", Nil)));;
(*set!*)
tag_parse   (Pair(Symbol "set!", Pair(Symbol "x", Pair(Number (Int 7), Nil))) );;
(*define*)
tag_parse   (Pair(Symbol "define", Pair(Symbol "x", Pair(Number (Int 5), Nil))) );;
tag_parse (Pair(Symbol "define", Pair(Symbol "sq", Pair(Pair(Symbol "*", Pair(Symbol "x", Pair(Symbol "x", Nil))), Nil))));;
(*or*)
tag_parse   (Pair(Symbol "or", Nil) );;
tag_parse  ( Pair(Symbol "or", Pair(Number (Int 1), Pair(Number (Int 2), Pair(Number (Int 3), Nil)))) );;
(*lambdaSimple*)
tag_parse (Pair(Symbol "lambda", Pair(
  Pair(Symbol "x", Pair(Symbol "y", Pair(Symbol "z", Nil))),
  Pair(Number (Int 1), Pair(Number (Int 2), Pair(Number (Int 3), Nil))))) );;
tag_parse (Pair(Symbol "lambda", Pair(Pair(Symbol "x", Pair(Symbol "y", Pair(Symbol "z", Nil))), Pair(Pair(Symbol "x", Nil), Nil))));;

tag_parse (Pair(Symbol "lambda", Pair(Pair(Symbol "x", Nil), Pair(Pair(Symbol "+", Pair(Symbol "x", Pair(Symbol "x", Nil))), Nil))));;
tag_parse(Pair(Symbol "lambda", Pair(Pair(Symbol "x", Pair(Symbol "y", Pair(Symbol "z", Nil))), Pair(Pair(Number(Int 1), Nil), Nil))));;
(*no args*)
tag_parse (Pair(Symbol "lambda", Pair(Nil, Pair(Number (Int 5), Nil))) );;
(*lambdaOpt*)
tag_parse (Pair(Symbol "lambda", Pair(Pair(Symbol "x", Pair(Symbol "y", Symbol "z")), Pair(Pair(Symbol "x", Nil), Nil))));;
tag_parse  (Pair(Symbol "lambda", Pair(Pair(Symbol "x", Pair(Symbol "y", Symbol "z")), Pair(Pair(Symbol "+", Pair(Symbol "x", Pair(Symbol "y", Nil))), Pair(Number (Int 2), Pair(Number (Int 3), Pair(Number (Int 5), Nil)))))));;
tag_parse (Pair(Symbol "lambda", Pair(Pair(Nil, Symbol "z"), Pair(Pair(Symbol "x", Nil), Nil))));;
tag_parse (Pair(Symbol "lambda", Pair(Pair(Nil, Symbol "z"), Pair(Symbol "x", Nil))));;
tag_parse (Pair(Symbol "lambda", Pair(Pair(Symbol "x", Pair(Symbol "y", Symbol "z")), Pair(Symbol "x", Nil))));;
(*variadict*)
tag_parse (Pair(Symbol "lambda", Pair(Symbol "x", Pair(Symbol "x", Nil))));;
tag_parse (Pair(Symbol "lambda", Pair(Pair(Symbol "x", Pair(Symbol "y", Nil)), Pair(Symbol "x", Nil))));;
(*let*)
tag_parse(Pair(Symbol "let", Pair(Pair(Pair(Symbol "a", Pair(Number (Int 1), Nil)), Pair(Pair(Symbol "b", Pair(Number (Int 2), Nil)), Nil)), Pair(Pair(Symbol "+", Pair(Symbol "a", Pair(Symbol "b", Nil))), Nil))));;
tag_parse (Pair(Symbol "let", Pair(Pair(Pair(Symbol "a", Pair(Number (Int 1), Nil)), Pair(Pair(Symbol "b", Pair(Number (Int 2), Nil)), Pair(Pair(Symbol "c", Pair(Number (Int 3), Nil)), Nil))), Pair(Symbol "a", Nil))));;
tag_parse (Pair(Symbol "let*", Pair(Pair(Pair(Symbol "a", Pair(Number (Int 1), Nil)), Pair(Pair(Symbol "c", Pair(Number (Int 2), Nil)), Nil)), Pair(Symbol "a", Nil)))
);;
tag_parse (Pair(Symbol "let", Pair(Pair(Symbol "a", Pair(Number (Int 1), Nil)), Pair(Symbol "a", Nil))));;
tag_parse (Pair(Symbol "let*", Pair(Pair(Pair(Symbol "a", Pair(Number (Int 1), Nil)), Pair(Pair(Symbol "c", Pair(Number (Int 2), Nil)), Nil)), Pair(Symbol "a", Nil))));;
tag_parse (Pair(Symbol "let*", Pair(Pair(Pair(Symbol "a", Pair(Number (Int 1), Nil)), Pair(Pair(Symbol "c", Pair(Number (Int 2), Nil)), Pair(Pair(Symbol "b", Pair(Number (Int 3), Nil)), Nil))), Pair(Symbol "a", Pair(Symbol "b", Nil))))
);;
tag_parse (Pair(Symbol "let*", Pair(Nil, Pair(Symbol "a", Pair(Symbol "b", Nil)))));;
*)
let test sexpr=
  match sexpr with 
  | Pair (Symbol "define", Pair (Pair (name, args), sexpr)) -> tag_parse (
    Pair (Symbol "define", Pair (name, Pair (Pair (Symbol "lambda", Pair (args, sexpr)), Nil)))) 
  | _-> raise X_not_yet_implemented;;
 
  let p = Pair(Symbol "letrec", Pair(Pair(Pair(Symbol "a", Pair(Number (Int 1), Nil)), Pair(Pair(Symbol "b", Pair(Number (Int 2), Nil)), Nil)), Pair(Symbol "a", Pair(Symbol "b", Nil))));;
 tag_parse (Pair(Symbol "define", Pair(Pair(Symbol "square", Pair(Symbol "x", Nil)), Pair(Pair(Symbol "*", Pair(Symbol "x", Pair(Symbol "x", Nil))), Nil)))
 );;
 tag_parse (Pair(Symbol "*", Pair(Symbol "x", Pair(Symbol "x", Nil))));;

 (*let arg =
         List.map(fun x -> Pair(x, Symbol("whatever")))  vars  in
      let start_of_body = List.map (fun x -> Pair (Symbol ("set!"), x)) (to_list args) in  
      let body_end = to_list body in 
      let body = start_of_body::body_end in 
      let body = pair_from_list body in 
      Pair (Symbol "let", Pair (arg,body)))*)