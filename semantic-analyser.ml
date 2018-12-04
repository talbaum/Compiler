(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct
let second e= (List.hd (List.tl e));;

let rec annotate_lex e paramsList boundList =  match e with
  | Const(e) -> Const'(e)
  | If (testExp , thenExp , elseExp) -> If'(annotate_lex testExp paramsList boundList  , annotate_lex thenExp paramsList boundList , annotate_lex elseExp paramsList boundList )
  | Seq(expr_list) ->  Seq'(map_annotate expr_list paramsList boundList )
  | Set (name , value) -> Set'(annotate_lex name paramsList boundList , annotate_lex value paramsList boundList )
  | Def (name , value) -> Def'(annotate_lex name paramsList boundList , annotate_lex value paramsList boundList )
  | Or(expr_list) -> Or'(map_annotate  expr_list paramsList boundList )
  | LambdaSimple (args, body) ->  lambdaSimpleHandler args body paramsList boundList
  | LambdaOpt (args, vs, body) -> LambdaOpt' (args, vs, annotate_lex body args (num_of_lambdas + 1))
  | Applic (function_name , args) -> get_type_of_applic function_name args
  | Var(e) -> get_type_of_var e paramsList

(*------------------------------------------ need to implement new_params and new_boundlist*)
and lambdaSimpleHandler  args body paramsList boundList  = 
let new_params= in 
let new_boundlist = in 
let new_body = (annotate_lex body new_params new_boundlist) in
LambdaSimple'(args, new_body)

and map_annotate list paramsList boundList  = List.map (annotate_lex paramsList boundList) list  

and get_type_of_applic function_name args = raise X_not_yet_implemented

and  get_type_of_var e paramsList= 
let curSecond = (second e) in
if (List.mem curSecond paramsList) then
let index = indexInParametersList curSecond paramsList 0 in
VarParam(curSecond, index);;





let rec indexInParametersList name params i = 
if List.empty params then -1
else if (List.hd params) == name then i 
    else indexInParametersList (List.tl) name (i+1)


let annotate_lexical_addresses e = annotate_lex e [] 0 ;;

let annotate_tail_calls e = raise X_not_yet_implemented;;

let box_set e = raise X_not_yet_implemented;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
