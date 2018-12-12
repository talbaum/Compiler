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
  val test :  string -> expr'
end;;

module Semantics : SEMANTICS = struct

let rec annotate_lex e paramsList boundList =  match e with
  | Const(e) -> Const'(e)
  | If (testExp , thenExp , elseExp) -> If'(annotate_lex testExp paramsList boundList  , annotate_lex thenExp paramsList boundList , annotate_lex elseExp paramsList boundList )
  | Seq(expr_list) ->  Seq'(map_annotate expr_list paramsList boundList )
  | Set (name , value) -> Set'(annotate_lex name paramsList boundList , annotate_lex value paramsList boundList )
  | Def (name , value) -> Def'(annotate_lex name paramsList boundList , annotate_lex value paramsList boundList )
  | Or(expr_list) -> Or'(map_annotate  expr_list paramsList boundList )
  | LambdaSimple (args, body) ->  lambdaSimpleHandler args body boundList
  | LambdaOpt (args, vs, body) -> lambdaOptHandler args vs body boundList
  | Applic (function_name , args) -> Applic'((annotate_lex function_name paramsList boundList), (map_annotate args paramsList boundList))
  | Var(e) -> get_type_of_var e paramsList boundList

(*------------------------------------------ need to implement new_boundlist*)
 and lambdaSimpleHandler  args body boundList  = 
let incLevel_boundList = (higher_lambda_level boundList) in
let new_boundlist = expand_bound_list incLevel_boundList args in 
let new_body = (annotate_lex body args new_boundlist) in
LambdaSimple'(args, new_body)  

and lambdaOptHandler  args vs body boundList  = 
let incLevel_boundList = (higher_lambda_level boundList) in
let new_vs_boundlist = expand_bound_list incLevel_boundList [vs] in 
let new_boundlist = expand_bound_list new_vs_boundlist args in 
let new_body = (annotate_lex body args new_boundlist) in
LambdaOpt'(args,vs, new_body)  

and expand_bound_list boundList params_to_add =
let new_list = List.map (fun(param)-> [param ; (string_of_int (-1)) ;  (string_of_int (indexInParametersList param params_to_add 0))]) params_to_add in
new_list @ boundList 

and higher_lambda_level boundList = 
List.map (fun(param)-> [(List.hd param) ; (string_of_int ((int_of_string (List.nth param 1))+1)) ;  (List.nth param 2)]) boundList

and  indexInParametersList name params i = 
if List.length params == 0 then -1
else if (List.hd params) == name then i 
    else indexInParametersList name (List.tl params) (i+1)
    
and map_annotate list paramsList boundList  = List.map (fun(element) -> annotate_lex element paramsList boundList) list  



and  get_type_of_var e paramsList boundList= 
if (List.mem e paramsList) then
let index = indexInParametersList e paramsList 0 in
Var'(VarParam(e, index))
else
let boundVarNames = List.map (fun(triplet)->List.hd triplet) boundList in
if (List.mem e boundVarNames) then
let tripletindex = (indexInParametersList e boundVarNames 0)in
let currentTriplet = List.nth boundList tripletindex in
let majorIndex = int_of_string (List.nth currentTriplet 1) in
let minorIndex = int_of_string (List.nth currentTriplet 2) in
Var'(VarBound(e,majorIndex,minorIndex))
else Var'(VarFree(e));;



let rec annotate_tp e in_tp =  match e with
  | Const'(e) -> Const'(e)
  | If' (testExp , thenExp , elseExp) -> if in_tp then If'(annotate_tp testExp false,annotate_tp thenExp true,annotate_tp elseExp true) else 
    If'(annotate_tp testExp false,annotate_tp thenExp false,annotate_tp elseExp false)
  | Seq'(expr_list) ->  if in_tp then Seq'(map_annotate_tp expr_list)else Seq'(map_annotate_tp_all_false expr_list)
  | Set' (name , value) -> Set'(annotate_tp name false , annotate_tp value false)
  | Def' (name , value) -> Def'(annotate_tp name false , annotate_tp value false )
  | Or'(expr_list) -> if in_tp then Or'(map_annotate_tp  expr_list) else Or'(map_annotate_tp_all_false expr_list)
  | LambdaSimple' (args, body) ->  LambdaSimple' (args,(annotate_tp body true))
  | LambdaOpt' (args, vs, body) -> LambdaOpt' (args, vs, (annotate_tp body true))
  | Applic' (function_name , args) -> if in_tp then ApplicTP'((annotate_tp function_name true), (map_annotate_tp_all_false args ))
            else Applic'((annotate_tp function_name false), map_annotate_tp_all_false args )
  | Var'(e) -> Var'(e)
  | Box'(e) -> Box'(e) 
  | BoxGet'(e) -> BoxGet'(e)
  | BoxSet'(e,expr) ->  BoxSet'(e,annotate_tp expr false ) 
  (* | ApplicTP'(e,r) ->raise X_not_yet_implemented   *)
  | _ ->raise X_syntax_error  

and map_annotate_tp list    = 
let reversed = List.rev list in
let tail = List.tl reversed in
let allButLast = List.rev tail in
let last = List.hd reversed in
let annotatedLast = annotate_tp last true in
let annotatedAllButLast = List.map (fun(element) -> annotate_tp element false) allButLast  in
annotatedAllButLast @ [annotatedLast]

and map_annotate_tp_all_false list  = List.map (fun(element) -> annotate_tp element false) list  ;;


let rec annotate_box e box_args=  match e with
| Const'(e) -> Const'(e)
| If' (testExp , thenExp , elseExp) -> If'(annotate_box testExp box_args,annotate_box thenExp box_args,annotate_box elseExp box_args)
| Seq'(expr_list) ->  Seq'(map_annotate_box expr_list box_args)
(* | Set' (name, value) -> check_smthg *)
| Def' (name , value) -> Def'(annotate_box name box_args , annotate_box value box_args)
| Or'(expr_list) -> Or'(map_annotate_box  expr_list box_args) 
| LambdaSimple' (args, body) -> 
     LambdaSimple' (args,annotate_box body box_args)
| LambdaOpt' (args, vs, body) -> 
    LambdaOpt' (args, vs, annotate_box body box_args)
| Applic' (function_name , args) -> Applic'((annotate_box function_name box_args), map_annotate_box args box_args)
| ApplicTP'(function_name,args) -> ApplicTP'((annotate_box function_name box_args),map_annotate_box args box_args)
| Var'(VarParam(e, minor))  ->Var'(VarParam(e, minor))
(* | Var'(VarBound(e,major, minor)) -> check_other_smthg *)
| Var'(VarFree(e))  -> Var'(VarFree(e))
| Box'(e) -> Box'(e) 
| BoxGet'(e) -> BoxGet'(e)
| BoxSet'(e,expr) ->  BoxSet'(e,annotate_box expr box_args)  
| _ ->raise X_syntax_error

and map_annotate_box list box_args  = List.map (fun(element) -> annotate_box element box_args ) list  


(* and should_box e var = 
let read_lambdas = is_read_appaerance e var in
let write_lambdas = is_write_appearence e var in
let clean_read_lambdas = remove_true read_lambdas in
let clean_write_lambdas = remove_true write_lambdas in
if List.length clean_read_lambdas > 0 && List.length clean_write_lambdas > 0 then
List.map(fun(elem) -> (( if List.mem elem clean_read_lambdas == false then return true ))) clean_write_lambdas
List.map(fun(elem) -> (( if List.mem elem clean_write_lambdas == false then return true ))) clean_read_lambdas
return false *)


and remove_true list =
let predicate (element,_) = element != true in
List.filter (predicate) list
(* 

and is_read_appaerance e var = match e with
  | Const'(e) -> []
  | Var' (e) -> (match var with
       |Var'(v) ->  if e == v then [true] else []
       | _ -> raise X_not_yet_implemented)
  | Box' (e)-> []
  | BoxGet' (e) ->[]
  | BoxSet'(e,p) -> []
  | If' (test, _then, _else) -> (is_read_appaerance test var) @ (is_read_appaerance _then var) @ (is_read_appaerance _else var)
  | Seq' (expr_list) -> map_is_read expr_list var
  | Set' (name,value) -> (is_read_appaerance name var) @ (is_read_appaerance value var)
  | Def'(name,value) -> (is_read_appaerance name var) @ (is_read_appaerance value var)
  | Or' (expr_list) -> map_is_read expr_list var
  | LambdaSimple' (args, body) ->  let parsed_body = is_read_appaerance body var in
                                   if parsed_body == [] then [] else [e]
  | LambdaOpt' (args,vs, body) -> let parsed_body = is_read_appaerance body var in
                                   if parsed_body == [] then [] else [e]
  | Applic' (function_name , args) -> (is_read_appaerance function_name var)  @ (is_read_appaerance args var) 
  | ApplicTP' (function_name , args) -> (is_read_appaerance function_name var)  @ (is_read_appaerance args var) 

and map_is_read list var  = List.map (fun(element) -> is_read_appaerance element var ) list  

and is_write_appearence e var = match e with
  | Const'(e) -> []
  | Var' (e) -> []
  | Box' (e)-> []
  | BoxGet' (e) ->[]
  | BoxSet'(e) -> []
  | If' (test, _then, _else) -> (is_write_appearence test var) @ (is_write_appearence _then var) @ (is_write_appearence _else var)
  | Seq' (expr_list) -> map_is_write expr_list var
  | Set' (name,value) -> (match var with
       |Var'(v) ->  if name == v then [true] else []
       | _ -> raise X_not_yet_implemented)
  | Def'(name,value) -> (is_write_appearence name var) @ (is_write_appearence value var)
  | Or' (expr_list) -> map_is_write expr_list var
  | LambdaSimple' (args, body) ->  let parsed_body = is_write_appearence body var in
                                   if parsed_body == [] then [] else [e]
  | LambdaOpt' (args,vs, body) -> let parsed_body = is_write_appearence body var in
                                   if parsed_body == [] then [] else [e]
  | Applic' (function_name , args) -> (is_write_appearence function_name var)  @ (is_write_appearence args var) 
  | ApplicTP' (function_name , args) -> (is_write_appearence function_name var)  @ (is_write_appearence args var) 

  and map_is_write list var  = List.map (fun(element) -> is_write_appearence element var ) list ;; *)
  ;;


let annotate_lexical_addresses e = annotate_lex e [] [] ;;

let annotate_tail_calls e =  annotate_tp e false;;

let box_set e = annotate_box e [] ;;

let test e = annotate_lexical_addresses (Tag_Parser.tag_parse_expression (Reader.read_sexpr(e)))

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
