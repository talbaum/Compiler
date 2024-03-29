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
     
| Box'(var1), Box'(var2) -> expr'_eq (Var'(var1)) (Var'(var2))
| BoxGet'(var1), BoxGet'(var2) -> expr'_eq (Var'(var1)) (Var'(var2))
| BoxSet'(var1,expr1), BoxSet'(var2,expr2) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
(expr'_eq (expr1) (expr2))

  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'

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

 and lambdaSimpleHandler  args body boundList  = 
let incLevel_boundList = (higher_lambda_level boundList) in
let new_boundlist = expand_bound_list incLevel_boundList args in 
let new_body = (annotate_lex body args new_boundlist) in
LambdaSimple'(args, new_body)  

and lambdaOptHandler  args vs body boundList  = 
let newArgs = args @ [vs] in
let incLevel_boundList = (higher_lambda_level boundList) in
let new_boundlist = expand_bound_list incLevel_boundList newArgs in 
let new_body = (annotate_lex body newArgs new_boundlist) in
LambdaOpt'(args,vs, new_body)  

and expand_bound_list boundList params_to_add =
let new_list = List.map (fun(param)-> [param ; (string_of_int (-1)) ;  (string_of_int (indexInParametersList param params_to_add 0))]) params_to_add in
new_list @ boundList 

and higher_lambda_level boundList = 
List.map (fun(param)-> [(List.hd param) ; (string_of_int ((int_of_string (List.nth param 1))+1)) ;  (List.nth param 2)]) boundList

and  indexInParametersList name params i = 
if List.length params = 0 then -1
else if (compare (List.hd params) name) = 0 then i 
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
  | Applic' (function_name , args) -> if in_tp then ApplicTP'((annotate_tp function_name false), (map_annotate_tp_all_false args ))
            else Applic'((annotate_tp function_name false), map_annotate_tp_all_false args )
  | Var'(e) -> Var'(e)
  | Box'(e) -> Box'(e) 
  | BoxGet'(e) -> BoxGet'(e)
  | BoxSet'(e,expr) ->  BoxSet'(e,annotate_tp expr false ) 
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


 let add_one  counter = 
 let getCounter = !counter in
 let () = incr counter in 
    getCounter;; 

let counter_write_init : int ref = ref 0;;
let counter_read_init : int ref = ref 0 ;;
 
let rec annotate_box e box_args=  match e with
| Const'(e) -> Const'(e)
| If' (testExp , thenExp , elseExp) -> If'(annotate_box testExp box_args,annotate_box thenExp box_args,annotate_box elseExp box_args)
| Seq'(expr_list) ->  Seq'(map_annotate_box expr_list box_args)
| Def' (name , value) -> Def'(annotate_box name box_args , annotate_box value box_args)
| Or'(expr_list) -> Or'(map_annotate_box  expr_list box_args) 
| Box'(e) -> Box'(e)  
| BoxGet'(vari) -> e
| BoxSet'(vari,expr) -> e
| Set' (Var'(name) as name_var, value) -> 
        if is_in_list name_var box_args then BoxSet'(name,annotate_box value box_args) 
        else Set'(annotate_box name_var box_args,annotate_box value box_args) 
| LambdaSimple' (args, body) -> lambda_handler args "" body false box_args 
| LambdaOpt' (args, vs, body) -> lambda_handler args vs body true box_args 
| Applic' (function_name , args) -> let expr = annotate_box function_name box_args in 
                                     Applic'(expr, map_annotate_box args box_args)
| ApplicTP'(function_name,args) -> let expr = annotate_box function_name box_args in
                                    ApplicTP'(expr, map_annotate_box args box_args)
| Var'(VarBound(name,major,minor) as var_expr)-> if is_in_list e box_args then BoxGet'(var_expr) else Var'(VarBound(name,major,minor))
| Var'(VarParam(name,minor) as var_expr)-> if is_in_list e box_args then BoxGet'(var_expr) else Var'(VarParam(name,minor))
| Var'(VarFree(name))->  Var'(VarFree(name))
| _ ->raise X_syntax_error

and map_annotate_box list box_args  = List.map (fun(element) -> annotate_box element box_args ) list  
 
and is_in_list search_me list = 
  List.mem search_me list 


and update_arg element =   
    match element with
    |Var'(VarBound(name,major,minor))->Var'(VarBound(name, major+1,minor))
    |Var'(VarParam(name,minor))->Var'(VarBound(name, 0, minor))
    |rest ->rest

and is_not_empty v =   
  (compare v "" )!=0

and set_first_exprs v args vs is_param bad_val =  
    if is_not_empty v then
    let minor = indexInParametersList v args 0 in 
    if minor = -1 then if (compare v vs) = 0 then  let vs_index = List.length args in
                                                          if is_param then Var'(VarParam(v, vs_index))
                                                           else Set'(Var'(VarParam(v, vs_index)), Box'(VarParam(v, vs_index)))
                  else bad_val
    else
      if is_param then Var'(VarParam(v, minor))
                  else Set'(Var'(VarParam(v, minor)), Box'(VarParam(v, minor)))
    else bad_val 

and lambda_handler args vs body is_opt box_args =
    let argsWithVS = if(is_opt) then  args @ [vs] else args in  
    let update_vars_in_box_args = List.map (fun(element)->(update_arg element))  box_args in  
    let filtered_box_Vars = List.filter (fun(element) -> (should_box body element)) argsWithVS in  
    let bad_val = Const'(Sexpr(String(""))) in 
    let parmaters = (List.map (fun(v) -> set_first_exprs v args vs true bad_val ) filtered_box_Vars) in 
    let first_exprs = (List.map (fun(v) -> set_first_exprs v args vs false bad_val) filtered_box_Vars) in 
    let without_bad_vals_list = List.filter (fun(x) -> (is_not_equal x bad_val)) first_exprs in  
    let filtered_parmaters = List.filter (fun(element)-> (is_not_equal element bad_val)) parmaters in 
    let new_box_args = filtered_parmaters @ update_vars_in_box_args in 
    let parsed_body = annotate_box body new_box_args in

    if (is_opt) then (lambda_opt_generator args vs parsed_body without_bad_vals_list) 
    else (lambda_simple_generator args parsed_body without_bad_vals_list)

and lambda_opt_generator args vs parsed_body without_bad_vals_list =   
    let new_body = match without_bad_vals_list with 
     | [] -> LambdaOpt' (args,vs,parsed_body)   
     | _ -> let isExistSeq = Seq'(without_bad_vals_list @ [parsed_body]) in
            LambdaOpt' (args,vs,isExistSeq) in
    new_body  

and lambda_simple_generator args parsed_body without_bad_vals_list = 
    let new_body = match without_bad_vals_list with 
     | [] -> LambdaSimple' (args,parsed_body)   
     | _ -> let isExistSeq = Seq'(without_bad_vals_list @ [parsed_body]) in                       
            LambdaSimple' (args,isExistSeq) in
    new_body  

and is_not_equal first second =  
  (compare first second )!=0


and should_box e var = 
let read_lambdas = (is_read_write_appaerance e var  counter_read_init true) in
let write_lambdas = (is_read_write_appaerance e var counter_write_init false) in
if List.length read_lambdas > 0 && List.length write_lambdas > 0 then
let ans = is_same_lambda read_lambdas write_lambdas in
if List.mem true ans then true else false
else false 

and is_same_lambda readlist writelist = 
   List.flatten (List.map (fun (e) -> List.map (fun (e2) -> if (compare e e2) != 0 then true else false) writelist) readlist)



and is_read_write_appaerance e var counter read_flag= 
 match e with
  | Const'(e) -> []
  | Box' (e)-> []
  | BoxGet' (e) ->[]
  | BoxSet'(e,p) -> []
  | If' (test, _then, _else) -> (is_read_write_appaerance test var counter read_flag) @ (is_read_write_appaerance _then var counter read_flag) @ (is_read_write_appaerance _else var counter read_flag)
  | Seq' (expr_list) -> map_is_read_write expr_list var  counter read_flag
  | Def'(name,value) ->  (is_read_write_appaerance  value var counter read_flag)
  | Or' (expr_list) -> map_is_read_write expr_list var  counter read_flag
  | Applic' (function_name , args) -> (map_is_read_write args var counter read_flag) @ (is_read_write_appaerance function_name var counter read_flag)
  | ApplicTP' (function_name , args) -> (map_is_read_write args var counter read_flag) @ (is_read_write_appaerance function_name var counter read_flag)
  | LambdaSimple' (args, body) -> handle_lambda args "" body var counter read_flag
  | LambdaOpt' (args,vs, body) -> handle_lambda args vs body var counter read_flag
  |  Var'(VarBound(name, major,minor)) -> if read_flag then (if (is_equal name var)then [-1] else []) else []  
  |  Var'(VarParam(name, minor)) -> if read_flag then (if (is_equal name var)then [-1] else []) else []       
  | Set' (Var'(VarBound(name, major,minor)),value) -> if read_flag then is_read_write_appaerance value var counter read_flag
                                                                   else test_equality name var counter @ (is_read_write_appaerance value var counter read_flag)
  | Set' (Var'(VarParam(name, minor)),value)-> if read_flag then is_read_write_appaerance value var counter read_flag
                                                            else test_equality name var counter @  (is_read_write_appaerance value var counter read_flag)
  | Set' (Var'(VarFree(name)),value) -> if read_flag then is_read_write_appaerance value var counter read_flag
                                                                   else test_equality name var counter @ (is_read_write_appaerance value var counter read_flag)
  | _->[]


and handle_lambda args vs body var counter read_flag =
let all_args = if(is_not_empty vs) then  args @ [vs] else args in
if not (List.mem var all_args) then
  let lambda_num = add_one counter in
  let parsed_body = is_read_write_appaerance body var counter read_flag in
  if List.length parsed_body > 0 then [lambda_num] else []
else []


and map_is_read_write list var counter read_flag= 
let biglist = List.map (fun(element) -> is_read_write_appaerance element var counter read_flag) list  in
List.flatten biglist

and is_equal first second = 
  compare first second =0

and test_equality name var counter  =  
  let test_val = is_equal name var in
    match test_val with
    |true -> [-1]
    |false -> []

;;

(* and print_list = function 
[] -> ()
| e::l -> print_int e ; print_string " " ; print_list l  *)

let annotate_lexical_addresses e = annotate_lex e [] [] ;;

let annotate_tail_calls e =  annotate_tp e false;;

let box_set e = annotate_box e [] ;;


let run_semantics expr = 
  box_set(
    (annotate_tail_calls
       (annotate_lexical_addresses expr)));;
  
 
end;; (* struct Semantics *)
