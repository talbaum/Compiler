#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * ('a * string)) list
  val make_fvars_tbl : expr' list -> (string * 'a) list
  val generate : (constant * ('a * string)) list -> (string * 'a) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
  let list_to_string s =
    String.concat "" (List.map (fun str ->  str) s);;

  let rec collect_all_sexprs asts sexpr_list = match asts with
  | Const'(e) -> [sexpr_list] @ [e] (* verify order *)
  | If' (testExp , thenExp , elseExp) -> collect_all_sexprs testExp sexpr_list @ collect_all_sexprs thenExp sexpr_list @ collect_all_sexprs elseExp sexpr_list 
  | Seq'(expr_list) ->  map_collect_sexprs expr_list sexpr_list 
  | Set'(name , value) -> collect_all_sexprs name sexpr_list @ collect_all_sexprs value sexpr_list 
  | Def' (name , value) -> collect_all_sexprs name sexpr_list @ collect_all_sexprs value sexpr_list 
  | Or'(expr_list) -> map_collect_sexprs  expr_list sexpr_list 
  | LambdaSimple' (args, body) ->  collect_all_sexprs body sexpr_list (*check if should do for args too *)
  | LambdaOpt' (args, vs, body) -> collect_all_sexprs body sexpr_list
  | Applic' (function_name , args) -> collect_all_sexprs function_name sexpr_list @ map_collect_sexprs args sexpr_list
  | ApplicTP' (function_name , args) -> collect_all_sexprs function_name sexpr_list @ map_collect_sexprs args sexpr_list
  | Box' (e)-> type_of_var e sexpr_list
  | BoxGet' (e) -> type_of_var e sexpr_list
  | BoxSet'(e,p) ->  type_of_var e sexpr_list @ collect_all_sexprs p sexpr_list
  | Var'(e) -> type_of_var e sexpr_list
  |_ -> []
  
  and map_collect_sexprs list sexpr_list  =
   let after_map_list = List.map (fun(element) -> collect_all_sexprs element sexpr_list) list in
  List.flatten after_map_list

  and type_of_var e sexpr_list= match e with
  | VarBound(name, major,minor) -> [sexpr_list] @ [Sexpr(String(name))] 
  | VarParam(name, minor) -> [sexpr_list] @ [Sexpr(String(name))] 
  | VarFree(name) -> [sexpr_list] @ [Sexpr(String(name))] 
;;

(* let tmp element copy_list = 
let rev_list = List.rev copy_list in
let without_first_elem = List.remove_assoc element rev_list in
let list_without_first_elem_good_order = List.rev without_first_elem in 
if List.length list_without_first_elem_good_order = List.length copy_list then element else Nil

let rec remove_duplicate list = let copy_list = list in
match list with
|[] -> Nil
|[hd,tl]-> tmp hd copy_list @ [remove_duplicate (List.tl copy_list)]
;; *)

let is_in_list elem list = if List.mem elem list then list else elem :: list
let remove_duplicate list = List.fold_right is_in_list list []
let isEqual_constant e1 e2=
  match e1, e2 with
  |  Void,  Void -> true
  | (Sexpr s1), (Sexpr s2) -> sexpr_eq s1 s2
  | _-> false;;

let find_element e constant_table = 
  let find_me = (match e with 
  | Symbol(x) -> String(x)
  | rest -> rest) in
  let offset_list = List.map (fun(tuple)-> 
          let (sexpr,offset,_) = tuple in
          if isEqual_constant ((Sexpr(find_me))) sexpr = true then offset else -1) constant_table in
  let ans = List.filter (fun(x) -> x!= -1) offset_list in 
  match ans with
  | [num] -> string_of_int num
  | _ -> raise X_not_yet_implemented
 ;;


let rec build_topolig_list constant_set = 
(* List.fold_right handle_single_sexpr sexpr_set *)
List.map handle_single_constant constant_set

and handle_single_constant constants = match constants with
  | Sexpr(Symbol(str)) as sym -> [Sexpr(String(str))] @ [sym] 
  | Sexpr(Pair (hd,tail)) as p -> ([Sexpr(hd)] @ [Sexpr(tail)] @ [p]) @ (handle_single_constant (Sexpr(hd))) @ (handle_single_constant (Sexpr (tail))) (* verify order *)
  | Sexpr(Vector(sexpr_list)) as v -> handle_vector(sexpr_list) @ [v]
  | Void -> []
  | Sexpr(rest) as const_rest -> [const_rest]

and handle_vector sexpr_list = 
(* List.fold_right handle_single_vector_elem sexpr_list *)
let tmp = List.map (fun(e) -> handle_single_constant (Sexpr(e)) )sexpr_list in
List.flatten tmp;;

let get_size elem = match elem with
  | Sexpr(Nil) -> 1
  | Void -> 1
  | Sexpr(Bool(e)) -> 2
  | Sexpr(Char(e)) -> 2
  | Sexpr(Number(e)) -> 9
  | Sexpr(Symbol (e)) -> 9 
  | Sexpr(String (e)) -> String.length e + 9
  | Sexpr(Pair (car,cdr)) -> 17
  | Sexpr(Vector (sexprs_list))-> ((List.length sexprs_list) * 8) + 9
;;

let get_offset constant_table = match constant_table with
| [] -> 0
| _ -> let rev_table = List.rev constant_table in
       let last = List.hd rev_table in
       let (_,last_offset,_)=last in
       last_offset;;

let rec get_represent elem constant_table= match elem with
  | Sexpr(Nil) -> "MAKE_NIL"
  | Void -> "MAKE_VOID"
  | Sexpr(Bool(e)) -> if e = true then "MAKE_BOOL(1)" else "MAKE_BOOL(0)"
  | Sexpr(Char(e)) -> "MAKE_CHAR(" ^ (Char.escaped e) ^ ")"
  | Sexpr(Number(Int(e))) -> "MAKE_INT(" ^ (string_of_int e) ^ ")"
  | Sexpr(Number(Float(e))) -> "MAKE_FLOAT(" ^(string_of_float e) ^ ")"
  | Sexpr(Symbol (e) as tmp) ->  "MAKE_LITERAL_SYMBOL(" ^ (find_element tmp constant_table) ^  ")"                             (*implement this*)
  | Sexpr(String (e)) -> "MAKE_STRING(" ^ e ^ ")"
  | Sexpr(Pair (car,cdr)) -> "MAKE_LITERAL_PAIR(" ^ (find_element car constant_table) ^ "," ^ (find_element cdr constant_table) ^ ")"
  | Sexpr(Vector (sexprs_list))-> "MAKE_VECTOR(" ^ 
      (list_to_string(List.map (fun(elem) -> get_represent (Sexpr(elem)) constant_table) sexprs_list )) ^ ")"
;;

let create_const_table list constant_table= 
let parsed_table =  List.map (fun(elem)-> 
  let size = get_size elem in
  let offset = get_offset constant_table in
  let represent = get_represent elem constant_table in
  constant_table  @ [(elem , (size + offset) , represent)]) list in 
let rev_list = List.rev parsed_table in 
List.hd rev_list;;


  let make_consts_tbl asts = 
  let constants_list = collect_all_sexprs asts (Sexpr(Nil)) in
  let constants_set  = remove_duplicate constants_list in
  let expanded_list = build_topolig_list constants_set in
  let no_dups_list = remove_duplicate expanded_list in
  create_const_table (List.flatten no_dups_list) [];; 
  
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

