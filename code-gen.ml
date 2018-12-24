#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * ('a * string)) list
  val make_fvars_tbl : expr' list -> (string * 'a) list
  val generate : (constant * ('a * string)) list -> (string * 'a) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  let rec collect_all_sexprs asts sexpr_list = match asts with
  | Const'(Sexpr(e)) -> [sexpr_list] @ [e]
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
  | Var'(VarBound(name, major,minor)) ->[sexpr_list] @ [String(name)]
  | Var'(VarParam(name, minor)) -> [sexpr_list] @ [String(name)]
  | Var'(VarFree(name)) -> [sexpr_list] @ [String(name)] 
  |_ -> []
  
  and map_collect_sexprs list sexpr_list  =
   let after_map_list = List.map (fun(element) -> collect_all_sexprs element sexpr_list) list in
  List.flatten after_map_list

  and type_of_var e sexpr_list= match e with
  | VarBound(name, major,minor) -> [sexpr_list] @ [String(name)] 
  | VarParam(name, minor) -> [sexpr_list] @ [String(name)] 
  | VarFree(name) -> [sexpr_list] @ [String(name)] 
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

let rec build_topolig_list sexpr_set = 
(* List.fold_right handle_single_sexpr sexpr_set *)
List.map handle_single_sexpr sexpr_set


and handle_single_sexpr sexprs = match sexprs with
  | Symbol(str) as sym -> [String(str)] @ [sym] 
  | Pair (hd,tail) as p -> ([hd] @ [tail] @ [p]) @ (handle_single_sexpr hd) @ (handle_single_sexpr tail)
  | Vector(sexpr_list) as v -> handle_vector(sexpr_list) @ [v]
  | rest -> [rest]

and handle_vector sexpr_list = 
(* List.fold_right handle_single_vector_elem sexpr_list *)
let tmp = List.map handle_single_vector_elem sexpr_list in
List.flatten tmp

and handle_single_vector_elem sexpr_list = match sexpr_list with
  | Symbol(str) as sym -> [String(str)] @ [sym] 
  | Pair (hd,tail) as p -> ([hd] @ [tail] @ [p]) @ (handle_single_vector_elem hd) @ (handle_single_vector_elem tail)
  | Vector(sexpr_list) as v -> handle_vector(sexpr_list) @ [v]
  | rest -> [rest]
;;
let create_const_table = raise X_not_yet_implemented;;

  let make_consts_tbl asts = 
  let sexpr_list = collect_all_sexprs asts Nil in
  let sexpr_set  = remove_duplicate sexpr_list in
  let expanded_list = build_topolig_list sexpr_set in
  let no_dups_list = remove_duplicate expanded_list in
  create_const_table no_dups_list;; 
  
  ;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

