#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * int * string) list
  (*  val make_consts_tbl : expr' list -> (constant * ('a * string) list*)
  val make_fvars_tbl : expr' list -> (string * int) list
  (*  val make_fvars_tbl : expr' list -> (string * 'a) list *)
  val generate : (constant * int * string) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

(*---------------------------- Constant var table -----------------------------*)

  let list_to_string s =
    String.concat "" (List.map (fun str ->  str) s);;

  let rec collect_all_sexprs asts sexpr_list = 
  (match asts with
  | [] -> []
  |(ast::others) -> 
  (match ast with
  | Const'(e) -> [sexpr_list] @ [e] @ (collect_all_sexprs others sexpr_list) (* verify order *)
  | If' (testExp , thenExp , elseExp) -> collect_all_sexprs [testExp] sexpr_list @ collect_all_sexprs [thenExp] sexpr_list @ collect_all_sexprs [elseExp] sexpr_list @ (collect_all_sexprs others sexpr_list) 
  | Seq'(expr_list) ->  collect_all_sexprs expr_list sexpr_list @ (collect_all_sexprs others sexpr_list)  
  | Set'(name , value) -> collect_all_sexprs [name] sexpr_list @ collect_all_sexprs [value] sexpr_list @ (collect_all_sexprs others sexpr_list) 
  | Def' (name , value) -> collect_all_sexprs [name] sexpr_list @ collect_all_sexprs [value] sexpr_list @ (collect_all_sexprs others sexpr_list) 
  | Or'(expr_list) -> collect_all_sexprs  expr_list sexpr_list @ (collect_all_sexprs others sexpr_list) 
  | LambdaSimple' (args, body) ->  collect_all_sexprs [body] sexpr_list @ (collect_all_sexprs others sexpr_list) 
  | LambdaOpt' (args, vs, body) -> collect_all_sexprs [body] sexpr_list @ (collect_all_sexprs others sexpr_list) 
  | Applic' (function_name , args) -> collect_all_sexprs [function_name] sexpr_list @ collect_all_sexprs args sexpr_list @ (collect_all_sexprs others sexpr_list) 
  | ApplicTP' (function_name , args) -> collect_all_sexprs [function_name] sexpr_list @ collect_all_sexprs args sexpr_list @ (collect_all_sexprs others sexpr_list) 
  | Box' (e)-> type_of_var [e] sexpr_list @ (collect_all_sexprs others sexpr_list) 
  | BoxGet' (e) -> type_of_var [e] sexpr_list @ (collect_all_sexprs others sexpr_list) 
  | BoxSet'(e,p) ->  type_of_var [e] sexpr_list @ collect_all_sexprs [p] sexpr_list @ (collect_all_sexprs others sexpr_list) 
  | Var'(e) -> type_of_var [e] sexpr_list @ (collect_all_sexprs others sexpr_list) ))


  and type_of_var e sexpr_list= match e with
  | [VarBound(name, major,minor)] -> [sexpr_list] @ [Sexpr(String(name))] 
  | [VarParam(name, minor)] -> [sexpr_list] @ [Sexpr(String(name))] 
  | [VarFree(name)] -> [sexpr_list] @ [Sexpr(String(name))] 
  | _ -> []
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
  | Sexpr(Char(e)) -> "MAKE_LITERAL_CHAR(\'" ^ (Char.escaped e) ^ "\')"
  | Sexpr(Number(Int(e))) -> "MAKE_LITERAL_INT(" ^ (string_of_int e) ^ ")"
  | Sexpr(Number(Float(e))) -> "MAKE_LITERAL_FLOAT(" ^(string_of_float e) ^ ")"
  | Sexpr(Symbol (e) as tmp) ->  "MAKE_LITERAL_SYMBOL(consts+" ^ (find_element tmp constant_table) ^  ")"                             (*implement this*)
  | Sexpr(String (e)) -> "MAKE_LITERAL_STRING \"" ^ e ^ "\""
  | Sexpr(Pair (car,cdr)) -> "MAKE_LITERAL(consts+" ^ (find_element car constant_table) ^ ",consts+" ^ (find_element cdr constant_table) ^ ")"
  | Sexpr(Vector (sexprs_list))-> "MAKE_LITERAL_VECTOR(" ^ 
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


(*---------------------------- Free var table -----------------------------*)


 let rec collect_all_fvars asts fvar_list =   match asts with
  | [] -> []
  |(ast::others) -> 
  (match ast with
  | Const'(e) -> collect_all_fvars others fvar_list 
  | If' (testExp , thenExp , elseExp) -> collect_all_fvars [testExp] fvar_list @ collect_all_fvars [thenExp] fvar_list @ collect_all_fvars [elseExp] fvar_list @ collect_all_fvars others fvar_list
  | Seq'(expr_list) ->  collect_all_fvars expr_list fvar_list @ collect_all_fvars others fvar_list
  | Set'(name , value) -> collect_all_fvars [name] fvar_list @ collect_all_fvars [value] fvar_list @ collect_all_fvars others fvar_list
  | Def' (name , value) -> collect_all_fvars [name] fvar_list @ collect_all_fvars [value] fvar_list @ collect_all_fvars others fvar_list
  | Or'(expr_list) -> collect_all_fvars  expr_list fvar_list @ collect_all_fvars others fvar_list
  | LambdaSimple' (args, body) ->  collect_all_fvars [body] fvar_list @ collect_all_fvars others fvar_list
  | LambdaOpt' (args, vs, body) -> collect_all_fvars [body] fvar_list @ collect_all_fvars others fvar_list
  | Applic' (function_name , args) -> collect_all_fvars [function_name] fvar_list @ collect_all_fvars args fvar_list @ collect_all_fvars others fvar_list
  | ApplicTP' (function_name , args) -> collect_all_fvars [function_name] fvar_list @ collect_all_fvars args fvar_list @ collect_all_fvars others fvar_list
  | Box' (e)-> type_of_var [e] fvar_list @ collect_all_fvars others fvar_list
  | BoxGet' (e) -> type_of_var [e] fvar_list @ collect_all_fvars others fvar_list 
  | BoxSet'(e,p) ->  type_of_var [e] fvar_list @ collect_all_fvars [p] fvar_list @ collect_all_fvars others fvar_list
  | Var'(e) -> type_of_var [e] fvar_list @ collect_all_fvars others fvar_list)

  and type_of_var e fvar_list= match e with
  | [VarBound(name, major,minor)] -> [] 
  | [VarParam(name, minor)] -> (*fvar_list @ [name]*) [] 
  | [VarFree(name)] -> fvar_list @ [name] 
  | _ -> []
;;

let init_const_table = [(Void, 0, "MAKE_VOID");
(Sexpr(Nil), 1, "MAKE_NIL");
(Sexpr(Bool false), 2, "MAKE_BOOL(0)");
(Sexpr(Bool true), 4, "MAKE_BOOL(1)");];;

let rec create_fvar_table fvar_set index = match fvar_set with
| [] -> []
| [x] -> [(x,index)]
| hd::tl -> [(hd,index)] @ (create_fvar_table tl (index + 1)) ;;


  let make_consts_tbl asts = 
  let constants_list = collect_all_sexprs asts (Sexpr(Nil)) in
  let constants_set  = remove_duplicate constants_list in
  let expanded_list = build_topolig_list constants_set in
  let no_dups_list = remove_duplicate expanded_list in
  let initialzied = init_const_table in 
  create_const_table (List.flatten no_dups_list) initialzied;; 
  
  let make_fvars_tbl asts = 
  let fvar_list = collect_all_fvars asts [] in
  let fvar_set = remove_duplicate fvar_list in 
  create_fvar_table fvar_set 0
  ;;
  
  let generate consts fvars e = raise X_not_yet_implemented;;
 (* Printf.sprintf   *)
  (* let generate consts fvars e = match e with
  | Const'(x)->"mov rax,AddressInConstTable(" ^ x ^")" 
  | Var'(VarFree(str)) ->"mov rax, qword [LabelInFVarTable(" ^ str ^")]"
  | Var'(VarParam (str , minor)) -> "mov rax, qword [rbp + 8 ∗ (4 + minor)]"
  | Var'(VarBound (str ,major, minor)) ->"mov rax, qword [rbp + 8 ∗ 2]
  mov rax, qword [rax + 8 ∗ major]
  mov rax, qword [rax + 8 ∗ minor]"
  (* | Box' of var *) (*  /////////////// check if need to implement*)
  | BoxGet'(Var'(v) as vari)-> (generate consts fvars vari ) ^ "\n mov rax, qword [rax]"
  | BoxSet'(Var'(v) as vari ,value) -> 
    let  value_text =(generate consts fvars value ) ^ "\n push rax" in
    let var_text = (generate consts fvars vari ) ^ " \n pop qword [rax]
    mov rax, sob_void" in
    value_text ^ var_text
  | If'(test,dit,dif)->
    let test_text= (generate consts fvars test ) ^ "cmp rax, sob_false
      je Lelse \n" in
    let dit_text = (generate consts fvars dit ) ^ "jmp Lexit
      Lelse: \n" in 
    let dif_text = (generate consts fvars dif ) ^ "Lexit:" in
    test_text ^ dit_text ^ dif_text 
  | Seq' (list) ->(gen_map list "\n")
  | Set(Var'(VarParam'(_, minor)),value)-> (generate consts fvars value ) ^ "
  mov qword [rbp + 8 ∗ (4 + minor)], rax
  mov rax, sob_void"
  | Set(Var'(VarBound' (str ,major, minor)),value)->(generate consts fvars value ) ^
  "mov rbx, qword [rbp + 8 ∗ 2]
  mov rbx, qword [rbx + 8 ∗ major]
  mov qword [rbx + 8 ∗ minor], rax
  mov rax, sob_void"
  | Set(Var'(VarFree'(str)),value)->"mov qword [LabelInFVarTable(v)], rax
  mov rax, sob_void"
  (* | Def' of expr' * expr' *) (*  /////////////// check if need to implement*)
  | Or'(list)-> ((gen_map list "
  cmp rax, sob_false
  jne Lexit") ^ "
  Lexit:")
  (* | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);; *)
  |_->""
  ;;

  let gen_map list code_to_write = 
  let mapped = List.map (fun(elem)-> (generate elem) ^ code_to_write) list in
  (list_to_string mapped) ;; *)


end;;

 let test = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs "(list \"ab\" '(1 2) 'c 'ab)"));;

  let freevartest = make_fvars_tbl test ;; 
  let constvartest = make_consts_tbl test ;; 


