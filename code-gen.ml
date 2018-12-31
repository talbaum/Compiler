
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
  | Const'(e) -> sexpr_list @ [e] @ (collect_all_sexprs others sexpr_list) (* verify order *)
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
  | [VarBound(name, major,minor)] -> sexpr_list @ [Sexpr(String(name))] 
  | [VarParam(name, minor)] -> sexpr_list @ [Sexpr(String(name))] 
  | [VarFree(name)] ->[]
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
let remove_dups_wrapper list = let rev = List.rev list in
let rem = remove_duplicate rev in
List.rev rem;;

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
  | _ -> "not found"
 ;;


let rec build_topolig_list constant_set =  match constant_set with
| [] -> []
| (constant :: others) ->
   (match constant with
  | Sexpr(Symbol(str)) as sym -> [Sexpr(String(str))] @ [sym] @ build_topolig_list others
  | Sexpr(Pair (hd,tail)) as p -> [Sexpr(hd)]  @ build_topolig_list [Sexpr(hd)] @ build_topolig_list [Sexpr (tail)]  @ [Sexpr(tail)] @ [p] @ build_topolig_list others(* verify order *)
  | Sexpr(Vector(sexpr_list)) as v -> handle_vector(sexpr_list) @ [v] @ build_topolig_list others
  | Void -> build_topolig_list others
  | Sexpr(rest) as const_rest -> [const_rest] @ build_topolig_list others )

and handle_vector sexpr_list = 
(* List.fold_right handle_single_vector_elem sexpr_list *)
let tmp = List.map (fun(e) -> build_topolig_list [Sexpr(e)] )sexpr_list in
List.flatten tmp;;

let get_size table =  let elem = (List.rev table) in
match elem with
| [] -> 0
| (first::others) ->
let (e,_,_) = first in 
match e with
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
let get_offset_fvars fvars_table = match fvars_table with
| [] -> 0
| _ -> let rev_table = List.rev fvars_table in
       let last = List.hd rev_table in
       let (_,last_offset)=last in
       last_offset;;

let rec get_represent elem constant_table= match elem with
  | Sexpr(Nil) -> "MAKE_NIL"
  | Void -> "MAKE_VOID"
  | Sexpr(Bool(e)) -> if e = true then "MAKE_BOOL(1)" else "MAKE_BOOL(0)"
  | Sexpr(Char(e)) -> Printf.sprintf "MAKE_LITERAL_CHAR(%d)" (Char.code e)
  | Sexpr(Number(Int(e))) -> "MAKE_LITERAL_INT(" ^ (string_of_int e) ^ ")"
  | Sexpr(Number(Float(e))) -> "MAKE_LITERAL_FLOAT(" ^(string_of_float e) ^ ")"
  | Sexpr(Symbol (e) as tmp) ->  "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (find_element tmp constant_table) ^  ")"                             (*implement this*)
  | Sexpr(String (e)) -> "MAKE_LITERAL_STRING \"" ^ e ^ "\""
  | Sexpr(Pair (car,cdr)) -> "MAKE_LITERAL_PAIR(const_tbl+" ^ (find_element car constant_table) ^ ",const_tbl+" ^ (find_element cdr constant_table) ^ ")"
  | Sexpr(Vector (sexprs_list))->
  let tmp = "MAKE_LITERAL_VECTOR(" ^ 
      (list_to_string(List.map (fun(elem) -> "const_tbl+" ^ find_element (elem) constant_table ^ ",") sexprs_list )) in
   String.sub tmp 0 (String.length tmp - 1) ^ ")"
;;
let build_single_constant_row elem constant_table = 
  let size = get_size constant_table in
  let offset = get_offset constant_table in
  let represent = get_represent elem constant_table in
 [(elem , (size + offset) , represent)]


let rec create_const_table list constant_table= match list with
| [] -> []
| (elem::others) -> let new_row = build_single_constant_row elem constant_table in 
  new_row @ (create_const_table others (constant_table @ new_row));;

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

let init_basics = [Void;(Sexpr(Nil));(Sexpr(Bool false));(Sexpr(Bool true));];;

let add_basics list =
init_basics @ list;;

  let make_consts_tbl asts = 
  let constants_list = collect_all_sexprs asts [] in
  let constants_set  = remove_duplicate constants_list in
  let expanded_list = build_topolig_list constants_set in
  let add_basics_to_const_list = add_basics expanded_list in
  let no_dups_list = remove_dups_wrapper add_basics_to_const_list in
  create_const_table no_dups_list [];; 
  

  let init_fvars =  [("boolean?",0);("float?",1);("integer?",2);("pair?",3);("null?",4);("char?",5);("vector?",6);("string?",7);("procedure?",8);("symbol?",9);( "string-length",10);("string-ref",11);("string-set!",12);("make-string",13);("vector-length",14);("vector-ref",15);("vector-set!",16);("make-vector",17);("symbol->string",18);("char->integer",19);("integer->char",20);("eq?",21);("+",22);("*",23);("-",24);("/",25);("<",26);("=",27);("car",28); ("cdr",29); ("set-car!",30);("set-cdr!",31);("cons",32);("apply",33)];;


  let make_fvars_tbl asts = 
  let fvar_list = collect_all_fvars asts [] in
  let fvar_set = remove_duplicate fvar_list in 
  init_fvars @ (create_fvar_table fvar_set 34)
  ;;
    



let rec addressInConstTable constant_table find_me= match constant_table with
| [] -> 0
| _ -> let first = List.hd constant_table in
       let (sexpr,address,_) = first in
       if isEqual_constant sexpr find_me then address else addressInConstTable (List.tl constant_table) find_me;;
       

let rec addressInFvarTable fvar_table find_me= match fvar_table with
| [] -> 0
| _ -> let first = List.hd fvar_table in
       let (fvar_name,address) = first in
       if  fvar_name = find_me then address else addressInFvarTable (List.tl fvar_table) find_me;;
       
let rec get_param_names_as_string params = match params with
| [] -> ""
| (hd::tl) -> hd ^ (get_param_names_as_string tl);;

(* let counter : int ref = ref 0;;
 let add_one  counter = 
 let getCounter = !counter in
 let () = incr counter in 
    getCounter;;  *)
(*let counter=0;*)

   let rec generate_handle consts fvars e env counter =match e with
  | Const'(x)-> let address = addressInConstTable consts x in
                "mov rax, const_tbl+" ^ string_of_int address
  | Var'(VarFree(str)) -> let address = addressInFvarTable fvars str in
                "mov rax, qword [fvar_tbl+" ^ string_of_int address ^"*WORD_SIZE]"
  | Var'(VarParam (str , minor)) -> "mov rax, qword [rbp + (4 + "^string_of_int minor^")*WORD_SIZE]"
  | Var'(VarBound (str ,major, minor)) ->"mov rax, qword [rbp + 8 ∗ 2]
  mov rax, qword [rax + 8 ∗ "^string_of_int major^"]
  mov rax, qword [rax + 8 ∗ "^string_of_int minor^"]"
  (* | Box' of var *) (*  /////////////// check if need to implement generate to var parmam inside the box
  and then it comes back in rax, so after u didi genreate append malloc array (size 1 = size 8)  
  put the address inside the array
   *)
  | BoxGet'(((v)) as vari)-> (generate_handle consts fvars (Var'(vari)) env counter ) ^ "\n mov rax, qword [rax]"
  | BoxSet'((v) as vari ,value) -> 
    let  value_text =(generate_handle consts fvars value env counter ) ^ "\n push rax" in
    let var_text = (generate_handle consts fvars  (Var'(vari)) env counter) ^ " \n pop qword [rax]
    mov rax, SOB_VOID_ADDRESS" in
    value_text ^ var_text
  | If'(test,dit,dif)->  let counter = counter+1 in 
    let test_text= (generate_handle consts fvars test env counter ) ^ "\n cmp rax, SOB_FALSE_ADDRESS
      je Lelse"^ string_of_int(counter) ^" \n" in
    let dit_text = (generate_handle consts fvars dit env counter) ^ "\n jmp Lexit"^ string_of_int(counter) ^"
      Lelse"^ string_of_int(counter) ^": \n" in 
    let dif_text = (generate_handle consts fvars dif env counter) ^ "\n Lexit"^ string_of_int(counter) ^":" in
    test_text ^ dit_text ^ dif_text 
  | Seq' (list) ->(gen_map list "\n" consts fvars env counter)
  | Set'(Var'(VarParam(_, minor)),value)-> (generate_handle consts fvars value env counter) ^ "
  mov qword [rbp + 8 ∗ (4 + "^string_of_int minor^")], rax
  mov rax, SOB_VOID_ADDRESS"
  | Set'(Var'(VarBound (str ,major, minor)),value)->(generate_handle consts fvars value env counter)  ^
  "mov rbx, qword [rbp + 8 ∗ 2]
  mov rbx, qword [rbx + 8 ∗"^string_of_int  major^"]
  mov qword [rbx + 8 ∗"^string_of_int  minor^"], rax
  mov rax, SOB_VOID_ADDRESS"
  | Set'(Var'(VarFree(str)),value)->
  let value_text = (generate_handle consts fvars value env counter) in
  let address = addressInFvarTable fvars str in
  value_text^"\n mov qword [fvar_tbl+" ^ string_of_int address ^"*WORD_SIZE], rax
  mov rax, SOB_VOID_ADDRESS"
  | Def'(Var'(VarFree(str)) , value)-> 
  let value_text = (generate_handle consts fvars value env counter) in
  let address =  addressInFvarTable fvars str in
  value_text ^ "\n" ^
   "mov [fvar_tbl+" ^ (string_of_int address) ^"*WORD_SIZE], rax \n"^ "mov rax, SOB_VOID_ADDRESS \n"

  | Or'(list)-> ((gen_map list ("
  cmp rax, SOB_FALSE_ADDRESS
  jne LexitOr\n") consts fvars env counter) ^ "
  LexitOr:" )
  | LambdaSimple' (params , body) ->
      let lambda_body       = generate_handle consts fvars body (env + 1) counter  in 
      let new_env_size      = string_of_int ((env + 1) * 8) in
      let old_env_size      = string_of_int env in
      let parmas_len        =  string_of_int(List.length params) in 
"
chin:
mov r8, " ^parmas_len^" 	              ;get number of args [rbp+3*WORD_SIZE]
mov r9, r8                                ;r9 <- num_of_args for loop of extending env
shl r8, 3				                          ;size to allocate <- pointer size * num of args
MALLOC r8, r8                             ;r8 <- new_vector

mov r10, 0                                ;r10 <- index of current param

add_params_to_env:                    ;copying args to new env
cmp r10, r9                               ;r10 = num_of_args?
je finish_params                      ;true -> jump to next action
mov r11,PVAR(r10)                         ;r11 <- current param
mov [r8+r10*WORD_SIZE], r11               ;new_vector[r10] <- r11
inc r10                                  ;r10 <- next param
jmp add_params_to_env

finish_params:                        ;finished copying args to new_vector

mov r10, "^new_env_size^"
MALLOC r10, r10                           ;r10 <- new env with size = (env_size + 1) * 8
mov [r10], r8                             ;r10[0] <- pointer to new_vector

mov rsi, 0                                ;rsi = index of major in old env starting from 0
mov rdi, 1                                ;rdi = index of major in new_env starting from 1
copy_old_env:                         ;Copying old env to new env
cmp rsi, " ^old_env_size^ "               ;rsi = size of old env?
je  finished_new_env                  ;true -> go to next action

mov r9, [rbp + WORD_SIZE*2]               ;r9 <- location of old_env in stack
mov r9, [r9 + rsi*WORD_SIZE]              ;r9 <- old_env[rsi] (pointer current vector)
mov [r10+rdi*WORD_SIZE], r9               ;new_env[rdi] <- old_env[rsi]

inc rsi                                   ;inc index of major in old_env
inc rdi                                   ;inc index of major in new_env

jmp copy_old_env                      ;copy next vector from old_env to new_env

finished_new_env:                     ;finished creating new_env

MAKE_CLOSURE (rax, r10,  lambda_code) ;create a new closure, with new_env at r10, body at label address
jmp lambda_end                        ;Skip lambda body. will only execute when called

lambda_code:
push rbp                                  
mov rbp,rsp
" ^ lambda_body ^ "
pop rbp
ret

lambda_end:"



 (* | LambdaOpt' of string list * string * expr' *)
  | Applic' (proc , arg_list) -> 
          let counter=counter+1 in
          let rev = List.rev arg_list in
          let args_text = gen_map rev "\n push rax \n" consts fvars env  counter in
          let post_args = args_text ^ "\n push "^ (string_of_int (List.length arg_list))^" \n" in
          let proc_text = generate_handle consts fvars proc env counter in
          let with_proc = post_args ^ proc_text in
          let assembly_check = 
          "\n 
          cmp byte[rax],  T_CLOSURE
          jne invalid     
          CLOSURE_ENV rbx, rax
          push rbx
          CLOSURE_CODE rbx, rax
          call rbx
          add rsp, 8*1         ; pop env
          pop rbx ; pop arg count
          shl rbx, 3 ; rbx = rbx * 8
          add rsp, rbx; pop args
          
          " in
          with_proc ^ assembly_check 
(* 
  | ApplicTP'  (proc , arg_list) ->
          let rev = List.rev arg_list in
          let args_text = gen_map rev "push rax \n" consts fvars counter in
          let post_args = args_text ^ "push n \n" in
          let proc_text = generate_handle consts fvars proc env  counterin
          let with_proc = post_args ^ proc_text in
          let assembly_check = 
          "
          cmp byte [rax] T_CLOSURE
          jne ApplicTPexit
          push rax qword [rax+1]
          push qword [rbp + 8 * 1] ; old ret addr
          add rsp, 8*1 ; pop env
          pop rbx ; pop
          arg count
          shl rbx, 3 ; rbx = rbx * 8
          add rsp, rbx; pop args
          ApplicTPexit:
          " in 
          with_proc ^ assembly_check
*)
  |_->""
  

  and gen_map list code_to_write consts fvars env counter = 
  let mapped = List.map (fun(elem)-> (generate_handle consts fvars elem env counter) ^ code_to_write) list in
  (list_to_string mapped) ;; 

   let generate consts fvars e = generate_handle consts fvars e 0 0 ;;

end;;
