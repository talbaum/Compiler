
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
   |Const'(e) -> (match e with
      | Void -> sexpr_list @ [] @ (collect_all_sexprs others sexpr_list)
      | Sexpr(e) -> sexpr_list @ handle_const e sexpr_list) @ (collect_all_sexprs others sexpr_list)
  (* | Const'(e) -> sexpr_list @ [e] @ (collect_all_sexprs others sexpr_list) (*verify order *) *)
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

  and handle_const e sexpr_list = match e with
    | Nil-> []
    | Bool (b) -> []
    | Char (x) -> [Sexpr(Char x)]
    | String (x) -> [Sexpr (String x)]
    | Number (Int (x)) -> [Sexpr (Number (Int x))]
    | Number (Float (x))-> [Sexpr (Number (Float x))]
    | Symbol (x) -> [Sexpr (String x); Sexpr (Symbol x)]
    | Pair (car ,cdr) ->(handle_const car sexpr_list ) @(handle_const cdr sexpr_list) @ [Sexpr (Pair (car ,cdr))]
    | Vector (vector_list) -> (List.flatten( List.map (fun (elem )-> handle_const elem sexpr_list) vector_list))@ [Sexpr(Vector vector_list)]

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

 let add_one  counter = 
 let getCounter = !counter in
 let () = incr counter in 
    getCounter;;

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


let random_suffix x =
let bound =1073741823 in
 string_of_int(Random.int bound);;
 

   let rec generate_handle consts fvars e env previous_arg_number lambda_depth =match e with
  | Const'(x)-> let address = addressInConstTable consts x in
                "mov rax, const_tbl+" ^ string_of_int address
  | Var'(VarFree(str)) -> let address = addressInFvarTable fvars str in
                "mov rax, qword [fvar_tbl+" ^ string_of_int address ^"*WORD_SIZE]"
  | Var'(VarParam (str , minor)) -> "
  mov r10, (4 + "^string_of_int minor^")*WORD_SIZE     ;                          // RETURN IT
  mov rax, qword [rbp + r10]                              ;                      // RETURN IT
; mov rax, qword [rbp +8 *(4+"^string_of_int minor^")] 
 
 "
  | Var'(VarBound (str ,major, minor)) ->"mov rax, qword [rbp + 2 * WORD_SIZE]
  mov rax, qword [rax + "^string_of_int major^"*WORD_SIZE]
  mov rax, qword [rax + "^string_of_int minor^"*WORD_SIZE]"
   | Box' (v) -> generate_handle consts fvars (Var'(v)) env previous_arg_number lambda_depth ^ "
    mov rbx, rax
    MALLOC rax,8
    mov rax,[rbx]
"  
  | BoxGet'(((v)) as vari)-> (generate_handle consts fvars (Var'(vari)) env previous_arg_number lambda_depth ) ^ "\n mov rax, qword [rax]"
  | BoxSet'((v) as vari ,value) -> 
    let  value_text =(generate_handle consts fvars value env previous_arg_number lambda_depth) ^ "\n push rax \n" in
    let var_text = (generate_handle consts fvars  (Var'(vari)) env previous_arg_number lambda_depth) ^ " \n pop qword [rax]
    mov rax, SOB_VOID_ADDRESS" in
    value_text ^ var_text
  | If'(test,dit,dif)-> 
   let else_suffix = random_suffix() in
   let exit_suffix = random_suffix() in
    let test_text= (generate_handle consts fvars test env previous_arg_number lambda_depth ) ^ "\n cmp rax, SOB_FALSE_ADDRESS
      je Lelse"^ else_suffix ^" \n" in
    let dit_text = (generate_handle consts fvars dit env previous_arg_number lambda_depth) ^ "\n jmp Lexit"^ exit_suffix ^"
      Lelse"^ else_suffix ^": \n" in 
    let dif_text = (generate_handle consts fvars dif env previous_arg_number lambda_depth) ^ "\n Lexit"^ exit_suffix ^":" in
    test_text ^ dit_text ^ dif_text 
  | Seq' (list) ->(gen_map list "\n" consts fvars env previous_arg_number lambda_depth)
  | Set'(Var'(VarParam(_, minor)),value)-> (generate_handle consts fvars value env previous_arg_number lambda_depth) ^ "
  mov qword [rbp + (4 + "^string_of_int minor^")*WORD_SIZE], rax
  mov rax, SOB_VOID_ADDRESS"
  | Set'(Var'(VarBound (str ,major, minor)),value)->(generate_handle consts fvars value env previous_arg_number lambda_depth)  ^
  "mov rbx, qword [rbp + 8 ∗ 2]
  mov rbx, qword [rbx + 8 ∗"^string_of_int  major^"]
  mov qword [rbx + 8 ∗"^string_of_int  minor^"], rax
  mov rax, SOB_VOID_ADDRESS"
  | Set'(Var'(VarFree(str)),value)->
  let value_text = (generate_handle consts fvars value env previous_arg_number lambda_depth) in
  let address = addressInFvarTable fvars str in
  value_text^"\n mov qword [fvar_tbl+" ^ string_of_int address ^"*WORD_SIZE], rax
  mov rax, SOB_VOID_ADDRESS"
  | Def'(Var'(VarFree(str)) , value)-> 
  let value_text = (generate_handle consts fvars value env previous_arg_number lambda_depth) in
  let address =  addressInFvarTable fvars str in
  value_text ^ "\n" ^
   "mov [fvar_tbl+" ^ (string_of_int address) ^"*WORD_SIZE], rax \n"^ "mov rax, SOB_VOID_ADDRESS \n"
  | Or'(list)-> 
   let () =Random.self_init() in 
      let suffix = random_suffix() in
      ((gen_map list ("
  cmp rax, SOB_FALSE_ADDRESS
  jne LexitOr"^suffix^"\n") consts fvars env previous_arg_number lambda_depth) ^ "
  LexitOr"^suffix^":" )

 | LambdaSimple' (params , body) -> 
      let () =Random.self_init() in 
      let old_env_size = env in
      let ext_env_size = old_env_size + 1 in
      let ext_env_size_address = string_of_int(ext_env_size * 8) in
      let params_len = (List.length params) in 
      let suffix = random_suffix() in
      let code ="
     ; allocate size for the whole extenv
      mov r15, " ^ext_env_size_address ^" 
      MALLOC r15, r15
      mov r14, "^string_of_int old_env_size ^"
      cmp r14, 0
      je no_params"^suffix^"

    allocate_first_ext_env"^suffix^":
        mov r14,"^ string_of_int previous_arg_number ^ "
        shl r14 , 3
        MALLOC r14, r14      ; allocate size for the extenv[0] for params
        mov qword[r15], r14

                               ;take_params into extenv[0]
        %assign i 0
        %rep "^ string_of_int previous_arg_number ^"
        mov r13, 32
        add r13, i*WORD_SIZE
        add r13, rbp 
        mov r13, [r13]    ;                 mov r13, [rbp + 8 * 4 + i*8]
        mov r12, i*WORD_SIZE
        mov [r14 + r12], r13       ;  mov[r14+ i*8] , r13
        %assign i i+1
        %endrep
        %assign i 0                                    ;take_old_array_cells - extenv[j] = env[i]
        %rep "^ string_of_int old_env_size ^"
        mov r13, 16
        add r13, i*WORD_SIZE
        add r13, rbp 
        mov r13, [r13]    ;         mov r13, [rbp + 8 * 2 + (i*8)]
        mov r12, i*WORD_SIZE
        add r12, 8
        mov [r15 + r12], r13            ;         mov [r15 + (i+1)*8], r13
        %assign i i+1
        %endrep
       jmp create_closure"^suffix^"

      no_params"^suffix^":
        mov r15 , qword SOB_NIL_ADDRESS
      create_closure"^suffix^":
        MAKE_CLOSURE(rax, r15, Lcode"^suffix^")
        jmp Lcont"^suffix^"

      Lcode"^suffix^":
        push rbp
        mov rbp, rsp
        "^ generate_handle consts fvars body env params_len ext_env_size  ^"
        leave
        ret

      Lcont"^suffix^":
            
      " in code

  | LambdaOpt'(params , vs ,body)  ->
      let () =Random.self_init() in 
      let old_env_size = env in
      let ext_env_size = old_env_size + 1 in
      let ext_env_size_address = string_of_int(ext_env_size * 8) in
      let params_len = (List.length params) in 
      let params_len_plus_one = params_len +1 in
      let suffix = random_suffix() in
      let code ="
      ; allocate size for the whole extenv
      mov r15, " ^ext_env_size_address ^" 
      MALLOC r15, r15
      mov r14, "^string_of_int old_env_size ^"
      cmp r14, 0
      je no_params"^suffix^"

    allocate_first_ext_env"^suffix^":
        mov r14,"^ string_of_int previous_arg_number ^ "
        shl r14 , 3
        MALLOC r14, r14     ; allocate size for the extenv[0] for params
        mov qword[r15], r14

                                                     ;take_params into extenv[0]
        %assign i 0
        %rep "^ string_of_int previous_arg_number ^"
        mov r13, 32
        add r13, i*WORD_SIZE
        add r13, rbp 
        mov r13, [r13]    ;                 mov r13, [rbp + 8 * 4 + i*8]
        mov r12, i*WORD_SIZE
        mov [r14 + r12], r13       ;  mov[r14+ i*8] , r13
        %assign i i+1
        %endrep
        %assign i 0                              ;take_old_array_cells - extenv[j] = env[i]
        %rep "^ string_of_int old_env_size ^"
        mov r13, 16
        add r13, i*WORD_SIZE
        add r13, rbp 
        mov r13, [r13]    ;         mov r13, [rbp + 8 * 2 + (i*8)]
        mov r12, i*WORD_SIZE
        add r12, 8
        mov [r15 + r12], r13            ;         mov [r15 + (i+1)*8], r13
        %assign i i+1
        %endrep
       jmp create_closure"^suffix^"

      no_params"^suffix^":
        mov r15 , qword SOB_NIL_ADDRESS
      create_closure"^suffix^":
        MAKE_CLOSURE(rax, r15, LcodeOPT"^suffix^")
        jmp LcontOPT"^suffix^"
      " in
   let lcodeOPT = "
  LcodeOPT"^ suffix ^":
      push rbp
      mov rbp, rsp

      mov r13, SOB_NIL_ADDRESS
      mov r15, qword [rbp + 3*WORD_SIZE] 
      mov rsi,r15 
      shl rsi, 3
      sub r15, "^string_of_int params_len ^"   
      cmp r15,0
      je done_fix"^ suffix ^"

      mov r12, 32
      add r12, rsi
      add r12, rbp

  build_opt_list"^ suffix ^":
      cmp r15, 0 
      je finish"^suffix^"
      mov r8, r13
      sub r12, 8 
      mov rdi ,[r12]
      MAKE_PAIR (r13, rdi, r8)
      dec r15
      jmp build_opt_list"^ suffix ^"
      
    finish"^suffix^":
      mov [r12],r13
     
     ; change_args_count"^ suffix ^":        ;; change the arg count to be paramslist +1
     ;      mov qword[rbp+3*WORD_SIZE] ,"^(string_of_int params_len_plus_one)^"


  done_fix"^ suffix ^":
   " ^ (generate_handle consts fvars body (env+1) params_len_plus_one ext_env_size) ^"

    mov   rbp, rsp    
    pop   rbp
    ret
  LcontOPT"^suffix ^":

" in
  code  ^ lcodeOPT 

  | Applic' (proc , arg_list) -> 
          (*let () = incr counter in*)
          let chino = "
          ; mov r10,SOB_NIL_ADDRESS ; MAGIC PARAM - NULL?
          push qword SOB_NIL_ADDRESS  
          " in
          let rev = List.rev arg_list in
          let args_text = gen_map rev "\n push rax \n" consts fvars env  previous_arg_number lambda_depth in
          let post_args = args_text ^ "\n push "^ string_of_int (List.length arg_list)^" \n" in
          let proc_text = generate_handle consts fvars proc env previous_arg_number lambda_depth in
          let with_proc = post_args ^ proc_text in
          let assembly_check = 
          " 
          cmp byte[rax],  T_CLOSURE
          jne invalid     
          CLOSURE_ENV rbx, rax
          push rbx
          CLOSURE_CODE rax, rax 
          call rax
      

          add rsp, 8*1         ; pop env
          pop rbx ; pop arg count
          shl rbx, 3 ; rbx = rbx * 8
          add rsp, rbx; pop args
          add rsp , 8
          ;pop r10
          
          " in
          chino^with_proc ^ assembly_check 

  (* | ApplicTP'  (proc , arg_list) ->
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
          with_proc ^ assembly_check  *)
  |_->""
  

  and gen_map list code_to_write consts fvars env previous_arg_number lambda_depth = 
  let mapped = List.map (fun(elem)-> (generate_handle consts fvars elem env previous_arg_number lambda_depth) ^ code_to_write) list in
  (list_to_string mapped) ;; 

   let generate consts fvars e =
    (* let counter : int ref = ref 0 in *)
   generate_handle consts fvars e 1 0 0 ;;

end;;
