
#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * int * string) list
  val make_fvars_tbl : expr' list -> (string * int) list
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
    | Vector (elements) -> (List.flatten( List.map (fun (elem )-> handle_const elem sexpr_list) elements))@ [Sexpr(Vector elements)]
    | Pair (first ,second) ->(handle_const first sexpr_list )@(handle_const second sexpr_list)@[ Sexpr (Pair (first ,second))]
    | Bool (b) -> []
    | Symbol (sym) -> [Sexpr (String (sym)); Sexpr (Symbol (sym))]
    | e -> [Sexpr(e)]
;;


let rec remove_duplicate original new_list = 
let length = List.length original in
if length = 0 then  new_list
else 
let head = (List.hd original) in
let tail =(List.tl original) in
if List.mem head new_list then remove_duplicate tail new_list 
else  remove_duplicate tail (new_list @ [head]);;


let isEqual_constant e1 e2=
  match e1, e2 with
  |  Void,  Void -> true
  | (Sexpr s1), (Sexpr s2) -> sexpr_eq s1 s2
  | _-> false;;


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

let ascii_string string =
let ascii_code = List.map Char.code (string_to_list string) in 
let ascii_list = List.map (fun(x) -> (string_of_int x )) ascii_code in
let ans = String.concat "," ascii_list in
ans;;



let find_element e constant_table = 
  let find_me =e in
  let offset_list = List.map (fun(tuple)-> 
          let (sexpr,offset,_) = tuple in
          if isEqual_constant ((Sexpr(find_me))) sexpr = true then offset else -1) constant_table in
  let ans = List.filter (fun(x) -> x!= -1) offset_list in 
  match ans with
  | [num] -> string_of_int num
  | _ -> "0"
 ;;

let rec get_represent elem constant_table= match elem with
  | Sexpr(Nil) -> "MAKE_NIL"
  | Void -> "MAKE_VOID"
  | Sexpr(Bool(e)) -> if e = true then "MAKE_BOOL(1)" else "MAKE_BOOL(0)"
  | Sexpr(Char(e)) -> Printf.sprintf "MAKE_LITERAL_CHAR(%d)" (Char.code e)
  | Sexpr(Number(Int(e))) -> "MAKE_LITERAL_INT(" ^ (string_of_int e) ^ ")"
  | Sexpr(Number(Float(e))) -> "MAKE_LITERAL_FLOAT(" ^(string_of_float e) ^ ")"
  | Sexpr(Symbol (e) ) ->  "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (find_element (String(e)) constant_table) ^  ")"                             
  | Sexpr(String (e)) -> "MAKE_LITERAL_STRING " ^ (ascii_string e) ^ ""
  | Sexpr(Pair (car,cdr)) -> "MAKE_LITERAL_PAIR(const_tbl+" ^ (find_element car constant_table) ^ ",const_tbl+" ^ (find_element cdr constant_table) ^ ")"
  | Sexpr(Vector (sexprs_list))->
  let tmp = "MAKE_LITERAL_VECTOR " ^ 
      (list_to_string(List.map (fun(elem) -> "const_tbl+" ^ find_element (elem) constant_table ^ ",") sexprs_list )) in
   String.sub tmp 0 (String.length tmp - 1) ^ ""
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
  | [VarParam(name, minor)] ->  [] 
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
  let constants_set  = remove_duplicate constants_list [] in
  let expanded_list = build_topolig_list constants_set in
  let add_basics_to_const_list = add_basics expanded_list in
  let no_dups_list = remove_duplicate add_basics_to_const_list [] in
  create_const_table no_dups_list [];; 
  

  let init_fvars =  [("boolean?",0);("float?",1);("integer?",2);("pair?",3);("null?",4);("char?",5);("vector?",6);("string?",7);("procedure?",8);("symbol?",9);( "string-length",10);("string-ref",11);("string-set!",12);("make-string",13);("vector-length",14);("vector-ref",15);("vector-set!",16);("make-vector",17);("symbol->string",18);("char->integer",19);("integer->char",20);("eq?",21);("+",22);("*",23);("-",24);("/",25);("<",26);("=",27);("car",28); ("cdr",29); ("set-car!",30);("set-cdr!",31);("cons",32);("apply",33)];;


  let make_fvars_tbl asts = 
  let fvar_list = collect_all_fvars asts [] in
  let fvar_set = remove_duplicate fvar_list [] in 
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


   let rec generate_handle consts fvars e env previous_arg_number lambda_depth params_so_far=match e with
  | Const'(x)-> let address = addressInConstTable consts x in
                "mov rax, const_tbl+" ^ string_of_int address
  | Var'(VarFree(str)) -> let address = addressInFvarTable fvars str in
                "mov rax, qword [fvar_tbl+" ^ string_of_int address ^"*WORD_SIZE]"
  | Var'(VarParam (str , minor)) -> "
  mov r10, (4 + "^string_of_int minor^")*WORD_SIZE    
  mov rax, qword [rbp + r10]                              
 
 "
  | Var'(VarBound (str ,major, minor)) ->"
  mov rax, qword [rbp + 2 * WORD_SIZE]
  mov rax, qword [rax + "^string_of_int major^"*WORD_SIZE]
  mov rax, qword [rax + "^string_of_int minor^"*WORD_SIZE]"
  | Box' (v) ->  "
   MALLOC rdi, 8 \n"^
   (generate_handle consts fvars (Var'(v)) env  previous_arg_number lambda_depth params_so_far )
    ^"
    mov qword[rdi], rax
    mov rax,rdi
   " 
  
  | BoxGet'(((v)) as vari)-> (generate_handle consts fvars (Var'(vari)) env previous_arg_number lambda_depth params_so_far) ^ "\n mov rax, qword [rax]"
  | BoxSet'((v) as vari ,value) -> 
    let  value_text =(generate_handle consts fvars value env previous_arg_number lambda_depth params_so_far) ^ "\n push rax \n" in
    let var_text = (generate_handle consts fvars  (Var'(vari)) env previous_arg_number lambda_depth params_so_far) ^ " \n pop qword [rax]
    mov rax, SOB_VOID_ADDRESS" in
    value_text ^ var_text
  | If'(test,dit,dif)-> 
   let else_suffix = random_suffix() in
   let exit_suffix = random_suffix() in
    let test_text= (generate_handle consts fvars test env previous_arg_number lambda_depth params_so_far) ^ "\n cmp rax, SOB_FALSE_ADDRESS
      je Lelse"^ else_suffix ^" \n" in
    let dit_text = (generate_handle consts fvars dit env previous_arg_number lambda_depth params_so_far) ^ "\n jmp Lexit"^ exit_suffix ^"
      Lelse"^ else_suffix ^": \n" in 
    let dif_text = (generate_handle consts fvars dif env previous_arg_number lambda_depth params_so_far) ^ "\n Lexit"^ exit_suffix ^":" in
    test_text ^ dit_text ^ dif_text 
  | Seq' (list) ->(gen_map list "\n" consts fvars env previous_arg_number lambda_depth params_so_far) 
  | Set'(Var'(VarParam(_, minor)),value)-> (generate_handle consts fvars value env previous_arg_number lambda_depth params_so_far) ^ "
  mov qword [rbp + (4 + "^string_of_int minor^")*WORD_SIZE], rax
  mov rax, SOB_VOID_ADDRESS"
  | Set'(Var'(VarBound (str ,major, minor)),value)->(generate_handle consts fvars value env previous_arg_number lambda_depth params_so_far)  ^"
  mov rbx, qword [rbp + 16]
  mov rbx, qword [rbx + "^string_of_int  major^"*WORD_SIZE]
  mov qword [rbx +"^string_of_int  minor^"*WORD_SIZE], rax
  mov rax, SOB_VOID_ADDRESS"
  | Set'(Var'(VarFree(str)),value)->
  let value_text = (generate_handle consts fvars value env previous_arg_number lambda_depth params_so_far) in
  let address = addressInFvarTable fvars str in
  value_text^"\n mov qword [fvar_tbl+" ^ string_of_int address ^"*WORD_SIZE], rax
  mov rax, SOB_VOID_ADDRESS"
  | Def'(Var'(VarFree(str)) , value)-> 
  let value_text = (generate_handle consts fvars value env previous_arg_number lambda_depth params_so_far) in
  let address =  addressInFvarTable fvars str in
  value_text ^ "\n" ^
   "mov [fvar_tbl+" ^ (string_of_int address) ^"*WORD_SIZE], rax \n"^ "mov rax, SOB_VOID_ADDRESS \n"
  | Or'(list)-> 
   let () =Random.self_init() in 
      let suffix = random_suffix() in
      ((gen_map list ("
  cmp rax, SOB_FALSE_ADDRESS
  jne LexitOr"^suffix^"\n") consts fvars env previous_arg_number lambda_depth params_so_far) ^ "
  LexitOr"^suffix^":" )


 | LambdaSimple' (params , body) -> 
      let () =Random.self_init() in 
      let old_env_size = env in
      let old_env_size_str =string_of_int (old_env_size) in  
      let ext_env_size = old_env_size + 1 in
      let ext_env_size_address = string_of_int(ext_env_size * 8) in
      let params_len = (List.length params) in 
      let params_so_far = params_so_far + params_len in
      let previous_arg_number_str = string_of_int previous_arg_number in
      let suffix = random_suffix() in
                
     let init= "start"^suffix^":                               ; init
      mov r15, " ^ext_env_size_address ^" 
      MALLOC r15, r15
      mov r14, "^old_env_size_str ^"
      cmp r14, 0      
      jne continue_process"^suffix^"
      mov r15 ,  SOB_NIL_ADDRESS 
      jmp  create_closure"^suffix^"
      continue_process"^suffix^":
      mov r9, rbp
      add r9 , 16
      mov r9, qword[r9]
      mov r11 ,0 \n" in
      let copyParams = 
     "\n take_params"^suffix^":                                      ; copy params  
        cmp r11,"^ old_env_size_str ^"
        je allocate_first_ext_env"^suffix^"
        mov r10, r11
        shl r10,3
        add r10, r9
        mov r13, [r10]
        inc r11
        mov r10, r11
        shl r10,3
        add r10, r15
        mov [r10], r13
        jmp take_params"^suffix ^"\n" in
        let malocEnv0 = "
      allocate_first_ext_env"^suffix^":                           ; allocate space for exat env[0]
        mov r14,"^ previous_arg_number_str ^ "
        shl r14 , 3
        MALLOC r14, r14      
        mov qword[r15], r14
        mov r11,0 \n" in
      let copyOldEnv = "
  take_old_array_cells"^suffix^":                             ; extenv[j] = env[i]
        cmp r11, "^ previous_arg_number_str ^"
        je create_closure"^suffix^"
        mov r10, r11
        shl r10, 3
        add r10, 32
        add r10, rbp
        mov r13, [r10]
        sub r10,rbp
        sub r10, 32
        add r10, r14
        mov [r10],r13
        inc r11
        jmp take_old_array_cells"^suffix ^"\n" in
      let makeClosure="  
      create_closure"^suffix^":                                             ; create closureu
        MAKE_CLOSURE(rax, r15, Lcode"^suffix^")
        jmp Lcont"^suffix^"\n" in
      let lcode = "\n
      Lcode"^suffix^":                                              ; lcode
        push rbp
        mov rbp, rsp
        "^ generate_handle consts fvars body ext_env_size params_len ext_env_size params_so_far  ^"
        leave
        ret
      Lcont"^suffix^":\n        
      " in 
            let code = init^ copyParams^malocEnv0^copyOldEnv^makeClosure^lcode in
            code

  | LambdaOpt'(params , vs ,body)  ->
      let () =Random.self_init() in 
      let old_env_size = env in
      let old_env_size_str =string_of_int (old_env_size) in  
      let ext_env_size = old_env_size + 1 in
      let ext_env_size_address = string_of_int(ext_env_size * 8) in
      let params_len = (List.length params) in 
      let params_len_plus_one = params_len +1 in
      let previous_arg_number_str = string_of_int previous_arg_number in
      let params_so_far = params_so_far + params_len_plus_one in
      let suffix = random_suffix() in
       let init= "start"^suffix^":                               ; init
      mov r15, " ^ext_env_size_address ^" 
      MALLOC r15, r15
      mov r14, "^old_env_size_str ^"
      cmp r14, 0      
      jne continue_process"^suffix^"
      mov r15 ,  SOB_NIL_ADDRESS 
      jmp  create_closure"^suffix^"
      continue_process"^suffix^":
      mov r9, rbp
      add r9 , 16
      mov r9, qword[r9]
      mov r11 ,0 \n" in
      let copyParams = 
     "\n take_params"^suffix^":                                      ; copy params  
        cmp r11,"^ old_env_size_str ^"
        je allocate_first_ext_env"^suffix^"
        mov r10, r11
        shl r10,3
        add r10, r9
        mov r13, [r10]
        inc r11
        mov r10, r11
        shl r10,3
        add r10, r15
        mov [r10], r13
        jmp take_params"^suffix ^"\n" in
        let malocEnv0 = "
      allocate_first_ext_env"^suffix^":                           ; allocate space for exat env[0]
        mov r14,"^ previous_arg_number_str ^ "
        shl r14 , 3
        MALLOC r14, r14      
        mov qword[r15], r14
        mov r11,0 \n" in
      let copyOldEnv = "
  take_old_array_cells"^suffix^":                             ; extenv[j] = env[i]
        cmp r11, "^ previous_arg_number_str ^"
        je create_closure"^suffix^"
        mov r10, r11
        shl r10, 3
        add r10, 32
        add r10, rbp
        mov r13, [r10]
        sub r10,rbp
        sub r10, 32
        add r10, r14
        mov [r10],r13
        inc r11
        jmp take_old_array_cells"^suffix ^"\n" in
      let makeClosure="  
      create_closure"^suffix^":                                             ; create closureu
        MAKE_CLOSURE(rax, r15, LcodeOPT"^suffix^")
        jmp LcontOPT"^suffix^"\n" in
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

  done_fix"^ suffix ^":
   " ^ (generate_handle consts fvars body (env+1) params_len_plus_one ext_env_size params_so_far) ^"
    mov   rbp, rsp    
    pop   rbp
    ret
  LcontOPT"^suffix ^":
" in
 let code = init^ copyParams^malocEnv0^copyOldEnv^makeClosure^lcodeOPT in
            code
   | Applic' (proc , arg_list) -> 
          let magic = "
          push SOB_NIL_ADDRESS  
          " in
          let rev = List.rev arg_list in
          let args_text = gen_map rev "\n push rax \n" consts fvars env  previous_arg_number lambda_depth params_so_far in
          let args_and_length = args_text ^ "\n push "^ string_of_int (List.length arg_list)^" \n" in
          let proc_text = generate_handle consts fvars proc env previous_arg_number lambda_depth params_so_far in
          let with_proc = args_and_length ^ proc_text in                
          magic^with_proc^ 
          "\n cmp byte[rax],  T_CLOSURE
          jne invalid           
          CLOSURE_ENV rbx, rax
          push rbx
          CLOSURE_CODE rax, rax 
          call rax \n 
          add rsp, 8*1        ; pop env
          pop rbx             ; pop arg count
          shl rbx, 3          ; rbx = rbx * 8
          add rsp, rbx        ; pop args
          add rsp , 8     
          "  
  
          | ApplicTP'(proc , arg_list) ->
          let magic = "\n;TP \n push qword SOB_NIL_ADDRESS  \n" in
          let rev = List.rev arg_list in
          let args_text = gen_map rev "\n push rax \n" consts fvars env   previous_arg_number lambda_depth params_so_far in
          let post_args = args_text ^ "\n push "^ string_of_int (List.length arg_list)^" \n" in
          let shiftFrameArg = string_of_int ((List.length arg_list)+5) in
          let proc_text = generate_handle consts fvars proc env  previous_arg_number lambda_depth params_so_far in
          let with_proc = post_args ^ proc_text in  
          magic^with_proc ^ 
          "\n cmp byte[rax],  T_CLOSURE
          jne invalid   
          CLOSURE_ENV rbx, rax
          push rbx 
          mov r14, rbp
          add r14, 8
          push qword [r14]
          mov r14, qword [rbp]                       ;;;;;;;;; TP ;;;;;;;;;;;;;;
          mov r8, 3
          shl r8, 3
          add r8, rbp
          mov r9, qword[r8]
          SHIFT_FRAME "^ shiftFrameArg ^   
          "\nadd r9,5
          shl r9, 3     
          add rsp, r9
          mov rbp, r14 \n                            
          CLOSURE_CODE r12, rax 
          jmp r12
          "     
|_->""

  and gen_map list code_to_write consts fvars env   previous_arg_number lambda_depth params_so_far = 
  let mapped = List.map (fun(elem)-> (generate_handle consts fvars elem env  previous_arg_number lambda_depth params_so_far) ^ code_to_write) list in
  (list_to_string mapped) ;; 

   let generate consts fvars e =
   generate_handle consts fvars e 0 0 0 0 ;;

end;;

