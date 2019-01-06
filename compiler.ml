#use "code-gen.ml";;

let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;



let string_to_asts s = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s));;

 let primitive_names_to_labels = 
  ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
   "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
   "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
   "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
   "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
   "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
   "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
   "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";
   "car","car_nasm"; "cdr","cdr_nasm"; "set-car!","set_car"; "set-cdr!","set_cdr"; "cons","cons_nasm";
    "apply","apply_nasm" ];;


let isEqual_constant e1 e2=
  match e1, e2 with
  |  Void,  Void -> true
  | (Sexpr s1), (Sexpr s2) -> sexpr_eq s1 s2
  | _-> false;;

let rec get_constAddress find_me constant_table = match constant_table with
| [] -> 0
| _ -> let first = List.hd constant_table in
       let (sexpr,address,_) = first in
       if isEqual_constant sexpr find_me then address else get_constAddress  find_me (List.tl constant_table) ;;
       

let rec get_fvarAddress find_me fvar_table = match fvar_table with
| [] -> 0
| _ -> let first = List.hd fvar_table in
       let (fvar_name,address) = first in
       if  fvar_name = find_me then address else get_fvarAddress find_me (List.tl fvar_table) ;;
   
  

let make_prologue consts_tbl fvars_tbl =
  let get_const_address const ="const_tbl+"^(string_of_int(get_constAddress const consts_tbl)) in
  let get_fvar_address const = "fvar_tbl+"^string_of_int(get_fvarAddress const fvars_tbl) in
  let make_primitive_closure (prim, label) =
"    MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ label  ^ ")
    mov [" ^ (get_fvar_address prim)  ^ "*WORD_SIZE], rax" in
  let make_constant (c, a, s) = s in
  
"
;;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s
%include \"compiler.s\"
section .bss
malloc_pointer:
    resq 1
section .data
const_tbl:
" ^ (String.concat "\n" (List.map make_constant consts_tbl)) ^ "
;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID_ADDRESS " ^ get_const_address Void ^ "
%define SOB_NIL_ADDRESS " ^ get_const_address (Sexpr Nil) ^ "
%define SOB_FALSE_ADDRESS " ^ get_const_address (Sexpr (Bool false)) ^ "
%define SOB_TRUE_ADDRESS " ^ get_const_address (Sexpr (Bool true)) ^ "
fvar_tbl:
" ^ (String.concat "\n" (List.map (fun _ -> "dq T_UNDEFINED") fvars_tbl)) ^ "
section .text
global main
main:
    ;; set up the heap
    mov rdi, MB(100)
    call malloc
    mov [malloc_pointer], rax
    ;; Set up the dummy activation frame
    ;; The dummy return address is T_UNDEFINED
    ;; (which a is a macro for 0) so that returning
    ;; from the top level (which SHOULD NOT HAPPEN
    ;; AND IS A BUG) will cause a segfault.
    push 0
    push qword SOB_NIL_ADDRESS
    push qword T_UNDEFINED
    push rsp
    mov rbp, rsp
    call code_fragment
    add rsp, 4*8
    ret
code_fragment:
    ;; Set up the primitive stdlib fvars:
    ;; Since the primtive procedures are defined in assembly,
    ;; they are not generated by scheme (define ...) expressions.
    ;; This is where we emulate the missing (define ...) expressions
    ;; for all the primitive procedures.
" ^ (String.concat "\n" (List.map make_primitive_closure primitive_names_to_labels)) ^"
 
";;

let init_VarTable fvar_tabel = 
List.map (fun(x)->(x))


let epilogue = "
car_nasm:
    push rbp
    mov rbp, rsp
    mov rsi, PVAR(0)
    cmp byte[rsi] , T_PAIR
    jne invalid
    mov rax, qword[rsi+1]
    leave
    ret
cdr_nasm:
    push rbp
    mov rbp, rsp
    mov rsi, PVAR(0)
    cmp byte[rsi] , T_PAIR
    jne invalid
    mov rax, qword[rsi+1+8]
    leave
    ret
set_car:
    push rbp
    mov rbp, rsp
    mov rsi, PVAR(0)
    mov rdi, PVAR(1)
    cmp byte[rsi] , T_PAIR
    jne invalid
    mov qword[rsi+1], rdi
    mov rax, SOB_VOID_ADDRESS
    leave
    ret
set_cdr:
    push rbp
    mov rbp, rsp
    mov rsi, PVAR(0)
    mov rdi, PVAR(1)
    cmp byte[rsi] , T_PAIR
    jne invalid
    mov qword[rsi+1+8], rdi
    mov rax, SOB_VOID_ADDRESS
    leave
    ret
cons_nasm:
    push rbp
    mov rbp, rsp
    mov rsi, PVAR(0)
    mov rdi, PVAR(1)
    mov r8, PVAR(2)
    mov r8, [r8]
    MAKE_PAIR(r8, rsi, rdi)
    mov rax, r8
    leave
    ret



apply_nasm:
  
    push rbp
    mov rbp, rsp
    push SOB_NIL_ADDRESS
    mov rdx, qword[rbp+3*8]      ;will be = the counter of params not in the vs
    sub rdx,2
    mov rsi, rdx
    mov rdi, rbp
    add rdi, 40
    mov r12, rdx

point_to_vs1:
    cmp r12, 0
    je start_counting
    add rdi, 8
    dec r12
    jmp point_to_vs1              

start_counting:
    mov r12, [rdi]                ; points to the vs list = rdi           
    mov r10, 0                     
count_vs:
    cmp r12, SOB_NIL_ADDRESS
    je done_count_vs
    add r10, 1
    CDR rax,r12
    mov r12,rax
    jmp count_vs
                     
done_count_vs: 
    mov r15, r10
    mov rcx, r10
    ;sub r15, 1
    mov r8, r15             
start_push:
    mov r12, qword[rdi]      ;r12 is the list
    cmp rcx, 0
    je rev_list_end

mov r13, r12    
mov r8,SOB_NIL_ADDRESS
rev_list1:
    cmp r15, 0               ;r15 points to the list
    je rev_list_end1
    CAR r14, r13
    CDR rax, r13
    mov r13, rax
    MAKE_PAIR (rax ,r14, r8)
    mov r8, rax
    dec r15
    jmp rev_list1
rev_list_end1:
mov r15, r10
push_list1:
    cmp r15, 0                   ;r15 points to the list
    je push_list_end1
    CAR r14, r8
    push r14
    CDR rax, r8
    mov r8, rax
    dec r15
    jmp push_list1
push_list_end1:

rev_list_end:
    mov r8,rsi
    add r8, r10 

    mov r13,rdi
    sub r13, rbp
push_reg_params_list:
    cmp rsi, 0                   ;r15 points to the list
    je push_list_end
    sub r13,8
    push qword[rbp+r13]
    dec rsi
    jmp push_reg_params_list

push_list_end:
    push r8
    sub r13,8
    mov rdi, qword[rbp+r13]
    CLOSURE_ENV rsi, rdi
    push rsi                      
    push qword [rbp + 8]           
    push qword[rbp]                
    mov rdx, r8
    add rdx, 5
    mov r15, qword [rbp + 3*8] 
    SHIFT_FRAMESKI rdx
tuli:
    add r15,5
    shl r15,3
    add rsp,r15
    CLOSURE_CODE rsi,rdi
    pop rbp
    jmp rsi

invalid:
leave
ret


";;
exception X_missing_input_file;;

try
  let infile = Sys.argv.(1) in
  let code =  (*(file_to_string "stdlib.scm") ^ *)(file_to_string infile) in
  let asts = string_to_asts code in
  let consts_tbl = Code_Gen.make_consts_tbl asts in
  let fvars_tbl = Code_Gen.make_fvars_tbl asts in
  let generate = Code_Gen.generate consts_tbl fvars_tbl in
  let code_fragment = String.concat "\n   \n"
                        (List.map
                           (fun ast -> (generate ast) ^ "\n    call write_sob_if_not_void")
                           asts) in
  let provided_primitives = file_to_string "prims.s" in
                   
  print_string ((make_prologue consts_tbl fvars_tbl)  ^
                  code_fragment ^ "\n ret \n" ^
                    provided_primitives ^ "\n" ^ epilogue)

with Invalid_argument(x) -> raise X_missing_input_file;;


(**------------------------------------------------------------------------------------------------------- *)

