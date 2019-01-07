 | LambdaSimple' (params , body) -> 
      let () =Random.self_init() in 
      let old_env_size = env in
      (* let old_env_size_address =string_of_int (8 * old_env_size) in  *)
      let ext_env_size = old_env_size + 1 in
      let ext_env_size_address = string_of_int(ext_env_size * 8) in
      let params_len = (List.length params) in 
      let params_so_far = params_so_far + params_len in
      (* let params_so_far_address = 8 * params_so_far in  *)
      let suffix = random_suffix() in
      let code ="
     ; allocate size for the whole extenv
     start"^suffix^": 
      mov r15, " ^ext_env_size_address ^" 
      MALLOC r15, r15
      mov r14, "^string_of_int old_env_size ^"
      cmp r14, 0      ;; check maybe 1 or change down to 0
      je no_params"^suffix^"

      take_params"^suffix^":                         ;take_params into extenv[0]
        mov r12, qword[rbp + 8 * 2]
        %assign i 0
        %rep "^ string_of_int old_env_size ^"
        mov r13, [r12 + (i* 8)]
        mov [r15 + (i+1)*8], r13
        %assign i i+1
        %endrep

    allocate_first_ext_env"^suffix^":
        mov r14,"^ string_of_int previous_arg_number ^ "
        shl r14 , 3
        MALLOC r14, r14      ; allocate size for the extenv[0] for params
        mov qword[r15], r14

        
  take_old_array_cells"^suffix^":
        %assign i 0                                    ; extenv[j] = env[i]
        %rep "^ string_of_int previous_arg_number ^"
         mov r13, [rbp + 32 + (i*8)]
         mov [r14 + i*8], r13       
        %assign i i+1
        %endrep
       jmp create_closure"^suffix^"

      no_params"^suffix^":
        mov r15 ,  SOB_NIL_ADDRESS
        
      create_closure"^suffix^":
        MAKE_CLOSURE(rax, r15, Lcode"^suffix^")
        jmp Lcont"^suffix^"

      Lcode"^suffix^":
        push rbp
        mov rbp, rsp
        "^ generate_handle consts fvars body (env+1) params_len ext_env_size params_so_far  ^"
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
      let params_so_far = params_so_far + params_len_plus_one in
      let suffix = random_suffix() in
      let code ="
      ; allocate size for the whole extenv
     start"^suffix^": 
      mov r15, " ^ext_env_size_address ^" 
      MALLOC r15, r15
      mov r14, "^string_of_int old_env_size ^"
      cmp r14, 0      ;; check maybe 1 or change down to 0
      je no_params"^suffix^"

      take_params"^suffix^":                         ;take_params into extenv[0]
        mov r12, qword[rbp + 8 * 2]
        %assign i 0
        %rep "^ string_of_int old_env_size ^"
        mov r13, [r12 + (i* 8)]
        mov [r15 + (i+1)*8], r13
        %assign i i+1
        %endrep

    allocate_first_ext_env"^suffix^":
        mov r14,"^ string_of_int previous_arg_number ^ "
        shl r14 , 3
        MALLOC r14, r14      ; allocate size for the extenv[0] for params
        mov qword[r15], r14

        
  take_old_array_cells"^suffix^":
        %assign i 0                                    ; extenv[j] = env[i]
        %rep "^ string_of_int previous_arg_number ^"
         mov r13, [rbp + 32 + (i*8)]
         mov [r14 + i*8], r13       
        %assign i i+1
        %endrep
       jmp create_closure"^suffix^"

      no_params"^suffix^":
        mov r15 ,  SOB_NIL_ADDRESS
        
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
   " ^ (generate_handle consts fvars body (env+1) params_len_plus_one ext_env_size params_so_far) ^"

    mov   rbp, rsp    
    pop   rbp
    ret
  LcontOPT"^suffix ^":

" in
  code  ^ lcodeOPT 
