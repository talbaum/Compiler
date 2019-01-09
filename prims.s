is_boolean:
    push rbp
    mov rbp, rsp
 
    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_BOOL
    jne .wrong_type
    mov rax, SOB_TRUE_ADDRESS
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE_ADDRESS
.return:
    leave
    ret

is_float:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_FLOAT
    jne .wrong_type
    mov rax, SOB_TRUE_ADDRESS
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE_ADDRESS
.return:
    leave
    ret

is_integer:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_INTEGER
    jne .wrong_type
    mov rax, SOB_TRUE_ADDRESS
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE_ADDRESS
.return:
    leave
    ret

is_pair:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_PAIR
    jne .wrong_type
    mov rax, SOB_TRUE_ADDRESS
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE_ADDRESS
.return:
    leave
    ret

is_null:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_NIL
    jne .wrong_type
    mov rax, SOB_TRUE_ADDRESS
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE_ADDRESS
.return:
    leave
    ret

is_char:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_CHAR
    jne .wrong_type
    mov rax, SOB_TRUE_ADDRESS
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE_ADDRESS
.return:
    leave
    ret

is_vector:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_VECTOR
    jne .wrong_type
    mov rax, SOB_TRUE_ADDRESS
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE_ADDRESS
.return:
    leave
    ret

is_string:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_STRING
    jne .wrong_type
    mov rax, SOB_TRUE_ADDRESS
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE_ADDRESS
.return:
    leave
    ret

is_procedure:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_CLOSURE
    jne .wrong_type
    mov rax, SOB_TRUE_ADDRESS
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE_ADDRESS
.return:
    leave
    ret

is_symbol:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_SYMBOL
    jne .wrong_type
    mov rax, SOB_TRUE_ADDRESS
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE_ADDRESS
.return:
    leave
    ret

string_length:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    STRING_LENGTH rsi, rsi
    MAKE_INT(rax, rsi)

    leave
    ret

string_ref:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0) 
    STRING_ELEMENTS rsi, rsi
    mov rdi, PVAR(1)
    INT_VAL rdi, rdi
    shl rdi, 0
    add rsi, rdi

    mov sil, byte [rsi]
    MAKE_CHAR(rax, sil)

    leave
    ret

string_set:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0) 
    STRING_ELEMENTS rsi, rsi
    mov rdi, PVAR(1)
    INT_VAL rdi, rdi
    shl rdi, 0
    add rsi, rdi

    mov rax, PVAR(2)
    CHAR_VAL rax, rax
    mov byte [rsi], al
    mov rax, SOB_VOID_ADDRESS

    leave
    ret

make_string:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    mov rdi, PVAR(1)
    CHAR_VAL rdi, rdi
    and rdi, 255

    MAKE_STRING rax, rsi, dil

    leave
    ret

vector_length:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    VECTOR_LENGTH rsi, rsi
    MAKE_INT(rax, rsi)

    leave
    ret

vector_ref:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0) 
    VECTOR_ELEMENTS rsi, rsi
    mov rdi, PVAR(1)
    INT_VAL rdi, rdi
    shl rdi, 3
    add rsi, rdi

    mov rax, [rsi]

    leave
    ret

vector_set:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0) 
    VECTOR_ELEMENTS rsi, rsi
    mov rdi, PVAR(1)
    INT_VAL rdi, rdi
    shl rdi, 3
    add rsi, rdi

    mov rdi, PVAR(2)
    mov [rsi], rdi
    mov rax, SOB_VOID_ADDRESS

    leave
    ret

make_vector:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    mov rdi, PVAR(1)
    

    MAKE_VECTOR rax, rsi, rdi

    leave
    ret

symbol_to_string:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    SYMBOL_VAL rsi, rsi
    
    STRING_LENGTH rcx, rsi
    STRING_ELEMENTS rdi, rsi

    push rcx
    push rdi

    mov dil, byte [rdi]
    MAKE_CHAR(rax, dil)
    push rax
    MAKE_INT(rax, rcx)
    push rax
    push 2
    push SOB_NIL_ADDRESS
    call make_string
    add rsp, 4*8

    STRING_ELEMENTS rsi, rax

    pop rdi
    pop rcx

.loop:
    cmp rcx, 0
    je .end
    lea r8, [rdi+rcx]
    lea r9, [rsi+rcx]

    mov bl, byte [r8]
    mov byte [r9], bl
    
    dec rcx
    jmp .loop
.end:

    leave
    ret

char_to_integer:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    CHAR_VAL rsi, rsi
    and rsi, 255
    MAKE_INT(rax, rsi)

    leave
    ret

integer_to_char:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    and rsi, 255
    MAKE_CHAR(rax, sil)

    leave
    ret

is_eq:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    mov rdi, PVAR(1)
    cmp rsi, rdi
    je .true
    mov rax, SOB_FALSE_ADDRESS
    jmp .return

.true:
    mov rax, SOB_TRUE_ADDRESS

.return:
    leave
    ret

bin_add:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    addsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    leave
    ret

bin_mul:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    mulsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    leave
    ret

bin_sub:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    subsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    leave
    ret

bin_div:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    divsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    leave
    ret

bin_lt:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    cmpltsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    INT_VAL rsi, rax
    cmp rsi, 0
    je .return_false
    mov rax, SOB_TRUE_ADDRESS
    jmp .final_return

.return_false:
    mov rax, SOB_FALSE_ADDRESS

.final_return:


    leave
    ret

bin_equ:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL_ADDRESS
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE_ADDRESS
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    cmpeqsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    INT_VAL rsi, rax
    cmp rsi, 0
    je .return_false
    mov rax, SOB_TRUE_ADDRESS
    jmp .final_return

.return_false:
    mov rax, SOB_FALSE_ADDRESS

.final_return:


    leave
    ret

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
    push SOB_NIL_ADDRESS            ; push magic to the stack
    mov r11, qword[rbp+3*8]         ; num of arguments   
    sub r11,2                       ; without the function and the vs list
    mov r9, r11
    mov r10, rbp
    add r10, 40                     ; start the loop to point to the vs list
    mov r8, r11

point_to_vs1:
    cmp r8, 0                       ; start pointing on rbp+40
    je start_counting               ; stop
    add r10, 8                      ; add Word_size to the register - point to the next cell
    dec r8                          ; num of args -2 --
    jmp point_to_vs1                ; jmp again to the loop    

start_counting:
    mov r8, [r10]                   ; get the actual value of the vs list             
    mov rdx, 0                      ; count how many arguments are in the list
count_vs:
    cmp r8, SOB_NIL_ADDRESS         ; if the vs list is empty - stop
    je done_count_vs                ; jmp to the end
    add rdx, 1                      ; increase the counter
    CDR rax,r8                      ; count the tail of the vs list
    mov r8,rax                      ; load r8 again
    jmp count_vs                    ; jmp again to the loop
                     
done_count_vs: 
    mov r13, rdx
    mov r15, rdx
    ;sub r13, 1
    mov r14, r13             
start_push:
mov r8, qword[r10]                  ; get the actual value of the vs list
    cmp r15, 0                      ; if there are 0 arguments - dont push nothing
    je rev_list_end                 ; jmp to end

mov r12, r8                         ; point to the list
mov r14,SOB_NIL_ADDRESS             ; init empty list
rev_list1:
    cmp r13, 0                      ; if the list is empty
    je rev_list_end1                ; stop and jmp to the end
    CAR rbx, r12                    ; get the first element of the vs list and put it inside rbx
    CDR rax, r12                    ; get the tail of the vs list and put it inside rbx
    mov r12, rax
    MAKE_PAIR (rax ,rbx, r14)       ; make pair of thehead of the list and the reversed one
    mov r14, rax                    ; load the cdr of the next list
    dec r13                         ; decrease the counter of the loop
    jmp rev_list1
rev_list_end1:
mov r13, rdx                        ; r13 = number of args in the vs list 
push_list1:                         ; start pushing the vs list
    cmp r13, 0                      ; if r13 is 0 stop counting
    je push_list_end1               ; jmp to the end of pushing
    CAR rbx, r14                    ; take the first element of the reversed vs list
    push rbx                        ; push it
    CDR rax, r14                    ; take the tail of the vs list
    mov r14, rax                    ; load r14 the tail
    dec r13                         ; decrease the loop counter
    jmp push_list1                  ; jmp again to push the tail
push_list_end1:

rev_list_end:
    mov r14,r9                      ; r14 = number of regular parameters
    add r14, rdx                    ; r15 = number of regular parameters + number of parameters in the vs list

    mov r12,r10                     ; point to [rbp+8*5]
    sub r12, rbp                    ; point to 40 address
push_reg_params_list:
    cmp r9, 0                       ; if number of regular args counter is 0 stop pushing
    je push_list_end                ; jmp to the end
    sub r12,8                       ; go to the next refular parameter
    push qword[rbp+r12]             ; push it 
    dec r9                          ; decrease the regular args counter
    jmp push_reg_params_list

push_list_end:
    push r14                        ; push the number of args
    sub r12,8                       
    mov r10, qword[rbp+r12]         ; save the env
    CLOSURE_ENV r9, r10             ; call closure env macro
    push r9                         ; push the new env
    push qword [rbp + 8]            ; push retuen address  
    push qword[rbp]                 ; push rbp     
    mov r11, r14                    ; r11= number of args
    add r11, 5                      ; r11 = number of args+ 5 
    mov r13, qword [rbp + 3*8]      ; r13 = num of args
    SHIFT_FRAMESKI r11              ; shift frame r11
tuli:
    add r13,5                       ; rsp = rsp + numberof args +40
    shl r13,3
    add rsp,r13                     
    CLOSURE_CODE r9,r10             ; call closure code macro 
    pop rbp
    jmp r9
    

invalid:
leave
ret

