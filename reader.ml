(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(n1), Number(n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (Char.lowercase ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;




(*-------------------------Spaces and comments---------------------------*)
let _Space_ = PC.nt_whitespace;;
let _Spaces_ = PC.star _Space_ ;;
let _not_psikuda_ = 
  let a =(PC.range (char_of_int 32) (char_of_int 127)) in
  PC.guard a (fun(literal)-> ( literal!=';'));;
let _psikuda_ = PC.char ';' ;;
let _many_not_psikuda_ = PC.plus _not_psikuda_;;
let _comment_start_ =  PC.caten _many_not_psikuda_ _psikuda_;;
let _comment_char_data_ =
let a =(PC.range (char_of_int 32) (char_of_int 127)) in
PC.guard a (fun(literal)-> ( literal!='\n'));;
let _comment_full_data_ = PC.star _comment_char_data_;;
let _comment_start_and_data_ = PC.caten _comment_start_ _comment_full_data_ ;;
let _end_of_comment_ = PC.char '\n' ;;
let _Comment_ = PC.caten _comment_start_and_data_ _end_of_comment_;;
let _Skip_ = PC.disj _Spaces_ _Comment_;;


let _Space_Comment_wrapper_ p =
let _prefix_ = PC.caten _Skip_ p in
let _parsed_format_ = PC.caten _prefix_ _Spaces_ in
PC.pack _parsed_format_ (fun((prefix, data), suffix) ->data);;

PC.test_string _Sexp_ " (1 2 ); chino \n";;


(* ------------------- Boolean Parser ------------------------------ *)

let _tchar_ = (PC.char_ci 't');;
let _fchar_= (PC.char_ci 'f');;
let _sulamit_ =  (PC.char '#');;
let _trueParser_ =
  let _truep_ = PC.caten _sulamit_ _tchar_ in
  PC.pack _truep_ (fun(s,t) -> Bool(true));;

let _falseParser_ =
  let _falsep_ = PC.caten _sulamit_ _fchar_ in
  PC.pack _falsep_ (fun(s,f) -> Bool(false));;

let _Boolean_no_space_ = PC.disj _trueParser_ _falseParser_;;
let _Boolean_ = _Space_Comment_wrapper_ _Boolean_no_space_;;

(* ----------------------------- number ----------------------------- *)
let _Digit_ = PC.range '0' '9' ;;
let _Natural_ = 
  let _Digits_ = PC.plus _Digit_ in
  PC.pack _Digits_ (fun (digits) -> Int (int_of_string(list_to_string digits)));;

let _Natural_val_ = 
  let _Digits_ = PC.plus _Digit_ in
  PC.pack _Digits_ (fun (digits) ->  (list_to_string digits));;

let _Sign_ = (PC.caten (PC.maybe (PC.one_of("+-")))_Natural_);;


let _Integer_val_ = 
      PC.pack _Sign_ (fun (sign, number) -> match sign, number with
    |Some '+' , Int(number)->  number
    |Some '-',  Int(number) ->  number*(-1)
    |_ , Int(number) -> number
    |_,_ -> raise PC.X_no_match);;

let _Integer_no_space_ = 
      PC.pack _Integer_val_ (fun ( number) -> Number(Int(number)));; 

let _Integer_ = _Space_Comment_wrapper_ _Integer_no_space_;;

let _Float_no_space_=
  let _dot_ = PC.char '.' in
    let _dot_natural_ = PC.caten _dot_ _Natural_val_ in
      let _float_format_ = PC.caten _Integer_val_ _dot_natural_ in
        PC.pack _float_format_ (fun(n, (dot, n2)) -> Number(Float(float_of_string(string_of_int n ^ "." ^ n2))));;

let _Float_ = _Space_Comment_wrapper_ _Float_no_space_;;

let _HexPrefix_ = 
  let _sulamit_ = PC.char '#' in
  let _x_ = PC.char 'x' in
  PC.caten _sulamit_ _x_;;

let _Lower_ = PC.range 'a' 'f';;
let _Digit_ = PC.range '0' '9' ;;
let _Capital_ = PC.range 'A' 'F';;

let _HexDigit_ = PC.disj_list [_Digit_ ; _Lower_ ; _Capital_ ;];;
let _HexNatural_ = PC.plus _HexDigit_;;

let _Hex_Natural_val_ = 
  let _Digits_ = PC.plus _HexDigit_ in
  PC.pack _Digits_ (fun (digits) ->  list_to_string(digits)) ;;

let _Sign_hex_ = (PC.caten (PC.maybe (PC.one_of("+-")))_HexNatural_)

let _HexInteger_no_space_ = 
let _hex_integer_format_ = PC.caten _HexPrefix_ _Sign_hex_ in
PC.pack _hex_integer_format_ (fun(((prefix1,prefix2),(sign,digits))) -> match sign with
|None -> Number(Int((int_of_string(list_to_string('0' :: 'x'::digits))))) 
| Some '-' ->  Number(Int((-1)*(int_of_string(list_to_string('0' :: 'x'::digits)))))
| Some '+' ->   Number(Int((int_of_string(list_to_string('0' :: 'x'::digits))))) 
| _ -> raise PC.X_no_match);;

let _HexInteger_ = _Space_Comment_wrapper_ _HexInteger_no_space_;;

let _HexIntegerval_ = 
let _hex_integer_format_ = PC.caten _HexPrefix_ _Sign_hex_ in
PC.pack _hex_integer_format_ (fun(((prefix1,prefix2),(sign,digits))) -> match sign with
|None -> list_to_string('0' :: 'x'::digits)
| Some '-' -> (list_to_string('-'::'0' :: 'x'::digits))
| Some '+' -> list_to_string('0' :: 'x'::digits)
| _ -> raise PC.X_no_match);;

let _HexFloat_no_sapce_ = 
let _dot_ = PC.char '.' in
    let _dot_hex_natural_ = PC.caten _dot_ _Hex_Natural_val_ in
      let _hex_float_format_ = PC.caten _HexIntegerval_ _dot_hex_natural_ in
        PC.pack _hex_float_format_ (fun(n, (dot, n2)) -> Number(Float(float_of_string(n ^ "." ^ n2)))) ;;

let _HexFloat_ = _Space_Comment_wrapper_ _HexFloat_no_sapce_;;

let _Number_ = PC.disj_list [_HexFloat_;_Float_;_HexInteger_; _Integer_; ] ;;

(* ----------------------------- char ------------------------------- *)

let _backslash_ = (PC.char '\\');;
let _CharPrefix_ =  PC.caten _sulamit_  _backslash_;;
let _x_ = (PC.char_ci 'x');;

let _Lower_ = PC.range 'a' 'f';;
let _Digit_ = PC.range '0' '9' ;;
let _Capital_ = PC.range 'A' 'F';;

let _HexDigit_ = PC.disj_list [_Digit_ ; _Lower_ ; _Capital_ ;];;

let _HexChar_ =
  let chars = PC.plus _HexDigit_ in
  let zxchars = PC.caten _x_ chars in
  PC.pack zxchars (fun (x,cl) -> Char(char_of_int((int_of_string(list_to_string('0'::'x'::cl))))));;

let _newline_ =  
PC.pack (PC.word_ci "newline") (fun(x)-> Char(char_of_int (10)));;
let _page_=PC.pack (PC.word_ci "page") (fun(x)-> Char(char_of_int (12))) ;;
let _return_= PC.pack (PC.word_ci "return") (fun(x)-> Char(char_of_int (13)) );;
let _space_= PC.pack (PC.word_ci "space") (fun(x)-> Char(char_of_int (32))) ;;
let _tab_= PC.pack (PC.word_ci "tab") (fun(x)-> Char(char_of_int (9))) ;;
let _nul_= PC.pack (PC.word_ci "nul") (fun(x)-> Char(char_of_int (0))) ;;

let named = PC.disj_list[_newline_; _page_;_return_; _space_;_tab_; _nul_];;

let _NamedChar_  =
  PC.pack named (fun(x)->x);;
  
let _greaterThanSpace_ = (PC.range (char_of_int 32) (char_of_int 127));;

let _VisibleSimpleChar_ = 
  PC.pack _greaterThanSpace_ (fun (c)-> Char(c));;
  
let _Char_no_space_  = 
let prefixAndChar = PC.caten _CharPrefix_  (PC.disj_list [_NamedChar_;  _HexChar_;_VisibleSimpleChar_;]) in
PC.pack prefixAndChar (fun(x,c)->c);;

let _Char_ = _Space_Comment_wrapper_ _Char_no_space_;;


(*-------------------------------------- String ------------------------------------------- *)


let _StringHexChar_ =
  let _Hexdigits_ = PC.plus _HexDigit_ in
  let xhexa = PC.caten  _x_ _Hexdigits_ in
  let backxhexa = PC.caten _backslash_ xhexa in
  let nekuda = PC.caten backxhexa (PC.char ';') in
  PC.pack nekuda (fun((backslash, (x, digits)),nekudapsik)->(char_of_int(int_of_string(list_to_string('0'::'x'::digits)))));;


let _backslash_ = (PC.char '\\');;
let _merchaot_ = PC.char '\"';;

let meta1 =
let word = (PC.word_ci "\\\"") in
 PC.pack  word(fun(x)-> '\"');;
let meta2 = 
let word = (PC.word_ci "\\t") in
PC.pack word (fun(x)-> '\t');;
let meta3 = 
let word = (PC.word_ci "\\f") in
PC.pack word (fun(x)-> '\012');;
let meta4 = 
let word = (PC.word_ci "\\n") in
PC.pack word (fun(x)-> '\n');;
let meta5 = 
let word= (PC.word_ci "\\r") in
PC.pack  word(fun(x)-> '\r');;
let meta6 = 
let word = (PC.word_ci "\\\\") in
PC.pack word (fun(x)-> ('\\'));;

let first_disf = PC.disj meta5 meta6;;
let second_disf = PC.disj meta4 first_disf;;
let third_disf = PC.disj meta2 second_disf;;
let final = PC.disj meta1 third_disf;;

let _StringMetaChar_=  PC.disj_list[meta1;meta2;meta3; meta4; meta5; meta6;];;

let _StringLiteralChar_ =
let chars =  (PC.range (char_of_int 32) (char_of_int 127)) in
PC.guard chars (fun(literal)-> ( literal!='\"') && literal!='\\');;

let _StringChar_ = PC.disj_list [_StringMetaChar_ ;_StringHexChar_;_StringLiteralChar_;];;

let _String_no_space_ = 
let kleeneString = PC.caten _merchaot_ (PC.caten (PC.star _StringChar_) _merchaot_) in
PC.pack kleeneString (fun(x, (s,y))-> String(list_to_string s));;

let _String_ = _Space_Comment_wrapper_ _String_no_space_;;

(*--------------Symbol----------------*)

let _bang_ = PC.char '!';;
let _dollar_ = PC.char '$';;
let _exp_ = PC.char '^';;
let _kohavit_ = PC.char '*';;
let _makaf_ = PC.char '-';;
let _low_makaf_ = PC.char '_';;
let _equal_ = PC.char '=';;
let _plus_ = PC.char '+';;
let _meshulash_open_ = PC.char '<';;
let _meshulash_close_ = PC.char '>';;
let _question_ = PC.char '?';;
let _forward_slash_ = PC.char '/';;
let _dots_ = PC.char ':';;
let _letters_ = PC.range_ci 'a' 'z';;
let _digit_chars_ = PC.range '0' '9' ;;

let _parsed_=
let _capital_letters = PC.range 'A' 'Z' in
 PC.pack _capital_letters (fun (ch) -> lowercase_ascii ch);;

let _SymbolChar_ = PC.disj_list [_parsed_; _digit_chars_;_letters_;_bang_; _dollar_; _exp_; _kohavit_; _makaf_; _low_makaf_; _equal_; _plus_; _meshulash_open_; _meshulash_close_; _question_; _forward_slash_; _dots_;];;

let _Symbol_no_space_ =
  let _SymbolChars_ = PC.plus _SymbolChar_ in
  PC.pack _SymbolChars_ (fun (chars) ->  Symbol(list_to_string chars));;

let _Symbol_ = _Space_Comment_wrapper_ _Symbol_no_space_;;


(*--------------------------------- 3 Dots ----------------------------------------*)

let nt_close_all = PC.word "...";;
let nt_open = PC.char '(';;
let nt_close = PC.char ')';;

(*-------------------------------- recursive --------------------------------------*)

let poteah = PC.char '(' ;;
let soger = PC.char ')' ;;
let squarePoteah = PC.char '[' ;;
let squareSoger = PC.char ']' ;;
let _nil_ = 
let a = PC.caten poteah (PC.caten _Skip_ soger) in
PC.pack a (fun(s) -> Nil);;


let _atoms_ = PC.disj_list[_Boolean_;_Char_; _Number_; _String_; _Symbol_;];;
let rec _Sexp_ s = PC.disj_list[_atoms_;_compound_; ] s

and _compound_  s= 
let packed = PC.disj_list [_List_;_Vector_;_Quoted_;_QuasiQuoted_;_Unquoted_;_UnquoteAndSpliced_;] in
packed s


(*---------------------------- LIST --------------------------------------*)

and _List_no_space_ s =
let a = PC.caten (PC.caten poteah (PC.star _Sexp_)) soger in
let b =  PC.caten (PC.caten squarePoteah (PC.star _Sexp_)) squareSoger in 
let aORb = PC.disj a b in
let packed =  PC.pack aORb (fun((x,lst_sexp),y)->List.fold_right (fun n1 n2 -> Pair(n1,n2))  lst_sexp Nil) in
packed s

and _List_ s = 
let packed = _Space_Comment_wrapper_ _List_no_space_ in
packed s



(*---------------------------- Dotted LIST --------------------------------------*)
and _DottedList_no_space_ s=
let a = PC.caten (PC.caten poteah (PC.plus _Sexp_)) (PC.char '.') in
let b = PC.caten a _Sexp_ in
let sogerPoteahAndContent =  PC.caten b soger in
let square_a = PC.caten (PC.caten squarePoteah (PC.plus _Sexp_)) (PC.char '.') in
let square_b = PC.caten square_a _Sexp_ in
let sogerPoteahAndContent1 =  PC.caten square_b squareSoger in
let squareOrNot = PC.disj sogerPoteahAndContent sogerPoteahAndContent1 in
let packed =  PC.pack squareOrNot (fun((((p,lst_sexp),nekuda),sexp),soger)->List.fold_right (fun n1 n2 -> Pair(n1,n2)) lst_sexp sexp) in
packed s

and _DottedList_ s = 
let packed = _Space_Comment_wrapper_ _DottedList_no_space_ in
packed s

(*---------------------------- Vector --------------------------------------*)
and _Vector_no_space_ s = 
let sulPoteah = PC.caten (PC.char '#') poteah in
let a = PC.caten sulPoteah (PC.star _Sexp_) in
let sogerPoteahAndContent =  PC.caten a soger in
let packed =  PC.pack sogerPoteahAndContent (fun(((sulamit,p),lst_sexp),y)-> Vector(lst_sexp)) in
packed s

and _Vector_ s = 
let packed = _Space_Comment_wrapper_ _Vector_no_space_ in
packed s
(*---------------------------- Quoted --------------------------------------*)

and _Quoted_no_space_ s= 
let prefix = (PC.caten (PC.char '\'') _Sexp_) in
let packed = PC.pack  prefix (fun(x,s)->Pair(Symbol("quote"), Pair(s, Nil))) in
packed s

and _Quoted_ s = 
let packed = _Space_Comment_wrapper_ _Quoted_no_space_ in
packed s

(*---------------------------- QuasiQuoted --------------------------------------*)
and _QuasiQuoted_no_space_ s=
let prefix =  (PC.caten (PC.char '`') _Sexp_ ) in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("quasiquote"), Pair(s, Nil))) in
packed s

and _QuasiQuoted_ s = 
let packed = _Space_Comment_wrapper_ _QuasiQuoted_no_space_ in
packed s
(*---------------------------- Unquoted --------------------------------------*)

and _Unquoted_no_space_ s= 
let prefix = PC.caten (PC.char ',')  _Sexp_  in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("unquote"), Pair(s, Nil))) in
packed s

and _Unquoted_ s = 
let packed = _Space_Comment_wrapper_ _Unquoted_no_space_ in
packed s

(*---------------------------- ⟨UnquoteAndSpliced⟩ --------------------------------------*)
and _UnquoteAndSpliced_no_space_ s =
let prefix = PC.caten (PC.word ",@")  _Sexp_  in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("unquote-splicing"), Pair(s, Nil))) in
packed s 

and _UnquoteAndSpliced_ s = 
let packed = _Space_Comment_wrapper_ _UnquoteAndSpliced_no_space_ in
packed s;;

(*--------------------------- Sceintific Notation ---------------------------------------*)

let _Float_val_=
  let _dot_ = PC.char '.' in
    let _dot_natural_ = PC.caten _dot_ _Natural_val_ in
      let _float_format_ = PC.caten _Integer_val_ _dot_natural_ in
        PC.pack _float_format_ (fun(n, (dot, n2)) -> float_of_string(string_of_int n ^ "." ^ n2));;

 
let _e_ = PC.char_ci 'e' ;;
let _prefix_and_e_ = PC.caten _Integer_val_ _e_;;
let _sceintific_format_int_ = PC.caten _prefix_and_e_ _Integer_val_;;
let _sceintific_notation_int_ =
PC.pack _sceintific_format_int_ (fun ((before,e),after)-> Number(Int(int_of_float((float_of_string (string_of_int before)) *. (10.0 **  float_of_string (string_of_int (after)))))));;

let _Fprefix_and_e_ = PC.caten _Float_val_ _e_;;
let _sceintific_format_float_ = PC.caten _Fprefix_and_e_ _Integer_val_;;
let _sceintific_notation_float_ =
PC.pack _sceintific_format_float_ (fun ((before,e),after)-> Number(Float(before *. (10.0 **   float_of_string (string_of_int (after))))));;
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(n1), Number(n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (Char.lowercase ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let read_sexpr string = raise X_not_yet_implemented ;;

let read_sexprs string = raise X_not_yet_implemented;;


(*-------------------------Spaces and comments---------------------------*)
let _Space_ = PC.nt_whitespace;;
let _Spaces_ = PC.star _Space_ ;;
let _not_psikuda_ = 
  let a =(PC.range (char_of_int 32) (char_of_int 127)) in
  PC.guard a (fun(literal)-> ( literal!=';'));;
let _psikuda_ = PC.char ';' ;;
let _many_not_psikuda_ = PC.plus _not_psikuda_;;
let _comment_start_ =  PC.caten _many_not_psikuda_ _psikuda_;;
let _comment_char_data_ =
let a =(PC.range (char_of_int 32) (char_of_int 127)) in
PC.guard a (fun(literal)-> ( literal!='\n'));;
let _comment_full_data_ = PC.star _comment_char_data_;;
let _comment_start_and_data_ = PC.caten _comment_start_ _comment_full_data_ ;;
let _end_of_comment_ = PC.char '\n' ;;
let _Comment_ = PC.caten _comment_start_and_data_ _end_of_comment_;;
let _Skip_ = PC.disj _Spaces_ _Comment_;;


let _Space_Comment_wrapper_ p =
let _prefix_ = PC.caten _Skip_ p in
let _parsed_format_ = PC.caten _prefix_ _Spaces_ in
PC.pack _parsed_format_ (fun((prefix, data), suffix) ->data);;

PC.test_string _Sexp_ " (1 2 ); chino \n";;


(* ------------------- Boolean Parser ------------------------------ *)

let _tchar_ = (PC.char_ci 't');;
let _fchar_= (PC.char_ci 'f');;
let _sulamit_ =  (PC.char '#');;
let _trueParser_ =
  let _truep_ = PC.caten _sulamit_ _tchar_ in
  PC.pack _truep_ (fun(s,t) -> Bool(true));;

let _falseParser_ =
  let _falsep_ = PC.caten _sulamit_ _fchar_ in
  PC.pack _falsep_ (fun(s,f) -> Bool(false));;

let _Boolean_no_space_ = PC.disj _trueParser_ _falseParser_;;
let _Boolean_ = _Space_Comment_wrapper_ _Boolean_no_space_;;

(* ----------------------------- number ----------------------------- *)
let _Digit_ = PC.range '0' '9' ;;
let _Natural_ = 
  let _Digits_ = PC.plus _Digit_ in
  PC.pack _Digits_ (fun (digits) -> Int (int_of_string(list_to_string digits)));;

let _Natural_val_ = 
  let _Digits_ = PC.plus _Digit_ in
  PC.pack _Digits_ (fun (digits) ->  (list_to_string digits));;

let _Sign_ = (PC.caten (PC.maybe (PC.one_of("+-")))_Natural_);;


let _Integer_val_ = 
      PC.pack _Sign_ (fun (sign, number) -> match sign, number with
    |Some '+' , Int(number)->  number
    |Some '-',  Int(number) ->  number*(-1)
    |_ , Int(number) -> number
    |_,_ -> raise PC.X_no_match);;

let _Integer_no_space_ = 
      PC.pack _Integer_val_ (fun ( number) -> Number(Int(number)));; 

let _Integer_ = _Space_Comment_wrapper_ _Integer_no_space_;;

let _Float_no_space_=
  let _dot_ = PC.char '.' in
    let _dot_natural_ = PC.caten _dot_ _Natural_val_ in
      let _float_format_ = PC.caten _Integer_val_ _dot_natural_ in
        PC.pack _float_format_ (fun(n, (dot, n2)) -> Number(Float(float_of_string(string_of_int n ^ "." ^ n2))));;

let _Float_ = _Space_Comment_wrapper_ _Float_no_space_;;

let _HexPrefix_ = 
  let _sulamit_ = PC.char '#' in
  let _x_ = PC.char 'x' in
  PC.caten _sulamit_ _x_;;

let _Lower_ = PC.range 'a' 'f';;
let _Digit_ = PC.range '0' '9' ;;
let _Capital_ = PC.range 'A' 'F';;

let _HexDigit_ = PC.disj_list [_Digit_ ; _Lower_ ; _Capital_ ;];;
let _HexNatural_ = PC.plus _HexDigit_;;

let _Hex_Natural_val_ = 
  let _Digits_ = PC.plus _HexDigit_ in
  PC.pack _Digits_ (fun (digits) ->  list_to_string(digits)) ;;

let _Sign_hex_ = (PC.caten (PC.maybe (PC.one_of("+-")))_HexNatural_)

let _HexInteger_no_space_ = 
let _hex_integer_format_ = PC.caten _HexPrefix_ _Sign_hex_ in
PC.pack _hex_integer_format_ (fun(((prefix1,prefix2),(sign,digits))) -> match sign with
|None -> Number(Int((int_of_string(list_to_string('0' :: 'x'::digits))))) 
| Some '-' ->  Number(Int((-1)*(int_of_string(list_to_string('0' :: 'x'::digits)))))
| Some '+' ->   Number(Int((int_of_string(list_to_string('0' :: 'x'::digits))))) 
| _ -> raise PC.X_no_match);;

let _HexInteger_ = _Space_Comment_wrapper_ _HexInteger_no_space_;;

let _HexIntegerval_ = 
let _hex_integer_format_ = PC.caten _HexPrefix_ _Sign_hex_ in
PC.pack _hex_integer_format_ (fun(((prefix1,prefix2),(sign,digits))) -> match sign with
|None -> list_to_string('0' :: 'x'::digits)
| Some '-' -> (list_to_string('-'::'0' :: 'x'::digits))
| Some '+' -> list_to_string('0' :: 'x'::digits)
| _ -> raise PC.X_no_match);;

let _HexFloat_no_sapce_ = 
let _dot_ = PC.char '.' in
    let _dot_hex_natural_ = PC.caten _dot_ _Hex_Natural_val_ in
      let _hex_float_format_ = PC.caten _HexIntegerval_ _dot_hex_natural_ in
        PC.pack _hex_float_format_ (fun(n, (dot, n2)) -> Number(Float(float_of_string(n ^ "." ^ n2)))) ;;

let _HexFloat_ = _Space_Comment_wrapper_ _HexFloat_no_sapce_;;

let _Number_ = PC.disj_list [_HexFloat_;_Float_;_HexInteger_; _Integer_; ] ;;

(* ----------------------------- char ------------------------------- *)

let _backslash_ = (PC.char '\\');;
let _CharPrefix_ =  PC.caten _sulamit_  _backslash_;;
let _x_ = (PC.char_ci 'x');;

let _Lower_ = PC.range 'a' 'f';;
let _Digit_ = PC.range '0' '9' ;;
let _Capital_ = PC.range 'A' 'F';;

let _HexDigit_ = PC.disj_list [_Digit_ ; _Lower_ ; _Capital_ ;];;

let _HexChar_ =
  let chars = PC.plus _HexDigit_ in
  let zxchars = PC.caten _x_ chars in
  PC.pack zxchars (fun (x,cl) -> Char(char_of_int((int_of_string(list_to_string('0'::'x'::cl))))));;

let _newline_ =  
PC.pack (PC.word_ci "newline") (fun(x)-> Char(char_of_int (10)));;
let _page_=PC.pack (PC.word_ci "page") (fun(x)-> Char(char_of_int (12))) ;;
let _return_= PC.pack (PC.word_ci "return") (fun(x)-> Char(char_of_int (13)) );;
let _space_= PC.pack (PC.word_ci "space") (fun(x)-> Char(char_of_int (32))) ;;
let _tab_= PC.pack (PC.word_ci "tab") (fun(x)-> Char(char_of_int (9))) ;;
let _nul_= PC.pack (PC.word_ci "nul") (fun(x)-> Char(char_of_int (0))) ;;

let named = PC.disj_list[_newline_; _page_;_return_; _space_;_tab_; _nul_];;

let _NamedChar_  =
  PC.pack named (fun(x)->x);;
  
let _greaterThanSpace_ = (PC.range (char_of_int 32) (char_of_int 127));;

let _VisibleSimpleChar_ = 
  PC.pack _greaterThanSpace_ (fun (c)-> Char(c));;
  
let _Char_no_space_  = 
let prefixAndChar = PC.caten _CharPrefix_  (PC.disj_list [_NamedChar_;  _HexChar_;_VisibleSimpleChar_;]) in
PC.pack prefixAndChar (fun(x,c)->c);;

let _Char_ = _Space_Comment_wrapper_ _Char_no_space_;;


(*-------------------------------------- String ------------------------------------------- *)


let _StringHexChar_ =
  let _Hexdigits_ = PC.plus _HexDigit_ in
  let xhexa = PC.caten  _x_ _Hexdigits_ in
  let backxhexa = PC.caten _backslash_ xhexa in
  let nekuda = PC.caten backxhexa (PC.char ';') in
  PC.pack nekuda (fun((backslash, (x, digits)),nekudapsik)->(char_of_int(int_of_string(list_to_string('0'::'x'::digits)))));;


let _backslash_ = (PC.char '\\');;
let _merchaot_ = PC.char '\"';;

let meta1 =
let word = (PC.word_ci "\\\"") in
 PC.pack  word(fun(x)-> '\"');;
let meta2 = 
let word = (PC.word_ci "\\t") in
PC.pack word (fun(x)-> '\t');;
let meta3 = 
let word = (PC.word_ci "\\f") in
PC.pack word (fun(x)-> '\012');;
let meta4 = 
let word = (PC.word_ci "\\n") in
PC.pack word (fun(x)-> '\n');;
let meta5 = 
let word= (PC.word_ci "\\r") in
PC.pack  word(fun(x)-> '\r');;
let meta6 = 
let word = (PC.word_ci "\\\\") in
PC.pack word (fun(x)-> ('\\'));;

let first_disf = PC.disj meta5 meta6;;
let second_disf = PC.disj meta4 first_disf;;
let third_disf = PC.disj meta2 second_disf;;
let final = PC.disj meta1 third_disf;;

let _StringMetaChar_=  PC.disj_list[meta1;meta2;meta3; meta4; meta5; meta6;];;

let _StringLiteralChar_ =
let chars =  (PC.range (char_of_int 32) (char_of_int 127)) in
PC.guard chars (fun(literal)-> ( literal!='\"') && literal!='\\');;

let _StringChar_ = PC.disj_list [_StringMetaChar_ ;_StringHexChar_;_StringLiteralChar_;];;

let _String_no_space_ = 
let kleeneString = PC.caten _merchaot_ (PC.caten (PC.star _StringChar_) _merchaot_) in
PC.pack kleeneString (fun(x, (s,y))-> String(list_to_string s));;

let _String_ = _Space_Comment_wrapper_ _String_no_space_;;

(*--------------Symbol----------------*)

let _bang_ = PC.char '!';;
let _dollar_ = PC.char '$';;
let _exp_ = PC.char '^';;
let _kohavit_ = PC.char '*';;
let _makaf_ = PC.char '-';;
let _low_makaf_ = PC.char '_';;
let _equal_ = PC.char '=';;
let _plus_ = PC.char '+';;
let _meshulash_open_ = PC.char '<';;
let _meshulash_close_ = PC.char '>';;
let _question_ = PC.char '?';;
let _forward_slash_ = PC.char '/';;
let _dots_ = PC.char ':';;
let _letters_ = PC.range_ci 'a' 'z';;
let _digit_chars_ = PC.range '0' '9' ;;

let _parsed_=
let _capital_letters = PC.range 'A' 'Z' in
 PC.pack _capital_letters (fun (ch) -> lowercase_ascii ch);;

let _SymbolChar_ = PC.disj_list [_parsed_; _digit_chars_;_letters_;_bang_; _dollar_; _exp_; _kohavit_; _makaf_; _low_makaf_; _equal_; _plus_; _meshulash_open_; _meshulash_close_; _question_; _forward_slash_; _dots_;];;

let _Symbol_no_space_ =
  let _SymbolChars_ = PC.plus _SymbolChar_ in
  PC.pack _SymbolChars_ (fun (chars) ->  Symbol(list_to_string chars));;

let _Symbol_ = _Space_Comment_wrapper_ _Symbol_no_space_;;


(*--------------------------------- 3 Dots ----------------------------------------*)

let nt_close_all = PC.word "...";;
let nt_open = PC.char '(';;
let nt_close = PC.char ')';;

(*-------------------------------- recursive --------------------------------------*)

let poteah = PC.char '(' ;;
let soger = PC.char ')' ;;
let squarePoteah = PC.char '[' ;;
let squareSoger = PC.char ']' ;;
let _nil_ = 
let a = PC.caten poteah (PC.caten _Skip_ soger) in
PC.pack a (fun(s) -> Nil);;


let _atoms_ = PC.disj_list[_Boolean_;_Char_; _Number_; _String_; _Symbol_;];;
let rec _Sexp_ s = PC.disj_list[_atoms_;_compound_; ] s

and _compound_  s= 
let packed = PC.disj_list [_List_;_Vector_;_Quoted_;_QuasiQuoted_;_Unquoted_;_UnquoteAndSpliced_;] in
packed s


(*---------------------------- LIST --------------------------------------*)

and _List_no_space_ s =
let a = PC.caten (PC.caten poteah (PC.star _Sexp_)) soger in
let b =  PC.caten (PC.caten squarePoteah (PC.star _Sexp_)) squareSoger in 
let aORb = PC.disj a b in
let packed =  PC.pack aORb (fun((x,lst_sexp),y)->List.fold_right (fun n1 n2 -> Pair(n1,n2))  lst_sexp Nil) in
packed s

and _List_ s = 
let packed = _Space_Comment_wrapper_ _List_no_space_ in
packed s



(*---------------------------- Dotted LIST --------------------------------------*)
and _DottedList_no_space_ s=
let a = PC.caten (PC.caten poteah (PC.plus _Sexp_)) (PC.char '.') in
let b = PC.caten a _Sexp_ in
let sogerPoteahAndContent =  PC.caten b soger in
let square_a = PC.caten (PC.caten squarePoteah (PC.plus _Sexp_)) (PC.char '.') in
let square_b = PC.caten square_a _Sexp_ in
let sogerPoteahAndContent1 =  PC.caten square_b squareSoger in
let squareOrNot = PC.disj sogerPoteahAndContent sogerPoteahAndContent1 in
let packed =  PC.pack squareOrNot (fun((((p,lst_sexp),nekuda),sexp),soger)->List.fold_right (fun n1 n2 -> Pair(n1,n2)) lst_sexp sexp) in
packed s

and _DottedList_ s = 
let packed = _Space_Comment_wrapper_ _DottedList_no_space_ in
packed s

(*---------------------------- Vector --------------------------------------*)
and _Vector_no_space_ s = 
let sulPoteah = PC.caten (PC.char '#') poteah in
let a = PC.caten sulPoteah (PC.star _Sexp_) in
let sogerPoteahAndContent =  PC.caten a soger in
let packed =  PC.pack sogerPoteahAndContent (fun(((sulamit,p),lst_sexp),y)-> Vector(lst_sexp)) in
packed s

and _Vector_ s = 
let packed = _Space_Comment_wrapper_ _Vector_no_space_ in
packed s
(*---------------------------- Quoted --------------------------------------*)

and _Quoted_no_space_ s= 
let prefix = (PC.caten (PC.char '\'') _Sexp_) in
let packed = PC.pack  prefix (fun(x,s)->Pair(Symbol("quote"), Pair(s, Nil))) in
packed s

and _Quoted_ s = 
let packed = _Space_Comment_wrapper_ _Quoted_no_space_ in
packed s

(*---------------------------- QuasiQuoted --------------------------------------*)
and _QuasiQuoted_no_space_ s=
let prefix =  (PC.caten (PC.char '`') _Sexp_ ) in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("quasiquote"), Pair(s, Nil))) in
packed s

and _QuasiQuoted_ s = 
let packed = _Space_Comment_wrapper_ _QuasiQuoted_no_space_ in
packed s
(*---------------------------- Unquoted --------------------------------------*)

and _Unquoted_no_space_ s= 
let prefix = PC.caten (PC.char ',')  _Sexp_  in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("unquote"), Pair(s, Nil))) in
packed s

and _Unquoted_ s = 
let packed = _Space_Comment_wrapper_ _Unquoted_no_space_ in
packed s

(*---------------------------- ⟨UnquoteAndSpliced⟩ --------------------------------------*)
and _UnquoteAndSpliced_no_space_ s =
let prefix = PC.caten (PC.word ",@")  _Sexp_  in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("unquote-splicing"), Pair(s, Nil))) in
packed s 

and _UnquoteAndSpliced_ s = 
let packed = _Space_Comment_wrapper_ _UnquoteAndSpliced_no_space_ in
packed s;;

(*--------------------------- Sceintific Notation ---------------------------------------*)

let _Float_val_=
  let _dot_ = PC.char '.' in
    let _dot_natural_ = PC.caten _dot_ _Natural_val_ in
      let _float_format_ = PC.caten _Integer_val_ _dot_natural_ in
        PC.pack _float_format_ (fun(n, (dot, n2)) -> float_of_string(string_of_int n ^ "." ^ n2));;

 
let _e_ = PC.char_ci 'e' ;;
let _prefix_and_e_ = PC.caten _Integer_val_ _e_;;
let _sceintific_format_int_ = PC.caten _prefix_and_e_ _Integer_val_;;
let _sceintific_notation_int_ =
PC.pack _sceintific_format_int_ (fun ((before,e),after)-> Number(Int(int_of_float((float_of_string (string_of_int before)) *. (10.0 **  float_of_string (string_of_int (after)))))));;

let _Fprefix_and_e_ = PC.caten _Float_val_ _e_;;
let _sceintific_format_float_ = PC.caten _Fprefix_and_e_ _Integer_val_;;
let _sceintific_notation_float_ =
PC.pack _sceintific_format_float_ (fun ((before,e),after)-> Number(Float(before *. (10.0 **   float_of_string (string_of_int (after))))));;

let _sceintific_notation_no_space_ = PC.disj _sceintific_notation_int_ _sceintific_notation_float_ ;;
let _sceintific_notation_ = _Space_Comment_wrapper_ _sceintific_notation_no_space_;;

let read_sexpr string = 
let (a,b)=_Sexp_ (string_to_list (string)) in
a;;

let read_sexprs string = 
let (a,b)= (PC.star _Sexp_)(string_to_list string) in
a;;


end;; (* struct Reader *)
