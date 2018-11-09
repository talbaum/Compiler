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

let _Boolean_ = PC.disj _trueParser_ _falseParser_;;
(* ------------------------------------------------------------------ *)
(* ----------------------------- number ----------------------------- *)

let _Number_ = PC.disj_list [_HexFloat_;_Float_;_HexInteger_; _Integer_; ] ;;
let _Digit_ = PC.range '0' '9' ;;
let _Natural_ = 
  let _Digits_ = PC.plus _Digit_ in
  PC.pack _Digits_ (fun (digits) -> Int (int_of_string(list_to_string digits)));;

let _Natural_val_ = 
  let _Digits_ = PC.plus _Digit_ in
  PC.pack _Digits_ (fun (digits) ->  (list_to_string digits));;

let _Sign_ = (PC.caten (PC.maybe (PC.one_of("+-")))_Natural_);;

let _Integer_ = 
      PC.pack _Integer_val_ (fun ( number) -> Number(Int(number)));; 

let _Integer_val_ = 
      PC.pack _Sign_ (fun (sign, number) -> match sign, number with
    |Some '+' , Int(number)->  number
    |Some '-',  Int(number) ->  number*(-1)
    |_ , Int(number) -> number);;

let _Float_=
  let _dot_ = PC.char '.' in
    let _dot_natural_ = PC.caten _dot_ _Natural_val_ in
      let _float_format_ = PC.caten _Integer_val_ _dot_natural_ in
        PC.pack _float_format_ (fun(n, (dot, n2)) -> Number(Float(float_of_string(string_of_int n ^ "." ^ n2))));;

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

let _HexInteger_ = 
let _hex_integer_format_ = PC.caten _HexPrefix_ _Sign_hex_ in
PC.pack _hex_integer_format_ (fun(((prefix1,prefix2),(sign,digits))) -> match sign with
|None -> Number(Int((int_of_string(list_to_string('0' :: 'x'::digits))))) 
| Some '-' ->  Number(Int((-1)*(int_of_string(list_to_string('0' :: 'x'::digits)))))
| Some '+' ->   Number(Int((int_of_string(list_to_string('0' :: 'x'::digits))))) 
| _ -> raise PC.X_no_match);;

let _HexIntegerval_ = 
let _hex_integer_format_ = PC.caten _HexPrefix_ _Sign_hex_ in
PC.pack _hex_integer_format_ (fun(((prefix1,prefix2),(sign,digits))) -> match sign with
|None -> list_to_string('0' :: 'x'::digits)
| Some '-' -> (list_to_string('-'::'0' :: 'x'::digits))
| Some '+' -> list_to_string('0' :: 'x'::digits)
| _ -> raise PC.X_no_match);;

let _HexFloat_ = 
let _dot_ = PC.char '.' in
    let _dot_hex_natural_ = PC.caten _dot_ _Hex_Natural_val_ in
      let _hex_float_format_ = PC.caten _HexIntegerval_ _dot_hex_natural_ in
        PC.pack _hex_float_format_ (fun(n, (dot, n2)) -> Number(Float(float_of_string(n ^ "." ^ n2)))) ;;


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
  

let _greaterThanSpace_ = PC.range '!' '~';;

let _VisibleSimpleChar_ = 
  PC.pack _greaterThanSpace_ (fun (c)-> Char(c));;
  
let _Char_  = 
let chino = PC.caten _CharPrefix_  (PC.disj_list [_NamedChar_;  _HexChar_;_VisibleSimpleChar_;]) in
PC.pack chino (fun(x,c)->c);;


(*-------------------------------------- String ------------------------------------------- *)



let _StringHexChar_ =
  let _Hexdigits_ = PC.plus _HexDigit_ in
  let xhexa = PC.caten  _x_ _Hexdigits_ in
  let backxhexa = PC.caten _backslash_ xhexa in
  let nekuda = PC.caten backxhexa (PC.char ';') in
  PC.pack nekuda (fun((backslash, (x, digits)),_)->(char_of_int(int_of_string(list_to_string('0'::'x'::digits)))));;


(*let _backslash_ = (PC.char '\\');;*)
let _backslash_ = (PC.char '\\');;
let _merchaot_ = PC.char '\"';;

let meta1 = PC.pack (PC.word_ci "\\\"") (fun(_)-> '\"');;
let meta2 = PC.pack (PC.word_ci "\\t") (fun(_)-> '\t');;
let meta3 = PC.pack (PC.word_ci "\\f") (fun(_)-> '\012');;
let meta4 = PC.pack (PC.word_ci "\\n") (fun(_)-> '\n');;
let meta5 = PC.pack (PC.word_ci "\\r") (fun(_)-> '\r');;
let meta6 = PC.pack (PC.word_ci "\\\\") (fun(_)-> ('\\'));;

let first_disf = PC.disj meta5 meta6;;
let second_disf = PC.disj meta4 first_disf;;
let third_disf = PC.disj meta2 second_disf;;
let final = PC.disj meta1 third_disf;;

let _StringMetaChar_=  PC.disj_list[meta1;meta2;meta3; meta4; meta5; meta6;];;

let _StringLiteralChar_ = 
PC.guard (PC.range (char_of_int 32) (char_of_int 127)) (fun(literal)-> (literal!='\\' && literal!='\"'));;

let _StringChar_ = PC.disj_list [_StringMetaChar_ ;_StringHexChar_;_StringLiteralChar_;];;

let _String_ = 
let meta_merchaot1 =  PC.char '\"' in
let meta_star = PC.star _StringChar_  in
let kleeneString = PC.caten meta_merchaot1 (PC.caten meta_star meta_merchaot1) in
PC.pack kleeneString (fun(_, (s,_))-> String(list_to_string s));;
PC.test_string _String_ "\"\"";;

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
let _Symbol_ =
  let _SymbolChars_ = PC.plus _SymbolChar_ in
  PC.pack _SymbolChars_ (fun (chars) ->  Symbol(list_to_string chars));;

(*-------------------------Spaces and comments---------------------------*)
let _Space_ = PC.nt_whitespace;;
let _Spaces_ = PC.star _Space_ ;;
let _Comment_ = raise PC.X_not_yet_implemented;;
let _Skip_ = PC.disj _Spaces_ _Spaces_  ;;


let poteah = PC.char '(' ;;
let soger = PC.char ')' ;;
let _nil_ = 
let a = PC.caten poteah (PC.caten _Skip_ soger) in
PC.pack a (fun(s) -> Nil);;

let _atoms_ = PC.disj_list[_Boolean_;_Char_; _Number_; _String_; _Symbol_;];;
let rec _Sexp_ s = PC.disj_list[_atoms_;_compound_; ] s

and _compound_  s= 
let packed = PC.disj_list [_List_;_Vector_;_Quoted_;_QuasiQuoted_;_Unquoted_;] in
packed s

(*---------------------------- LIST --------------------------------------*)
and _List_ s =
let a = PC.caten poteah (PC.star _Sexp_) in
let sogerPoteahAndContent =  PC.caten a soger in
let packed =  PC.pack sogerPoteahAndContent (fun((x,lst_sexp),y)->List.fold_right (fun n1 n2 -> Pair(n1,n2)) lst_sexp Nil) in
packed s

(*---------------------------- Dotted LIST --------------------------------------*)
and _DottedList_ s=
let a = PC.caten (PC.caten poteah (PC.plus _Sexp_)) (PC.char '.') in
let b = PC.caten a _Sexp_ in
let sogerPoteahAndContent =  PC.caten b soger in
let packed =  PC.pack sogerPoteahAndContent (fun((((p,lst_sexp),nekuda),sexp),soger)->List.fold_right (fun n1 n2 -> Pair(n1,n2)) lst_sexp sexp) in
packed s


(*---------------------------- Vector --------------------------------------*)

and _Vector_ s = 
let sulPoteah = PC.caten (PC.char '#') poteah in
let a = PC.caten sulPoteah (PC.star _Sexp_) in
let sogerPoteahAndContent =  PC.caten a soger in
let packed =  PC.pack sogerPoteahAndContent (fun(((sulamit,p),lst_sexp),y)-> Vector(lst_sexp)) in
packed s


(*---------------------------- Quoted --------------------------------------*)

and _Quoted_ s= 
let prefix = (PC.caten (PC.char '\'') _Sexp_) in
let packed = PC.pack  prefix (fun(x,s)->Pair(Symbol("quote"), Pair(s, Nil))) in
packed s

(*---------------------------- QuasiQuoted --------------------------------------*)
and _QuasiQuoted_ s=
let prefix =  (PC.caten (PC.char '`') _Sexp_ ) in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("quasiquote"), Pair(s, Nil))) in
packed s
(*---------------------------- Unquoted --------------------------------------*)

and _Unquoted_ s= 
let prefix = PC.caten (PC.char ',')  _Sexp_  in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("unquote"), Pair(s, Nil))) in
packed s

(*---------------------------- ⟨UnquoteAndSpliced⟩ --------------------------------------*)
and _UnquoteAndSpliced_ s =
let prefix = PC.caten (PC.word ",@")  _Sexp_  in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("unquote-splicing"), Pair(s, Nil))) in
packed s ;;

(*--------------------------- Sceintific Notation ---------------------------------------*)





end;; (* struct Reader *)
