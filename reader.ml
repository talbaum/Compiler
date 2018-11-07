
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

let _Digit_ = PC.range '0' '9' ;;
let _Natural_ = 
  let _Digits_ = PC.plus _Digit_ in
  PC.pack _Digits_ (fun (digits) -> Int (int_of_string(list_to_string digits)))

let _Sign_ = (PC.caten (PC.maybe (PC.one_of("+-")))_Natural_)

let _Integer_ = 
      PC.pack _Sign_ (fun (sign, number) -> match sign, number with
    |Some '+' , Int(number)->  Int(number)
    |Some '-',  Int(number) ->  Int(number*(-1))
    |None , Int (number) ->  Int(number)
    | _ -> raise PC.X_no_match);;
PC.test_string _Integer_ "-21";;

let _Float_=
  let _dot_ = PC.char '.' in
    let _dot_natural_ = PC.caten _dot_ _Natural_ in
      let _float_format_ = PC.caten _Integer_ _dot_natural_ in
        PC.pack _float_format_ (fun(n, (dot, n2)) -> match n , n2 with
       |Int(n),Int(n2) -> Float(float_of_string(string_of_int(n) ^ "." ^ string_of_int(n2)))
       | _ -> raise PC.X_no_match);;

let _str_natural_ = PC.pack _Natural_ (fun(ds) -> match ds with
    |Int(ds) -> (string_of_int(ds))
    | _ -> raise PC.X_no_match);;
let _dot_natural_ = PC.pack _str_natural_ (fun(str)-> ("." ^ str));;
let _int_as_str_ = PC.pack _Integer_ (fun (num) -> match num with
    |Int(num) -> (string_of_int(num))
    | _ -> raise PC.X_no_match);;
  
  let _Float2_=
      let _float_format_ = PC.caten _int_as_str_ _dot_natural_ in
        PC.pack _float_format_ (fun(s1,s2) -> Float(float_of_string(s1 ^ s2)));;

PC.trace_pc "Test" _Float_ ['1'; '.'; '0'];;
PC.trace_pc "Test" _Float_  (string_to_list("0005.0129")) ;;

PC.test_string _Float2_ "-1.123";; 
PC.test_string _Float2_ "1.0" ;; (* miss .0 after the 1 *)
PC.test_string _Float2_ "0005.0129" ;; (* miss 0 after the dot *)
PC.test_string _Float2_ "501.100000000000000000000" ;; (* exception int of string *)
PC.test_string _Float2_ "-0.0" ;; (* miss .0 after the 1 *)
PC.test_string _Float2_ "-102.000000000000001" ;;(* shold be -102. instead of -102.1 *)

let _HexPrefix_ = 
let _sulamit_ = PC.char '#' in
let _x_ = PC.char 'x' in
PC.caten _sulamit_ _x_;;
(*
let _HexDigit_ = PC.X_not_yet_implemented;;
let _HexNatural_ = PC.plus _HexDigit_;;
let _HexInteger_ = 
let _hex_prefix_and_sign_ = PC.caten _HexPrefix_ _Sign_ in


let _HexFloat_ = 
let _dot_ = PC.char '.' in
    let _dot_hex_natural_ = PC.caten _dot_ _HexNatural_ in
      let _hex_float_format_ = PC.caten _HexInteger_ _dot_hex_natural_ in
        PC.pack _hex_float_format_ (fun(n, (dot, n2)) -> match n , n2 with
       |Int(n),Int(n2) -> Float(float_of_string(string_of_int(n) ^ "." ^ string_of_int(n2)))
       | _ -> raise PC.X_no_match);;
   

 let _Number_ = PC.disj_list [_Float_; _Integer_; _HexFloat_; _HexInteger_;] ;;  
     *) 
     let _Number_ = PC.disj_list [_Float_; _Integer_;] ;;


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

let _merchaot_ = PC.char '"';;

let _StringHexChar_ =
  let _Hexdigits_ = PC.plus _HexDigit_ in
  let xhexa = PC.caten  _x_ _Hexdigits_ in
  let backxhexa = PC.caten _backslash_ xhexa in
  PC.pack backxhexa (fun(backslash, (x, digits))->String(s));;

let _StringMetaChar_=  raise X_not_yet_implemented;;
let _StringLiteralChar_ = raise X_not_yet_implemented;;
let _StringChar_ = PC.disj_list [_StringLiteralChar_ ; _StringMetaChar_ ; _StringHexChar_;];;

let _String_ = 
let kleeneString = PC.kleeneString _StringChar_ in
let startmerchaot = PC.caten _merchaot_ kleeneString in
let EndMerchaot = PC.caten startmerchaot _merchaot_ in
PC.pack EndMerchaot (fun(s)-> String(s));;

end;; (* struct Reader *)
