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
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) ->
  if List.length l1 = List.length l2 then
   List.for_all2 sexpr_eq l1 l2 else
   false
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (Char.lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;



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


(* ----------------------------- number ----------------------------- *)

let _Digit_ = PC.range '0' '9' ;;
let _Natural_ =
  let _Digits_ = PC.plus _Digit_ in
  PC.pack _Digits_ (fun (digits) -> Int (int_of_string(list_to_string digits)));;

let _Natural_val_ =
  let _Digits_ = PC.plus _Digit_ in
  PC.pack _Digits_ (fun (digits) ->  (list_to_string digits));;

let _Sign_ = (PC.caten (PC.maybe (PC.one_of("+-")))_Natural_val_);;


let _Integer_val_ =
      PC.pack _Sign_ (fun (sign, number) -> match sign with
    |Some '+' ->  number
    |Some '-' ->  "-" ^ number
    |_ -> number);;

let _Integer_ =
      PC.pack _Integer_val_ (fun ( number) -> Number(Int(int_of_string number)));;



let _Float_=
  let _dot_ = PC.char '.' in
    let _dot_natural_ = PC.caten _dot_ _Natural_val_ in
      let _float_format_ = PC.caten _Integer_val_ _dot_natural_ in
        PC.pack _float_format_ (fun(n, (dot, n2)) ->  Number(Float(float_of_string(n ^ "." ^ n2))));;

let _Float_val_=
  let _dot_ = PC.char '.' in
    let _dot_natural_ = PC.caten _dot_ _Natural_val_ in
      let _float_format_ = PC.caten _Integer_val_ _dot_natural_ in
        PC.pack _float_format_ (fun(n, (dot, n2)) -> float_of_string( n ^ "." ^ n2));;



let _HexPrefix_ =
  let _sulamit_ = PC.char '#' in
  let _x_ = PC.char_ci 'x' in
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


(*--------------------------- Sceintific Notation ---------------------------------------*)


let _e_ = PC.char_ci 'e' ;;
let _prefix_and_e_ = PC.caten _Integer_val_ _e_;;
let _sceintific_format_int_ = PC.caten _prefix_and_e_ _Integer_val_;;
let _sceintific_notation_int_ =
PC.pack _sceintific_format_int_ (fun ((before,e),after)-> Number(Float((float_of_string ( before)) *. (10.0 **  float_of_string ( (after))))));;

let _Fprefix_and_e_ = PC.caten _Float_val_ _e_;;
let _sceintific_format_float_ = PC.caten _Fprefix_and_e_ _Integer_val_;;
let _sceintific_notation_float_ =
PC.pack _sceintific_format_float_ (fun ((before,e),after)-> Number(Float(before *. (10.0 **   float_of_string ( (after))))));;

let _sceintific_ = PC.disj _sceintific_notation_float_ _sceintific_notation_int_;;

let _only_number_ = PC.disj_list [_sceintific_;_HexFloat_;_Float_;_HexInteger_; _Integer_; ];;
let _Number_ =
PC.not_followed_by _only_number_ _SymbolChar_;;
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

let _Char_  =
let prefixAndChar = PC.caten _CharPrefix_  (PC.disj_list [_NamedChar_;  _HexChar_;_VisibleSimpleChar_;]) in
PC.pack prefixAndChar (fun(x,c)->c);;



(*-------------------------------------- String ------------------------------------------- *)


let _StringHexChar_ =
  let _Hexdigits_ = PC.plus _HexDigit_ in
  let xhexa = PC.caten  _x_ _Hexdigits_ in
  let backxhexa = PC.caten _backslash_ xhexa in
  let nekuda = PC.caten backxhexa (PC.char ';') in
  PC.pack nekuda (fun((backslash, (x, digits)),nekudapsik)->(char_of_int(int_of_string(list_to_string('0'::'x'::digits)))));;


let _backslash_ = (PC.char '\\');;
let _merchaot_ = PC.char '\"';;
let input_merchaot = (PC.word_ci "\\\"");;
let input_t =  (PC.word_ci "\\t");;
let input_f = (PC.word_ci "\\f");;
let input_n =  (PC.word_ci "\\n");;
let input_r = (PC.word_ci "\\r");;
let input_slash = (PC.word_ci "\\\\") ;;

let meta1 = PC.pack  input_merchaot(fun(x)-> '\"');;
let meta2 = PC.pack input_t (fun(x)-> '\t');;
let meta3 = PC.pack input_f (fun(x)-> '\012');;
let meta4 = PC.pack input_n (fun(x)-> '\n');;
let meta5 = PC.pack  input_r(fun(x)-> '\r');;
let meta6 = PC.pack input_slash (fun(x)-> ('\\'));;

let first_disf = PC.disj meta5 meta6;;
let second_disf = PC.disj meta4 first_disf;;
let third_disf = PC.disj meta2 second_disf;;
let final = PC.disj meta1 third_disf;;

let _StringMetaChar_=  PC.disj_list[meta1;meta2;meta3; meta4; meta5; meta6;];;

let _StringLiteralChar_ =
let chars =  (PC.range (char_of_int 32) (char_of_int 127)) in
PC.guard chars (fun(literal)-> ( literal!='\"') && literal!='\\');;

let _StringChar_ = PC.disj_list [_StringMetaChar_ ;_StringHexChar_;_StringLiteralChar_;];;

let _String_ =
let kleeneString = PC.caten _merchaot_ (PC.caten (PC.star _StringChar_) _merchaot_) in
PC.pack kleeneString (fun(x, (s,y))-> String(list_to_string s));;



(*--------------------------------- 3 Dots ----------------------------------------*)

let nt_close_all = PC.word "...";;
let nt_open = PC.char '(';;
let nt_close = PC.char ')';;

(*-------------------------------- recursive --------------------------------------*)
let sexp_comment_prefix = PC.word  "#;";;
let _psikuda_ = PC.char ';';;
let poteah = PC.char '(' ;;
let soger = PC.word ")" ;;
let squarePoteah = PC.char '[' ;;
let squareSoger = PC.word "]" ;;


let _atoms_ = PC.disj_list[ _Boolean_;_Char_; _Number_ ; _String_; _Symbol_;];;

let rec _Sexp_ s =
let spaces_before_and_sexp= (PC.caten _comments_and_spaces_ (PC.disj _atoms_ _compound_ )) in
let sexp_and_spaces_after = PC.caten spaces_before_and_sexp _comments_and_spaces_ in
(PC.pack sexp_and_spaces_after (fun((first_spaces, sexp),last_spaces)->sexp)) s

and _nested_Sexp_ s =
let spaces_before_and_sexp= (PC.caten _comments_and_spaces_ (PC.disj _atoms_ _nested_compound_ )) in
let sexp_and_spaces_after = PC.caten spaces_before_and_sexp _comments_and_spaces_ in
(PC.pack sexp_and_spaces_after (fun((first_spaces, sexp),last_spaces)->sexp)) s

and _compound_  s=
let packed =  (PC.disj_list [_List_;_Vector_;_DottedList_;_Quoted_;_QuasiQuoted_;_Unquoted_;_UnquoteAndSpliced_;] )in
packed s

and _nested_compound_  s=
let packed = PC.disj_list [_nested_DottedList_;_nested_List_;_nested_Vector_;_nested_Quoted_;_nested_QuasiQuoted_;_nested_Unquoted_;_nested_UnquoteAndSpliced_;] in
packed s

(*---------------------------- SEXPER COMMENT --------------------------------------*)

and _Sexpr_Comment_ s  =
let _Scomment_format_= PC.caten  sexp_comment_prefix _Sexp_ in
let packed =PC.pack _Scomment_format_ (fun(x,y)->Nil) in
packed s


and _line_comment_ s=
let _end_of_file = PC.pack PC.nt_end_of_input (fun _ -> '\n') in
let _end_of_comment_ = PC.disj (PC.char '\n') _end_of_file   in
let _no_newline_ =(PC.range (char_of_int 32) (char_of_int 127)) in
let _comment_char_data_ = PC.diff PC.nt_any _end_of_comment_ in
let _comment_full_data_ = PC.star _comment_char_data_ in
let _comment_start_and_data_ = PC.caten _psikuda_ _comment_full_data_ in
let _line_Comment1_ =  PC.pack (PC.caten _comment_start_and_data_ _end_of_comment_) (fun ((x,y),z)->Nil)  in
_line_Comment1_ s


and _comments_and_spaces_ s=
let _Space_ =  PC.pack (PC.nt_whitespace) (fun(x)->Nil) in
let _Comment_ = PC.disj   _line_comment_ _Sexpr_Comment_ in
let _Skip_ =  (PC.star (PC.disj _Comment_ _Space_ )) in
_Skip_ s

and _nil_ s =
let _poteach_space_ = PC.caten poteah _comments_and_spaces_ in
let _nil_spaces_format_ = PC.caten  _poteach_space_ soger in
let packed = PC. pack _nil_spaces_format_ (fun(x) -> Nil)
in packed s

(*---------------------------- LIST --------------------------------------*)

and _List_ s =
let a = PC.caten (PC.caten poteah (PC.caten _comments_and_spaces_((PC.star _Sexp_)))) soger in
let b =  PC.caten (PC.caten squarePoteah (PC.caten _comments_and_spaces_((PC.star _Sexp_)))) squareSoger in
let aORb = PC.disj a b in
let c = PC.caten (PC.caten poteah (PC.caten _comments_and_spaces_(PC.star _nested_Sexp_))) (PC.word "...") in
let d =  PC.caten (PC.caten squarePoteah (PC.caten _comments_and_spaces_((PC.star _nested_Sexp_)))) (PC.word "...") in
let cORd = PC.disj c d in
let final = PC.disj aORb cORd  in
let non_empty_list =  PC.pack final (fun((p,(sp,sexp)),y)->List.fold_right (fun head tail -> Pair(head,tail))  sexp Nil) in
let packed = PC.disj  non_empty_list _nil_ in
packed s

and _nested_List_ s =
let a = PC.caten (PC.caten poteah (PC.star _nested_Sexp_)) (PC.maybe soger) in
let b =  PC.caten (PC.caten squarePoteah (PC.star _nested_Sexp_))(PC.maybe squareSoger)  in
let aORb = PC.disj a b in
let packed =  PC.pack aORb (fun((x,lst_sexp),y)->List.fold_right (fun n1 n2 -> Pair(n1,n2))  lst_sexp Nil) in
packed s
(*---------------------------- Dotted LIST --------------------------------------*)
and _DottedList_ s=
let a = PC.caten (PC.caten poteah (PC.plus _Sexp_)) (PC.char '.') in
let sogerPoteahAndContent = PC.caten (PC.caten a _Sexp_) soger in
let square_a = PC.caten (PC.caten squarePoteah (PC.plus _Sexp_)) (PC.char '.') in
let sogerPoteahAndContent1 = PC.caten(PC.caten square_a _Sexp_) squareSoger in
let squareOrNot = PC.disj sogerPoteahAndContent sogerPoteahAndContent1 in
let dots1 = PC.caten (PC.caten poteah (PC.plus _nested_Sexp_)) (PC.char '.') in
let dots2 = PC.caten (PC.caten dots1 _nested_Sexp_) (PC.word "...") in
let dots3 = PC.caten (PC.caten squarePoteah (PC.plus _nested_Sexp_)) (PC.char '.') in
let dots4 = PC.caten (PC.caten dots3 _nested_Sexp_)  (PC.word "...") in
let dotsSquareOrNot = PC.disj dots2 dots4 in
let chino = (PC.disj  squareOrNot dotsSquareOrNot) in
let packed =  PC.pack chino (fun((((p,sexp1),nekuda),sexp2),soger)->List.fold_right (fun head tail -> Pair(head,tail)) sexp1 sexp2) in
packed s

and _nested_DottedList_ s =
let a = PC.caten (PC.caten poteah (PC.plus _nested_Sexp_)) (PC.char '.') in
let sogerPoteahAndContent = PC.caten (PC.caten a _nested_Sexp_) (PC.maybe soger) in
let square_a = PC.caten (PC.caten squarePoteah (PC.plus _nested_Sexp_)) (PC.char '.') in
let sogerPoteahAndContent1 =PC.caten( PC.caten square_a _nested_Sexp_) (PC.maybe squareSoger) in
let squareOrNot = PC.disj sogerPoteahAndContent sogerPoteahAndContent1 in
let packed =  PC.pack squareOrNot (fun((((p,sexp1),nekuda),sexp2),soger)->List.fold_right (fun head tail -> Pair(head,tail)) sexp1 sexp2) in
packed s


(*---------------------------- Vector --------------------------------------*)
and _Vector_ s =
let sulPoteah = PC.caten (PC.char '#') poteah in
let sogerPoteahAndContent = PC.caten(PC.caten sulPoteah (PC.star _Sexp_)) soger in
let sogerPoteahAndContent1 = PC.caten(PC.caten sulPoteah (PC.star _nested_Sexp_)) (PC.word "...") in
let a = PC.disj sogerPoteahAndContent sogerPoteahAndContent1 in
let packed =  PC.pack a (fun(((sulamit,p),lst_sexp),y)-> Vector(lst_sexp)) in
packed s

and _nested_Vector_ s =
let sulPoteah = PC.caten (PC.char '#') poteah in
let a = PC.caten sulPoteah (PC.star _nested_Sexp_) in
let sogerPoteahAndContent =  PC.caten a (PC.maybe soger) in
let packed =  PC.pack sogerPoteahAndContent (fun(((sulamit,p),lst_sexp),y)-> Vector(lst_sexp)) in
packed s


(*---------------------------- Quoted --------------------------------------*)

and _Quoted_ s=
let prefix = (PC.caten (PC.char '\'') _Sexp_) in
let packed = PC.pack  prefix (fun(x,s)->Pair(Symbol("quote"), Pair(s, Nil))) in
packed s

and _nested_Quoted_ s=
let prefix = (PC.caten (PC.char '\'') _nested_Sexp_) in
let packed = PC.pack  prefix (fun(x,s)->Pair(Symbol("quote"), Pair(s, Nil))) in
packed s
(*---------------------------- QuasiQuoted --------------------------------------*)
and _QuasiQuoted_ s=
let prefix =  (PC.caten (PC.char '`') _Sexp_ ) in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("quasiquote"), Pair(s, Nil))) in
packed s

and _nested_QuasiQuoted_ s=
let prefix =  (PC.caten (PC.char '`') _nested_Sexp_ ) in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("quasiquote"), Pair(s, Nil))) in
packed s

(*---------------------------- Unquoted --------------------------------------*)

and _Unquoted_ s=
let prefix = PC.caten (PC.char ',')  _Sexp_  in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("unquote"), Pair(s, Nil))) in
packed s

and _nested_Unquoted_ s=
let prefix = PC.caten (PC.char ',')  _nested_Sexp_  in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("unquote"), Pair(s, Nil))) in
packed s
(*---------------------------- ⟨UnquoteAndSpliced⟩ --------------------------------------*)
and _UnquoteAndSpliced_ s =
let prefix = PC.caten (PC.word ",@")  _Sexp_  in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("unquote-splicing"), Pair(s, Nil))) in
packed s

and _nested_UnquoteAndSpliced_ s =
let prefix = PC.caten (PC.word ",@")  _nested_Sexp_  in
let packed = PC.pack prefix (fun(x,s)->Pair(Symbol("unquote-splicing"), Pair(s, Nil))) in
packed s ;;

(*------------ spaces comments---------------------*)


let read_sexpr string =
let (a,b)=_Sexp_ (string_to_list (string)) in
a;;

let read_sexprs string =
let (a,b)=(PC.star _Sexp_) (string_to_list (string)) in
a;;



end;; (* struct Reader *)


