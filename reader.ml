
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


#use "pc.ml";;
let _tParser_ = (PC.char 't');;

let _fParser_= (PC.char 'f');;

let _trueParser_ =
  let _sulamit_ =  (PC.char '#') in
  let _truep_ = PC.caten _sulamit_ _tParser_ in
  PC.pack _truep_ (fun(s,t) -> Bool(true));;

let _falseParser_ =
  let _sulamit_ =  (PC.char '#') in
  let _falsep_ = PC.caten _sulamit_ _fParser_ in
  PC.pack _falsep_ (fun(s,f) -> Bool(false));;

let _booleanParser_ = PC.disj _trueParser_ _falseParser_;;

PC.test_string _booleanParser_ "#t";;

let _Sexpr_ = PC.disj
                    
(* ------------------------------------------------------------------ *)

#use "pc.ml";;
let _digit_ = PC.range '0' '9' ;;
let _dot_ = PC.char '.';;

let _integerParser_ =
  let _digits_ = PC.plus _digit_ in
  PC.pack _digits_ (fun (ds) -> Number (Int((int_of_string (list_to_string ds)))));;

let _floatParser_=
  let _digits_ = PC.plus _digit_ in
  PC.pack _digits_ _dot_ _digits_ (fun (ds dot ds2) -> float_of_string ((list_to_string ds) ^ "." ^(list_to_string ds2))));;

let _numberParser_ = PC.disj_list [_floatParser_ ; _integerParser_;];;
    
end;; (* struct Reader *)
