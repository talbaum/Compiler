(* testing-pc.ml
 * Code for TDD for the parser
 *
 * Programmer: Mayer Goldberg, 2018
 *)

(* USAGE: Look at how I defined the tester() function as a list of tests:
 *        Each test returns (), so there are no problems with the types
 * even though each parser may return objects of different types. Notice
 * that test_nt is called with a documentation string, a parser, an input-
 * string, and an object, which may be of any type, which is the object
 * you expect to get from the parser.
 *
 * If all runs as expected, i.e., the value found matches, and all the
 * chars are consumed, then NOTHING is printed. If the value found matches,
 * but some chars remain unconsumed, then a message is printed. If the
 * value does not match, or if the parser fails, appropriate messages are
 * printed. You need the doc_string to identify the test, so that you can
 * run it manually on your own. Your goal should be to supply lots of tests
 * with input strings that are consumed ENTIRELY so that no chars remain.
 *
 * To decide what the return value should be, run the test manually, and
 * check to make sure that the value makes sense. once you add it to the
 * tester, you can verify that the test will always pass, simply by
 * running tester();;
 *)
#use "pc.ml";;
open PC ;;
(* ================================ INSERT CODE HERE ==================== *)









(* ================================ INSERT CODE HERE ==================== *)

(* USAGE: change the value of the parsers below,
 to the names of your parsers.
 These parsers are according to the CFG, with the addition of line and sexpr comments  *)
let nt_not_implemented = nt_none;;

let ____Bool = nt_not_implemented ;;
let ____Number = nt_not_implemented ;;
let ____Char = nt_not_implemented;;
let ____String = nt_not_implemented ;;
let ____Symbol = nt_not_implemented ;;
let ____List = nt_not_implemented ;;
let ____Dotted_List = nt_not_implemented ;;
let ____Vector = nt_not_implemented ;;
let ____Qouted = nt_not_implemented ;;
let ____QuasiQuoted = nt_not_implemented ;;
let ____Unquoted = nt_not_implemented ;;
let ____UnquoteAndSpliced = nt_not_implemented ;;
let ____Sexpr = nt_not_implemented ;;



let test_nt doc_string nt input_string expected_value =
  try
    let (result, remaining_chars) = (nt (string_to_list input_string)) in
    if (result = expected_value)
    then if remaining_chars <> []
	 then Printf.printf
		"!!! test %s gave correct value, with remaining chars -->[%s]\n"
		doc_string
		(list_to_string remaining_chars)
	 else ()
    else Printf.printf "!!! test %s gave an incorrect value\n" doc_string
  with X_not_yet_implemented ->
    Printf.printf "!!! test %s failed\n" doc_string;;

let rec run_tests tests =
  match tests with
  |[] -> ()
  | test :: tests ->
     (test(); run_tests tests);;

let tester () =
  run_tests
    [(fun () -> test_nt "boolean test 1" ____Bool "#t" (Bool(true))) ;
    (fun () -> test_nt "boolean test 2" ____Bool "#T" (Bool(true))) ;
    (fun () -> test_nt "boolean test 3" ____Bool "#f" (Bool(false))) ;
    (fun () -> test_nt "boolean test 4" ____Bool "#F" (Bool(false))) ;
    (fun () -> test_nt "number test 1" ____Number "1" (Number(Int(1)))) ;
    (fun () -> test_nt "number test 2" ____Number "01290" (Number(Int(1290))));
    (fun () -> test_nt "number test 3" ____Number "-10" (Number(Int(-10))));
    (fun () -> test_nt "number test 4" ____Number "-03" (Number(Int(-3))));
    (fun () -> test_nt "number test 5" ____Number "-0" (Number(Int(0))));
    (fun () -> test_nt "number test 6" ____Number "+8" (Number(Int(8))));
    (fun () -> test_nt "number test 7" ____Number "#x16" (Number(Int(22))));
    (fun () -> test_nt "number test 8" ____Number "#xabfd" (Number(Int(44029))));
    (fun () -> test_nt "number test 10" ____Number "#x-1a" (Number(Int(-26))));
    (fun () -> test_nt "number test 11" ____Number "#x+1a" (Number(Int(26))));
    (fun () -> test_nt "number test 12" ____Number "1.0" (Number(Float(1.0))));
    (fun () -> test_nt "number test 13" ____Number  "0005.0129" (Number(Float(5.0129)))) ;
    (fun () -> test_nt "number test 14" ____Number  "501.100000000000000000000" (Number(Float(501.1)))) ;
    (fun () -> test_nt "number test 16" ____Number  "-0.0" (Number(Float(0.0)))) ;
    (fun () -> test_nt "number test 17" ____Number  "+999.12349999999" (Number(Float(999.12349999999)))) ;
    (fun () -> test_nt "number test 18" ____Number  "-102.000000000000001" (Number(Float(-102.)))) ;
    (fun () -> test_nt "number test 19" ____Number  "#x1.ab" (Number(Float(1.66796875)))) ;
    (fun () -> test_nt "number test 20" ____Number  "#x+a.0" (Number(Float(10.0)))) ;
    (fun () -> test_nt "number test 21" ____Number  "#x-1.ab000000000" (Number(Float(-1.66796875)))) ;
    (fun () -> test_nt "char test 1" ____Char "#\\a" (Char('a'))) ;
    (fun () -> test_nt "char test 2" ____Char "#\\A" (Char('A'))) ;
    (fun () -> test_nt "char test 3" ____Char "#\\?" (Char('?'))) ;
    (fun () -> test_nt "char test 4" ____Char "#\\~" (Char('~'))) ;
    (fun () -> test_nt "char test 5" ____Char "#\\x30" (Char('0'))) ;
    (fun () -> test_nt "char test 6" ____Char "#\\xa" (Char('\n'))) ;
    (fun () -> test_nt "char test 7" ____Char "#\\tab" (Char('\t'))) ;
    (fun () -> test_nt "char test 8" ____Char "#\\space" (Char(' '))) ;
    (fun () -> test_nt "char test 9" ____Char "#\\newline" (Char('\n'))) ;
    (fun () -> test_nt "char test 10" ____Char "#\\\\" (Char('\\'))) ;
    (fun () -> test_nt "string test 1" ____String "\"Hello\"" (String("Hello"))) ;
    (fun () -> test_nt "string test 3" ____String "\"Hello World!\"" (String("Hello World!"))) ;
    (fun () -> test_nt "string test 4" ____String "\"Hello\\n World!\"" (String("Hello\n World!"))) ;
    (fun () -> test_nt "string test 5" ____String "\"\\t\"" (String("\t"))) ;
    (fun () -> test_nt "string test 6" ____String "\"\\\\\"" (String("\\"))) ;
    (fun () -> test_nt "string test 7" ____String "\"\"" (String(""))) ;
    (fun () -> test_nt "string test 1" ____Symbol "wfkjwf" (Symbol("wfkjwf"))) ;
    (fun () -> test_nt "string test 2" ____Symbol "23148!" (Symbol("23148!"))) ;
    (fun () -> test_nt "string test 3" ____Symbol "x1" (Symbol("x1"))) ;
    (fun () -> test_nt "string test 4" ____Symbol "lambda" (Symbol "lambda" )) ;
    (fun () -> test_nt "string test 5" ____Symbol "define" (Symbol("define"))) 
    ];;
tester ();;