# use "tag-parser.ml";;

tag_parser (Bool true);;
tag_parser (Number (Int 5));;
tag_parser (Number (Float 5.3));;
tag_parser (Nil);;
tag_parser (Char 'a');;
tag_parser (String "this is a string");;
tag_parser (Symbol "let");;
tag_parser (Symbol "x");;
tag_parser (Symbol "x");;
tag_parser (Pair(Symbol "quote", Pair(Bool true, Nil)) );;
tag_parser ( Pair(Symbol("if"), Pair(Bool true, Pair(Char 'a', Pair(Char 'b', Nil)))) );;
tag_parser (Pair(Symbol "if", Pair(Bool true, Pair(Number (Int 5), Nil))) );;
tag_parser (Pair(Symbol "begin", Nil));;

tag_parser  (Pair(Symbol "begin", Pair(Number (Int 5), Pair(Number (Int 1), Pair(Number (Int 2), Nil)))) );;
tag_parser  (Pair(Symbol "begin", Pair(Number (Int 5), Nil)) );;
tag_parser  (Pair(Symbol "begin", Nil) );;
tag_parser  (Pair(Symbol "begin", Pair(Symbol"a", Nil)));;

tag_parser   (Pair(Symbol "set!", Pair(Symbol "x", Pair(Number (Int 7), Nil))) );;
tag_parser   (Pair(Symbol "define", Pair(Symbol "x", Pair(Number (Int 5), Nil))) );;
tag_parser (Pair(Symbol "define", Pair(Pair(Symbol "square", Nil), Pair(Pair(Symbol "*", Pair(Symbol "x", Pair(Symbol "x", Nil))), Nil))));;
tag_parser (Pair(Symbol "+", Pair(Number (Int 1), Pair(Number (Int 2), Nil))));;
 

tag_parser (Pair(Symbol "lambda", Pair(
  Pair(Symbol "x", Pair(Symbol "y", Pair(Symbol "z", Nil))),
  Pair(Number (Int 1), Pair(Number (Int 2), Pair(Number (Int 3), Nil))))) );;

  tag_parser (  Pair(Symbol "lambda", Pair(
    Pair(Symbol "x", Pair(Symbol "x", Pair(Symbol "z", Nil))), Pair(Number (Int 5), Nil))) );;

    tag_parser (    Pair(Symbol "lambda", Pair(Nil, Pair(Number (Int 5), Nil))) );;


tag_parser (Pair(Symbol "lambda", Pair(Pair(Symbol "x", Pair(Symbol "y", Symbol "z")), Pair(Symbol "x", Nil))));;
tag_parser (Pair(Symbol "lambda", Pair(Symbol "x", Pair(Pair(Symbol "+", Pair(Symbol "x", Pair(Symbol "x", Nil))), Nil))));;
tag_parser  (Pair(Symbol "lambda", Pair(Pair(Symbol "x", Pair(Symbol "y", Symbol "z")), Pair(Pair(Symbol "+", Pair(Symbol "x", Pair(Symbol "y", Nil))), Pair(Number (Int 2), Pair(Number (Int 3), Pair(Number (Int 5), Nil)))))));;
tag_parser  (Pair(Symbol "lambda", Pair(Symbol "x", Pair(Pair(Symbol "+", Pair(Symbol "x", Pair(Symbol "x", Nil))), Pair(Number (Int 2), Nil)))));;

)lambda x (=xx )

tag_parser   (Pair(Symbol "or", Nil) );;
tag_parser  ( Pair(Symbol "or", Pair(Number (Int 1), Pair(Number (Int 2), Pair(Number (Int 3), Nil)))) );;












