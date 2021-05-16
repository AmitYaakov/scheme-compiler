
#use "pc.ml";;
open PC ;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;


let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

(***********************<WhiteSpaces><Line Comments> <Sexpr Comments>***********************)

let parse_whitespaces = pack nt_whitespace (fun spaces -> []);;

let parse_line_comments =
  let new_line_list = pack (char '\n') (fun newline -> [newline]) in
  let prefix = char ';' in
  let end_of_line_comment = disj new_line_list nt_end_of_input in
  let char_not_eolc =  diff nt_any end_of_line_comment in
  let body_comment = star char_not_eolc in
      pack (caten (caten prefix body_comment ) end_of_line_comment) (fun comment -> [])


(*********************** <End Of <WhiteSpaces> <Line Comments> <Sexpr Comments> ***********************)

let hash_tag = char '#' ;;
let dot =  char '.' ;;

let exclamation = char '!' ;;
let dollar = char '$' ;;
let expo = char '^' ;;
let asterisk = char '*' ;;
let under_line = char '_' ;;
let equals = char '=' ;;
let less_than = char '<' ;;
let greater_than = char '>' ;;
let question_mark = char '?' ;;
let slash = char '/' ;;
let colon = char ':' ;;

let lower_case_letters = range 'a' 'z' ;;
let upper_case_letters = range 'A' 'Z' ;;
let upper_to_lower = pack upper_case_letters (fun letter -> Char.lowercase_ascii letter)

let digit = range '0' '9' ;;
let nt_plus = char '+' ;;
let nt_minus = char '-' ;;
let symbol_char_no_dot = (disj_list [digit; lower_case_letters; upper_to_lower; exclamation; dollar; expo; asterisk; nt_minus; under_line; equals; nt_plus; less_than;greater_than; question_mark;slash; colon;]) ;;
let symbol_char = disj symbol_char_no_dot dot ;;


(*********************** <Boolean> ***********************)

let parse_boolean =
  let f_char =  (char_ci 'f') in
  let t_char = (char_ci 't') in
  let nt_false = caten hash_tag f_char in
  let nt_true = caten hash_tag t_char in
  pack ((disj nt_false nt_true)) (fun bool_exp -> match bool_exp with
  | '#' , 't' | '#' , 'T' -> Bool(true)
  | '#' , 'f' | '#' , 'F' -> Bool(false)
  | _ -> raise X_no_match) ;;
  
(*********************** End of <Boolean> ***********************)


(*********************** <Char> ***********************)

let char_prefix =  (word "#\\");;

let named_char_nul = pack (word_ci "nul") (fun word -> char_of_int 0) ;;
let named_char_new_line = pack (word_ci "newline") (fun word -> char_of_int 10) ;;
let named_char_return = pack (word_ci "return") (fun word -> char_of_int 13) ;;
let named_char_tab =  pack (word_ci "tab") (fun word -> '\t') ;;
let named_char_page = pack (word_ci "page") (fun word -> (char_of_int 12)) ;;
let named_char_space = pack (word_ci "space") (fun word -> (char_of_int 32)) ;;

let parse_named_char = disj_list [named_char_nul; named_char_new_line; named_char_return; named_char_tab;named_char_page; named_char_space;];;

let parse_visible_simple_char = pack (diff nt_any nt_whitespace) (fun simple_char -> simple_char);;
let char_postfix = disj parse_named_char parse_visible_simple_char;;
let parse_char = pack (caten char_prefix char_postfix) (fun (pre, post) -> Char(post));;

(*********************** End of <Char> ***********************)

(*********************** <Number> ***********************)
let slash = char '/' ;;
let nt_plus = char '+' ;;
let nt_minus = char '-';;
let digit = (range '0' '9') ;;
let natural = plus digit ;;


let list_to_natural_number lst =
  List.fold_left (fun acc list_element ->
  let number_value = int_of_char list_element - int_of_char '0' in
  10 * acc + number_value) 0 lst ;;

let list_to_after_dot lst =
  List.fold_right (fun list_element acc ->
  let number_value = (float_of_int (int_of_char list_element)) -. (float_of_int (int_of_char '0')) in
  (acc +. number_value) /. 10. ) lst 0.0 ;;

let sign  = pack (maybe (disj nt_plus nt_minus)) (fun (sign) -> match sign with
  | Some('-') -> -1
  | _ -> +1);;


let parse_integer = pack (caten sign natural)
  (fun (sign , num) ->
    let final_num = sign * (list_to_natural_number num) in
      Number(Fraction(final_num, 1)));;


let parse_fraction = pack (caten sign (caten (caten natural slash) natural))
                    (fun (sign,((nominator, slash) , denominator )) ->
  let final_num_nominator = list_to_natural_number nominator in
  let final_num_denominator = list_to_natural_number denominator in
  let rec gcd nominator denominator =
    if denominator = 0 then nominator else gcd denominator (nominator mod denominator) in
  let gcd_calc = gcd final_num_nominator final_num_denominator in
  match gcd_calc with
  | 1 -> Number(Fraction(sign * final_num_nominator, final_num_denominator))
  | _ -> Number(Fraction(sign * (final_num_nominator / gcd_calc), final_num_denominator / gcd_calc))
    );;


let parse_float = pack (caten sign (caten (caten natural dot) natural))
  (fun (sign,((num_before_dot, dot) , num_after_dot )) ->
  let float_sign = float_of_int sign in
  let float_num_before_dot = float_of_int (list_to_natural_number num_before_dot) in
  let float_num_after_dot = list_to_after_dot num_after_dot in
  Number(Float(float_sign *. (float_num_before_dot +. float_num_after_dot))));;

let parse_scientific_notation =
    let nt_e = char_ci 'e' in
    let scientific_notation =  caten (caten (disj parse_float parse_integer) nt_e) parse_integer in
    pack scientific_notation (fun ((before , e ), after) -> match before,after with
    | (Number(Fraction(x,1)), Number(Fraction(y,1))) -> Number(Float((float_of_int x) *. (10. ** float_of_int y)))
    | (Number(Float(x)),Number(Fraction(y,1))) -> Number(Float(x *. (10. ** float_of_int y)))
    | _ -> raise X_no_match);;

let parse_number_list = [parse_scientific_notation; parse_fraction; parse_float; parse_integer;];;
let parse_number = not_followed_by (disj_list parse_number_list) symbol_char;;

(*********************** End of <Number> ***********************)


(*********************** <String> ***********************)

let string_prefix =  char '\"' ;;
let back_slash = char '\\' ;;

let string_meta_char_backslash = pack (word_ci "\\\\") (fun word -> char_of_int 92) ;;
let string_meta_char_new_line = pack (word_ci "\\n") (fun word -> char_of_int 10) ;;
let string_meta_char_return = pack (word_ci "\\r") (fun word -> char_of_int 13) ;;
let string_meta_char_tab =  pack (word_ci "\\t") (fun word -> char_of_int 9) ;;
let string_meta__char_page = pack (word_ci "\\f") (fun word -> (char_of_int 12)) ;;
let string_meta_char_double_qoute = pack (word_ci "\\\"") (fun word -> (char_of_int 34)) ;;

let parse_string_meta_char = disj_list [string_meta_char_backslash; string_meta_char_new_line; string_meta_char_return; string_meta_char_tab; string_meta__char_page; string_meta_char_double_qoute;];;

let parse_string_literal_char = pack (diff nt_any (disj string_prefix back_slash)) (fun e -> e);;

let string_postfix = star (disj parse_string_meta_char parse_string_literal_char) ;;

let parse_string = pack (make_paired string_prefix string_prefix (string_postfix)) (fun (post) -> String(list_to_string post));;


(*********************** End of <String> ***********************)


(*********************** <Symbol> ***********************)


let parse_symbol =
  let symbol_char_at_least_two = pack (caten symbol_char (plus symbol_char)) (fun (c,lst) -> c::lst) in
  let symbol_char_no_dot_list = pack symbol_char_no_dot (fun char_no_dot -> [char_no_dot]) in
  let symbol = disj symbol_char_at_least_two symbol_char_no_dot_list  in
  pack symbol (fun sym -> Symbol(String.lowercase_ascii(list_to_string sym)));;


(*********************** End of <Symbol> ***********************)


(*********************** <Sexp> ***********************)


let rec parse_sexpr_main s = make_paired to_ignore to_ignore sexp_list s
and parse_atomic_sexpr s = disj_list [parse_boolean ; parse_char; parse_number; parse_string ; parse_symbol;] s
and sexp_list s = (disj_list [parse_list; parse_quote; parse_atomic_sexpr;]) s
and comment_prefix s = (caten hash_tag (char ';')) s
and parse_sexp_comments s = pack(caten comment_prefix parse_sexpr_main) (fun e -> []) s
and to_ignore s = star (disj_list [parse_line_comments; parse_whitespaces; parse_sexp_comments; ]) s
and parse_nt_epsilon s = pack nt_epsilon (fun eps -> []) s

(*********************** <List> ***********************)
and left_parenthesis s = make_paired to_ignore to_ignore (char '(') s
and right_parenthesis s = make_paired to_ignore to_ignore (char ')') s
and dot s = make_paired to_ignore to_ignore (char '.') s
and parse_list s = (make_paired to_ignore to_ignore (disj parse_no_dotted_list parse_dotted_list )) s

and parse_dotted_list s = pack (caten (caten (caten (caten left_parenthesis
(plus (parse_sexpr_main))) dot) (parse_sexpr_main)) right_parenthesis)
    (fun ((((left, begin_list), dot) , last_element) , right) ->
            dotted_list_body (begin_list ,last_element)) s

and parse_no_dotted_list s = pack (caten (caten left_parenthesis
                        (star (parse_sexpr_main))) right_parenthesis)
                          (fun ((left, body), right) -> no_dotted_list_body body) s

and no_dotted_list_body s = (function
| [] -> Nil
| car :: cdr -> Pair(car, (no_dotted_list_body cdr))) s
and dotted_list_body s = (fun (begin_list, last_element) -> match begin_list with
| [] -> last_element
| car :: cdr -> Pair(car, (dotted_list_body (cdr, last_element)))) s

(*********************** <Quotes> ***********************)

and parse_quote s = disj_list [quote; quasi_quoted; unqoute; unquote_and_spliced; ] s

and quote s = pack (caten (make_paired to_ignore to_ignore (word "\'")) sexp_list)
    (fun (_, sexp_) -> Pair(Symbol("quote"), Pair(sexp_, Nil))) s
and quasi_quoted s = pack (caten (make_paired to_ignore to_ignore (word "`"))  sexp_list)
    (fun (_, sexp_) -> Pair( Symbol("quasiquote"), Pair(sexp_, Nil))) s
and unqoute s = pack (caten (make_paired to_ignore to_ignore  (word ",")) sexp_list)
    (fun (_, sexp_) -> Pair(Symbol("unquote"), Pair(sexp_, Nil))) s
and unquote_and_spliced s = pack (caten (make_paired to_ignore to_ignore (word ",@")) sexp_list)
    (fun (_, sexp_) -> Pair(Symbol("unquote-splicing"), Pair(sexp_, Nil))) s
;;

(*********************** End of <Sexp> ***********************)

let read s = make_paired to_ignore to_ignore (star parse_sexpr_main) s ;;
let read_sexprs string = let (exps, remainder) = read (string_to_list string) in
match remainder with
| [] -> exps
| _ -> raise X_no_match;;


end;;
