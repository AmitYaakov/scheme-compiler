#use "reader.ml";;
type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	

exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;

(* work on the tag parser starts here *)

let rec tag_parse sexpr = match sexpr with
| Bool _ -> Const (Sexpr(sexpr))
| Nil -> Const(Void)
| Number _ -> Const(Sexpr(sexpr))
| Char _ -> Const(Sexpr(sexpr))
| String _ -> Const(Sexpr(sexpr))


| Pair(Symbol("quote"), Pair(sexpr, Nil)) ->
      Const(Sexpr(sexpr))
| Pair(Symbol("quasiquote"), Pair(sexpr, Nil)) ->
      tag_parse (expand_quasiquote_expr sexpr)

| Symbol(symbol) -> if (reserved_word symbol) then raise X_syntax_error else Var(symbol)

| Pair(Symbol("cond"), rib_sexprs) -> tag_parse (expand_cond_expr rib_sexprs)

| Pair (Symbol("let"), let_rest) ->  expand_let_expr let_rest
| Pair (Symbol("let*"), let_star_rest) ->  expand_let_star_expr let_star_rest
| Pair (Symbol("letrec"), letrec_rest) ->  expand_letrec_expr letrec_rest

| Pair (Symbol("if"), Pair(test, Pair(dit, dif))) ->
  ( match dif with
  | Nil -> If(tag_parse test, tag_parse dit, Const Void)
  | Pair(dif, Nil) ->  If(tag_parse test, tag_parse dit, tag_parse dif)
  | _ -> raise X_syntax_error)


| Pair (Symbol("begin") , Nil) -> Const Void
| Pair (Symbol("begin") , Pair(x , Nil)) -> tag_parse x
| Pair (Symbol("begin") , sexpr) -> Seq (sexpr_to_lst_tagparser sexpr)

| Pair (Symbol("set!") , Pair(var, Pair(expr, Nil))) -> Set((tag_parse var), (tag_parse expr))
| Pair (Symbol("pset!") , expr_list) -> (expand_pset_expr expr_list)

| Pair (Symbol("define") , Pair(Symbol (var), expr)) ->
  (match expr with
  | Nil -> Def((tag_parse (Symbol(var))), Const Void)
  | Pair(expr, Nil) -> Def((tag_parse (Symbol(var))), tag_parse expr)
  | _ -> raise X_syntax_error)
| Pair (Symbol("define"), Pair(Pair(var, arglist), expr_plus)) -> expand_define_expr var arglist expr_plus


| Pair (Symbol("or"),Nil) -> Const (Sexpr(Bool false))
| Pair (Symbol("or"), Pair(expr, Nil)) -> tag_parse expr
| Pair (Symbol("or"), sexpr) ->
    let or_list = (pair_to_list sexpr) in
    let or_list_parse = List.map tag_parse or_list in
    Or (or_list_parse)


| Pair (Symbol("lambda"), Pair(Symbol(x) , body)) ->
      LambdaOpt([], x , (tag_parse (Pair(Symbol "begin" , body))))
| Pair (Symbol("lambda"), Pair(args , body)) ->
    (let proper_list = is_proper_list args in
    let args_to_list = (create_args_list (pair_to_list args)) in
    if proper_list
     then LambdaSimple(args_to_list, (tag_parse (Pair(Symbol "begin" ,body))))
     else LambdaOpt((get_all_body_but_tail args_to_list) , (get_tail args_to_list), (tag_parse (Pair(Symbol "begin" ,body)))))

| Pair (Symbol("and"), and_body) -> (expand_and_expr and_body)

| Pair (sexpr_head, sexpr_rest) ->
      if is_proper_list sexpr_rest
      then Applic(tag_parse sexpr_head, (sexpr_to_lst_tagparser sexpr_rest))
      else raise X_syntax_error


(********************** expansions *********************)
and expand_and_expr and_body = match and_body with
  | Nil -> Const (Sexpr(Bool(true)))
  | Pair (expr , Nil) -> tag_parse expr
  | Pair (expr , rest) -> If(tag_parse expr, expand_and_expr rest , Const (Sexpr(Bool(false))))
  | _ -> raise X_syntax_error

and expand_define_expr var arglist expr_plus =
  tag_parse (Pair(Symbol("define"), Pair(var, Pair (Pair(Symbol("lambda"),
          Pair(arglist, expr_plus)), Nil))))

and expand_letrec_expr letrec_rest = match letrec_rest with
  | Pair(letrec_args, letrec_body) ->
      (
      let whatever = Pair(Symbol("quote"), Pair( Symbol("whatever"), Nil)) in
      let create_whatever_pairs element = Pair(element, Pair (whatever,Nil)) in
      let create_setbang_pairs element_var element_val =
        Pair(Symbol "set!" , Pair(element_var, Pair(element_val ,Nil))) in
      let list_letrec_args  = (pair_to_list (letrec_args)) in
      let list_args_var = (List.map create_var_list list_letrec_args) in
      let list_args_val = List.map create_val_list list_letrec_args in
      let let_whatever_pairs = (list_to_pair (List.map create_whatever_pairs list_args_var)) in
      let let_setbang_pairs = (List.map2 create_setbang_pairs list_args_var list_args_val) in
      let last_let = Pair(Symbol"let", Pair(Nil , letrec_body)) in

      let final_list = List.append (List.append [Symbol "let" ; let_whatever_pairs] let_setbang_pairs) [last_let] in
      tag_parse (list_to_pair final_list))

  | _ -> raise X_syntax_error

and expand_let_star_expr let_star_rest  = (match let_star_rest with
  | Pair(let_args, let_body) ->
  (match let_args with
      (**** first case ****)
      | Nil -> tag_parse (Pair(Symbol("let") , Pair (Nil , let_body)))

      (**** second case ****)
      | Pair(Pair (var, Pair (_val , Nil)), Nil) ->
        tag_parse (Pair(Symbol "let" , Pair(let_args, let_body)))

      (**** third case ****)
      | Pair(Pair (var, Pair (_val , Nil)), let_star_rest) -> (
        tag_parse (Pair( Symbol("let") ,
                    Pair(Pair(Pair(var, Pair(_val,Nil)),Nil),
                      Pair( Pair(Symbol("let*") , Pair(let_star_rest , let_body) ) , Nil)))))

      | _ -> raise X_syntax_error)
    | _ -> raise X_syntax_error)

and expand_let_expr let_rest = (match let_rest with
  | Pair (let_args, let_body) ->
        let list_let_args  = (pair_to_list (let_args)) in
        let list_args_var = List.map create_var_list list_let_args in
        let list_args_val = List.map create_val_list list_let_args in

        let lambda_params = list_to_pair list_args_var in
        let applic_values = list_to_pair list_args_val in
        let let_to_lambda = tag_parse (Pair (Pair (Symbol "lambda", Pair (lambda_params, let_body)), applic_values)) in
        let_to_lambda
  | _ -> raise X_syntax_error)


and expand_quasiquote_expr sexpr =  match sexpr with
  |  Pair(Symbol("unquote"), Pair(sexpr, Nil)) -> sexpr
  |  Pair(Symbol("unquote-splicing"), x) -> raise X_syntax_error
  |  Nil -> Pair(Symbol("quote"), Pair(Nil, Nil))
  |  Symbol(x) -> Pair(Symbol("quote"), Pair(Symbol(x), Nil))
  |  Pair(car , cdr) -> (match car with
        |  (Pair( Symbol("unquote-splicing") , (Pair(x ,Nil)))) ->
                Pair(Symbol("append"), Pair(x , Pair(expand_quasiquote_expr cdr, Nil)))
        | _ -> (match cdr with
      | Pair(Symbol("unquote-splicing") , x) ->  Pair(Symbol("cons"), Pair(expand_quasiquote_expr car , x))
      |_ -> Pair(Symbol("cons"), Pair(expand_quasiquote_expr car , Pair(expand_quasiquote_expr cdr, Nil)))))
  | Bool _ | Char _ | Number _ | String _ -> sexpr


and expand_cond_expr rib_sexprs = match rib_sexprs with

  (******** else ********)
  | Pair(Pair(Symbol("else") , _else) , rest_ribs) -> (Pair(Symbol ("begin") , _else ))

   (******** => ********)
  | Pair(Pair(test , Pair(Symbol ("=>") , Pair(_then, Nil))) , rest_ribs) ->

      let value_var = Pair(Symbol "value", Pair(test, Nil)) in
      let f_var = Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(_then, Nil))), Nil)) in
      let if_then = Pair(Pair(Symbol("f"),Nil) , Pair(Symbol("value"), Nil)) in

      (match rest_ribs with
        | Nil -> (

            let var_list_no_rest =  Pair (value_var , Pair(f_var  ,Nil)) in
            let body_list_no_rest = Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(if_then,Nil))), Nil) in

            let let_body = Pair(var_list_no_rest , body_list_no_rest) in
            let let_exp_no_rest =  Pair(Symbol("let"), let_body) in
            let_exp_no_rest)

        | _ -> (

            let if_else =  Pair(Symbol "rest", Nil)  in
            let rest_var = Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(expand_cond_expr rest_ribs, Nil))), Nil)), Nil) in

            let var_list_rest =  Pair (value_var , Pair(f_var , rest_var)) in
            let body_list_rest = Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(if_then, Pair(if_else, Nil)))), Nil) in

            let let_body = Pair(var_list_rest , body_list_rest) in
            let let_ex_rest =  Pair(Symbol("let"), let_body) in
            let_ex_rest))

  (******** regular ********)
  | Pair(Pair(test, seq) ,rest) ->
      let recursive_rest = (match rest with
        | Nil -> Nil
        | _ -> Pair(Pair(Symbol("cond"), rest),Nil)) in

      let _then = Pair(Symbol("begin") , seq) in
       Pair(Symbol("if"),
                Pair(test,
                Pair( _then,
                recursive_rest)))
  | _ -> raise X_syntax_error



and expand_pset_expr expr_list  = match expr_list with
  | Nil -> tag_parse expr_list
  | _ ->  let pset_list = pair_to_list expr_list in
    let var_list = List.map create_var_list pset_list in
    let n_i_list = List.mapi create_n_i_list var_list in
    let val_list = List.map create_val_list pset_list in

    let set_pair = List.map2 create_set_pairs var_list n_i_list in

    let _lambda = list_to_pair (List.append
    (List.append [Symbol "lambda"]  [list_to_pair n_i_list]) set_pair) in
    let final_expr = list_to_pair (List.append [_lambda] val_list) in
    tag_parse final_expr


(********************** End of expansions *********************)


(********************** Helper Functions *********************)

and create_var_list element = match element with
  | Pair(var,_val) -> var
  | _ -> raise X_syntax_error

and create_val_list element = match element with
  | Pair(var, Pair(_val, Nil)) -> _val
  | _ -> raise X_syntax_error

and create_args_list lst =
  List.map remove_symbol lst

and remove_symbol sym = match sym with
  | Symbol(sym) -> sym
  | _ -> ""

and get_all_body_but_tail lst = match List.rev lst with
  | tail :: all_but_tail-> List.rev all_but_tail
  | _ -> raise X_syntax_error

and get_tail lst = List.hd (List.rev lst)

and is_proper_list lst = match lst with
  | Nil -> true
  | Pair (car , cdr) -> is_proper_list cdr
  | _ -> false


and reserved_word s =
  List.mem s reserved_word_list

and flatten_begin = function
  | Pair ((Pair (Symbol "begin", first)), rest) -> List.append (flatten_begin (Pair (Symbol "begin", first))) (flatten_begin rest)
  | Pair (Symbol "begin", rest) -> flatten_begin rest
  | Pair (car, cdr) -> car::(flatten_begin cdr)
  | Nil -> []
  | x -> [x]

and sexpr_to_lst_tagparser s =
  let lst_no_begin = flatten_begin s in
  List.map tag_parse lst_no_begin

and pair_to_list pair = match pair with
  | Nil -> []
  | Pair (x , Nil) -> [x]
  | Pair (x , Pair(y , z)) -> x :: (pair_to_list (Pair(y,z)))
  | Pair (x , y) -> [x ; y]
  | _ -> raise X_syntax_error

and list_to_pair list = List.fold_right list_to_pair_helper list Nil
and list_to_pair_helper = (fun left right -> Pair(left, right))


and create_n_i_list i element =
  Symbol(String.concat "n" [""; string_of_int i])

and create_set_pairs var n_i =
  Pair(Symbol "set!", Pair(var, Pair(n_i, Nil)))

(********************** End of Helper Functions *********************)

(**** main function****)
let tag_parse_expressions sexpr = List.map tag_parse sexpr
end;; (* struct Tag_Parser *)