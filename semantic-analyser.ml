#use "tag-parser.ml";;

type var =
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

  let rec expr'_eq e1 e2 =
    match e1, e2 with
    | Const' Void, Const' Void -> true
    | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
    | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
    | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
    | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
    | Box'(VarFree v1), Box'(VarFree v2) -> String.equal v1 v2
    | Box'(VarParam (v1,mn1)), Box'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
    | Box'(VarBound (v1,mj1,mn1)), Box'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
    | BoxGet'(VarFree v1), BoxGet'(VarFree v2) -> String.equal v1 v2
    | BoxGet'(VarParam (v1,mn1)), BoxGet'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
    | BoxGet'(VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
    | BoxSet'(VarFree v1,e1), BoxSet'(VarFree v2, e2) -> String.equal v1 v2 && (expr'_eq e1 e2)
    | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2),e2) -> String.equal v1 v2 && mn1 = mn2 && (expr'_eq e1 e2)
    | BoxSet'(VarBound (v1,mj1,mn1),e1), BoxSet'(VarBound (v2,mj2,mn2),e2) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 && (expr'_eq e1 e2)
    | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                              (expr'_eq th1 th2) &&
                                                (expr'_eq el1 el2)
    | (Seq'(l1), Seq'(l2)
    | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
    | (Set'(var1, val1), Set'(var2, val2)
    | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                               (expr'_eq val1 val2)
    | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
    | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
       (String.equal var1 var2) &&
         (List.for_all2 String.equal vars1 vars2) &&
           (expr'_eq body1 body2)
    | Applic'(e1, args1), Applic'(e2, args2)
    | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
     (expr'_eq e1 e2) &&
       (List.for_all2 expr'_eq args1 args2)
    | _ -> false;
exception X_syntax_error;;

module type SEMANTICS = sig
    val run_semantics : expr -> expr'
    val annotate_lexical_addresses : expr -> expr'
    val annotate_tail_calls : expr' -> expr'
    val box_set : expr' -> expr'
  end;;

module Semantics : SEMANTICS = struct

let rec element_index_in_list element list = (match list with
 | [] -> raise X_syntax_error
 | head :: tail -> if (element = head)
                   then 0
                   else 1 + (element_index_in_list element tail));;

let rec element_index_in_list2 element list i =
  if i = List.length list then -1
  else
    if (List.nth list i) = element then i
    else element_index_in_list2 element list (i+1);;

let rec sublist start _end list =
  match list with
    [] -> raise X_syntax_error
  | car :: cdr ->
      let tail = if _end = 0 then [] else sublist (start-1) (_end-1) cdr in
      if start > 0 then tail else car :: cdr
;;
(********************** Lexical Address *********************)

let rec annotate_lexical_addresses_helper e current_params bound_params = match e with
  | Const(e) -> Const'(e)
  | Var(x) -> Var'(annotate_lexical_addresses_var x current_params bound_params)
  | Or(e_list) -> Or'(annotate_lexical_list e_list current_params bound_params)

  | If(test, dit, dif) ->  If'(annotate_lexical_addresses_helper test current_params bound_params,
                                annotate_lexical_addresses_helper dit current_params bound_params,
                                annotate_lexical_addresses_helper dif current_params bound_params)
  | Seq(seq) -> Seq'(annotate_lexical_list seq current_params bound_params)
  | Set(Var(_var), _val) ->
        Set'(annotate_lexical_addresses_var _var current_params bound_params,
            annotate_lexical_addresses_helper _val current_params bound_params)
  | Def(Var(x), expr) ->  Def'(annotate_lexical_addresses_var x current_params bound_params,
                              annotate_lexical_addresses_helper expr current_params bound_params)
  | LambdaSimple(vars, body) ->
        LambdaSimple'(vars, annotate_lexical_addresses_helper body vars ([current_params] @ bound_params))
  | LambdaOpt(vars, var, body) ->
        LambdaOpt'(vars, var, annotate_lexical_addresses_helper body (vars @ [var]) ([current_params] @ bound_params))

  | Applic(proc, e_list) -> Applic'(annotate_lexical_addresses_helper proc current_params bound_params,
                                     annotate_lexical_list e_list current_params bound_params)

  |  _ -> raise X_syntax_error

and annotate_lexical_addresses_var e current_params bound_params =
  if is_in_list e current_params
  then (VarParam(e, element_index_in_list e current_params))
  else
    find_bound_major e bound_params 0


and annotate_lexical_list list current_params bound_params =
    List.map (fun e -> annotate_lexical_addresses_helper e current_params bound_params) list

and find_bound_major e bound_params acc =
  match bound_params with
  | [] -> (VarFree(e))
  | car :: cdr -> if is_in_list e car
                  then
                    let minor = element_index_in_list e car in
                    VarBound(e, acc, minor)
                  else (find_bound_major e cdr (acc+1))

and is_in_list element list = List.mem element list ;;


let annotate_lexical_addresses e = (annotate_lexical_addresses_helper e [] []) ;;

(********************** End of Lexical Address *********************)


(********************** Tail Call *********************)

let rec annotate_tail_calls_helper e tp = match e with
  | Const'(e) -> Const'(e)
  | Var'(e) -> Var'(e)
  | Or'(e_list) -> Or'(annotate_last_element e_list tp)
  | If'(test, dit, dif) -> If'(annotate_tail_calls_helper test false,
                            annotate_tail_calls_helper dit tp,
                            annotate_tail_calls_helper dif tp)
  | Seq'(seq) -> Seq'(annotate_last_element seq tp)
  | Set'(_var, _val) -> Set'(_var, annotate_tail_calls_helper _val false)
  | Def'(x, expr) -> Def'(x, annotate_tail_calls_helper expr false)
  | LambdaSimple'(vars, body) -> LambdaSimple'(vars, annotate_tail_calls_helper body true)
  | LambdaOpt'(vars, var, body) -> LambdaOpt'(vars,var, annotate_tail_calls_helper body true)
  | Applic'(proc, e_list) ->
    (match tp with
     | false -> Applic'(annotate_tail_calls_helper proc false, List.map annotate_lambda_body e_list)
     | true -> ApplicTP'(annotate_tail_calls_helper proc false, List.map annotate_lambda_body e_list))

  |  _ -> raise X_syntax_error


and annotate_lambda_body element =
  annotate_tail_calls_helper element false

and annotate_last_element lst tp =
  let reverse_list = List.rev lst in
  let head = List.hd reverse_list in
  let tail = List.tl reverse_list in
  List.append (List.map annotate_tail_false (List.rev tail)) [(annotate_tail_calls_helper head tp)]

and annotate_tail_false element =
  annotate_tail_calls_helper element false
;;

let annotate_tail_calls e = annotate_tail_calls_helper e false;;

(********************** End of Tail Call *********************)


(********************** Box Set *********************)

let replace_first_expr_seq var minor body =
  let box = Set'(VarParam(var, minor), Box'(VarParam(var, minor))) in
  match body with
    | Seq'(seq) ->
        let new_list = [box] @ seq in
        Seq'(new_list)
    | _ ->
      let new_list = [box] @ [body] in
      Seq'(new_list)
;;

let rec boolean_read_write_criteria_rec result_array param rib_major expr = match expr with
    | Const'(x) -> result_array
    | Var'(VarFree(var)) -> result_array
    | Var'(VarParam(var, index)) ->
          if (var = param)
          then (begin ((List.nth result_array 0) := !(List.nth result_array 0) @ [rib_major.contents]);
                ((List.nth result_array 2) := !(List.nth result_array 2) @ [0]);
                (result_array) end)
          else result_array
    | Var'(VarBound(var, major,minor)) ->
          if (var = param)
          then (begin ((List.nth result_array 0) := !(List.nth result_array 0) @ [rib_major.contents]);
                ((List.nth result_array 2) := !(List.nth result_array 2) @ [0]);
                (result_array) end)
          else result_array
    | Box'(var) -> result_array
    | BoxGet'(var) -> result_array
    | BoxSet'(var, e) -> boolean_read_write_criteria_rec result_array param rib_major e
    | If'(test, dit, dif) -> handle_read_write_list result_array param rib_major [test; dit; dif;]
    | Seq'(seq) -> handle_read_write_list_applic result_array param rib_major seq
    | Or'(expr) -> handle_read_write_list result_array param rib_major expr
    | Def'(_var, _val) -> handle_read_write_list result_array param rib_major [Var'(_var); _val]
    | Set'(_var, _val) -> handle_read_write_set result_array param rib_major _var _val
    | LambdaSimple'(vars, body) -> if (List.mem param vars)
                                   then result_array
                                   else (begin (rib_major := !rib_major+1;);
                                        (boolean_read_write_criteria_rec result_array param rib_major body) end)
    | LambdaOpt'(vars, var, body) -> if (List.mem param (vars@[var]))
                                     then result_array
                                     else (begin (rib_major := !rib_major+1;);
                                     (boolean_read_write_criteria_rec result_array param rib_major body) end)
    | Applic'(proc, e_list) -> handle_read_write_list_applic result_array param rib_major ([proc]@e_list)
    | ApplicTP'(proc, e_list) -> handle_read_write_list_applic result_array param rib_major ([proc]@e_list)


and handle_read_write_list_applic result_array param rib_major list =
  let result = (List.mapi (fun i x ->
  let _ = (rib_major := !rib_major+i;) in
                            (boolean_read_write_criteria_rec result_array param rib_major x)) list) in
  List.hd result

and handle_read_write_list result_array param rib_major list =
    let result = (List.map (boolean_read_write_criteria_rec result_array param rib_major) list) in
    List.hd result

and handle_read_write_set result_array param rib_major _var _val =
  let string_var _var  =  match _var with
      | VarParam(v,index) -> v
      | VarFree(v) -> v
      | VarBound(v,major,minor) -> v in
  if (param = (string_var _var))
  then (begin ((List.nth result_array 1) := !(List.nth result_array 1) @ [rib_major.contents]);
              ((List.nth result_array 2) := !(List.nth result_array 2) @ [1]);
              boolean_read_write_criteria_rec result_array param rib_major _val end)
  else boolean_read_write_criteria_rec result_array param rib_major _val
;;


let rec check_all_boxing_criterias param expr =
  let rib_major = ref 0 in
  let result_read = ref [] in
  let result_write = ref [] in
  let result_write_read_bool = ref [] in
  let result_array =  [result_read; result_write; result_write_read_bool] in

  let _ = boolean_read_write_criteria_rec result_array param rib_major expr in
  true
  (* if (result_read = ref [] || result_write = ref [])
  then false
  (* check that the read and write are in different ribs *)
  else
    if (check_different_ribs result_read result_write = false)
    then false
    (* if both criterias dont match then we need to box *)
    else
    match expr with
    | Seq'(seq) ->
        ((false = first_criteria result_read result_write result_write_read_bool)
          && (false = second_criteria result_read result_write result_write_read_bool))
    | _ ->  true *)

and first_criteria result_read result_write result_write_read_bool =
  let write_depth_zero = element_index_in_list2 0 result_write.contents 0 in
  if (write_depth_zero = -1)
  then false
  else
    (* first write index in boolean array in current SEQ *)
    let curr_write_occurence_index = (find_occurence_boolean_list (write_depth_zero+1) 0 1 result_write_read_bool) in
     (* first read index after write *)
    let first_read_after_curr_write_index = (find_first_after (curr_write_occurence_index+1) 0 result_write_read_bool) in
    let find_read_index = (count_occurences_before 0 first_read_after_curr_write_index 0 0 result_write_read_bool) in
    let sub_read_list = sublist find_read_index (List.length result_read.contents -1 ) result_read.contents in
    find_major sub_read_list

and second_criteria result_read result_write result_write_read_bool =
  let read_depth_zero = element_index_in_list2 0 result_read.contents 0 in
  if (read_depth_zero = -1)
  then false
  else
    (* first read index in boolean array in current SEQ *)
    let curr_read_occurence_index = (find_occurence_boolean_list (read_depth_zero+1) 0 0 result_write_read_bool) in
      (* first write index after read in bool list *)
    let first_write_after_curr_read_index = (find_first_after (curr_read_occurence_index+1) 1 result_write_read_bool) in
    let find_write_index = (count_occurences_before 0 first_write_after_curr_read_index 0 1 result_write_read_bool) in
   let sub_write_list = sublist find_write_index (List.length result_write.contents -1 ) result_write.contents in
  find_major sub_write_list


and count_occurences_before i first_index counter_read true_or_false result_write_read_bool =
  if i = List.length result_write_read_bool.contents then counter_read else
  if i = first_index
  then counter_read
  else
    let x = (List.nth result_write_read_bool.contents i) in
    if (x = true_or_false)
    then (count_occurences_before (i+1) first_index (counter_read+1) true_or_false result_write_read_bool)
    else (count_occurences_before (i+1) first_index counter_read true_or_false result_write_read_bool)

and find_major sub_list =
    let bool_sub_list = List.mapi (fun i x -> (List.nth sub_list i) > 0) sub_list in
    List.mem true bool_sub_list

and find_first_after index true_or_false result_write_read_bool =
  let x = (List.length result_write_read_bool.contents) in
  if (index = x) then -1
  else
    let y = List.nth result_write_read_bool.contents index in
    if (true_or_false = y) then index
    else (find_first_after (index + 1) true_or_false result_write_read_bool)


and find_occurence_boolean_list counter index read_or_write result_write_read_bool =
  let x = (List.nth result_write_read_bool.contents index) in
  if (x = read_or_write)
  then (match counter with
          | 1 -> index
          | _ -> find_occurence_boolean_list (counter-1) (index+1) read_or_write result_write_read_bool)
  else (find_occurence_boolean_list counter (index+1) read_or_write result_write_read_bool)


and check_different_ribs result_read result_write =
  let bool_result_list_read = List.map (check_occurence result_write) result_read.contents in
  let bool_result_list_write = List.map (check_occurence result_read) result_write.contents in
  List.mem false (bool_result_list_read @ bool_result_list_write)

and check_occurence result_write element =
   List.mem element result_write.contents;;

let rec replace_set_get_occurances param expr = match expr with
  | Const'(x) -> Const'(x)
  | Var'(VarFree(var)) -> Var'(VarFree(var))
  | Var'(VarParam(var, index)) -> if (var = param)
                                  then BoxGet'(VarParam(var, index))
                                  else Var'(VarParam(var, index))
  | Var'(VarBound(var, major,minor)) ->  if (var = param)
                                         then BoxGet'(VarBound(var, major,minor))
                                         else Var'(VarBound(var, major,minor))
  | Box'(var) -> Box'(var)
  | BoxGet'(var) -> BoxGet'(var)
  | BoxSet'(var, e) ->  BoxSet'(var, replace_set_get_occurances param e)
  | If'(test, dit,dif) -> If'(replace_set_get_occurances param test,replace_set_get_occurances param dit,replace_set_get_occurances param dif)
  | Seq'(seq) -> Seq'(handle_set_get_occurances_list param seq)
  | Or'(or_expr) -> Or'(handle_set_get_occurances_list param or_expr)
  | Def'(_var, _val) ->  Def'(_var, replace_set_get_occurances param _val)
  | Set'(_var, _val) -> if ((get_string_value _var) = param)
                        then BoxSet'(_var , replace_set_get_occurances param _val)
                        else Set'(_var, replace_set_get_occurances param _val)
  | LambdaSimple'(vars, body) ->  if (List.mem param vars)
                                  then LambdaSimple'(vars, body)
                                  else LambdaSimple'(vars, replace_set_get_occurances param body)
  | LambdaOpt'(vars, var, body) -> if (List.mem param (vars @ [var]))
                                  then LambdaOpt'(vars, var, body)
                                  else LambdaOpt'(vars, var, replace_set_get_occurances param body)
  | Applic'(proc, e_list) -> Applic'(replace_set_get_occurances param proc, handle_set_get_occurances_list param e_list)
  | ApplicTP'(proc, e_list) -> ApplicTP'(replace_set_get_occurances param proc, handle_set_get_occurances_list param e_list)

and handle_set_get_occurances_list param list =
  List.map (replace_set_get_occurances param) list

and get_string_value _var = match _var with
     | VarParam(v,index) -> v
     | VarFree(v) -> v
     | VarBound(v,major,minor) -> v
;;

let rec create_var_minor_pairs vars len =
  (if (len = List.length vars)
  then []
  else  [List.nth vars len, len] @ create_var_minor_pairs vars (len + 1)) ;;

let box_set_helper_lambda_param param body =
    match param with
    | (var, minor) ->
      (* do we need to box the param *)
      (let box_result = check_all_boxing_criterias var body in
      if box_result
      then
        let new_body = replace_set_get_occurances var body in
          replace_first_expr_seq var minor new_body
      else
        body)
  ;;

let box_set_helper_lambda vars body =
  (* make pairs of var + minor *)
  let params_pairs = create_var_minor_pairs vars 0 in
  (* for each parameter check if need to box *)
  List.fold_right box_set_helper_lambda_param params_pairs body ;;

let rec box_set_helper e = match e with
  | Const'(x) -> Const'(x)
  | Var'(x) -> Var'(x)
  | Box'(var) -> Box'(var)
  | BoxGet'(var) -> BoxGet'(var)
  | BoxSet'(var, e) -> BoxSet'(var, box_set_helper e)
  | If'(test, dit,dif) -> If'(box_set_helper test,box_set_helper dit, box_set_helper dif)
  | Seq'(seq) -> Seq'(List.map box_set_helper seq)
  | Or'(seq) -> Or'(List.map box_set_helper seq)
  | Def'(_var, _val) -> Def'(_var, box_set_helper _val)
  | Set'(_var, _val) -> Set'(_var, box_set_helper _val)
  | LambdaSimple'(vars, body) -> LambdaSimple'(vars, box_set_helper (box_set_helper_lambda vars body))
  | LambdaOpt'(vars, var, body) -> LambdaOpt'(vars,var, box_set_helper (box_set_helper_lambda (vars @ [var]) body))
  | Applic'(proc, e_list) -> Applic'(box_set_helper proc , (List.map box_set_helper e_list))
  | ApplicTP'(proc, e_list) -> ApplicTP'(box_set_helper proc , (List.map box_set_helper e_list));;

let box_set e = box_set_helper e ;;

(********************** End of Box Set *********************)

let run_semantics expr =
  box_set
    (annotate_tail_calls
        (annotate_lexical_addresses expr));;

end;;
