#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second
     argument is the fvars table type, and the third is an expr' that has been annotated
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  (*************************** Helper Functions***************************)
  let rec remove_duplicate_element element const_list = match const_list with
    | [] -> []
    | x :: [] -> if x = element then []
                else (x :: [])
    | x :: rest -> if x = element then (remove_duplicate_element element rest)
                        else (x :: (remove_duplicate_element element rest)) ;;

  let rec remove_duplicate const_list = match const_list with
    | [] -> []
    | x :: rest -> [x] @ (remove_duplicate (remove_duplicate_element x rest));;


  (*************************** Const Table ***************************)
  let rec make_consts_tbl_helper_step_one acc ast = match ast with
     | Const'(const) -> acc @ [const]
     | BoxSet'(_var, expr) -> make_consts_tbl_helper_step_one acc expr
     | If' (test, dit, dif) -> (make_consts_tbl_helper_step_one acc test) @
                               (make_consts_tbl_helper_step_one acc dit) @ (make_consts_tbl_helper_step_one acc dif)
     | Seq'(seq) -> List.flatten (List.map (make_consts_tbl_helper_step_one acc) seq)
     | Set'(_var, _val) ->  (make_consts_tbl_helper_step_one acc _val)
     | Def'(x, expr) -> (make_consts_tbl_helper_step_one acc expr)
     | Or'(or_list) -> List.flatten  (List.map (make_consts_tbl_helper_step_one acc) or_list)
     | LambdaSimple'(vars,body) ->(make_consts_tbl_helper_step_one acc body)
     | LambdaOpt'(vars, var, body) -> (make_consts_tbl_helper_step_one acc body)
     | Applic'(proc, e_list) -> (make_consts_tbl_helper_step_one acc proc) @
                                List.flatten (List.map (make_consts_tbl_helper_step_one acc) e_list)
     | ApplicTP'(proc, e_list) -> (make_consts_tbl_helper_step_one acc proc) @
                                List.flatten (List.map (make_consts_tbl_helper_step_one acc) e_list)
     | _ -> acc

  let rec expand_sub_constants const_element = match const_element with
     | Sexpr(Symbol(x)) -> [Sexpr (String(x)); const_element]
     | Sexpr(Pair(x,rest)) -> (expand_sub_constants (Sexpr(x))) @ (expand_sub_constants (Sexpr(rest))) @ [const_element]
     | Sexpr(x) -> [const_element]
     | Void-> [Void] ;;

  let rec find_string_offset consts_table element = match consts_table with
     | [] -> raise X_syntax_error
     | car :: cdr -> match car with
       | (_type, (offset, make)) -> if _type = element then offset else find_string_offset cdr element
     ;;

  let rec create_consts_table_full consts_table offset const_list = match const_list with
     | [] -> consts_table
     |  car :: cdr -> (match car with
                       | Void -> create_consts_table_full (consts_table @ [(Void, (0, "db T_VOID"))]) (offset+1) cdr
                       | Sexpr (y) -> (match y with
                          | Nil -> create_consts_table_full (consts_table @ [(Sexpr(Nil), (1, "db T_NIL"))]) (offset+1) cdr
                          | Bool(false) -> create_consts_table_full (consts_table @
                              [(Sexpr(Bool(false)), (2, "db T_BOOL, 0"))])
                            (offset+2) cdr
                          | Bool(true) -> create_consts_table_full (consts_table @
                            [(Sexpr(Bool(true)), (4, "db T_BOOL, 1"))])
                            (offset+2) cdr
                          | Char(x) -> create_consts_table_full
                              (consts_table @ [(Sexpr(Char(x)), (offset, "MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char x)) ^")"))])
                              (offset+2) cdr
                          | Number(x) -> (match x with
                             | Fraction(x,y) -> create_consts_table_full (consts_table @
                                         [((Sexpr(Number(Fraction(x,y)))), (offset, "MAKE_LITERAL_RATIONAL(" ^ string_of_int x ^ "," ^ string_of_int y ^ ")"))])
                                         (offset+17) cdr
                             | Float(x) -> create_consts_table_full (consts_table @
                                       [((Sexpr(Number(Float(x)))), (offset, "MAKE_LITERAL_FLOAT(" ^ string_of_float x ^ ")"))])
                                         (offset+9) cdr)
                          | String(x) -> create_consts_table_full (consts_table @
                                        [(Sexpr(String(x)), (offset, "MAKE_LITERAL_STRING \"" ^ x ^ "\""))])
                                        (offset + 9 + String.length x) cdr
                          | Symbol(x) -> let x_offset = string_of_int (find_string_offset consts_table (Sexpr(String(x)))) in
                                        create_consts_table_full (consts_table @
                                        [(Sexpr(Symbol(x)), (offset, "MAKE_LITERAL_SYMBOL(const_tbl+" ^ x_offset ^ ")"))])
                                        (offset+9) cdr
                          | Pair(first, second) -> let first_offset = string_of_int (find_string_offset consts_table (Sexpr(first))) in
                                                    let second_offset = string_of_int (find_string_offset consts_table (Sexpr(second))) in
                                        create_consts_table_full (consts_table @
                                        [(Sexpr(Pair(first,second)), (offset, "MAKE_LITERAL_PAIR(const_tbl+" ^ first_offset ^ ", const_tbl+" ^ second_offset ^ ")"))])
                                        (offset+17) cdr))
  ;;



  let create_consts_table const_list =
      create_consts_table_full [] 0 const_list ;;


  let rec make_consts_tbl_helper acc asts =
      let step_one_table = List.flatten (List.map (make_consts_tbl_helper_step_one acc) asts) in
      let step_two_table = remove_duplicate step_one_table in
      let step_three_table = List.flatten (List.map expand_sub_constants step_two_table) in
      let step_three_table = [Void; Sexpr(Nil); Sexpr(Bool(false)); Sexpr(Bool(true))] @ step_three_table in
      let step_four_table = remove_duplicate step_three_table in
      let step_five_table = create_consts_table step_four_table in
      step_five_table;;


  (*************************** FVAR Table ***************************)

  let rec make_fvars_tbl_helper_step_one acc ast = match ast with
     | Var'(VarFree(x)) -> [x] @ acc
     | BoxSet'(_var, expr) -> make_fvars_tbl_helper_step_one acc expr
     | If' (test, dit, dif) -> (make_fvars_tbl_helper_step_one acc test) @ (make_fvars_tbl_helper_step_one acc dit) @ (make_fvars_tbl_helper_step_one acc dif)
     | Seq'(seq) -> List.flatten (List.map (make_fvars_tbl_helper_step_one acc) seq)
     | Set'(_var, _val) -> (make_fvars_tbl_helper_step_one acc (Var'(_var))) @ (make_fvars_tbl_helper_step_one acc _val)
     | Def'(x, expr) -> (make_fvars_tbl_helper_step_one acc (Var'(x))) @ (make_fvars_tbl_helper_step_one acc expr)
     | Or'(or_list) -> List.flatten  (List.map (make_fvars_tbl_helper_step_one acc) or_list)
     | LambdaSimple'(vars,body) -> (make_fvars_tbl_helper_step_one acc body)
     | LambdaOpt'(vars, var, body) -> (make_fvars_tbl_helper_step_one acc body)
     | Applic'(proc, e_list) -> (make_fvars_tbl_helper_step_one acc proc) @
                                List.flatten (List.map (make_fvars_tbl_helper_step_one acc) e_list)
     | ApplicTP'(proc, e_list) -> (make_fvars_tbl_helper_step_one acc proc) @
                                List.flatten (List.map (make_fvars_tbl_helper_step_one acc) e_list)
     | _ -> acc;;


  let create_pair_fvar counter fvar =
    (fvar, 8*(counter+1));;

  let rec make_fvars_tbl_helper acc ast =
      let built_in_procedures = [
      "boolean?"; "flonum?"; "rational?";
      "pair?";"null?"; "char?"; "string?";
      "procedure?";"symbol?";
      "string-length"; "string-ref"; "string-set!";
      "make-string"; "symbol->string";
      "char->integer"; "integer->char"; "exact->inexact";
      "eq?";"+";"*"; "/"; "="; "<";
      "numerator"; "denominator"; "gcd"; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!" ;"apply";
    ] in
    let step_one_fvars_tbl = built_in_procedures @ (List.flatten (List.map (make_fvars_tbl_helper_step_one acc) ast)) in
    let step_two_fvars_tbl = remove_duplicate step_one_fvars_tbl in
    let step_three_table = List.mapi create_pair_fvar step_two_fvars_tbl in
    step_three_table;;


  (*************************** Generate ***************************)
  let label_counter = ref 0;;

  let rec find_address_in_consts_tbl consts_tbl const = (match consts_tbl with
    | [] -> raise X_syntax_error
    | car :: cdr -> (match car with
            | (x, (offset,make)) -> if (x = const) then offset
                                    else find_address_in_consts_tbl cdr const)
    );;

  let rec find_label_in_fvars_tbl fvars_tbl _var = (match fvars_tbl with
    | [] -> raise X_syntax_error
    | car :: cdr -> (match car with
            | (v, counter) -> if (v = _var) then "fvar_tbl+"^(string_of_int counter)
                                    else find_label_in_fvars_tbl cdr _var)
    );;


  let rec generate_helper consts_tbl fvars_tbl env_size  expr = match expr with
    | Const'(c) -> generate_const_helper consts_tbl c
    | Var'(VarParam(_, minor)) -> generate_varparam_helper consts_tbl minor
    | Var'(VarBound(_, major, minor)) -> generate_varbounds_helper consts_tbl minor major
    | Var'(VarFree(v)) -> generate_varfree_helper fvars_tbl v
    | Set'(VarParam(_, minor),eps) -> generate_setparam_helper consts_tbl fvars_tbl env_size minor eps
    | Set'(VarBound(_,major,minor),eps) -> generate_setbound_helper consts_tbl fvars_tbl env_size minor major eps
    | Set'(VarFree(v),eps) -> generate_setvfree_helper consts_tbl fvars_tbl env_size v eps
    | Seq'(e_list) -> generate_seq_helper consts_tbl fvars_tbl env_size e_list
    | Or'(or_list) -> generate_or_helper consts_tbl fvars_tbl env_size or_list
    | If'(test, dit, dif) -> generate_if_helper consts_tbl fvars_tbl env_size test dit dif
    | Box'(x) -> generate_box_helper consts_tbl fvars_tbl env_size (Var'(x))
    | BoxGet'(v) -> generate_boxget_helper consts_tbl fvars_tbl env_size (Var'(v))
    | BoxSet'(v,eps) -> generate_boxset_helper consts_tbl fvars_tbl env_size (Var'(v)) eps
    | LambdaSimple'(param_list , body) -> generate_lambdasimple_helper consts_tbl fvars_tbl env_size param_list body
    | LambdaOpt'(param_list, param, body) -> generate_lambdaopt_helper consts_tbl fvars_tbl env_size param_list param body
    | Def'(v, exp) -> generate_define_helper consts_tbl fvars_tbl env_size v exp
    | Applic'(proc, e_list) -> generate_applic_helper consts_tbl fvars_tbl env_size proc e_list
    | ApplicTP'(proc, e_list) -> generate_applictp_helper consts_tbl fvars_tbl env_size proc e_list


  and generate_const_helper consts_tbl const =
    let offset = string_of_int(find_address_in_consts_tbl consts_tbl const) in
    ";generate const
      mov rax, const_tbl+"^offset^"\n"

  and generate_varparam_helper consts_tbl minor =
    ";generate var param
      mov rax,qword[rbp+8*(4+"^(string_of_int minor)^")]\n"

  and generate_varfree_helper fvars_tbl _var =
    let label =  (find_label_in_fvars_tbl fvars_tbl _var) in
    ";generate var free
      mov rax,qword[" ^label^"]\n"

  and generate_varbounds_helper consts_tbl minor major =
    ";generate var bound
      mov rax,qword[rbp+8*2]
      mov rax, qword[rax+8*"^(string_of_int major)^"]\n" ^
     "mov rax, qword[rax+8*"^(string_of_int minor)^"]\n"

  and generate_setparam_helper consts_tbl fvars_tbl env_size minor eps =
      (generate_helper consts_tbl fvars_tbl env_size eps)^"\n" ^
      ";generate set param
      mov qword[rbp+8*(4+"^(string_of_int minor)^")], rax\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"

  and generate_setbound_helper consts_tbl fvars_tbl env_size minor major eps =
      ";generate set bound param\n"^((generate_helper consts_tbl fvars_tbl env_size  eps))^"
      mov rbx, qword[rbp+8*2]
      mov rbx, qword[rbx+8*"^(string_of_int major)^"]
      mov qword [rbx+8*"^(string_of_int minor)^"], rax
      mov rax, SOB_VOID_ADDRESS\n"

  and generate_setvfree_helper consts_tbl fvars_tbl env_size _var eps =
      let label = (find_label_in_fvars_tbl fvars_tbl _var) in
      ";generate set free param\n"^generate_helper consts_tbl fvars_tbl env_size  eps^"
      mov qword[" ^ label ^ "],rax
      mov rax, SOB_VOID_ADDRESS\n"

  and generate_seq_helper consts_tbl fvars_tbl env_size e_list =
    let _func = (fun acc expr -> acc ^ (generate_helper consts_tbl fvars_tbl env_size  expr)) in
    ";generate seq\n"^(List.fold_left _func "" e_list)

  and generate_or_helper consts_tbl fvars_tbl env_size or_list =
    let _ = (label_counter := !label_counter+1)in
    let current_label = "Lexit" ^ (string_of_int !label_counter) in
    let _func = (fun acc expr ->
                    (acc ^ (generate_helper consts_tbl fvars_tbl env_size  expr)^ "
                    cmp rax, SOB_FALSE_ADDRESS
                    jne " ^current_label^"\n")) in
    ";generate or\n"^(List.fold_left _func "" or_list)^current_label^":\n"

  and generate_if_helper consts_tbl fvars_tbl env_size test dif dit =
    let _ = (label_counter := !label_counter+1) in
    let current_label_lelse = "Lelse" ^ (string_of_int !label_counter) in
    let current_label_lexit = "Lexit" ^ (string_of_int !label_counter) in
    ";generate if\n"^(generate_helper consts_tbl fvars_tbl env_size  test)^ "
    cmp rax, SOB_FALSE_ADDRESS
    je "^current_label_lelse^"\n"^(generate_helper consts_tbl fvars_tbl env_size  dif)^ "
    jmp "^current_label_lexit^"\n"^current_label_lelse^":\n"^(generate_helper consts_tbl fvars_tbl env_size  dit)^current_label_lexit^":\n"

  and generate_box_helper consts_tbl fvars_tbl env_size x =
    let box_body =
    "MALLOC r8, WORD_SIZE
    mov qword [r8] , rax
    mov rax, r8\n" in
    ";generate box\n"^(generate_helper consts_tbl fvars_tbl env_size x) ^ box_body


  and generate_boxget_helper consts_tbl fvars_tbl env_size _var =
    ";generate box get\n"^(generate_helper consts_tbl fvars_tbl env_size _var) ^
    "mov rax, qword[rax]\n"

  and generate_boxset_helper consts_tbl fvars_tbl env_size _var eps =
    ";generate box set\n"^(generate_helper consts_tbl fvars_tbl env_size  eps) ^ "push rax\n" ^
    (generate_helper consts_tbl fvars_tbl env_size  _var) ^
    "pop qword[rax]
    mov rax, SOB_VOID_ADDRESS\n"

  and generate_define_helper consts_tbl fvars_tbl env_size _var _val =
   let var_string _var = match _var with | (VarFree(x)) -> x
                                         | _ -> raise X_no_match in
    ";generate define\n"^(generate_helper consts_tbl fvars_tbl env_size _val)^
    "mov qword[" ^ (find_label_in_fvars_tbl fvars_tbl (var_string _var)) ^ "], rax
    mov rax, SOB_VOID_ADDRESS\n"

  and generate_lambdasimple_helper consts_tbl fvars_tbl env_size param_list body =
   let _ = (label_counter := !label_counter+1) in

    let generate_lambdasimple_first_env consts_tbl fvars_tbl env_size param_list body =
      (*************** labels ***************)
      let current_label_counter = (string_of_int !label_counter) in
      let current_label_lcode = "Lcode" ^ current_label_counter ^ ":\n" in
      let current_label_lcont = "Lcont" ^current_label_counter ^ ":\n" in

      let lcode =
      current_label_lcode ^ "
        push rbp
        mov rbp, rsp\n" ^
        (generate_helper consts_tbl fvars_tbl (env_size+1) body) ^ "
        leave
        ret\n" ^
        current_label_lcont in

      let allocate_closure_object =
      "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode" ^ current_label_counter ^ ")
      jmp Lcont" ^ current_label_counter ^ "\n" ^
      lcode in

      ";generate lambda simple empty env\n"^
      allocate_closure_object ^
      ";end of generate lambda simple empty env\n" in

    let generate_lambdasimple_not_first_env consts_tbl fvars_tbl env_size param_list body =
      (*************** labels ***************)
      let current_label_counter = (string_of_int !label_counter) in
      let env_size_string = (string_of_int env_size) in
      let current_label_lcode = "Lcode" ^ current_label_counter ^ ":\n" in
      let current_label_lcont = "Lcont" ^ current_label_counter ^ ":\n" in
      let current_label_ext_env_start = "loop_ext_env" ^ current_label_counter in
      let current_label_ext_env_end = "end_loop_ext_env" ^ current_label_counter in
      let current_label_copy_params_start = "copy_params" ^ current_label_counter in
      let current_label_copy_params_end = "end_copy_params" ^ current_label_counter in

      (*************** end of labels ***************)

      let allocate_ext_env = "
      MALLOC rax," ^ string_of_int(8 * (env_size + 1)) ^ "
      mov rsi, rax
      mov rcx ,0 ; loop counter
      mov r10, qword[rbp + 8*2] ; old env \n" ^
      current_label_ext_env_start ^ ":
        cmp rcx," ^ env_size_string ^ "
        je " ^ current_label_ext_env_end ^ "
        mov r8, qword [r10 + 8 * rcx]
        mov qword[rsi+ 8 * (rcx +1)], r8
        inc rcx
        jmp " ^ current_label_ext_env_start ^  "\n" ^
      current_label_ext_env_end ^ ":\n" in

      let allocate_new_params =
      "mov r15, qword[rbp + 8*3] ; number of params
      inc r15 ; for magic
      shl r15, 3 ; mul * 8
      MALLOC rbx, r15 ; new param array
      mov qword [rsi], rbx
      mov r15, qword[rbp + 8*3] ; number of params
      inc r15\n
      mov rcx, 0 ; counter \n" ^
      current_label_copy_params_start ^":
        cmp rcx, r15
        je " ^ current_label_copy_params_end ^ "
        mov r11, qword [rbp + 8 * (4 + rcx)]
        mov qword [rbx + 8 * (rcx)], r11
        inc rcx
        jmp "^current_label_copy_params_start ^ "\n" ^
      current_label_copy_params_end^":\n" in

     let lcode =
      current_label_lcode ^ "
      push rbp
      mov rbp, rsp " ^
      (generate_helper consts_tbl fvars_tbl (env_size+1) body) ^"
      leave
      ret\n" ^
      current_label_lcont in

      let allocate_closure_object =
      "MAKE_CLOSURE(rax, rsi, Lcode" ^ current_label_counter ^ ")
      jmp Lcont" ^ current_label_counter ^ "\n" ^
      lcode in

      ";generate lambda simple not empty env\n"^
      allocate_ext_env ^
      allocate_new_params ^
      allocate_closure_object ^
      ";end of generate lambda simple not empty env\n" in

   if (env_size == 0) then generate_lambdasimple_first_env consts_tbl fvars_tbl env_size param_list body
                      else generate_lambdasimple_not_first_env consts_tbl fvars_tbl env_size param_list body

  and generate_lambdaopt_helper consts_tbl fvars_tbl env_size param_list param body =
    let _ = (label_counter := !label_counter+1) in

    let generate_lambdaopt_first_env consts_tbl fvars_tbl env_size param_list param body =
      (*************** labels ***************)
      let current_label_counter = (string_of_int !label_counter) in
      let current_label_lcode = "Lcode" ^ current_label_counter ^ ":\n" in
      let current_label_lcont = "Lcont" ^current_label_counter ^ ":\n" in
      let current_label_replace_magic_to_empty_lst = "replace_magic_to_empty_lst" ^ current_label_counter in
      let current_label_create_opt_list = "create_opt_list" ^ current_label_counter in
      let current_label_end_create_opt_list = "end_create_opt_list" ^ current_label_counter in
      let current_label_end_replace_magic_to_empty_lst = "end_replace_magic_to_empty_lst" ^ current_label_counter in


      let adjust_stack_for_opt_args =
        let param_list_count = (List.length param_list) in
        "mov rax, qword [rbp + 3*8] ; param number
        mov r9, rax
        ;check if there is args in 'd';
        sub rax, " ^ (string_of_int param_list_count) ^ "; rax = number of parms in optional lambda list
        cmp rax,0
        je " ^ current_label_replace_magic_to_empty_lst ^ "
        mov rdx, r9 ; counter
        mov rdi, rax
        mov r11, qword [rbp + 8*(3+rdx)] ; car = pointer to param list
        mov r12, SOB_NIL_ADDRESS ; cdr \n" ^
        current_label_create_opt_list ^ ":
        cmp rax, 0 ; number of optional params
        je " ^  current_label_end_create_opt_list ^ "
        MAKE_PAIR (rbx, r11,r12)
        dec rdx
        dec rax
        mov r12, rbx ; new cdr (pair)
        mov r11, qword [rbp + 8*(3+rdx)]; new car
        jmp " ^  current_label_create_opt_list ^ "\n" ^
        current_label_end_create_opt_list ^ ":
        mov qword[rbp+8* (4 +" ^(string_of_int param_list_count) ^ ")], rbx;  update stack with the new list
        jmp " ^ current_label_end_replace_magic_to_empty_lst ^"\n" ^
        current_label_replace_magic_to_empty_lst ^ ":
        mov r15, SOB_NIL_ADDRESS
        mov qword[rbp+8*(4+"^(string_of_int param_list_count)^")], r15 ; replace magic with nil\n" ^ "\n" ^
        current_label_end_replace_magic_to_empty_lst ^ ":\n" in

      let lcode =
      current_label_lcode ^ "\n" ^
      "push rbp
      mov rbp, rsp\n" ^
      adjust_stack_for_opt_args ^ "\n" ^
      (generate_helper consts_tbl fvars_tbl (env_size+1) body) ^ "
      leave
      ret\n" ^
      current_label_lcont in

      let allocate_closure_object =
      "MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, Lcode" ^ current_label_counter ^ ")
      jmp Lcont" ^ current_label_counter ^ "\n" ^
      lcode in

      ";generate lambda opt empty env\n" ^
      allocate_closure_object ^
      ";end of generate lambda opt empty env\n" in



    let generate_lambdaopt_not_first_env consts_tbl fvars_tbl env_size param_list param body =
      (*************** labels ***************)
      let current_label_counter = (string_of_int !label_counter) in
      let env_size_string = (string_of_int env_size) in
      let current_label_lcode = "Lcode" ^ current_label_counter ^ ":\n" in
      let current_label_lcont = "Lcont" ^ current_label_counter ^ ":\n" in
      let current_label_ext_env_start = "loop_ext_env" ^ current_label_counter in
      let current_label_ext_env_end = "end_loop_ext_env" ^ current_label_counter in
      let current_label_copy_params_start = "copy_params" ^ current_label_counter in
      let current_label_copy_params_end = "end_copy_params" ^ current_label_counter in
      let current_label_replace_magic_to_empty_lst = "replace_magic_to_empty_lst" ^ current_label_counter in
      let current_label_create_opt_list = "create_opt_list" ^ current_label_counter in
      let current_label_end_create_opt_list = "end_create_opt_list" ^ current_label_counter in
      let current_label_end_replace_magic_to_empty_lst = "end_replace_magic_to_empty_lst" ^ current_label_counter in


      (*************** end of labels ***************)

      let allocate_ext_env = "
      MALLOC rax," ^ string_of_int(8 * (env_size + 1)) ^ "
      mov rsi, rax
      mov rcx ,0 ; loop counter
      mov r10, qword[rbp + 8*2] ; old env \n" ^
      current_label_ext_env_start ^ ":
        cmp rcx," ^ env_size_string ^ "
        je " ^ current_label_ext_env_end ^ "
        mov r8, qword [r10 + 8 * rcx]
        mov qword[rsi+ 8 * (rcx +1)], r8
        inc rcx
        jmp " ^ current_label_ext_env_start ^  "\n" ^
      current_label_ext_env_end ^ ":\n" in

      let allocate_new_params =
      "mov r15, qword[rbp + 8*3] ; number of params

      inc r15 ;for magic \n
      shl r15, 3 ; mul * 8
      MALLOC rbx, r15 ; new param array
      mov qword [rsi], rbx
      mov r15, qword[rbp + 8*3] ; number of params
      inc r15 \n
      mov rcx, 0 ; counter \n" ^
      current_label_copy_params_start ^":
        cmp rcx, r15
        je " ^ current_label_copy_params_end ^ "
        mov r11, qword [rbp + 8 * (4 + rcx)]
        mov qword [rbx + 8 * (rcx)], r11
        inc rcx
        jmp "^current_label_copy_params_start ^ "\n" ^
      current_label_copy_params_end^":\n" in

    let adjust_stack_for_opt_args =
       let param_list_count = (List.length param_list) in
       " mov rax, qword [rbp + 3*8] ; param number
        mov r9, rax
       ;check if there is args in 'd';
        sub rax, " ^ (string_of_int param_list_count) ^ "; rax = number of parms in optional lambda list
        cmp rax,0
        je " ^ current_label_replace_magic_to_empty_lst ^ "
        mov rdx, r9 ; counter
        mov rdi, rax
        mov r11, qword [rbp + 8*(3+rdx)] ; car = pointer to param list
        mov r12, SOB_NIL_ADDRESS ; cdr \n" ^
        current_label_create_opt_list ^ ":
        cmp rax, 0
        je " ^  current_label_end_create_opt_list ^ "
        MAKE_PAIR (rbx, r11,r12)
        dec rdx
        dec rax
        mov r12, rbx ; new cdr (pair)
        mov r11, qword [rbp + 8*(3+rdx)]; new car
        jmp " ^  current_label_create_opt_list ^ "\n" ^
        current_label_end_create_opt_list ^ ":

        mov qword[rbp+8* (4 + " ^(string_of_int param_list_count)^ ")], rbx;  update stack with the new list
        jmp " ^ current_label_end_replace_magic_to_empty_lst^"\n" ^
        current_label_replace_magic_to_empty_lst ^ ":
        mov r15, SOB_NIL_ADDRESS
        mov qword[rbp+8*(4+"^(string_of_int param_list_count)^")], r15 ; replace magic with nil\n" ^ "\n"
        ^ current_label_end_replace_magic_to_empty_lst ^ ":\n"
      in

    let lcode =
    current_label_lcode ^ "\n " ^
    "push rbp
    mov rbp, rsp\n" ^
    adjust_stack_for_opt_args ^ "\n" ^
    (generate_helper consts_tbl fvars_tbl (env_size+1) body) ^"
    leave
    ret\n" ^
    current_label_lcont in

      let allocate_closure_object =
      "MAKE_CLOSURE(rax, rsi, Lcode" ^ current_label_counter ^ ")
      jmp Lcont" ^ current_label_counter ^ "\n" ^
      lcode in

      ";generate lambda opt not empty env\n"^
      allocate_ext_env ^
      allocate_new_params ^
      allocate_closure_object ^
      ";end of generate lambda opt not empty env\n" in


    if (env_size == 0) then generate_lambdaopt_first_env consts_tbl fvars_tbl env_size param_list param body
                        else generate_lambdaopt_not_first_env consts_tbl fvars_tbl env_size param_list param body

  and generate_applic_helper consts_tbl fvars_tbl env_size proc e_list =
    let n = (string_of_int (List.length e_list)) in
    let args = List.rev e_list in
    let end_applic =
    "add rsp , 8
    pop rbx
    shl rbx , 3
    add rsp, rbx
    add rsp, 8 ;end of generate applic\n" in

    let evaluate_args = if (List.length e_list) == 0
                        then ""
                        else (String.concat "push rax\n" (List.map (generate_helper consts_tbl fvars_tbl env_size) args))^"push rax\n" in
    let evaluate_proc = (generate_helper consts_tbl fvars_tbl env_size proc) in
    ";generate applic
     push SOB_NIL_ADDRESS\n"^
    evaluate_args ^"
    push "^n^"\n"^
    evaluate_proc^"
    push qword [rax+TYPE_SIZE]
    call [rax+TYPE_SIZE+WORD_SIZE] \n" ^ end_applic

  and generate_applictp_helper consts_tbl fvars_tbl env_size proc e_list =
    let n = (string_of_int (List.length e_list)) in
    let args = List.rev e_list in
    let evaluate_args = if (List.length e_list) == 0
                        then ""
                        else (String.concat "push rax\n" (List.map (generate_helper consts_tbl fvars_tbl env_size) args))^"push rax\n" in
    let evaluate_proc = (generate_helper consts_tbl fvars_tbl env_size proc) in
    ";generate applicTP\n
    push SOB_NIL_ADDRESS ; push magic\n" ^
    evaluate_args ^"
    push "^n^"\n"^
    evaluate_proc^"
    CLOSURE_ENV r13, rax
    push r13 ; push env
    ;push qword [rax+TYPE_SIZE] ; env
    push qword [rbp + 8 * 1] ; old ret addr
    ;fix stack
    mov r8, qword[rbp] ; save rbp for later

    SHIFT_FRAME " ^ (string_of_int ((List.length e_list) + 5)) ^"\n
    CLOSURE_CODE r13, rax
    mov rbp, r8
    jmp r13 ; jmp to closure code \n"
  ;;

  (*************************** Final Functions ***************************)

  let make_consts_tbl asts = (make_consts_tbl_helper [] asts);;
  let make_fvars_tbl asts = make_fvars_tbl_helper [] asts;;
  let generate consts_tbl fvar_tbl e = generate_helper consts_tbl fvar_tbl 0 e;;

  end;;