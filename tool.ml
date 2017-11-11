module Thm = struct
  type t = thm;;
  let compare th0 th1 =
    Pervasives.compare th0 th1;;
end;;
module dict_thm = Map.Make(Thm);;

let dest_trefl =
  function (Trefl(t,th)) -> t,th | _ -> failwith "dest_trefl: not a Trefl";;

let dest_ttrans =
  function (Ttrans(th1,th2,th3)) -> th1,th2,th3 | _ -> failwith "dest_ttrans: not a Ttrans";;

let dest_tmk_comb =
  function (Tmk_comb(th1,th2,th3)) -> th1,th2,th3 | _ -> failwith "dest_tmk_comb: not a Tmk_comb";;

let dest_tabs =
  function (Tabs(t,th1,th2)) -> t,th1,th2 | _ -> failwith "dest_tabs: not a Tabs";;

let dest_tbeta =
  function (Tbeta(t,th)) -> t,th | _ -> failwith "dest_tbeta: not a Tbeta";;

let dest_tassume =
  function (Tassume(t,th)) -> t,th | _ -> failwith "dest_tassume: not a Tassume";;

let dest_teq_mp =
  function (Teq_mp(th1,th2,th3)) -> th1,th2,th3 | _ -> failwith "dest_teq_mp: not a Teq_mp";;

let dest_tdeduct_antisym_rule =
  function (Tdeduct_antisym_rule(th1,th2,th3)) -> th1,th2,th3 | _ -> failwith "dest_tdeduct_antisym_rule: not a Tdeduct_antisym_rule";;

let dest_tinst_type =
  function (Tinst_type(typl,th1,th2)) -> typl,th1,th1 | _ -> failwith "dest_tinst_type: not a Tinst_type";;

let dest_tinst =
  function (Tinst(tpl,th1,th2)) -> tpl,th1,th2 | _ -> failwith "dest_tinst: not a Tinst";;

let thm_of_record tt =
  match tt with
    Trefl(_,th) -> th
  | Ttrans(_,_,th) -> th
  | Tmk_comb(_,_,th) -> th
  | Tabs(_,_,th) -> th
  | Tbeta(_,th) -> th
  | Tassume(_,th) -> th
  | Teq_mp(_,_,th) -> th
  | Tdeduct_antisym_rule(_,_,th) -> th
  | Tinst_type(_,_,th) -> th
  | Tinst(_,_,th) -> th;;

type graph =
  | Leaf of thm * string * term
  | Lemma of thm
  | Uabs of thm * term * graph ref
  | Uinst of thm * (term * term) list * graph ref
  | Uinst_type of thm * (hol_type * hol_type) list * graph ref
  | Binary of thm * string * graph ref * graph ref;;

let thm_of_node node =
  match node with
    Leaf(th,_,_) -> th
  | Lemma(th) -> th
  | Uabs(th,_,_) -> th
  | Uinst(th,_,_) -> th
  | Uinst_type(th,_,_) -> th
  | Binary(th,_,_,_) -> th;;

(* Minimum size-node tree: BFS *)
let build_tree_v3 t_list thh =
  let no_sloop tt =
    match tt with
    | Trefl(_,_) | Tbeta(_,_) | Tassume(_,_) -> true
    | Tabs(_,th1,th2) | Tinst(_,th1,th2) | Tinst_type(_,th1,th2) -> not (equals_thm th1 th2)
    | Ttrans(th1,th2,th3) | Tmk_comb(th1,th2,th3) | Teq_mp(th1,th2,th3) | Tdeduct_antisym_rule(th1,th2,th3)
      -> not (equals_thm th1 th3) && not (equals_thm th2 th3) in
  let rec remove_all t_list th =
    match t_list with
      (h::t) -> let tmp = remove_all t th in
                if equals_thm th (thm_of_record h) then tmp
                else h::tmp
    | [] -> [] in
  let t_list = filter no_sloop t_list in
  let rec find_lemma t_list th_list =
    match t_list with
      (h::t) -> begin match h with
                | Trefl(_,th) | Tbeta(_,th) | Tassume(_,th)
                  -> find_lemma t (insert th th_list)
                | Tabs(_,th1,th2) | Tinst(_,th1,th2) | Tinst_type(_,th1,th2)
                  -> if mem th1 th_list then find_lemma t (insert th2 th_list)
                     else insert th1 (find_lemma t (insert th1 (insert th2 th_list)))
                | Ttrans(th1,th2,th3) | Tmk_comb(th1,th2,th3) | Teq_mp(th1,th2,th3) | Tdeduct_antisym_rule(th1,th2,th3)
                  -> if mem th1 th_list then
                       if mem th2 th_list then find_lemma t (insert th3 th_list)
                       else insert th2 (find_lemma t (insert th2 (insert th3 th_list)))
                     else
                      if mem th2 th_list then insert th1 (find_lemma t (insert th1 (insert th3 th_list)))
                      else insert th1 (insert th2 (find_lemma t (insert th1 (insert th2 (insert th3 th_list)))))
                end
    | [] -> ([]:thm list) in
  let lemmas = setify (find_lemma t_list ([]:thm list)) in
  let t_list = setify t_list in
  if mem thh lemmas then Lemma(thh) else
    let th_to_node = ref [] in
    let th_to_size = ref [] in
    let rec assign_lemma lemmas =
      match lemmas with
        (h::t) -> th_to_node := (h,Lemma(h))::(!th_to_node); th_to_size := (h,1)::(!th_to_size); assign_lemma t
      | [] -> () in
    let res = assign_lemma lemmas in
    let null_node = Lemma(thh) in
    let rec view t_list =
      match t_list with
        (h::t) -> let prev_node,prev_size = view t in begin
                    match h with
                      Trefl(t,th) -> Leaf(th,"refl",t), 1
                    | Tbeta(t,th) -> Leaf(th,"beta",t), 1
                    | Tassume(t,th) -> Leaf(th,"assume",t), 1
                    | Tabs(t,th1,th2) -> begin try let node' = assoc th1 !th_to_node in let size' = assoc th1 !th_to_size in
                                                 if size'+1 < prev_size then Uabs(th2,t,ref node'), size'+1
                                                 else prev_node, prev_size
                                               with Failure _ -> prev_node, prev_size end
                    | Tinst(tpl,th1,th2) -> begin try let node' = assoc th1 !th_to_node in let size' = assoc th1 !th_to_size in
                                                      if size'+1 < prev_size then Uinst(th2,tpl,ref node'), size'+1
                                                      else prev_node, prev_size
                                                  with Failure _ -> prev_node, prev_size end
                    | Tinst_type(typl,th1,th2) -> begin try let node' = assoc th1 !th_to_node in let size' = assoc th1 !th_to_size in
                                                            if size'+1 < prev_size then Uinst_type(th2,typl,ref node'), size'+1
                                                            else prev_node, prev_size
                                                        with Failure _ -> prev_node, prev_size end
                    | Ttrans(th1,th2,th3) -> begin try let node' = assoc th1 !th_to_node in let size' = assoc th1 !th_to_size in
                                                       let node'' = assoc th2 !th_to_node in let size'' = assoc th2 !th_to_size in
                                                       if size'+size''+1 < prev_size then Binary(th3,"trans",ref node',ref node''), size'+size''+1
                                                       else prev_node, prev_size
                                                   with Failure _ -> prev_node, prev_size end
                    | Tmk_comb(th1,th2,th3) -> begin try let node' = assoc th1 !th_to_node in let size' = assoc th1 !th_to_size in
                                                         let node'' = assoc th2 !th_to_node in let size'' = assoc th2 !th_to_size in
                                                         if size'+size''+1 < prev_size then Binary(th3,"mk_comb",ref node',ref node''), size'+size''+1
                                                         else prev_node, prev_size
                                                     with Failure _ -> prev_node, prev_size end
                    | Teq_mp(th1,th2,th3) -> begin try let node' = assoc th1 !th_to_node in let size' = assoc th1 !th_to_size in
                                                       let node'' = assoc th2 !th_to_node in let size'' = assoc th2 !th_to_size in
                                                       if size'+size''+1 < prev_size then Binary(th3,"eq_mp",ref node',ref node''), size'+size''+1
                                                       else prev_node, prev_size
                                                   with Failure _ -> prev_node, prev_size end
                    | Tdeduct_antisym_rule(th1,th2,th3) -> begin try let node' = assoc th1 !th_to_node in let size' = assoc th1 !th_to_size in
                                                                     let node'' = assoc th2 !th_to_node in let size'' = assoc th2 !th_to_size in
                                                                     if size'+size''+1 < prev_size then Binary(th3,"deduct_antisym_rule",ref node',ref node''), size'+size''+1
                                                                     else prev_node, prev_size
                                                                 with Failure _ -> prev_node, prev_size end
                  end
      | [] -> null_node, 1000000000 in
  let rec f t_list =
    let node,size = view t_list in let th = thm_of_node node in
    if equals_thm thh th then node else begin
      th_to_node := (th,node)::(!th_to_node); 
      th_to_size := (th,size)::(!th_to_size);
      f (remove_all t_list th) end in
  f t_list;;

(*
let achiv t =
  match t with
    Trefl(_,th) -> th
  | Ttrans(_,_,th) -> th
  | Tmk_comb(_,_,th) -> th
  | Tabs(_,_,th) -> th
  | Tbeta(_,th) -> th
  | Tassume(_,th) -> th
  | Teq_mp(_,_,th) -> th
  | Tdeduct_antisym_rule(_,_,th) -> th
  | Tinst_type(_,_,th) -> th
  | Tinst(_,_,th) -> th;;

let f ls =
  let oc = open_out "out" in
  let rec print_thm_list oc lst =
    match lst with
      (h::t) -> Printf.fprintf oc "%s\n" (string_of_thm h); print_thm_list oc t
    | [] -> () in
  print_thm_list oc ls;
  close_out oc;;
*)
