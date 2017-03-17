(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*            Derived from DpdGraph tools.                                    *)
(*   Copyright (C) 2009-2015 Anne Pacalet (Anne.Pacalet@free.fr)              *)
(*                       and Yves Bertot (Yves.Bertot@inria.fr)               *)
(*             ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~                                *)
(*        This file is distributed under the terms of the                     *)
(*         GNU Lesser General Public License Version 2.1                      *)
(*        (see the enclosed LICENSE file for mode details)                    *)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

DECLARE PLUGIN "depends"

open Pp

let debug msg = if false then Pp.msg_notice msg

let feedback msg = Pp.msg_notice (str "Info: " ++ msg)

let warning msg = Pp.msg_error (str "Warning: " ++ msg)

let error msg = Pp.msg_error (str "Error: " ++ msg)

module Data = struct
  type t = unit Globnames.Refmap.t

  let empty = Globnames.Refmap.empty 

  let add gref d = 
    Globnames.Refmap.add gref () d

  (* [f gref n acc] *)
  let fold f d acc = Globnames.Refmap.fold f d acc
end

let add_identifier (x:Names.identifier)(d:Data.t) = 
  failwith 
    (Printf.sprintf "Depends does not expect to find plain identifiers: %s" (Names.string_of_id x))

let add_sort (s:Term.sorts)(d:Data.t) = d

let add_constant (cst:Names.constant)(d:Data.t) =
  Data.add (Globnames.ConstRef cst) d

let add_inductive ((k,i):Names.inductive)(d:Data.t) =
  Data.add (Globnames.IndRef (k, i)) d

let collect_long_names (c:Term.constr) (acc:Data.t) =
  let rec add c acc =
    match Term.kind_of_term c with
        Term.Rel _ -> acc
      | Term.Var x -> add_identifier x acc
      | Term.Meta _ -> assert false
      | Term.Evar _ -> assert false
      | Term.Sort s -> add_sort s acc
      | Term.Cast (c,_,t) -> add c (add t acc)
      | Term.Prod (n,t,c) -> add t (add c acc)
      | Term.Lambda (n,t,c) -> add t (add c acc)
      | Term.LetIn (_,v,t,c) -> add v (add t (add c acc))
      | Term.App (c,ca) -> add c (Array.fold_right add ca acc)
      | Term.Const cst -> add_constant (Univ.out_punivs cst) acc
      | Term.Ind i -> add_inductive (Univ.out_punivs i) acc
      | Term.Construct cnst ->
	let (i,_) = Univ.out_punivs cnst in add_inductive i acc
      | Term.Case ({Term.ci_ind=i},c,t,ca) ->
        add_inductive i (add c (add t (Array.fold_right add ca acc)))
      | Term.Fix(_,(_,ca,ca')) -> 
        Array.fold_right add ca (Array.fold_right add ca' acc)
      | Term.CoFix(_,(_,ca,ca')) -> 
        Array.fold_right add ca (Array.fold_right add ca' acc)
      | Term.Proj(p, c) -> add c acc
  in add c acc

exception NoDef of Globnames.global_reference

let collect_type_deps gref =
  match gref with
  | Globnames.VarRef _ -> Data.empty
  | Globnames.ConstRef cst ->
    let cb = Environ.lookup_constant cst (Global.env ()) in
    (match cb.Declarations.const_type with
    | Declarations.RegularArity t -> collect_long_names t Data.empty
    | Declarations.TemplateArity _ -> Data.empty)
  | Globnames.IndRef _ -> Data.empty
  | Globnames.ConstructRef _ -> Data.empty

let collect_body_deps gref =
  match gref with
  | Globnames.VarRef _ -> Data.empty
  | Globnames.ConstRef cst ->
    let cb = Environ.lookup_constant cst (Global.env()) in
    (match Global.body_of_constant_body cb with
    | Some t -> collect_long_names t Data.empty
    | None -> Data.empty)
  | Globnames.IndRef i ->
      let _, indbody = Global.lookup_inductive i in
      let ca = indbody.Declarations.mind_user_lc in
      Array.fold_right collect_long_names ca Data.empty
  | Globnames.ConstructRef _ -> Data.empty

let is_opaque gref =
  match gref with
  | Globnames.VarRef _ -> false
  | Globnames.ConstRef cst ->
    let cb = Environ.lookup_constant cst (Global.env ()) in
    (match cb.Declarations.const_body with
    | Declarations.OpaqueDef _ -> true
    | _ -> false)
  | Globnames.IndRef _ | Globnames.ConstructRef _ -> false

let string_of_gref gref =
  match gref with
  | Globnames.VarRef _ -> ""
  | Globnames.ConstRef cst ->
    Names.string_of_kn (Names.canonical_con cst)
  | Globnames.IndRef (kn,_) ->
    Names.string_of_kn (Names.canonical_mind kn)
  | Globnames.ConstructRef _ -> ""

let is_prop gref =
  try
    let glob = Glob_term.GRef(Loc.ghost, gref, None) in
    let env = Global.env() in
    let sigma = Evd.from_env env in
    let sigma', c = Pretyping.understand_tcc env sigma glob in
    let sigma2 = Evarconv.consider_remaining_unif_problems env sigma' in
    let sigma3, nf = Evarutil.nf_evars_and_universes sigma2 in
    let pl, uctx = Evd.universe_context sigma3 in
    let env2 = Environ.push_context uctx (Evarutil.nf_env_evar sigma3 env) in
    let c2 = nf c in
    let t = Environ.j_type (Typeops.infer env2 c2) in
    let t2 = Environ.j_type (Typeops.infer env2 t) in
    Term.is_Prop t2
  with _ -> 
    begin
      warning (str "unable to determine the type of the type for ref");
      false
    end

let acc_gref gref () acc = 
  Printf.sprintf "\"%s\"" (string_of_gref gref) :: acc

let print_type_deps fmt gref delim =
  match gref with
  | Globnames.VarRef _  | Globnames.ConstructRef _ -> ()
  | Globnames.ConstRef _ | Globnames.IndRef _ ->
    let sdt = (Data.fold acc_gref) (collect_type_deps gref) [] in
    let s = Printf.sprintf
      "%s { \"name\": \"%s\", \"isProp\": %B, \"isOpaque\": %B, \"typeDepends\": [ %s ] }"
      !delim (string_of_gref gref) (is_prop gref) (is_opaque gref) (String.concat ", " sdt)
    in
    pp_with fmt (str s);
    delim := ",\n"

let print_all_deps fmt gref delim =
  match gref with
  | Globnames.VarRef _  | Globnames.ConstructRef _ -> ()
  | Globnames.ConstRef _ | Globnames.IndRef _ ->
    let sdt = (Data.fold acc_gref) (collect_type_deps gref) [] in
    let sdb = (Data.fold acc_gref) (collect_body_deps gref) [] in
    let s = Printf.sprintf
      "%s { \"name\": \"%s\", \"isProp\": %B, \"isOpaque\": %B, \"typeDepends\": [ %s ], \"bodyDepends\": [ %s ] }"
      !delim (string_of_gref gref) (is_prop gref) (is_opaque gref) (String.concat ", " sdt) (String.concat ", " sdb)
    in
    pp_with fmt (str s);
    delim := ",\n"

let locate_mp_dirpath ref =
  let (loc,qid) = Libnames.qualid_of_reference ref in
  try Nametab.dirpath_of_module (Nametab.locate_module qid)
  with Not_found -> 
    Errors.user_err_loc (loc, "", str "Unknown module " ++ Libnames.pr_qualid qid)

let get_dirlist_grefs dirlist =
  let selected_gref = ref [] in
  let select gref env constr =
    if Search.module_filter (dirlist, false) gref env constr then 
    (debug (str "Select " ++ Printer.pr_global gref);
     selected_gref := gref :: !selected_gref)
  in 
    Search.generic_search None select;
    !selected_gref

let buf = Buffer.create 1000

let formatter out =
  let fmt =
    match out with
    | Some oc -> Pp_control.with_output_to oc
    | None -> Buffer.clear buf; Format.formatter_of_buffer buf
  in
  Format.pp_set_max_boxes fmt max_int;
  fmt

VERNAC COMMAND EXTEND Depends CLASSIFIED AS QUERY
| [ "Depends" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    pp_with fmt (str "[\n");
    List.iter (fun r -> print_all_deps fmt (Nametab.global r) delim) rl;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "Depends" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    let delim = ref "" in
    pp_with fmt (str "[\n");
    List.iter (fun ref -> print_all_deps fmt (Nametab.global ref) delim) rl;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    close_out oc;
    feedback (str "wrote dependencies to file: " ++ str f)
  ]
| [ "TypeDepends" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    pp_with fmt (str "[\n");
    List.iter (fun r -> print_type_deps fmt (Nametab.global r) delim) rl;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "TypeDepends" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    let delim = ref "" in
    pp_with fmt (str "[\n");
    List.iter (fun ref -> print_type_deps fmt (Nametab.global ref) delim) rl;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    close_out oc;
    feedback (str "wrote type dependencies to file: " ++ str f)
  ]
| [ "ModuleDepends" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_all_deps fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "ModuleDepends" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_all_deps fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    close_out oc;
    feedback (str "wrote module dependencies to file: " ++ str f)
  ]
| [ "ModuleTypeDepends" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_type_deps fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "ModuleTypeDepends" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_type_deps fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    close_out oc;
    feedback (str "wrote module type dependencies to file: " ++ str f)
  ]
END
