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

let debug msg = if false then Pp.msgnl msg

let feedback msg = Pp.msgnl (str "Info: " ++ msg)

let warning msg = Pp.msgerrnl (str "Warning: " ++ msg)

let error msg = Pp.msgerrnl (str "Error: " ++ msg)

module Data = struct
  type t = int Globnames.Refmap.t

  let empty = Globnames.Refmap.empty 

  let add gref d = 
    let n = try  Globnames.Refmap.find gref d with Not_found -> 0 in
    Globnames.Refmap.add gref (n+1) d

      (* [f gref n acc] *)
  let fold f d acc = Globnames.Refmap.fold f d acc
end

let add_identifier (x:Names.identifier)(d:Data.t) = 
  failwith 
    ("SearchDep does not expect to find plain identifiers :" ^
     Names.string_of_id x)

let add_sort (s:Term.sorts)(d:Data.t) = d

let add_constant (cst:Names.constant)(d:Data.t) =
  Data.add (Globnames.ConstRef cst) d

let add_inductive ((k,i):Names.inductive)(d:Data.t) =
  Data.add (Globnames.IndRef (k, i)) d

let add_constructor(((k,i),j):Names.constructor)(d:Data.t) =
  Data.add (Globnames.ConstructRef ((k,i),j)) d

let collect_long_names (c:Term.constr) (acc:Data.t) =
  let rec add c acc =
    match Term.kind_of_term c with
        Term.Rel _ -> acc
      | Term.Var x -> add_identifier x acc
      | Term.Meta _ -> assert false
      | Term.Evar _ -> assert false
      | Term.Sort s -> add_sort s acc
      | Term.Cast(c,_,t) -> add c (add t acc)
      | Term.Prod(n,t,c) -> add t (add c acc)
      | Term.Lambda(n,t,c) -> add t (add c acc)
      | Term.LetIn(_,v,t,c) -> add v (add t (add c acc))
      | Term.App(c,ca) -> add c (Array.fold_right add ca acc)
      | Term.Const cst -> add_constant (Univ.out_punivs cst) acc
      | Term.Ind i -> add_inductive (Univ.out_punivs i) acc
      | Term.Construct cnst -> add_constructor (Univ.out_punivs cnst) acc
      | Term.Case({Term.ci_ind=i},c,t,ca) ->
          add_inductive i (add c (add t (Array.fold_right add ca acc)))
      | Term.Fix(_,(_,ca,ca')) -> 
          Array.fold_right add ca (Array.fold_right add ca' acc)
      | Term.CoFix(_,(_,ca,ca')) -> 
          Array.fold_right add ca (Array.fold_right add ca' acc)
      | Term.Proj(p, c) ->
          add c acc
  in add c acc

exception NoDef of Globnames.global_reference

let collect_type_deps gref =
  match gref with
  | Globnames.VarRef _ -> assert false
  | Globnames.ConstRef cst ->
      let cb = Environ.lookup_constant cst (Global.env()) in
      let cl = match cb.Declarations.const_type with
        | Declarations.RegularArity t -> [t]
        | Declarations.TemplateArity _ -> [] in
      List.fold_right collect_long_names cl Data.empty
  | Globnames.IndRef _ | Globnames.ConstructRef (_,_) ->
    Data.empty

let collect_deps gref =
  match gref with
  | Globnames.VarRef _ -> assert false
  | Globnames.ConstRef cst ->
      let cb = Environ.lookup_constant cst (Global.env()) in
      let cl = match Global.body_of_constant_body cb with
         Some e -> [e]
	| None -> [] in
      let cl = match cb.Declarations.const_type with
        | Declarations.RegularArity t -> t::cl
        | Declarations.TemplateArity _ ->  cl in
      List.fold_right collect_long_names cl Data.empty
  | Globnames.IndRef i | Globnames.ConstructRef (i,_) -> 
      let _, indbody = Global.lookup_inductive i in
      let ca = indbody.Declarations.mind_user_lc in
        Array.fold_right collect_long_names ca Data.empty

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

let display_type_deps gref =
  let display d =
    let pp gr n s = Printer.pr_global gr ++ spc () ++ s in
    let ip = if is_prop gref then str "true" else str "false" in
    Pp.msgnl (Printer.pr_global gref ++ str " " ++ ip ++ str " [ " ++ ((Data.fold pp) d (str " ]")))
  in try let data = collect_type_deps gref in display data
  with NoDef gref ->
    Pp.msgerrnl (Printer.pr_global gref ++ str " has no value")

let display_deps gref =
  let display d =
    let pp gr n s = Printer.pr_global gr ++ spc () ++ s in
    let ip = if is_prop gref then str "true" else str "false" in
    Pp.msgnl (Printer.pr_global gref ++ str " " ++ ip ++ str " [ " ++ ((Data.fold pp) d (str " ]")))
  in try let data = collect_deps gref in display data
  with NoDef gref ->
    Pp.msgerrnl (Printer.pr_global gref ++ str " has no value")

let locate_mp_dirpath ref =
  let (loc,qid) = Libnames.qualid_of_reference ref in
  try Nametab.dirpath_of_module (Nametab.locate_module qid)
  with Not_found -> 
    Errors.user_err_loc 
      (loc,"",str "Unknown module" ++ spc() ++ Libnames.pr_qualid qid)

let get_dirlist_grefs dirlist =
  let selected_gref = ref [] in
  let select gref env constr = 
    if Search.module_filter (dirlist, false) gref env constr then 
    (debug (str "Select " ++ Printer.pr_global gref);
     selected_gref := gref :: !selected_gref)
  in 
    Search.generic_search None select;
    !selected_gref

let display_module_deps dirlist = 
  let grefs = get_dirlist_grefs dirlist in
  List.iter (fun gref -> display_deps gref) grefs

VERNAC COMMAND EXTEND Depends
| ["Depends" global(ref) ] -> [ display_deps (Nametab.global ref) ]
| ["TypeDepends" global(ref) ] -> [ display_type_deps (Nametab.global ref) ]
| ["ModuleDepends" reference_list(dl) ] -> [ display_module_deps (List.map locate_mp_dirpath dl) ]
END
