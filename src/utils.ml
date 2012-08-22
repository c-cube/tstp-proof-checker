(*
tstp-proof-checker : a simple OCaml proof checker for TSTP derivations
Copyright (C) 2012 Simon Cruanes

This is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301 USA.
*)

(** utils to manipulate types, steps, etc. *)

open Types

(** name of the file being parsed *)
let cur_filename = ref ""

(** check whether the formula is a clause *)
let rec is_clause formula = match formula with
  | Atom _ | True | Equal _
  | Not (Atom _) | Not (Equal _) | Not True -> true
  | Or (a, b) -> is_clause a && is_clause b
  | And _ | Forall _ | Exists _ | Not _ -> false

(** extract literals from a clausal formula *)
let rec clause_lits formula =
  assert (is_clause formula);
  match formula with
  | Or (a, b) -> clause_lits a @ clause_lits b
  | _ -> [formula]

(** convert a clause to fof *)
let clause_to_fof formula =
  assert (is_clause formula);
  let rec fvars vars t = match t with
  | Leaf _ ->  vars
  | Var s -> if List.mem t vars then vars else t::vars
  | Node l -> List.fold_left fvars vars l
  and lit_fvars vars lit = match lit with
  | True -> vars
  | Atom t -> fvars vars t
  | Equal (a, b) -> fvars (fvars vars a) b
  | Not a -> lit_fvars vars a
  | _ -> assert false in
  let clause_fvars = List.fold_left lit_fvars [] (clause_lits formula) in
  (* quantify over all free variables *)
  if clause_fvars = [] then formula else Forall (clause_fvars, formula)

(** find the names used in the source of a step *)
let source_names step =
  let rec recurse acc annot = match annot with
  | AnnotFile (_, name) -> name :: acc
  | AnnotName name -> name :: acc
  | AnnotInference(_, annots) -> List.fold_left recurse acc annots
  in
  match step.step_role, step.step_annotation with
  | RoleAxiom, _-> []
  | RoleDerived, None -> failwith "derived formula has no annotation"
  | RoleDerived, Some annot -> recurse [] annot

(** build a proof from a list of steps *)
let make_derivation steps =
  List.fold_left (fun der step -> M.add step.step_name step der) M.empty steps

open Format

(** powerful sprintf *)
let sprintf format =
  let buffer = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buffer in
  Format.kfprintf
    (begin fun fmt ->
    Format.pp_print_flush fmt ();
    let s = Buffer.contents buffer in
    Buffer.clear buffer;
    s
    end)
  fmt
  format

let rec print_list ?(sep=", ") print_elem formatter l = match l with
  | [] -> ()
  | [x] -> print_elem formatter x
  | x::l' ->
    fprintf formatter "%a%s@,%a" print_elem x sep
      (print_list ~sep print_elem) l'

let rec print_term formatter term = match term with
  | Leaf s -> fprintf formatter "%s" s
  | Var s -> fprintf formatter "%s" s
  | Node (hd::tl) ->
    fprintf formatter "@[%a(%a)@]" print_term hd (print_list print_term) tl
  | Node [] -> assert false (* bad term *)

let rec print_formula ~cnf formatter formula =
  if cnf
    then begin
      assert (is_clause formula);
      let lits = clause_lits formula in
      fprintf formatter "(%a)" (print_list ~sep:" | " (print_formula ~cnf:false)) lits
    end else match formula with
    | Forall (vars, f) ->
      fprintf formatter "@[<h>![%a]:@] %a" (print_list print_term) vars
        (print_formula ~cnf) f
    | Exists (vars, f) ->
      fprintf formatter "@[<h>?[%a]:@] %a" (print_list print_term) vars
        (print_formula ~cnf) f
    | And (a, b) ->
      fprintf formatter "(%a & %a)" (print_formula ~cnf) a (print_formula ~cnf) b
    | Or (a, b) ->
      fprintf formatter "(%a | %a)" (print_formula ~cnf) a (print_formula ~cnf) b
    | True -> pp_print_string formatter "$true"
    | Not True -> pp_print_string formatter "$false"
    | Not (Equal (a, b)) ->
      fprintf formatter "(%a != %a)" print_term a print_term b
    | Not a -> fprintf formatter "~%a" (print_formula ~cnf) a
    | Atom t -> print_term formatter t
    | Equal (a, b) ->
      fprintf formatter "(%a = %a)" print_term a print_term b


let rec print_name ?(prefix="") = function
  | IntName i -> prefix ^ (string_of_int i)
  | StringName s -> prefix ^ s
and print_annotation ?(prefix="") = function
  | AnnotFile (f, name) -> "file(" ^ f ^ ", " ^ (print_name ~prefix name) ^ ")"
  | AnnotName name -> print_name ~prefix name
  | AnnotInference (name, annots) ->
    sprintf "@[<h>inference(%s, [], [%a])@]" name (print_list ~sep:"," pp_print_string)
      (List.map (print_annotation ~prefix) annots)
and print_role = function
  | RoleAxiom -> "axiom"
  | RoleDerived -> "derived"

let print_step ?(prefix="") formatter step =
  (* convert to fof if needed *)
  let cnf = is_clause step.step_formula in
  let formula = if cnf then clause_to_fof step.step_formula else step.step_formula in
  match step.step_annotation with
  | None ->
    fprintf formatter "@[<hov 4>fof(%s, %s,@ @[<h>%a@]).@]"
      (print_name ~prefix step.step_name) (print_role step.step_role)
      (print_formula ~cnf:false) formula
  | Some annot ->
    fprintf formatter "@[<hov 4>fof(%s, %s,@ @[<h>%a@],@ %s).@]"
      (print_name ~prefix step.step_name) (print_role step.step_role)
      (print_formula ~cnf:false) formula (print_annotation annot)
