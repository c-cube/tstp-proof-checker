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
    then
      let lits = clause_lits formula in
      fprintf formatter "(%a)" (print_list ~sep:" | " (print_formula ~cnf:false)) lits
    else match formula with
    | Forall (vars, f) ->
      fprintf formatter "@[<h>![%a]@] %a" (print_list print_term) vars
        (print_formula ~cnf) f
    | Exists (vars, f) ->
      fprintf formatter "@[<h>?[%a]@] %a" (print_list print_term) vars
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


let rec print_name = function
  | IntName i -> string_of_int i
  | StringName s -> s
and print_annotation = function
  | AnnotFile (f, name) -> "file(" ^ f ^ ", " ^ (print_name name) ^ ")"
  | AnnotName name -> print_name name
  | AnnotInference (name, annots) ->
    sprintf "@[<h>inference(%s, [], [%a])@]" name (print_list ~sep:"," pp_print_string)
      (List.map print_annotation annots)
and print_role = function
  | RoleAxiom -> "axiom"
  | RoleDerived -> "derived"

let print_step formatter step =
  let cnf = is_clause step.step_formula in
  let kind = if cnf then "cnf" else "fof" in
  match step.step_annotation with
  | None ->
    fprintf formatter "@[<hov 4>%s(%s, %s,@ @[<h>%a@]).@]" kind
      (print_name step.step_name) (print_role step.step_role)
      (print_formula ~cnf) step.step_formula
  | Some annot ->
    fprintf formatter "@[<hov 4>%s(%s, %s,@ @[<h>%a@],@ %s).@]" kind
      (print_name step.step_name) (print_role step.step_role)
      (print_formula ~cnf) step.step_formula (print_annotation annot)
