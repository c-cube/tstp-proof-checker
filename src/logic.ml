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

(** Types for first-order logic *)

(** A function or predicate symbol, or a quoted identifier *)
type symbol = string

(** A first order term *)
type term =
  | TVar of string
  | TNum of Num.num
  | TList of term list
  | TNode of symbol * term list

(** a first order formula *)
type formula =
  | FForall of term list * formula
  | FExists of term list * formula
  | FAnd of formula * formula
  | FOr of formula * formula
  | FImply of formula * formula
  | FEquiv of formula * formula
  | FNot of formula
  | FAtom of term
  | FEqual of term * term
  | FTrue
  | FFalse

type role = [ `Axiom | `Hypothesis | `Definition | `Assumption | `Lemma | `Derived
            | `Theorem | `Conjecture | `Negated_conjecture | `Plain | `Fi_domain
            | `Fi_functors | `Fi_predicates | `Type | `Unknown ]

(** Is the role an external input of the prover? *)
let input_role = function
  | `Axiom | `Hypothesis | `Definition | `Assumption -> true
  | _ -> false

type name = NameInt of int | NameString of string

let term_to_name = function
  | TNode (f, []) -> NameString f
  | TNum n when Num.is_integer_num n -> NameInt (Num.int_of_num n)
  | _ -> failwith "term is not a name"

let name_to_term = function
  | NameString f -> TNode (f, [])
  | NameInt i -> TNum (Num.num_of_int i)

(** a derivation step *)
type step = {
  step_name: name;                      (** unique index of the step *)
  step_role: role;                      (** role of the step *)
  step_formula: formula;                (** formula derived in this step *)
  step_annotation: term option;         (** annotation that justifies the formula *)
}

(*s term and formula constructors *)

let mk_var s = TVar s
let mk_int i = TNum (Num.num_of_int i)
let mk_num n = TNum n
let mk_list l = TList l
let mk_node f l = TNode (f, l)

let mk_forall vars f = match vars with | [] -> f | _ -> FForall (vars, f)
let mk_exists vars f = match vars with | [] -> f | _ -> FExists (vars, f)
let mk_and a b = match a, b with
  | FTrue, _ -> b | _, FTrue -> a | FFalse, _ | _, FFalse -> FFalse | _ -> FAnd (a, b)
let mk_or a b = match a, b with
  | FTrue, _ | _, FTrue -> FTrue | _, FFalse -> a | FFalse, _ -> b | _ -> FOr (a, b)
let mk_imply a b = FImply (a, b)
let mk_equiv a b = FEquiv (a, b)
let mk_xor a b = FNot (mk_equiv a b)
let mk_not a = match a with | FNot b -> b | FTrue -> FFalse | FFalse -> FTrue | _ -> FNot a
let mk_atom t = FAtom t
let mk_eq a b = FEqual (a, b)
let mk_true = FTrue
let mk_false = FFalse

(*s sets of terms, symbols and formula *)

module TSet = Set.Make(struct type t = term let compare=compare end)
module FSet = Set.Make(struct type t = formula let compare=compare end)
module SSet = Set.Make(struct type t = symbol let compare=compare end)

(*s maps of names *)

module NameMap = Map.Make(struct type t = name let compare=compare end)

(*s compute the signature, the set of predicate symbols... *)

(** Add symbols of the formula to the set *)
let rec formula_symbols set formula =
  match formula with
  | FForall (_, f) -> formula_symbols set f
  | FExists (_, f) -> formula_symbols set f
  | FAnd (a, b) | FOr (a, b) | FEquiv (a, b) | FImply (a, b) ->
    formula_symbols (formula_symbols set a) b
  | FNot f -> formula_symbols set f
  | FAtom t -> term_symbols set t
  | FEqual (a, b) -> term_symbols (term_symbols set a) b
  | FTrue | FFalse -> set
(** add symbols of the term to the set *)
and term_symbols set t = match t with
  | TVar _ | TNum _ -> set
  | TList l -> List.fold_left term_symbols set l
  | TNode (f,l) ->
    let set' = SSet.add f set in
    List.fold_left term_symbols set' l

(** check whether the formula is a clause *)
let rec is_clause formula = match formula with
  | FAtom _ | FTrue | FFalse | FEqual _
  | FNot (FAtom _) | FNot (FEqual _) | FNot FTrue -> true
  | FOr (a, b) -> is_clause a && is_clause b
  | FAnd _ | FForall _ | FExists _ | FNot _ | FEquiv _ | FImply _ -> false

(** extract literals from a clausal formula *)
let rec clause_lits formula =
  match formula with
  | FOr (a, b) -> clause_lits a @ clause_lits b
  | _ -> [formula]

(** convert a clause to fof *)
let clause_to_fof formula =
  let rec fvars vars t = match t with
  | TNum _ -> vars
  | TVar _ -> TSet.add t vars
  | TNode (_,l) | TList l -> List.fold_left fvars vars l
  and lit_fvars vars lit = match lit with
  | FTrue | FFalse -> vars
  | FAtom t -> fvars vars t
  | FEqual (a, b) -> fvars (fvars vars a) b
  | FForall (v, f) -> lit_fvars vars f  (* superset! *)
  | FExists (v, f) -> lit_fvars vars f
  | FNot a -> lit_fvars vars a
  | FAnd (a, b) | FOr (a, b) | FImply (a, b) | FEquiv (a, b) ->
    lit_fvars (lit_fvars vars a) b
  in
  let clause_fvars = List.fold_left lit_fvars TSet.empty (clause_lits formula) in
  (* quantify over all free variables *)
  if TSet.is_empty clause_fvars || not (is_clause formula)
    then formula
    else mk_forall (TSet.elements clause_fvars) formula

(** find the names used in the source of a step *)
let source_names step =
  let rec recurse acc annot = match annot with
  | TNode ("file", [_; TNode (name, [])]) -> (NameString name) :: acc
  | TNum n when Num.is_integer_num n -> (NameInt (Num.int_of_num n)) :: acc
  | TNode ("inference", [_; _; TList sources]) -> List.fold_left recurse acc sources
  | _ -> acc
  in
  match step.step_role, step.step_annotation with
  | role, _ when input_role role -> []
  | _, None -> failwith "derived formula has no annotation"
  | _, Some annot -> recurse [] annot

(*s pretty printing *)

let rec print_term formatter term = match term with
  | TVar s -> Format.fprintf formatter "%s" s
  | TNum n -> Format.fprintf formatter "%s" (Num.string_of_num n)
  | TNode (f, []) -> Format.fprintf formatter "%s" f
  | TNode (f, l) ->
    Format.fprintf formatter "%s(%a)" f (Utils.print_list print_term) l
  | TList l ->
    Format.fprintf formatter "%a" (Utils.print_list print_term) l

let rec print_formula ~cnf formatter formula =
  if cnf
    then begin
      assert (is_clause formula);
      let lits = clause_lits formula in
      Format.fprintf formatter "(%a)" (Utils.print_list ~sep:" | " (print_formula ~cnf:false)) lits
    end else match formula with
    | FForall (vars, f) ->
      Format.fprintf formatter "@[<h>![%a]:@] %a" (Utils.print_list print_term) vars
        (print_formula ~cnf) f
    | FExists (vars, f) ->
      Format.fprintf formatter "@[<h>?[%a]:@] %a" (Utils.print_list print_term) vars
        (print_formula ~cnf) f
    | FAnd (a, b) ->
      Format.fprintf formatter "(%a@ & %a)" (print_formula ~cnf) a (print_formula ~cnf) b
    | FOr (a, b) ->
      Format.fprintf formatter "(%a@ | %a)" (print_formula ~cnf) a (print_formula ~cnf) b
    | FImply (a, b) ->
      Format.fprintf formatter "(%a@ => %a)" (print_formula ~cnf) a (print_formula ~cnf) b
    | FEquiv (a, b) ->
      Format.fprintf formatter "(%a@ <=> %a)" (print_formula ~cnf) a (print_formula ~cnf) b
    | FTrue -> Format.pp_print_string formatter "$true"
    | FFalse -> Format.pp_print_string formatter "$false"
    | FNot (FEqual (a, b)) ->
      Format.fprintf formatter "@[<h>(%a != %a)@]" print_term a print_term b
    | FNot a -> Format.fprintf formatter "~%a" (print_formula ~cnf) a
    | FAtom t -> Format.fprintf formatter "@[<h>%a@]" print_term t
    | FEqual (a, b) ->
      Format.fprintf formatter "@[<h>(%a = %a)@]" print_term a print_term b

let print_role formatter role =
  Format.fprintf formatter "%s"
    (match role with
    | `Axiom -> "axiom"
    | `Hypothesis -> "hypothesis"
    | `Definition -> "definition"
    | `Assumption -> "assumption"
    | `Lemma -> "lemma"
    | `Theorem -> "theorem"
    | `Conjecture -> "conjecture"
    | `Negated_conjecture -> "negated_conjecture"
    | `Plain -> "plain"
    | `Derived -> "derived"
    | `Fi_domain -> "fi_domain"
    | `Fi_functors -> "fi_functor"
    | `Fi_predicates -> "fi_predicates"
    | `Type -> "type"
    | `Unknown -> "unknown")

let print_name formatter = function
  | NameInt i -> Format.fprintf formatter "%d" i
  | NameString s -> Format.fprintf formatter "%s" s

let print_step ?(prefix="") formatter step =
  (* convert to fof if needed *)
  let cnf = is_clause step.step_formula in
  let formula = if cnf then clause_to_fof step.step_formula else step.step_formula in
  match step.step_annotation with
  | None ->
    Format.fprintf formatter "@[<h>fof(%a, %a, @[<hv 2>%a@]).@]"
      print_name step.step_name print_role step.step_role
      (print_formula ~cnf:false) formula
  | Some annot ->
    Format.fprintf formatter "@[<h>fof(%a, %a, @[<hv 2>%a@], @[<h>%a@]).@]"
      print_name step.step_name print_role step.step_role
      (print_formula ~cnf:false) formula print_term annot
