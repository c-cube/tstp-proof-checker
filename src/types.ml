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

(** Types used in the proof checker *)

(** it's all in the name. *)
exception PARSE_ERROR
exception UNKNOWN_SYMBOL

(** A first order term *)
type term =
  | Leaf of string
  | Var of string
  | Node of term list

(** a first order formula *)
type formula =
  | Forall of term list * formula
  | Exists of term list * formula
  | And of formula * formula
  | Or of formula * formula
  | Not of formula
  | Atom of term
  | Equal of term * term
  | True

(** the (unique) name of a derivation step *)
type name = IntName of int | StringName of string
(** annotation for a step *)
and annotation =
  | AnnotFile of string * name                   (** file, name *)
  | AnnotName of name                            (** another step *)
  | AnnotInference of string * annotation list   (** inference name, premises list *)
(** role of a formula in a step *)
and role = RoleAxiom | RoleDerived

(** a derivation step *)
type step = {
  step_name: name;                      (** unique index of the step *)
  step_role: role;                      (** role of the step *)
  step_formula: formula;                (** formula derived in this step *)
  step_annotation: annotation option;   (** annotation that justifies the formula *)
}

(** type for maps of names to something *)
module M = Map.Make(
  struct
    type t = name
    let compare = Pervasives.compare
  end)

(** a proof is a set of name-indexed steps *)
type proof = step M.t
