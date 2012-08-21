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

(** a proof for a step *)
type derivation =
  | Axiom of string * string      (** file, name *)
  | Derived of string * int list  (** inference name, premises list *)

(** a derivation step *)
type step = {
  step_idx: int;                  (** unique index of the step *)
  step_formula: formula;          (** formula derived in this step *)
  step_derivation: derivation;    (** derivation that leads to the formula *)
}

(** type for maps of integers *)
module M = Map.Make(
  struct
    type t = int
    let compare = Pervasives.compare
  end)

(** a proof is a set of int-indexed steps *)
type proof = step M.t
