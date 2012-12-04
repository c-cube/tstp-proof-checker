(*
Zipperposition: a functional superposition prover for prototyping
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

(** main file, that parses arguments and check the proof *)

open Logic

let file = ref "stdin"

let print_problem = ref false

(** parse_args returns parameters *)
let parse_args () =
  (* options list *) 
  let options =
    [ ("-debug", Arg.Set_int Utils.debug_level, "set debug level");
      ("-pp", Arg.Set print_problem, "print problem after parsing");
    ]
  in
  Arg.parse options (fun f -> file := f) "check the given TSTP derivation"

(** parse given tptp file *)
let parse_file ~recursive f =
  (* [aux files steps] parses all files in files and add
     the resulting proof steps to clauses *)
  let rec aux files steps = match files with
  | [] -> steps
  | f::tail ->
    let new_steps, new_includes = parse_this f in
    if recursive
      then aux (List.rev_append new_includes tail) (List.rev_append new_steps steps)
      else (List.rev_append new_steps steps)
  (* parse the given file, raise exception in case of error *)
  and parse_this f =
    let input = match f with
    | "stdin" -> stdin
    | _ -> open_in f in
    try
      let buf = Lexing.from_channel input in
      Utils.cur_filename := f;
      Parser_tptp.parse_file Lexer_tptp.token buf
    with _ as e -> close_in input; raise e
  in aux [f] []

(** main entry point *)
let () =
  parse_args ();
  let steps = parse_file ~recursive:true !file in
  (if !print_problem
    then List.iter (Format.printf "@[<h>step %a@]@." (print_step ~prefix:"")) steps
    else Utils.debug 1 (lazy (Utils.sprintf "parsed file %s@.steps:@[<v>%a@]@." !file
                      (Utils.print_list ~sep:"" (print_step ~prefix:"")) steps)));
  let derivation = Checks.make_derivation steps in
  if not (Checks.derivation_is_dag derivation)
    then Format.printf "%% the derivation is not a DAG@.Failure.@."
    else
      Format.printf "%% the derivation is a DAG...@.";
      let validated_proof = Checks.check_all derivation in
      if Checks.check_structure validated_proof
        then Format.printf "%% checked steps form a valid proof.@.Success.@."
        else Format.printf "%% checked steps do not form a valid proof.@.Failure.@."
