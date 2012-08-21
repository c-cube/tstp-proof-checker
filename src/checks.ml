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

(** the module used to check proof steps and the proof structure itself *)

open Types
open Str

(** data useful to invoke a prover *)
class type prover_info =
  object
    method name : string                   (** name of the prover *)
    method command : string -> string      (** how to build a command to call the prover on a file *)
    method success : regexp                (** how to detect the success in the prover's output *)
  end

let prover_E = 
  object
    method name = "E"
    method command = "eprover --cpu-limit=10 -tAuto -xAuto -l0 --tstp-in"
    method success = regexp_case_fold "SZS Status Theorem"
  end

let prover_SPASS =
  object
    method name = "SPASS"
    method command = "SPASS -TPTP -TimeLimit 10 -Stdin"
    method success = regexp_case_fold "Proof found"
  end

(** list of known provers (TODO parse it from a config file?) *)
let default_provers = [prover_E; prover_SPASS]

(** print the proof obligation for the given step to the formatter *)
let print_proof_obligation formatter proof step_name =
  let goal_step = M.find step_name proof in
  (* all the steps used as premisses *)
  let premise_steps = List.map
    (fun name -> M.find name proof)
    (Utils.source_names goal_step) in
  (* print all premisses as axioms, and goal as conjecture *)
  List.iter
    (fun premise ->
      let premise = { premise with step_role=RoleAxiom; step_annotation=None} in
      Format.fprintf formatter "@[<h>%a@]@." (Utils.print_step ~prefix:"ax") premise)
    premise_steps;
  Format.fprintf formatter "@[<hov 4>fof(%s, %s,@ @[<h>%a@]).@]@."
    (Utils.print_name ~prefix:"goal" goal_step.step_name) "negated_conjecture"
    (Utils.print_formula ~cnf:false) (Not (Utils.clause_to_fof goal_step.step_formula))

(** open a fifo and convert it to a pair of channels *)
let make_channels (o,  i) =
  Unix.in_channel_of_descr o, Unix.out_channel_of_descr i

(** close the channels *)
let close_channels (o, i) =
  Unix.close (Unix.descr_of_in_channel o);
  Unix.close (Unix.descr_of_out_channel i)

(** slurp the entire content of the in_channel into a list of lines *)
let slurp_lines input =
  let lines = ref [] in
  let rec next_line () =
    try
      let line = input_line input in
      lines := line :: !lines;
      Format.printf "read line %s@." line;
      next_line ()
    with End_of_file -> !lines
  in next_line ()

(** check a proof step using a prover *)
let check_step prover derivation step_name =
  let step = M.find step_name derivation in
  match step.step_role with
  | RoleAxiom -> Success (prover#name, step_name)
  | RoleDerived ->
  (* start the prover *)
  let o1, i1 = Unix.pipe ()
  and o2, i2 = Unix.pipe () in
  if !debug > 0
    then Format.printf "run prover %s on step %s@." prover#name (Utils.print_name step_name);
  let pid = Unix.create_process "/bin/sh" [|prover#command|] o1 i2 i2 in
  let output, input = make_channels (o2, i1) in
  let in_formatter = Format.formatter_of_out_channel input in
  (* send derivation obligation to the prover *)
  print_proof_obligation in_formatter derivation step_name;
  print_proof_obligation Format.std_formatter derivation step_name;
  Format.pp_print_flush in_formatter ();
  flush input;
  (* wait for the prover to finish *)
  let lines = slurp_lines output in
  ignore (Unix.waitpid [] pid);
  Format.printf "prover %s on step %s is done.@." prover#name (Utils.print_name step_name);
  Unix.close o1;
  Unix.close i1;
  Unix.close o2;
  Unix.close i2;
  (* analyse output after the prover is done *)
  if List.exists
    (fun line -> try ignore (Str.search_forward prover#success line 0); true
                 with Not_found -> false) lines
    then Success (prover#name, step_name)
    else Failure (prover#name, step_name)

(** sequential check of steps *)
let check_all ?provers derivation =
  (* provers used to check steps *)
  let provers = match provers with
  | None -> default_provers
  | Some provers -> provers
  in
  let validated_proof = new validated_proof derivation in
  M.fold
    (fun step_name _ validated_proof ->
      (* check the step using all provers *)
      List.fold_left
        (fun validated_proof prover ->
          (* check step using this prover *)
          let result = check_step prover derivation step_name in
          validated_proof#add_result result)
        validated_proof provers)
    derivation validated_proof

(** check that the derivation is a DAG with axiom leaves *)
let derivation_is_dag derivation =
  (* recursive check *)
  let rec recurse step_name =
    try
      let step = M.find step_name derivation in
      if step.step_role = RoleAxiom then true else
      (* check premises *)
      List.for_all recurse (Utils.source_names step)
    with Not_found ->
      Format.printf "step %s not found@." (Utils.print_name step_name);
      false (* step not present *)
  in
  M.for_all (fun step_name _ -> recurse step_name) derivation

(** structural check of a validated_proof *)
let check_structure validated_proof =
  (* list of steps that contain $false *)
  let falses = M.fold
    (fun step_name step acc ->
      match step.step_formula with
      | Not True -> step_name :: acc
      | _ -> acc)
    validated_proof#derivation [] in
  if falses = [] then failwith "no $false found in proof" else
  (* function that checks that all steps up to axioms are well formed *)
  let rec check_step_rec step_name =
    let step = M.find step_name validated_proof#derivation in
    match step.step_role with
    | RoleAxiom -> true
    | RoleDerived ->
      let _, check_results = validated_proof#results_for step_name in
      let step_ok = List.for_all is_success check_results in
      let premises = Utils.source_names step in
      let premises_ok = List.for_all check_step_rec premises in
      step_ok && premises_ok
  in
  List.exists check_step_rec falses
