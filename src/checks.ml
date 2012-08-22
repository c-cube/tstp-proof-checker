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
    method success = regexp_case_fold "Proof found"
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
let print_proof_obligation proof formatter step_name =
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
    (Utils.print_name ~prefix:"goal" goal_step.step_name) "conjecture"
    (Utils.print_formula ~cnf:false) (Utils.clause_to_fof goal_step.step_formula)

(** slurp the entire content of the file_descr into a string *)
let slurp i_chan =
  let buf_size = 1024
  and content = ref "" in
  let rec next () =
    let buf = String.make buf_size 'a' in
    try really_input i_chan buf 0 buf_size;
        content := !content ^ buf; next ()
    with End_of_file -> !content ^ buf
  in next ()

(** call a subprocess with given string as input, and get its output as a string *)
let popen argv input =
  let o1, i1 = Unix.pipe ()
  and o2, i2 = Unix.pipe () in
  match Unix.fork () with
  | 0 -> (* parent process *)
    Unix.close o1;
    Unix.close i2;
    let output_chan = Unix.out_channel_of_descr i1
    and input_chan = Unix.in_channel_of_descr o2 in
    (* send input to child *)
    set_binary_mode_out output_chan false;
    output_string output_chan input;
    flush output_chan;
    close_out output_chan;
    (* read output from child *)
    set_binary_mode_in input_chan false;
    let output = slurp input_chan in
    (* cleanup and return *)
    Unix.close o2;
    output
  | child_pid ->
    Unix.close i1;
    Unix.close o2;
    (* redirect stdin *)
    Unix.dup2 o1 Unix.stdin;
    Unix.dup2 i2 Unix.stdout;
    Unix.dup2 i2 Unix.stderr;
    Unix.close o1;
    Unix.close i2;
    (* exec subprocess *)
    Unix.execvp argv.(0) argv

(** check a proof step using a prover *)
let check_step prover derivation step_name =
  let step = M.find step_name derivation in
  match step.step_role with
  | RoleAxiom -> Success (prover#name, step_name)
  | RoleDerived ->
    let obligation = Utils.sprintf "%a" (print_proof_obligation derivation) step_name in
    (* run the prover *)
    if !debug > 1 then Format.printf "run prover %s on step %s (obligation %s)@." prover#name (Utils.print_name step_name) obligation;
    let output = popen [|"sh"; "-c"; "exec "^prover#command|] obligation in
    if !debug > 1 then Format.printf "prover %s on step %s is done (result %s).@." prover#name (Utils.print_name step_name) output;
    let result =
      if (try ignore (Str.search_forward prover#success output 0); true
        with Not_found -> false)
      then Success (prover#name, step_name)
      else Failure (prover#name, step_name)
    in
    (if !debug > 0 then match result with
      | Success _ -> Format.printf "success of %s with prover %s@." (Utils.print_name step_name) prover#name
      | Failure _ -> Format.printf "failure of %s with prover %s@." (Utils.print_name step_name) prover#name);
    result

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
