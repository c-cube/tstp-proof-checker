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

open Logic
open Str

(** a derivation is a set of name-indexed steps *)
type derivation = step NameMap.t

let derivation_size d =
  let n = ref 0 in
  NameMap.iter (fun _ _ -> incr n) d;
  !n

let make_derivation steps =
  List.fold_left
    (fun der step -> NameMap.add step.step_name step der)
    NameMap.empty steps

(** result of checking the step: success or failure, with (prover, step name) *)
type check_result =
  | Unchecked of name           (** not checked, for some reason *)
  | Success of (string * name)
  | Failure of (string * name)

let check_result_name = function
  | Unchecked name
  | Success (_, name)
  | Failure (_, name) -> name

let is_success = function
  | Unchecked _ | Success _ -> true
  | Failure _ -> false

let is_failure res = not (is_success res)

(** a validated proof is a set of steps with associated check_results *)
class validated_proof derivation =
  object (self : 'a)
    val results : (name * check_result list) NameMap.t = NameMap.empty

    method derivation : derivation = derivation
    
    (** get the results for the given step *)
    method results_for step_name =
      try NameMap.find step_name results
      with Not_found -> (step_name, [])

    (** add a result for the given step *)
    method add_result result =
      let step_name = check_result_name result in
      let _, step_results = self#results_for step_name in
      ({< results = NameMap.add step_name (step_name, result::step_results) results >}
        :> 'a)
  end

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
    method success = regexp_case_fold "SZS status Theorem"
  end

let prover_SPASS =
  object
    method name = "SPASS"
    method command = "SPASS -TPTP -TimeLimit=10 -Stdin"
    method success = regexp_case_fold "Proof found"
  end

let prover_Zenon =
  object
    method name = "Zenon"
    method command = "zenon -itptp -p0 -max-time 10s -"
    method success = regexp_case_fold "PROOF-FOUND"
  end

(** list of known provers (TODO parse it from a config file?) *)
let default_provers = [prover_E; prover_SPASS]

(** print the proof obligation for the given step to the formatter *)
let print_proof_obligation proof formatter step_name =
  let goal_step = NameMap.find step_name proof in
  (* all the steps used as premisses *)
  let premise_steps = List.map
    (fun name -> NameMap.find name proof)
    (source_names goal_step) in
  (* print all premisses as axioms, and goal as conjecture *)
  List.iter
    (fun premise ->
      let premise = { premise with step_role= `Axiom; step_annotation=None} in
      Format.fprintf formatter "@[<h>%a@]@." (print_step ~prefix:"ax") premise)
    premise_steps;
  Format.fprintf formatter "@[<h>fof(goal%a, %s,@ @[<hv>%a@]).@]@."
    print_name goal_step.step_name "conjecture"
    (print_formula ~cnf:false) (clause_to_fof goal_step.step_formula)

(** slurp the entire content of the file_descr into a string *)
let slurp i_chan =
  let buf_size = 128 in
  let content = Buffer.create 120
  and buf = String.make 128 'a' in
  let rec next () =
    let num = input i_chan buf 0 buf_size in
    if num = 0
      then Buffer.contents content (* EOF *)
      else (Buffer.add_substring content buf 0 num; next ())
  in next ()

(** Call given command with given output, and return its output as a string *)
let popen cmd input =
  let from, into = Unix.open_process cmd in
  (* send input to the subprocess *)
  output_string into input;
  close_out into;
  (* read ouput from the subprocess *)
  let output = slurp from in
  (* wait for subprocess to terminate *)
  ignore (Unix.close_process (from, into));
  output

(** check a proof step using a prover *)
let check_step prover derivation step =
  let obligation = Utils.sprintf "%a" (print_proof_obligation derivation) step.step_name in
  (* run the prover *)
  Utils.debug 2 (lazy (Utils.sprintf "run prover %s on step %a (obligation %s)"
                 prover#name print_name step.step_name obligation));
  let cmd = prover#command in
  Utils.debug 3 (lazy (Utils.sprintf "command is %s, input is %s" cmd obligation));
  let output = popen cmd obligation in
  Utils.debug 2 (lazy (Utils.sprintf "prover %s on step %a is done (result %s)."
                 prover#name print_name step.step_name output));
  let result =
    if (try ignore (Str.search_forward prover#success output 0); true
      with Not_found -> false)
    then Success (prover#name, step.step_name)
    else Failure (prover#name, step.step_name)
  in
  let pp_result = if is_success result then "success" else "failure" in
  Utils.debug 1 (lazy (Utils.sprintf " ... %s of step %a with prover %s"
                 pp_result print_name step.step_name prover#name));
  result

let pp_progress num total =
  Format.printf "\r%% checking step %-5d on %5d" num total;
  Format.print_flush ()

(** sequential check of steps *)
let check_all ?provers derivation =
  let total = NameMap.cardinal derivation in
  (* provers used to check steps *)
  let provers = match provers with
  | None -> default_provers
  | Some provers -> provers
  in
  let validated_proof = new validated_proof derivation in
  let _, validated_proof = NameMap.fold
    (fun step_name _ (num, validated_proof) ->
      let step = NameMap.find step_name derivation in
      let results =
        match status step with
        | `input -> Utils.debug 1 (lazy (Utils.sprintf "* step %a is an input step" print_name step_name));
          [Unchecked step_name]
        | `cth -> Utils.debug 1 (lazy (Utils.sprintf "* step %a is a conjecture step" print_name step_name));
          [Unchecked step_name]
        | `esa -> Utils.debug 1 (lazy (Utils.sprintf "* step %a is an equisatisfiability step" print_name step_name))
        ; [Unchecked step_name]
        | `thm ->
          (* check the step using all provers *)
          (Utils.debug 1 (lazy (Utils.sprintf "* step %a is a derivation step" print_name step_name));
          List.map (fun prover -> check_step prover derivation step) provers)
        | `unknown -> Utils.debug 1 (lazy (Utils.sprintf "* step %a is unknown" print_name step_name));
          [Unchecked step_name]
      in
      (* integrate the results into the validated_proof *)
      pp_progress num total;
      let validated_proof = List.fold_left
        (fun validated_proof result -> validated_proof#add_result result)
        validated_proof results
      in num+1, validated_proof)
    derivation (1, validated_proof)
  in
  Format.printf "\n"; (* after the progress line *)
  validated_proof

module NameSet = Set.Make(struct type t = name let compare = compare end)

(** check that the derivation is a DAG with axiom leaves *)
let derivation_is_dag derivation =
  (* cache, to memoize which nodes have a DAG as dependencies *)
  let have_dag = ref NameSet.empty in
  (* recursive check *)
  let rec recurse explored step_name =
    try
      let step = NameMap.find step_name derivation in
      if NameSet.mem step_name explored
        then (Utils.debug 1 (lazy (Utils.sprintf "step %a depends on itself" print_name step_name)); false)
        else if NameSet.mem step_name !have_dag then true  (* already checked *)
        else
          let explored' = NameSet.add step_name explored in
          (* check premises, adding step_name to the set of explored steps *)
          let result = List.for_all (recurse explored') (source_names step) in
          (if result then have_dag := NameSet.add step_name !have_dag);
          result
    with Not_found ->
      Format.printf "step %a not found@." print_name step_name;
      false (* step not present *)
  (* check only if step contains 'false' *)
  and check_dag_from step_name = 
    let step = NameMap.find step_name derivation in
    match step.step_formula with
    | FFalse -> recurse NameSet.empty step_name  (* check DAG from the clause *)
    | _ -> true  (* do not start checking from this step *)
  in
  NameMap.for_all (fun step_name _ -> check_dag_from step_name) derivation

exception NoFalseFound  (** raised when no empty clause is found in the input *)

(** structural check of a validated_proof *)
let check_structure validated_proof =
  (* cache, to memoize which nodes have a correct structure *)
  let correct_structure = ref NameSet.empty in
  (* list of steps that contain $false *)
  let falses = NameMap.fold
    (fun step_name step acc ->
      match step.step_formula with
      | FFalse -> step_name :: acc
      | _ -> acc)
    validated_proof#derivation [] in
  if falses = [] then raise NoFalseFound else
  (* function that checks that all steps up to axioms are well formed *)
  let rec check_step_rec explored step_name =
    if NameSet.mem step_name explored then false (* cycle *)
    else if NameSet.mem step_name !correct_structure then true (* memoized *)
    else begin
      try
        let step = NameMap.find step_name validated_proof#derivation in
        match step.step_role with
        | role when input_role role -> true
        | _ ->
          let _, check_results = validated_proof#results_for step_name in
          (* not a derivation, or all provers agreed on success? *)
          let step_ok = List.for_all is_success check_results in
          let premises = source_names step in
          (* check premises recursively *)
          let explored' = NameSet.add step_name explored in
          let premises_ok = List.for_all (check_step_rec explored') premises in
          let result = step_ok && premises_ok in
          (if result then correct_structure := NameSet.add step_name !correct_structure);
          result
      with Not_found ->
        true
    end
  in
  (* is there an occurrence of $false that has a well-formed proof? *)
  List.exists (check_step_rec NameSet.empty) falses
