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

(** generic utils *)

open Format

let debug_level = ref 0

let debug level msg =
  if level <= !debug_level
    then (Format.print_string (Lazy.force msg);
          Format.print_newline ())


(** it's all in the name. *)
exception PARSE_ERROR
exception UNKNOWN_SYMBOL

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

(** pretty-print a list *)
let rec print_list ?(sep=", ") print_elem formatter l = match l with
  | [] -> ()
  | [x] -> print_elem formatter x
  | x::l' ->
    fprintf formatter "%a%s@,%a" print_elem x sep
      (print_list ~sep print_elem) l'

(*s utils for parsing *)

(** name of the file being parsed *)
let cur_filename = ref ""
