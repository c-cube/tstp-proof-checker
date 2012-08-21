/*
This file is part of the first order theorem prover Darwin
Copyright (C) 2006  The University of Iowa

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/


%{

  (** TSTP parser *)

  open Types

  (* includes from input *)
  let include_files: string list ref =
    ref []

%}
  
%token LEFT_PARENTHESIS
%token RIGHT_PARENTHESIS
%token LEFT_BRACKET
%token RIGHT_BRACKET
%token DOT
%token NEGATION
%token COLON
%token COMMA
%token EQUALITY
%token DISEQUALITY
%token EOI
%token FOF
%token CNF
%token THF
%token INCLUDE
%token INFERENCE
%token FILE
%token <string> SINGLE_QUOTED
%token <string> DOLLAR_WORD
%token <string> DOLLAR_DOLLAR_WORD
%token <string> DISTINCT_OBJECT
%token <string> LOWER_WORD
%token <string> UPPER_WORD
%token <string> UNSIGNED_INTEGER
%token <string> SIGNED_INTEGER
%token <string> REAL
%token DOLLAR_TRUE
%token DOLLAR_FALSE
%token DOLLAR
%token AND
%token OR
%token FORALL
%token EXISTS
%token BIJECTION
%token LEFT_IMPLICATION
%token RIGHT_IMPLICATION
%token UNKNOWN

%start parse_file
%type <Types.step list * string list> parse_file

%%

/* start rules */

parse_file:
  | file EOI 
      {
        let formulas = $1 in
        let includes = !include_files in

        (* reset for next parser run *)
        include_files := [];

        formulas, includes
      }

  | EOI
      { print_endline "empty problem specification";
        raise Types.PARSE_ERROR }


/* parse rules */



file:
  | tptp_input
      { match $1 with
        | Some formula -> [formula]
        | None        -> []
      }

  | tptp_input file
      { match $1 with
        | Some formula -> formula :: $2
        | None         -> $2
      }

tptp_input:
  | annotated_formula
      { Some $1 }

  | include_
      { None }



annotated_formula:
  | fof_annotated
      { $1 }

  | cnf_annotated
      { $1 }

  | thf_annotated
      { $1 }

thf_annotated:
  | THF LEFT_PARENTHESIS name COMMA formula_role COMMA
    fof_formula annotations RIGHT_PARENTHESIS DOT
    { failwith "Parser_tptp: tfh syntax not supported." }

fof_annotated:
  | FOF LEFT_PARENTHESIS name COMMA formula_role COMMA
    fof_formula annotations RIGHT_PARENTHESIS DOT
    {
      {
        step_name = $3;
        step_role = $5;
        step_formula = $7;
        step_annotation = $8;
      }
    }

fof_formula:
  | binary_formula
    { $1 }

  | unitary_formula
    { $1 }


binary_formula:
  | nonassoc_binary
    { $1 }

  | assoc_binary
    { $1 }

nonassoc_binary:
  | unitary_formula binary_connective unitary_formula
    { $2 $1 $3 }

binary_connective:
  | BIJECTION
    { fun x y -> And ((Or ((Not x), y)), (Or (x, (Not y)))) }
  | LEFT_IMPLICATION
    { fun x y -> Or ((Not x), y) }
  | RIGHT_IMPLICATION
    { fun x y -> Or (x, (Not y)) }
  | UNKNOWN
    { raise Types.UNKNOWN_SYMBOL }
  | NEGATION OR
    { fun x y -> Not (Or (x, y)) }
  | NEGATION AND
    { fun x y -> Not (And (x, y)) }

assoc_binary:
  | or_formula
    { $1 }
  | and_formula
    { $1 }

or_formula:
  | unitary_formula OR more_or_formula
    { Or ($1, $3) }

more_or_formula:
  | unitary_formula
    { $1 }
  | unitary_formula OR more_or_formula
    { Or ($1, $3) }

and_formula:
  | unitary_formula AND more_and_formula
    { And ($1, $3) }

more_and_formula:
  | unitary_formula
    { $1 }
  | unitary_formula AND more_and_formula
    { And ($1, $3) }

unitary_formula:
  | quantified_formula
    { $1 }
  | unary_formula
    { $1 }
  | LEFT_PARENTHESIS fof_formula RIGHT_PARENTHESIS
    { $2 }
  | atomic_formula
    { $1 }

quantified_formula:
  | quantifier LEFT_BRACKET variable_list RIGHT_BRACKET
    COLON unitary_formula
    { $1 $3 $6 }

quantifier:
  | FORALL
    { fun vars t -> Forall (vars, t) }
  | EXISTS
    { fun vars t -> Exists (vars, t) }

variable_list:
  | variable
    { [$1] }
  | variable COMMA variable_list
    { $1 :: $3 }

unary_formula:
  | unary_connective unitary_formula
    { $1 $2 }

unary_connective:
  | NEGATION
    { fun t -> Not t }


cnf_annotated:
  | CNF LEFT_PARENTHESIS name COMMA formula_role COMMA
    cnf_formula annotations RIGHT_PARENTHESIS DOT
      {
        (* let filename = !Utils.cur_filename in *)
        {
          step_name = $3;
          step_role = $5;
          step_formula = $7;
          step_annotation = $8;
        }
      }

formula_role:
  | LOWER_WORD
    { match $1 with 
      | "axiom" -> RoleAxiom 
      | "derived" -> RoleDerived
      | _ -> failwith ("unknown formula role "^$1) }

annotations:
  | null
      { None }
  | COMMA source
      { Some $2 }
  | COMMA source COMMA optional_info
      { Some $2 }



cnf_formula:
  | LEFT_PARENTHESIS disjunction RIGHT_PARENTHESIS
      { $2 }

  | disjunction
      { $1 }

disjunction:
  | literal
      { $1 }

  | literal OR disjunction
      { Or ($1, $3) }




literal:
  | atomic_formula
      { $1 }

  | NEGATION atomic_formula
      { Not $2 }

atomic_formula:
  | plain_atom
      { $1 }

  | defined_atom
      { $1 }

  | system_atom
      { $1 }

plain_atom:
  | plain_term_top
      { Atom $1 }

arguments:
  | term
      { [ $1 ] }

  | term COMMA arguments
      { $1 :: $3 }

defined_atom:
  | DOLLAR_TRUE
      { True }

  | DOLLAR_FALSE
      { Not True }

  | term EQUALITY term
      { Equal ($1, $3) }
  | term DISEQUALITY term
      { Not (Equal ($1, $3)) }

system_atom:
  | system_term_top
      { Atom $1 }

term:
  | function_term
      { $1 }

  | variable
      { $1 }

function_term:
  | plain_term
      { $1 }

  | defined_term
      { $1 }

  | system_term
      { $1 }

plain_term_top:
  | constant
      { Leaf $1 }

  | functor_ LEFT_PARENTHESIS arguments RIGHT_PARENTHESIS
      { let subterms = $1 :: $3 in
        Node subterms
      }

plain_term:
  | constant
      { Leaf $1 }

  | functor_ LEFT_PARENTHESIS arguments RIGHT_PARENTHESIS
      { let subterms = $1 :: $3 in
        Node subterms
      }

constant:
  | atomic_word
      { $1 }

functor_:
  | atomic_word
      { Leaf $1 }

defined_term:
  | number
      { print_endline ("Parser_tptp: <defined_term: number> not supported: "
                      ^ $1);
        raise Types.PARSE_ERROR }

  | DISTINCT_OBJECT
      { print_endline ("Parser_tptp: <defined_term: distinct_object> not supported: " ^ $1);
        raise Types.PARSE_ERROR }

system_term_top:
  | system_constant
      { Leaf $1 }

  | system_functor LEFT_PARENTHESIS arguments RIGHT_PARENTHESIS
      { let subterms = (Leaf $1) :: $3 in
        Node subterms
      }

system_term:
  | system_constant
      { Leaf $1 }

  | system_functor LEFT_PARENTHESIS arguments RIGHT_PARENTHESIS
      { let subterms = (Leaf $1) :: $3 in
        Node subterms
      }

system_functor:
  | atomic_system_word
      { $1 }
      
system_constant:
  | atomic_system_word
      { $1 }



variable:
  | UPPER_WORD
      { Var $1 }

source:
  | FILE LEFT_PARENTHESIS file_name COMMA name RIGHT_PARENTHESIS
      { AnnotFile ($3, $5) }
  | INFERENCE LEFT_PARENTHESIS inference_name COMMA useful_info COMMA
    parent_info_list RIGHT_PARENTHESIS
      { AnnotInference ($3, $7) }
  | name 
      { AnnotName $1 }

parent_info_list:
  | LEFT_BRACKET source_list RIGHT_BRACKET
      { $2 }

source_list:
  | source
      { [$1] }
  | source COMMA source_list
      { $1 :: $3 }

inference_name:
  | LOWER_WORD
      { $1 }

optional_info:
  | useful_info
      { "" }

  | null
      { "" }

useful_info:
  | LEFT_BRACKET general_term_list RIGHT_BRACKET
      { $2 }
      

include_:
  | INCLUDE LEFT_PARENTHESIS file_name formula_selection RIGHT_PARENTHESIS DOT
      { include_files := $3 :: !include_files }

formula_selection:
  | COMMA LEFT_BRACKET name_list RIGHT_BRACKET
      { $3 }

  | null
      { [] }

name_list:
  | name
      { [$1] }

  | name COMMA name_list
      { $1 :: $3 }



general_term:
  | general_data
      { "" }

  | general_data COLON general_term
      { "" }

  | general_list
      { "" }

general_data:
  | atomic_word
      { "" }

  | atomic_word LEFT_PARENTHESIS general_arguments RIGHT_PARENTHESIS
      { "" }

  | number
      { "" }

  | DISTINCT_OBJECT
      { "" }

general_arguments:
  | general_term
      { [$1] }

  | general_term COMMA general_arguments
      { $1 :: $3 }

general_list:
  | LEFT_BRACKET RIGHT_BRACKET
      { [] }

  | LEFT_BRACKET general_term_list RIGHT_BRACKET
      { $2 }

general_term_list:
  | general_term
      { [$1] }

  | general_term COMMA general_term_list
      { $1 :: $3 }


name:
  | atomic_word
      { StringName $1 }

  | UNSIGNED_INTEGER
      { IntName (int_of_string $1) }

atomic_word:
  | LOWER_WORD
      { $1 }

  | SINGLE_QUOTED
      { $1 }

atomic_system_word:
  | DOLLAR_DOLLAR_WORD
      { $1 }

number:
  | REAL
      { $1 }

  | SIGNED_INTEGER
      { $1 }

  | UNSIGNED_INTEGER
      { $1 }

file_name:
  | SINGLE_QUOTED
      { let quoted = $1 in
        String.sub quoted 1 (String.length quoted - 2)
      }

null:
      { }

%%




