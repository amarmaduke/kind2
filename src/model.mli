(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

module MIL : Map.S with type key = int list

(** Term or lambda expression *)
type value =
  | Term of Term.t
  | Lambda of Term.lambda
  | Map of Term.t MIL.t

(** A model is a list of variables and assignemnts *)
type t = value Var.VarHashtbl.t

(** A path is a map of state variables to assignments *)
type path = value list StateVar.StateVarHashtbl.t

(** Equality over values of model *)
val equal_value : value -> value -> bool

(** Offset of the variables at each step of a path. *)
val path_offset: Numeral.t

(** Pretty-print a value *)
val pp_print_value : ?as_type:Type.t -> Format.formatter -> value -> unit

(** Pretty-print a value in xml format *)
val pp_print_value_xml : ?as_type:Type.t -> Format.formatter -> value -> unit

(** Pretty-print a value in json format *)
val pp_print_value_json : ?as_type:Type.t -> Format.formatter -> value -> unit

(** Pretty-print a model *)
val pp_print_model : Format.formatter -> t -> unit

(** Pretty-print a path *)
val pp_print_path : Format.formatter -> path -> unit

(** Create a model of the given size *)
val create : int -> t

(** Create a path of the given size *)
val create_path : int -> path

(** Import a variable assignment from a different instance *)
val import_value : value -> value

(** Create a model of an association list *)
val of_list : (Var.t * value) list -> t

(** Return an association list with the assignments in the model *)
val to_list : t -> (Var.t * value) list

(** Return an association list with the assignments in the model *)
val path_to_list : path -> (StateVar.t * value list) list

(** Create a model of an association list *)
val path_of_list : (StateVar.t * value list) list -> path

(** Create a model of an association list *)
val path_of_term_list : (StateVar.t * Term.t list) list -> path

(** Convert a model to a path

    [path_from_model s m k] extracts from the model [m] a path of
    values for each of the state variables in [s] from the offset zero
    up to [k]. The lists of values for each state variable are of
    equal length. Values that are not defined in the model are filled
    with {!TermLib.default_of_type}. *)
val path_from_model : StateVar.t list -> t -> Numeral.t -> path

(** Return the length of the value paths 

    All value paths are of equal lengths. *)
val path_length : path -> int

(** Extract values at instant [k] from the path and return a model *)
val model_at_k_of_path : path -> Numeral.t -> t

(** Return a list of models, one for each step on the path *)
val models_of_path : path -> t list 

(** Return true if the predicate [p] applies at one step of the path *)
val exists_on_path : (t -> bool) -> path -> bool

(** Return true if the predicate [p] applies at each step of the path *)
val for_all_on_path : (t -> bool) -> path -> bool

(** Add [k] to offset of all variables in model *)
val bump_var : Numeral.t -> t -> t

(** Set offset of all variables in model to [k] *)
val set_var_offset : Numeral.t -> t -> t

(** Combine assignments of two models into one. If a variable has an
    assignment in both models, it gets the assignment in the second
    model. *)
val merge : t -> t -> t 

(** Combine assignments of two models into one as in {!merge}, but
    bump the variables in the second model by the given offset before
    merging. *)
val bump_and_merge : Numeral.t -> t -> t -> t 

(** Returns the bounds / dimension of the array value represented by the map in
    the model*)
val dimension_of_map : Term.t MIL.t -> int list

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
