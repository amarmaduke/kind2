(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

open Lib
open TypeLib

module Solver = SolverMethods.Make(SMTSolver.Make(SMTLIBSolver))

module Actlit = struct

  (* Translates the hash of a term into a string .*)
  let string_of_term term = string_of_int (Term.tag term)

  (* Creates a positive actlit as a UF. *)
  let generate term =
    let string =
      String.concat "" [ "actlit_" ; string_of_term term ]
    in
    UfSymbol.mk_uf_symbol string [] (Type.mk_bool ())

end

let actlit_from_term = Actlit.generate

let term_of_actlit actlit = Term.mk_uf actlit []

(* Returns true if the property is not falsified or valid. *)
let shall_keep trans (s,_) =
  match TransSys.get_prop_status trans s with
  | TransSys.PropInvariant
  | TransSys.PropFalse _ -> false
  | _ -> true

(* Check-sat and splits properties.. *)
let split trans solver k falsifiable to_split actlits =

  (* Function to run if sat. *)
  let if_sat () =
    (* Get-model function. *)
    let get_model = Solver.get_model solver in
    (* Getting the model. *)
    let model = TransSys.vars_of_bounds trans k k
                |> get_model in
    (* Extracting the counterexample. *)
    let cex =
      TransSys.path_from_model trans get_model k in
    (* Evaluation function. *)
    let eval term =
      Eval.eval_term (TransSys.uf_defs trans) model term
      |> Eval.bool_of_value in
    (* Splitting properties. *)
    let new_to_split, new_falsifiable =
      List.partition
        ( fun (_, term) ->
          Term.bump_state k term |> eval )
        to_split in
    (* Building result. *)
    Some (new_to_split, (new_falsifiable, cex))
  in

  (* Function to run if unsat. *)
  let if_unsat () =
    None
  in

  (* Check sat assuming with actlits. *)
  Solver.check_sat_assuming solver if_sat if_unsat actlits

(* Splits its input list of properties between those that can be
   falsified and those that cannot after asserting the actlit
   implications. *)
let split_closure trans solver k actlits to_split =

  let rec loop falsifiable list =
    (* Building negative term. *)
    let term =
      list
      |> List.map snd
      |> Term.mk_and |> Term.mk_not |> Term.bump_state k in
    (* Getting actlit for it. *)
    let actlit = actlit_from_term term in
    (* Declaring actlit. *)
    actlit |> Solver.declare_fun solver ;
    (* Asserting implication. *)
    Term.mk_or
        [ actlit |> term_of_actlit |> Term.mk_not ; term ]
    |> Solver.assert_term solver ;
    (* All actlits. *)
    let all_actlits = (term_of_actlit actlit) ::  actlits in
    (* Splitting. *)
    match split trans solver k falsifiable list all_actlits with
    | None -> list, falsifiable
    | Some ([], new_falsifiable) ->
       [], new_falsifiable :: falsifiable
    | Some (new_list, new_falsifiable) ->
       loop (new_falsifiable :: falsifiable) new_list
  in

  loop [] to_split

(* Performs the next check after updating its context with new
   invariants and falsified properties. Assumes the solver is
   in the following state:

   actlit(prop) => prop@i
     for all 0 <= i <= k-2 and prop      in 'unknowns';

   invariant@i
     for all 0 <= i <= k and invariant in 'invariants';

   T[i-1,i]
     for all 1 <= i <= k.

   Note that the transition relation for the current iteration is
   already asserted. *)
let rec next (trans, solver, k, invariants, unknowns) =

  (* Asserts terms from 0 to k. *)
  let assert_new_invariants terms =
    terms
    |> Term.mk_and
    |> Term.bump_and_apply_k
         (Solver.assert_term solver) k
  in

  (* Asserts terms at k. *)
  let assert_old_invariants terms =
    terms
    |> Term.mk_and
    |> Term.bump_state k
    |> Solver.assert_term solver
  in

  (* Getting new invariants and valid / falsified properties. *)
  let new_invariants, new_valids, new_falsifieds =
    Event.recv () |> Event.update_trans_sys_tsugi trans
  in

  (* Cleaning unknowns by removing invariants and falsifieds. *)
  let nu_unknowns =
    match new_valids, new_falsifieds with
    | [], [] -> unknowns
    | _ -> unknowns |> List.filter (shall_keep trans)
  in

  match nu_unknowns with
  | [] ->
     Stat.bmc_stop_timers ();
     Stat.smt_stop_timers ();
     Solver.delete_solver solver |> ignore

  | _ ->
     let k_int = Numeral.to_int k in

     (* Notifying framework of our progress. *)
     Stat.set k_int Stat.bmc_k ;
     Event.progress k_int ;
     Stat.update_time Stat.bmc_total_time ;

     (* Merging old and new invariants and asserting them. *)
     let nu_invariants =
       match invariants, new_invariants with
       | [],[] -> []
       | _, [] ->
          assert_old_invariants invariants ;
          invariants
       | [], _ ->
          assert_new_invariants new_invariants ;
          new_invariants
       | _ ->
          assert_old_invariants invariants ;
          assert_new_invariants new_invariants ;
          List.rev_append new_invariants invariants
     in

     (* Building the positive actlits and corresponding implications
        at k-1. *)
     let actlits, implications =
       nu_unknowns
       |> List.fold_left
            ( fun (actlits,implications) (_,term) ->
              (* Building the actlit. *)
              let actlit_term =
                actlit_from_term term |> term_of_actlit
              in

              (* Appending it to the list of actlits. *)
              actlit_term :: actlits,
              (* Building the implication and appending. *)
              (Term.mk_or [
                   Term.mk_not actlit_term ;
                   Term.bump_state Numeral.(k-one) term
              ]) :: implications )
            ([], [])
     in

     (* Asserting implications if k > 0. *)
     if Numeral.(k > zero) then
       implications
       |> Term.mk_and
       |> Solver.assert_term solver ;

     (* Splitting. *)
     let unfalsifiable, falsifiable =
       split_closure trans solver k actlits nu_unknowns
     in

     (* Broadcasting k-true properties. *)
     unfalsifiable
     |> List.iter
          ( fun (s, _) ->
            Event.prop_status
              (TransSys.PropKTrue (Numeral.to_int k))
              trans
              s ) ;

     (* Broadcasting falsified properties. *)
     falsifiable
     |> List.iter
          ( fun (p, cex) ->
            List.iter
              ( fun (s,_) ->
                Event.prop_status
                  (TransSys.PropFalse cex) trans s )
              p ) ;

     (* Asserting transition relation for next iteration. *)
     TransSys.trans_of_bound trans Numeral.(k + one)
     |> Solver.assert_term solver
     |> ignore ;     

     (* Looping. *)
     next (trans, solver, Numeral.(k+one), nu_invariants, unfalsifiable)

(* Initializes the solver for the first check. *)
let init trans =
  (* Starting the timer. *)
  Stat.start_timer Stat.bmc_total_time;

  (* Getting properties. *)
  let unknowns =
    (TransSys.props_list_of_bound trans Numeral.zero)
  in

  (* Creating solver. *)
  let solver =
    TransSys.get_logic trans
    |> Solver.new_solver ~produce_assignments:true
  in

  (* Declaring uninterpreted function symbols. *)
  TransSys.iter_state_var_declarations
    trans
    (Solver.declare_fun solver) ;

  (* Declaring positive actlits. *)
  List.iter
    (fun (_, prop) ->
     actlit_from_term prop
     |> Solver.declare_fun solver)
    unknowns ;

  (* Defining functions. *)
  TransSys.iter_uf_definitions
    trans
    (Solver.define_fun solver) ;

  (* Asserting init. *)
  TransSys.init_of_bound trans Numeral.zero
  |> Solver.assert_term solver
  |> ignore ;

  (trans, solver, Numeral.zero, [], unknowns)

(* Runs the base instance. *)
let run trans =
  init trans |> next


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

