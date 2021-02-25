(* This file is part of the Kind 2 model checker.

   Copyright (c) 2021 by the Board of Trustees of the University of Iowa

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
(** Translation of type checked AST to intermediate node model
  
     @author Andrew Marmaduke *)

open Lib
open LustreReporting

module A = LustreAst
module G = LustreGlobals
module N = LustreNode
module I = LustreIdent
module X = LustreIndex

module C = TypeCheckerContext

let rec compile_decls ctx decls = 
  (* let nodes = List.map declaration_to_node decls in *)
  let free_constants = get_free_constants ctx in
  (* let state_var_bounds = Lib.todo __LOC__ in *)
  let pp = LustreIndex.pp_print_index_trie true Var.pp_print_var
  in
    List.iter (fun c -> Format.printf "%a@." pp c) free_constants;
    Lib.todo __LOC__

and build_state_var
  ?is_input
  ?is_const
  ?for_inv_gen
  ?(shadow = false)
  scope
  ident
  index
  state_var_type
  state_var_source
=
  (* Concatenate identifier and indexes *)
  let state_var_name = 
    (* Filter out array indexes *)
    let filter_index = function
      | X.ArrayVarIndex _ 
      | X.ArrayIntIndex _ -> false
      | X.RecordIndex _
      | X.TupleIndex _
      | X.ListIndex _
      | X.AbstractTypeIndex _ -> true
    in Format.asprintf "%a%a"
      (I.pp_print_ident true) ident
      (X.pp_print_index true)
      (List.filter filter_index index)
  in
  (* For each index add a scope to the identifier to distinguish the
     flattened indexed identifier from unindexed identifiers

     The scopes indicate the positions from the back of the string in
     the flattened identifier where a new index begins.

     The following indexed identifiers are all flattened to x_y_z, but
     we can distinguish them by their scopes:

     x_y_z  [] 
     x.y.z  [2;2]
     x.y_z  [4]
     x_y.z  [2]

  *)
  let flatten_scopes = X.mk_scope_for_index index in
  (* Create or retrieve state variable *)
  let state_var =
    (* TODO check this *)
    try
      StateVar.state_var_of_string
        (state_var_name,
          (List.map Ident.to_string (scope @ flatten_scopes)))
    with Not_found ->
      StateVar.mk_state_var
        ?is_input
        ?is_const
        ?for_inv_gen 
        state_var_name
        (scope @ flatten_scopes)
        state_var_type 
  in
  state_var

and compile_node_decl ctx pos i ext inputs outputs locals items contracts =
  let name = I.mk_string_ident i in
  let node_scope = name |> I.to_scope in
  let is_extern = ext
  and instance = StateVar.mk_state_var
    ~is_const:true
    (I.instance_ident |> I.string_of_ident false)
    (I.to_scope name @ I.reserved_scope)
    Type.t_int
  and init_flag = StateVar.mk_state_var
    (I.instance_ident |> I.string_of_ident false)
    (I.to_scope name @ I.reserved_scope)
    Type.t_bool
  and inputs =
    (** TODO: The documentation on lustreNode says that a single argument
      node should have a non-list index (a singleton index), but the old
      node generation code does not seem to honor that *)
    let over_inputs = fun (compiled_input) (pos, i, ast_type, clock, is_const) ->
      match clock with
      | A.ClockTrue ->
        
        let n = X.top_max_index compiled_input |> succ
        and ident = I.mk_string_ident i
        and index_types = compile_ast_type ctx ast_type in
        let over_indices = fun index index_type accum ->
          let state_var = build_state_var
            ~is_input:true
            ~is_const
            (node_scope @ I.user_scope)
            ident
            index
            index_type
            (Some N.Input)
          in X.add (X.ListIndex n :: index) state_var accum
        in X.fold over_indices index_types compiled_input
      | _ -> fail_at_position pos "Clocked node inputs not supported"
    in List.fold_left over_inputs X.empty inputs
  and oracles = Lib.todo __LOC__
  and outputs =
    (** TODO: The documentation on lustreNode does not state anything about
      the requirements for indices of outputs, yet the old code makes it
      a singleton index in the event there is only one index *)
    let over_outputs = fun (is_single) (compiled_output) (pos, i, ast_type, clock) ->
      match clock with
      | A.ClockTrue ->
        let n = X.top_max_index compiled_output |> succ
        and ident = I.mk_string_ident i
        and index_types = compile_ast_type ctx ast_type in
        let over_indices = fun index index_type accum ->
          let state_var = build_state_var
            ~is_input:false
            (node_scope @ I.user_scope)
            ident
            index
            index_type
            (Some N.Output)
          and index' = if is_single then index
            else X.ListIndex n :: index
          in X.add index' state_var accum
        in X.fold over_indices index_types compiled_output
      | _ -> fail_at_position pos "Clocked node outputs not supported"
    and is_single = List.length outputs = 1
    in List.fold_left (over_outputs is_single) X.empty outputs
  and locals = Lib.todo __LOC__
  and equations = Lib.todo __LOC__
  and calls = Lib.todo __LOC__
  and asserts = Lib.todo __LOC__
  and props = Lib.todo __LOC__
  and contract = Lib.todo __LOC__
  and is_main = Lib.todo __LOC__
  and is_function = Lib.todo __LOC__
  and state_var_source_map = Lib.todo __LOC__
  and oracle_state_var_map = Lib.todo __LOC__
  and state_var_expr_map = Lib.todo __LOC__
  and silent_contracts = Lib.todo __LOC__
  in let (node:N.t) = { name;
    is_extern;
    instance;
    init_flag;
    inputs;
    oracles;
    outputs;
    locals;
    equations;
    calls;
    asserts;
    props;
    contract;
    is_main;
    is_function;
    state_var_source_map;
    oracle_state_var_map;
    state_var_expr_map;
    silent_contracts
  } in node

and compile_declaration ctx = function
| A.TypeDecl (pos, type_rhs) -> Lib.todo __LOC__
| A.ConstDecl (pos, const_decl) -> Lib.todo __LOC__
| A.FuncDecl (pos, (i, ext, [], inputs, outputs, locals, items, contracts))
  -> Lib.todo __LOC__
| A.NodeDecl (pos, (i, ext, [], inputs, outputs, locals, items, contracts)) ->
  compile_node_decl ctx pos i ext inputs outputs locals items contracts
| A.ContractNodeDecl (pos, node_decl) -> Lib.todo __LOC__
| A.NodeParamInst (pos, _)
| A.NodeDecl (pos, _) ->
  fail_at_position pos "Parametric nodes are not supported"
| A.FuncDecl (pos, _) ->
  fail_at_position pos "Parametric functions are not supported"

and compile_ast_type ctx = function
  | A.TVar _ -> Lib.todo __LOC__
  | A.Bool _ -> X.singleton X.empty_index Type.t_bool
  | A.Int _ -> X.singleton X.empty_index Type.t_int
  | A.UInt8 _ -> X.singleton X.empty_index (Type.t_ubv 8)
  | A.UInt16 _ -> X.singleton X.empty_index (Type.t_ubv 16)
  | A.UInt32 _ -> X.singleton X.empty_index (Type.t_ubv 32)
  | A.UInt64 _ -> X.singleton X.empty_index (Type.t_ubv 64)
  | A.Int8 _ -> X.singleton X.empty_index (Type.t_bv 8)
  | A.Int16 _ -> X.singleton X.empty_index (Type.t_bv 16)
  | A.Int32 _ -> X.singleton X.empty_index (Type.t_bv 32)
  | A.Int64 _ -> X.singleton X.empty_index (Type.t_bv 64)
  | A.Real _ -> X.singleton X.empty_index Type.t_real
  | A.IntRange (pos, lbound, ubound) -> 
    (* TODO: Old code does subtyping here, currently missing *)
    (* TODO: This type should only be well-formed if bounds are constants 
      This should be done in the type checker *)
    Lib.todo __LOC__
  | A.EnumType (pos, enum_name, enum_elements) ->
      let ty = Type.mk_enum enum_name enum_elements in
      X.singleton X.empty_index ty
  | A.UserType (pos, ident) ->
    (* Type checker should guarantee a type synonym exists *)
    let ty = C.lookup_ty_syn ctx ident |> Option.get in
    compile_ast_type ctx ty
  | A.AbstractType (pos, ident) ->
    X.singleton [X.AbstractTypeIndex ident] Type.t_int
  | A.RecordType (pos, record_fields) ->
    let over_fields = fun a (_, i, t) ->
      let over_indices = fun j t a -> X.add (X.RecordIndex i :: j) t a in
      let compiled_record_field_ty = compile_ast_type ctx t in
      X.fold over_indices compiled_record_field_ty a
    in
    List.fold_left over_fields X.empty record_fields
  | A.TupleType (pos, tuple_fields) ->
    let over_fields = fun (i, a) t ->
      let over_indices = fun j t a -> X.add (X.TupleIndex i :: j) t a in
      let compiled_tuple_field_ty = compile_ast_type ctx t in
      succ i, X.fold over_indices compiled_tuple_field_ty a
    in
    List.fold_left over_fields (0, X.empty) tuple_fields |> snd
  | A.GroupType _ -> assert false
      (* Lib.todo "Trying to flatten group type. Should not happen" *)
  | A.ArrayType (pos, (type_expr, size_expr)) ->
    (* TODO: Should we check that array size is constant here or later?
      If the var_size flag is set, variable sized arrays are allowed
      otherwise we should fail and make sure they are constant *)
    Lib.todo __LOC__
  | A.TArr _ -> assert false
      (* Lib.todo "Trying to flatten function type. This should not happen" *)

and get_free_constants ctx =
  let const_ids = C.get_constant_store ctx
  and compile = fun x -> match x with
  | Some (id, ty) ->
    let ident = I.mk_string_ident id in
    (* [_expr] is only an AST identifier with a
      redundant identifier string and the position information *)
    let tyd = compile_ast_type ctx ty in
    let op = fun i t vt ->
      let state_var = build_state_var
        ?is_input:(Some false)
        ?is_const:(Some true)
        ?for_inv_gen:(Some true)
        I.user_scope
        ident
        i
        t
        None
      in
      let v = Var.mk_const_state_var state_var in
      X.add i v vt
    in
    Some (X.fold op tyd X.empty)
  | None -> None
  (* TODO: The typechecker marks free constants with an identifier expresion
    Should it be refactored to track an option instead? *)
  and is_free = fun (id, (expr, ty)) ->
    match expr with
    | A.Ident (_, id') ->
      if Stdlib.compare id id' = 0
      then Some (id, ty)
      else None
    | _ -> None
  in
    const_ids |> C.IMap.to_seq 
      |> (Seq.filter_map (fun x -> x |> is_free |> compile))
      |> List.of_seq

