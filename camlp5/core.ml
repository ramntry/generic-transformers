(**************************************************************************
 *  Copyright (C) 2012-2014
 *  Dmitri Boulytchev (dboulytchev@math.spbu.ru), St.Petersburg State University
 *  Universitetskii pr., 28, St.Petersburg, 198504, RUSSIA
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301 USA
 *
 *  See the GNU Lesser General Public License version 2.1 for more details
 *  (enclosed in the file COPYING).
 **************************************************************************)

#load "pa_extend.cmo";;
#load "q_MLast.cmo";;

open List
open Printf
open Pcaml
open MLast
open Ploc
open Plugin

(** Simple utility functions, working with lists, tuples, and functions that are not available in
 *  the standard library.
 *
 *  Numeric suffix for names of these functions is the number of elements in a tuple or a number of
 *  arguments of functions with which they work. The return value can contain a different number of
 *  elements, or have a different arity.
 *)
let split3 list_of_tuples =
  List.fold_right (fun (a, b, c) (x, y, z) ->
    (a :: x, b :: y, c :: z)) list_of_tuples ([], [], [])

let split4 list_of_tuples =
  List.fold_right (fun (a, b, c, d) (x, y, z, u) ->
    (a :: x, b :: y, c :: z, d :: u)) list_of_tuples ([], [], [], [])

let split5 list_of_tuples =
  List.fold_right (fun (a, b, c, d, e) (x, y, z, u, v) ->
    (a :: x, b :: y, c :: z, d :: u, e :: v)) list_of_tuples ([], [], [], [], [])

let split6 list_of_tuples =
  List.fold_right (fun (a, b, c, d, e, f) (x, y, z, u, v, w) ->
    (a :: x, b :: y, c :: z, d :: u, e :: v, f :: w)) list_of_tuples ([], [], [], [], [], [])

let apply_to2 arg1 arg2 func = func arg1 arg2
let map2 func (e1, e2) = (func e1, func e2)

let snd3 (_, e2, _) = e2
let get3_3 (_, _, e3) = e3
let push4 (e1, e2, e3, e4) e = (e1, e2, e3, e4, e)
let insert2_2 e (e1, e2) = (e1, e, e2)
let unshift3 e (e1, e2, e3) = (e, e1, e2, e3)


let from_option_with_error loc = function
  | Some v -> v
  | _ -> oops loc "empty option (should not happen)"


(* Everywhere
 *     'parameter' stands for type parameter of some type (or class, or class type etc).
 *     'type' - currently being processed type declaration or its name etc.
 *     'type_decl' - Camlp5 record representing OCaml type declaration.
 *)

let name_of_type_decl loc type_decl : type_name =
  from_vaval loc (snd (from_vaval loc type_decl.tdNam))

let parameters_of_type_decl loc type_decl : parameter list =
  from_vaval loc type_decl.tdPrm
  |> map (fun (type_variable, _variance_flags) ->
      match from_vaval loc type_variable with
      | Some type_parameter -> type_parameter
      | None -> oops loc "wildcard type parameters not supported"
      )


(** Convert ctyp-expression in simplified and refined typ-expression, that contains information, needed by
 *  the framework in appropriate form. All original ctyp's preserved as first arguments of typ constructors.
 *)
let rec ctyp_to_typ_without_selfs ctyp : typ =
  match ctyp with
  | <:ctyp< ' $type_variable_name$ >> -> Variable (ctyp, type_variable_name)
  | <:ctyp< ( $list: ctyps$ ) >> -> Tuple (ctyp, map ctyp_to_typ_without_selfs ctyps)
  | (<:ctyp< $uid: module_or_type_name$ >> | <:ctyp< $lid: module_or_type_name$ >>) ->
      Instance (ctyp, [(* type arguments *)], [module_or_type_name])

  (* Type application case. Type expression ('a, 'b) t (or t 'a 'b in revised syntax) is representing by Camlp5 with
   *     TyApp (
   *       TyApp (
   *         TyLid "t",
   *         TyQuo "a"),
   *       TyQuo "b")
   *  (loc's (source location information, which is the first argument of every AST node) was omitted for clarity),
   *  so, convertion should be recursive. If any of type arguments of application is Arbitrary (unsupported type),
   *  the whole type expression is Arbitrary.
   *)
  | <:ctyp< $type_constructor$ $type_arg$ >> -> (
      match (ctyp_to_typ_without_selfs type_constructor, ctyp_to_typ_without_selfs type_arg) with
      | (_, Arbitrary _) -> Arbitrary ctyp
      | (Instance (_, type_args, qualified_name), arg) -> Instance (ctyp, type_args @ [arg], qualified_name)
      | _ -> Arbitrary ctyp
      )

  | <:ctyp< $qualified_path$ . $path_item$ >> -> (
      match map2 ctyp_to_typ_without_selfs (qualified_path, path_item) with
      | (Instance (_, [], qualified_name), Instance (_, [], [module_or_type_name])) ->
          Instance (ctyp, [], qualified_name @ [module_or_type_name])
      | _ -> Arbitrary ctyp
      )

  | _ -> Arbitrary ctyp


(** Check all type instances (type constructor applications) in typ-expression and find ones equal to
 *  current being processed type. Replace all of them with Self (see typ type defintion).
 *)
let rec find_selfs loc type_name type_parameters : typ -> typ = function
  | Instance (ctyp, type_args, qualified_name) as orig_typ when qualified_name = [type_name] ->
      begin try
        let params =
          type_args
          |> map (function
              | Variable (_, var_name) -> var_name
              | _ -> invalid_arg "Not a variable"
              )
        in
        if params = type_parameters
        then Self (ctyp, params, qualified_name)
        else oops loc "irregular types not supported"
      with Invalid_argument "Not a variable" -> orig_typ
      end
  | Tuple (ctyp, typs) ->
      Tuple (ctyp, map (find_selfs loc type_name type_parameters) typs)
  | typ -> typ


let ctyp_to_typ loc type_name type_parameters ctyp =
  ctyp
  |> ctyp_to_typ_without_selfs
  |> find_selfs loc type_name type_parameters

(** Recognize top level structure of type declaration and label it appropriately with polymorphic variant tag.
 * Convert all internals of that type declaration to typ-expression. Extract type name and list of type parameters.
 *)
let type_decl_to_description loc type_decl : (type_name * parameter list * [
      | `Variant of [> (* ! *)
            | `Constructor of string * typ list
            | `Tuple of typ list
            | `Type of typ
          ] list
      | `PolymorphicVariant of [> (* ! *)
            | `Constructor of string * typ list
            | `Type of typ
          ] list
      | `Record of (string * bool * typ) list
      | `Tuple of typ list
    ]) =
  let type_name = name_of_type_decl loc type_decl in
  let type_parameters = parameters_of_type_decl loc type_decl in
  let ctyp_to_my_typ = ctyp_to_typ loc type_name type_parameters in
  let recognize_top_level_and_convert_rest_to_typ type_definition =
    match type_definition with
    | <:ctyp< [ $list: constructors$ ] >> | <:ctyp< $_$ == $priv: _$ [ $list: constructors$ ] >> ->
        `Variant (
          constructors
          |> map (fun (loc, cname, cargs, d) ->
                  match d with
                  | None -> `Constructor (from_vaval loc cname, map ctyp_to_my_typ (from_vaval loc cargs))
                  | _    -> oops loc "unsupported constructor declaration"
                  )
        )

    | <:ctyp< [ = $list: variants$ ] >> ->
        let unsupported () = oops loc "unsupported polymorphic variant type constructor declaration" in
        `PolymorphicVariant (
          variants
          |> map (function
              | <:poly_variant< $typ$ >> -> (
                  match ctyp_to_my_typ typ with
                  | Arbitrary _ -> unsupported ()
                  | typ -> `Type typ
                  )
              | <:poly_variant< ` $cname$ >> -> `Constructor (cname, [])
              | <:poly_variant< ` $cname$ of $list: carg_ctyps$ >> ->
                  let carg_typs =
                    carg_ctyps
                    |> map (function
                        | <:ctyp< ( $list: tuple_elem_ctyps$ ) >> -> map ctyp_to_my_typ tuple_elem_ctyps
                        | ctyp -> [ctyp_to_my_typ ctyp]
                        )
                    |> flatten
                  in
                  `Constructor (cname, carg_typs)

              | _ -> unsupported ()
              )
        )

    | <:ctyp< { $list: fields$ } >> | <:ctyp< $_$ == $priv:_$ { $list: fields$ } >> ->
        let fields = map (fun (_, name, is_mutable, typ) -> (name, is_mutable, ctyp_to_my_typ typ)) fields in
        `Record fields

    | <:ctyp< ( $list: elem_ctyps$ ) >> ->
        `Tuple (map ctyp_to_my_typ elem_ctyps)

    (* TODO: It is not clear at all *)
    | ctyp -> (
        match ctyp_to_my_typ ctyp with
        | Arbitrary _ -> oops loc "unsupported type"
        | (Variable _ | Instance _ | Self _) as typ ->
            `Variant [
              match typ with
              | Variable (t, _) -> `Tuple [Tuple (<:ctyp< ( $list: [t]$ ) >>, [typ])]
              | _ -> `Type typ
            ]
        | _ -> oops loc "internal error: unrecognized tuple in type_decl_to_description, should not be"
        )
    in
    (type_name, type_parameters, recognize_top_level_and_convert_rest_to_typ type_decl.tdDef)


(** Return list of type case descriptions. Variant or polymorphic variant type has as many
 *  cases as constructors, tuple or record consist of one case - the tuple or record itself.
 *)
let type_case_descriptions description =
  match description with
  | (`Variant constructors | `PolymorphicVariant constructors) -> constructors
  | (`Tuple _ | `Record _) as tuple_or_record -> [tuple_or_record]


(** Get names of currently being processed types and types mentioned in polymorphic variant definitions.
 *  For descrs structure see comment to make_descrs function.
 *)
let involved_type_names descrs : type_name list =
  let processed_mut_rec_types = map fst descrs in
  descrs
  |> fold_left (fun acc (_, (_, description, _)) ->
       match description with
       | `PolymorphicVariant components ->
           components
           |> fold_left (fun local_acc typ ->
                match typ with
                | `Type (Instance (_, _, [type_name])) -> type_name :: local_acc
                | _ -> local_acc
                )
                acc
       | _ -> acc
       )
       processed_mut_rec_types


(** Returns piece of AST referred to a general catamorphism
 *  (in another words, a traversal function) for given qualified type name.
 *)
let generic_cata_for_qualified_name loc (is_one_of_processed_mut_rec_types : type_name -> bool) qualified_name =
  let module H = Plugin.Helper (struct let loc = loc end) in
  match qualified_name with
  | [type_name] when is_one_of_processed_mut_rec_types type_name ->
      <:expr< $lid: cata type_name$ >>
  | _ ->
      let gt_record = H.E.acc (map H.E.id qualified_name) in
      <:expr< $gt_record$.GT.gcata >>



module Names = struct
  (** Create a fresh (namespace : name_hint -> actual_name) which is an associative array of unique (with respect to given
   *  name_generator instance) actual names with name hints as array keys.
   *)
  let create_namespace (name_generator : < generate : string -> string; .. >) : string -> string =
    let new_namespace () =
      let already_generated_names = ref StringMap.empty in
      fun name_hint ->
        match StringMap.option_find name_hint !already_generated_names with
        | Some actual_name -> actual_name
        | None ->
            let actual_name = name_generator#generate name_hint in
            already_generated_names := StringMap.add name_hint actual_name !already_generated_names;
            actual_name
    in
    new_namespace ()


  (** Generate names for transformer classes.
   *)
  class transformer loc type_parameters =
    let generator = name_generator type_parameters in

    (** Generate names for type parameters.
     *)
    let attribute_parameters =
      type_parameters
      |> map (fun param ->
          ( param,
            ( generator#generate (inh_parameter param),
              generator#generate (syn_parameter param) )))
    in

    let inh = generator#generate "inh" in
    let syn = generator#generate "syn" in

    let parameters =
      let depending_on_type_parameters =
        attribute_parameters
        |> map (fun (param, (inh_param, syn_param)) -> [param; inh_param; syn_param])
        |> flatten
      in
      depending_on_type_parameters @ [inh; syn]
    in

    (** Generate names for some values.
     *)
    let parameter_transforms_obj = generator#generate "parameter_transforms_obj" in
    let self = generator#generate "self" in

    object (this)
      method type_parameters = type_parameters

      method attribute_parameters_of type_parameter =
        try assoc type_parameter attribute_parameters
        with Not_found -> oops loc "type variable image not found (should not happen)"

      method inh_for type_parameter = fst (this#attribute_parameters_of type_parameter)
      method syn_for type_parameter = snd (this#attribute_parameters_of type_parameter)

      method generator = generator
      method parameters = parameters
      method parameter_transforms_obj = parameter_transforms_obj
      method methods_of_transforms_obj = type_parameters
      method inh = inh
      method syn = syn
      method self = self
    end

  (** Generate names for metaclass.
   *)
  let metaclass =
    object (self)
      method name type_name = type_name ^ "_metaclass"
      method parameter_arg parameter = parameter ^ "_arg"
      method inh = "inh"
      method syn = "syn"
      method private type_instance = "type_instance"
      method private parameter_transforms_obj = "parameter_transforms_obj"

      method augmented_arg_parameters =
        [ self#inh
        ; self#type_instance
        ; self#syn
        ; self#parameter_transforms_obj
        ]
    end

  (** Generate names of generic catamorphism's actual arguments.
   *)
  class catamorphism reserved_names =
    let generator = name_generator reserved_names in

    let transformer = generator#generate "transformer" in
    let subject = generator#generate "subject" in
    let initial_inh = generator#generate "initial_inh" in

    let transform_for : parameter -> string =
      let actual_name_for = create_namespace generator in
      fun parameter -> actual_name_for (parameter_transform parameter)
    in
    object
      method transform_for = transform_for
      method reserved = reserved_names
      method transformer = transformer
      method subject = subject
      method initial_inh = initial_inh
    end


  type names = {
      transformer : transformer;
      catamorphism : catamorphism;
    }
end



let apply_plugins loc type_descriptor plugin_names : (plugin_name * (properties * plugin_generator)) list =
  let plugin_processors =
    plugin_names
    |> map Plugin.get
    |> map (from_option_with_error loc)
  in
  let properties_and_generators =
    plugin_processors
    |> map (apply_to2 loc type_descriptor)
  in
  combine plugin_names properties_and_generators


let generic_cata_match_case loc names plugin_names pattern method_name arg_names arg_typs =
  Plugin.load_plugins plugin_names;
  let module H = Plugin.Helper (struct let loc = loc end) in
  let method_selection =
    H.E.method_selection (H.E.id names.Names.catamorphism#transformer) method_name
  in
  let gt_make arg_transform non_augmented_arg =
    H.E.app [
        <:expr< GT.make >>;
        arg_transform;
        non_augmented_arg;
        H.E.id names.Names.transformer#parameter_transforms_obj
      ]
  in
  let expr =
    H.E.app ([
        method_selection;
        H.E.id names.Names.catamorphism#initial_inh;
        gt_make (H.E.id names.Names.transformer#self) (H.E.id names.Names.catamorphism#subject)
      ] @
      map (fun (arg_typ, arg_name) ->
          let rec should_be_augmented = function
          | Arbitrary _ | Instance _ -> false
          | Self      _ | Variable _ -> true
          | Tuple (_, typs) -> exists should_be_augmented typs
          in
          let rec augment id = function
          | Arbitrary _ | Instance _ ->  H.E.id id
          | Variable (_, name) -> gt_make (H.E.id (names.Names.catamorphism#transform_for name)) (H.E.id id)
          | Self (typ, args, t) -> gt_make (H.E.id names.Names.transformer#self) (H.E.id id)
          | Tuple (_, typs) as typ ->
              if should_be_augmented typ
              then
                let name_generator = names.Names.transformer#generator#copy in
                let tuple_element_names = mapi (fun i _ -> name_generator#generate (sprintf "element%d" i)) typs in
                H.E.let_nrec
                  [H.P.tuple (map H.P.id tuple_element_names), H.E.id id]
                  (H.E.tuple (map (fun (name, typ) -> augment name typ) (combine tuple_element_names typs)))
              else H.E.id id
          in
          augment arg_name arg_typ
       )
       (combine arg_typs arg_names)
    )
  in
  (pattern, expr)


let match_case_for loc names plugin_names is_one_of_processed_mut_rec_types is_polymorphic_variant case_description =
  let module H = Plugin.Helper (struct let loc = loc end) in
  let cata_match_case = generic_cata_match_case loc names plugin_names in
  match case_description with
  | `Record fields ->
      let (field_names, _is_mutable, field_typs) = split3 fields in
      let binded_names = map (fun name -> names.Names.transformer#generator#generate name) field_names in
      let pattern = H.P.record (combine (map H.P.id field_names) (map H.P.id binded_names)) in
      cata_match_case pattern vmethod binded_names field_typs

  | `Tuple element_typs ->
      let binded_names = mapi (fun i _ -> sprintf "elem%d" i) element_typs in
      let pattern = H.P.tuple (map H.P.id binded_names) in
      cata_match_case pattern vmethod binded_names element_typs

  | `Constructor (cname, carg_typs) ->
      let binded_names = mapi (fun i _ -> sprintf "arg%d" i) carg_typs in
      let constructor_tag = (if is_polymorphic_variant then H.P.variant else H.P.id) cname in
      let pattern = H.P.app (constructor_tag :: map H.P.id binded_names) in
      let match_case_method_name = cmethod cname in
      cata_match_case pattern match_case_method_name binded_names carg_typs

  | `Type (Instance (_, args, qname)) ->
      let args = map (function Variable (_, a) -> a | _ -> oops loc "unsupported case (non-variable in instance)") args in (* TODO *)
      let expr =
        H.E.app (
          (generic_cata_for_qualified_name loc is_one_of_processed_mut_rec_types qname)
          :: ((map (fun a -> H.E.id (names.Names.catamorphism#transform_for a)) args)
              @ [H.E.id names.Names.catamorphism#transformer;
                 H.E.id names.Names.catamorphism#initial_inh;
                 H.E.id names.Names.catamorphism#subject]))
      in
      (H.P.alias (H.P.type_p qname) (H.P.id names.Names.catamorphism#subject), expr)

  | _ -> oops loc "unsupported type case description (internal error in match_case_for function)"


let class_items_for_match_case_method_gen loc
                                          properties
                                          type_instance_ctyp
                                          parameter_transforms_obj_ctyp
                                          arg_typs
                                          method_name =
  let module H = Plugin.Helper (struct let loc = loc end) in
  let augmented_arg inh arg_type syn =
    H.T.app [<:ctyp< GT.a >>; inh; arg_type; syn; parameter_transforms_obj_ctyp]
  in
  let self_arg = augmented_arg properties.inh_t type_instance_ctyp properties.syn_t in
  let rec arg_ctyp_of_typ = function
    | Arbitrary ctyp | Instance (ctyp, _, _) -> ctyp
    | Tuple (_ctyp, typs) -> H.T.tuple (map arg_ctyp_of_typ typs)
    | Self (_ctyp, _, _) -> self_arg
    | Variable (ctyp, type_var) ->
        augmented_arg (properties.inh_t_of_parameter type_var) ctyp (properties.syn_t_of_parameter type_var)
  in
  let method_ctyp =
    H.T.arrow ([properties.inh_t; self_arg] @ (map arg_ctyp_of_typ arg_typs) @ [properties.syn_t])
  in
  ( <:class_str_item< method virtual $lid: method_name$ : $method_ctyp$ >>,
    <:class_sig_item< method virtual $lid: method_name$ : $method_ctyp$ >>,
    <:class_sig_item< method $lid: method_name$ : $method_ctyp$ >> )



let class_info loc ~is_virtual class_name class_parameters class_definition = {
    ciLoc = loc;
    ciVir = Ploc.VaVal is_virtual;
    ciPrm = (loc, Ploc.VaVal (class_parameters |> map (fun p -> Ploc.VaVal (Some p), None)));
    ciNam = Ploc.VaVal class_name;
    ciExp = class_definition;
  }


(** Returns list of type case argument types. Type case arguments are variant arguments in case of variant type,
 *  tuple elemements in case of tuple, field values in case of record and so on.
 *)
let arg_typs_of_case_description loc = function
  | `Record fields -> map get3_3 fields
  | `Tuple element_typs -> element_typs
  | `Constructor (_, carg_typs) -> carg_typs
  | `Type _ -> oops loc "arg_typs_of_case_description: metaclasses for type instances are not supported now"

let method_name_of_case_description loc = function
  | `Record _ | `Tuple _ -> vmethod
  | `Constructor (cname, _) -> cmethod cname
  | `Type _ -> oops loc "method_name_of_case_description: metaclasses for type instances are not supported now"


let metaclass_method loc
                     type_parameters (*TODO: For some assertions only! Maybe need to be removed.*)
                     case_description =
  let module H = Plugin.Helper (struct let loc = loc end) in
  let self_arg = H.T.app (<:ctyp< GT.a >> :: map H.T.var Names.metaclass#augmented_arg_parameters) in

  (* Returns ctyp of metaclass method actual argument that corresponds to some variant constructor argument or tuple
   * element or something else.
   *)
  let rec arg_ctyp_of_typ = function
    | Variable (_, type_var) ->
        (* If the argument type is one of the type parameters, actual argument type of metaclass method
         * should be abstracted out by corresponding metaclass parameter: parameter_arg.
         * This is so sad because actual type of transformation object method arguments, which class type
         * is should be derived from the metaclass, depends on whether the type parameter was fixed by
         * instantiation or not. In first case actual argument type should be equal to the type of corresponding
         * constructor argument (or tuple element or something), in second case it should be augmented.
         * So, we have to defer the decision.
         *)
        assert (mem type_var type_parameters);
        H.T.var (Names.metaclass#parameter_arg type_var)
    | Tuple (_, typs) ->
        (* TODO: Probably incosistent behaviour here: for some constructor arguments (or tuple elements or something)
         * we do deep pattern matching, in current case, if the argument is a tuple. But for arguments of other types
         * we don't, and can't do such thing in general case. So, for what we do it for tuples? Maybe because there is no
         * big difference between variant constructor with many arguments and a variant constructor with one
         * tuple argument wraping all that arguments together, especially if we deel with polymorphic variant type.
         * Or maybe it is just a mess.
         *)
        H.T.tuple (map arg_ctyp_of_typ typs)
    | Self (_ , _, _) -> self_arg
    | Arbitrary ctyp | Instance (ctyp, _, _) -> ctyp
  in
  let arg_typs = arg_typs_of_case_description loc case_description in
  let arg_ctyps = map arg_ctyp_of_typ arg_typs in
  let ctyp = H.T.arrow
    (H.T.var Names.metaclass#inh :: self_arg :: arg_ctyps @ [H.T.var Names.metaclass#syn])
  in
  let name = method_name_of_case_description loc case_description in
  <:class_sig_item< method $lid: name$ : $ctyp$ >>


let metaclass loc type_name type_parameters case_descriptions =
  let name = Names.metaclass#name type_name in
  let methods =
    case_descriptions
    |> map (metaclass_method loc type_parameters)
  in
  let definition = <:class_type< object $list: methods$ end >> in
  let parameters =
    let for_type_parameters =
      type_parameters
      |> map (fun p -> [p; Names.metaclass#parameter_arg p])
      |> flatten
    in
    for_type_parameters @ Names.metaclass#augmented_arg_parameters
  in
  <:str_item< class type $list: [class_info loc ~is_virtual:false name parameters definition]$ >>



let class_items loc
                properties
                type_instance_ctyp
                parameter_transforms_obj_ctyp
                transformer_names
                case_description =
  let class_items_for_match_case_method : typ list -> string (*method name*) -> _ =
    class_items_for_match_case_method_gen loc
                                          properties
                                          type_instance_ctyp
                                          parameter_transforms_obj_ctyp
  in
  let module H = Plugin.Helper (struct let loc = loc end) in
  match case_description with
  | `Record fields ->
      class_items_for_match_case_method (map get3_3 fields) vmethod
  | `Tuple element_typs ->
      class_items_for_match_case_method element_typs vmethod
  | `Constructor (cname, carg_typs) ->
      class_items_for_match_case_method carg_typs (cmethod cname)

  | `Type (Instance (_, args, qname)) ->
      let args = map (function Variable (_, a) -> a | _ -> oops loc "unsupported case (non-variable in instance)") args in (* TODO *)
      let targs =
        flatten (map (fun a ->
          [a; transformer_names#inh_for a; transformer_names#syn_for a]) args)
        @ [transformer_names#inh; transformer_names#syn]
      in
      let targs = map H.T.var targs in
      let ce    = <:class_expr< [ $list:targs$ ] $list:map_last loc class_t qname$ >> in
      let ct f  =
        let h, t = hdtl loc (map_last loc f qname) in
        let ct   =
          fold_left
            (fun t id -> let id = <:class_type< $id:id$ >> in <:class_type< $t$ . $id$ >>)
            <:class_type< $id:h$ >>
          t
        in
        <:class_type< $ct$ [ $list:targs$ ] >>
      in
      ( <:class_str_item< inherit $ce$ >>,
        <:class_sig_item< inherit $ct class_t$ >>,
        <:class_sig_item< inherit $ct class_tt$ >> )

  | _ -> oops loc "unsupported type case description (internal error in class_items_for function)"


let base_types_for loc = function
  | `Type (Instance (_, type_args, qualified_name)) -> [type_args, qualified_name]
  | `Record _ | `Tuple _ | `Constructor _ -> []
  | _ -> oops loc "unsupported type case description (internal error in base_types_for function)"



type context = {
  gen         : < generate : string -> string; copy : 'a > as 'a;
  proto_items : class_str_item list;
  items       : class_str_item list;
  defaults    : class_str_item list;
  self_name   : string;
  in_cluster  : bool;
  this        : string;
  self        : string;
  env         : string;
  env_sig     : class_sig_item list;
}

let get_plugin_classes_generator loc
                                 names
                                 descrs
                                 type_descriptor =
  let module H = Plugin.Helper (struct let loc = loc end) in
  let m = ref StringMap.empty in
  let obj_magic = <:expr< Obj.magic >> in
  object
    method get trait =
      try StringMap.find trait !m
      with Not_found ->
        let g = name_generator names.Names.catamorphism#reserved in
        let this = g#generate "this" in
        let env = g#generate "env"  in
        let self = g#generate "self" in
        let cn = g#generate ("c_" ^ type_descriptor.name) in
        let vals, inits, methods, env_methods = split4 (
          map
            (fun (t, (args, _, _)) ->
              let ct =
                if type_descriptor.name = t
                then cn
                else g#generate ("c_" ^ t)
              in
              let proto_t = trait_proto_t t trait in
              let mt = tmethod t in
              let args = map g#generate args in
              let attribute_parameters = map (fun param ->
                param, (g#generate (inh_parameter param), g#generate (syn_parameter param))) args
              in
              let type_descriptor  = {
                is_polymorphic_variant = false;
                parameters = args;
                name = t;
                default_properties = {
                  inh_t = H.T.var names.Names.transformer#inh;
                  syn_t = H.T.var names.Names.transformer#syn;
                  transformer_parameters = args;
                  syn_t_of_parameter = (fun type_parameter -> H.T.var (snd (assoc type_parameter attribute_parameters)));
                  inh_t_of_parameter = (fun type_parameter -> H.T.var (fst (assoc type_parameter attribute_parameters)));
                };
              }
              in
              let prop, _ = (from_option_with_error loc (Plugin.get trait)) loc type_descriptor in
              let typ = H.T.app (H.T.id t :: map H.T.var args) in
              let inh_t = prop.Plugin.inh_t in
              let targs = map (fun a ->
                H.T.arrow [prop.Plugin.inh_t_of_parameter a; H.T.var a; prop.Plugin.syn_t_of_parameter a]) type_descriptor.parameters
              in
              let mtype = H.T.arrow (targs @ [inh_t; typ; prop.Plugin.syn_t]) in
              <:class_str_item< value mutable $lid:ct$ = $H.E.app [obj_magic; H.E.unit]$ >>,
              (H.E.assign (H.E.id ct) (H.E.app [H.E.new_e [proto_t]; H.E.id self])),
              <:class_str_item< method $mt$ : $mtype$ = $H.E.method_selection (H.E.id ct) mt$ >>,
              <:class_sig_item< method $tmethod t$ : $mtype$ >>
            )
            (remove_assoc type_descriptor.name descrs)
         )
        in
        let items =
          let prop, _ = (from_option_with_error loc (Plugin.get trait)) loc type_descriptor in
          let this = H.E.coerce (H.E.id this) (H.T.app (H.T.id (trait_t type_descriptor.name trait)::map H.T.var prop.Plugin.transformer_parameters)) in
          vals @ [<:class_str_item< initializer $H.E.seq (H.E.app [H.E.lid ":="; H.E.id self; this]::inits)$ >>] @ methods
        in
        {gen         = g;
         this        = this;
         self        = self;
         env         = env;
         env_sig     = env_methods;
         proto_items = [];
         items       = items;
         defaults    = [];
         in_cluster  = length descrs > 1;
         self_name   = cn;
       }

    method put trait context = m := StringMap.add trait context !m
  end


let add_derived_member loc plugin_classes_generator is_one_of_processed_mut_rec_types type_descriptor =
  let module H = Plugin.Helper (struct let loc = loc end) in
  (fun case (trait, (prop, generator)) ->
    let p = from_option_with_error loc (Plugin.get trait) in
    let context = plugin_classes_generator#get trait in
    let g = context.gen#copy in
    let branch method_name met_args gen =
      let rec env = {
        Plugin.inh = g#generate "inh";
        Plugin.subject = g#generate "subject";
        Plugin.new_name = (fun s -> g#generate s);
        Plugin.trait =
          (fun s t ->
             if s = trait
             then
               let rec inner = function
               | Variable (_, a) -> H.E.gt_tp (H.E.id env.Plugin.subject) a
               | Instance (_, args, qname) ->
                   let args = map inner args in
                   (match qname with
                    | [t] when is_one_of_processed_mut_rec_types t && t <> type_descriptor.name ->
                        H.E.app ((H.E.method_selection (H.E.app [H.E.lid "!"; H.E.id context.env]) (tmethod t)) :: args)
                    | _  ->
                        let tobj =
                          match qname with
                          | [t] when t = type_descriptor.name -> H.E.id "this"
                          | _ -> H.E.new_e (map_last loc (fun name -> trait_t name trait) qname)
                        in
                        H.E.app ([H.E.acc (map H.E.id ["GT"; "transform"]); H.E.acc (map H.E.id qname)] @ args @ [tobj])
                   )
               | Self _ -> H.E.gt_f (H.E.id env.Plugin.subject)
               | _ -> invalid_arg "Unsupported type"
               in (try Some (inner t) with Invalid_argument "Unsupported type" -> None)
             else None
          )
      }
      in
      let m_def =
        let body = H.E.func (map H.P.id ([env.Plugin.inh; env.Plugin.subject] @ met_args)) (gen env) in
        <:class_str_item< method $lid:method_name$ = $body$ >>
      in
      {context with proto_items = m_def :: context.proto_items}
    in
    let context =
      match case with
      | `Record fields ->
          let fields = map (fun (n, m, t) -> g#generate n, (n,  m, t)) fields in
          branch vmethod (map fst fields) (fun env -> generator#record env fields)

      | `Tuple elems ->
          let elems = mapi (fun i t -> g#generate (sprintf "p%d" i), t) elems in
          branch vmethod (map fst elems) (fun env -> generator#tuple env elems)

      | `Constructor (cname, cargs) ->
          let args = mapi (fun i a -> g#generate (sprintf "p%d" i), a) cargs in
          branch (cmethod cname) (map fst args) (fun env -> generator#constructor env cname args)

      | `Type (Instance (_, args, qname)) ->
          let args = map (function Variable (_, a) -> a | _ -> oops loc "unsupported case (non-variable in instance)") args in (* TODO *)
          let qname, qname_proto, env_tt, name =
            let n, t = hdtl loc (rev qname) in
            rev ((trait_t n trait) :: t),
            rev ((trait_proto_t n trait) :: t),
            rev ((env_tt n trait) :: t),
            n
          in
          let type_descriptor = { type_descriptor with
            parameters = args;
            name = name;
            default_properties = prop;
          }
          in
          let prop = fst (p loc type_descriptor) in
          let i_def, _ = Plugin.generate_inherit false loc qname_proto (Some (H.E.id context.self, H.T.id "unit")) type_descriptor prop in
          let i_impl, _ = Plugin.generate_inherit false loc qname None type_descriptor prop in
          let i_def_proto, _ = Plugin.generate_inherit false loc qname_proto (Some (H.E.id context.env, H.T.id "unit")) type_descriptor prop in
          let _ , i_env = Plugin.generate_inherit false loc env_tt None type_descriptor prop in
          {context with defaults = i_impl :: context.defaults;
           items = i_def :: context.items;
           proto_items = i_def_proto :: context.proto_items;
           env_sig     = i_env :: context.env_sig
          }
      | _ -> oops loc "unsupported case (infernal error)"
    in
    plugin_classes_generator#put trait context
  )


let get_derived_classes loc plugin_classes_generator type_descriptor =
  let module H = Plugin.Helper (struct let loc = loc end) in
  let obj_magic = <:expr< Obj.magic >> in
  (fun (trait, p) ->
     let context = plugin_classes_generator#get trait in
     let i_def, _ = Plugin.generate_inherit true  loc [class_t type_descriptor.name] None type_descriptor (fst p) in
     let _ , i_decl = Plugin.generate_inherit true  loc [class_tt type_descriptor.name] None type_descriptor (fst p) in
     let p_def, _ =
       Plugin.generate_inherit false loc [trait_proto_t type_descriptor.name trait] (Some (H.E.id context.self, H.T.id "unit")) type_descriptor (fst p)
     in
     let cproto = <:class_expr< object ($H.P.id context.this$) $list:i_def::context.proto_items$ end >> in
     let ce =
       let ce = <:class_expr< object ($H.P.id context.this$) $list:i_def::p_def::context.defaults@context.items$ end >> in
       <:class_expr< let $flag:false$ $list:[H.P.id context.self, H.E.app [obj_magic; H.E.app [H.E.id "ref"; H.E.unit]]]$ in $ce$ >>
     in
     let env_t = <:class_type< object $list:context.env_sig$ end >> in
     let class_targs = map H.T.var (fst p).transformer_parameters in
     let cproto_t =
       <:class_type< [ $H.T.app [H.T.id "ref"; H.T.app (H.T.id (env_tt type_descriptor.name trait) :: class_targs)]$ ] -> object $list:[i_decl]$ end >>
     in
     let ct =
       let ct =
         match class_targs with
         | [] -> <:class_type< $id:env_tt type_descriptor.name trait$ >>
         | _  -> <:class_type< $id:env_tt type_descriptor.name trait$ [ $list:class_targs$ ] >>
       in
       let env_inh = <:class_sig_item< inherit $ct$ >> in
       <:class_type< object $list:[i_decl; env_inh]$ end >>
     in
     Plugin.generate_classes loc trait type_descriptor p (context.this, context.env, env_t, cproto, ce, cproto_t, ct)
  )

(** Generate list of ctyps of type parameter transformation functions (or transforms, in short.)
 *  All of those types looks like iparam -> param -> sparam.
 *  To generate such types you need know names, nothing more.
 *)
let make_parameter_transform_ctyps loc names : ctyp list =
  let module H = Plugin.Helper (struct let loc = loc end) in
  names.Names.transformer#type_parameters
  |> map (fun parameter -> H.T.arrow (map H.T.var [
        names.Names.transformer#inh_for parameter;
        parameter;
        names.Names.transformer#syn_for parameter;
     ]))


(** Create object full of type parameter transformation functions.
 *)
let create_parameter_transforms_obj loc names =
  let module H = Plugin.Helper (struct let loc = loc end) in
  let method_definitions =
    combine names.Names.transformer#type_parameters
            names.Names.transformer#methods_of_transforms_obj
    |> map (fun (parameter, transforms_obj_method) ->
        <:class_str_item< method $lid: transforms_obj_method$ =
                                 $H.E.id (names.Names.catamorphism#transform_for parameter)$ >>)
  in
  H.E.obj method_definitions


let generate_definitions_for_single_type loc descrs type_name type_parameters description plugin_names =
  Plugin.load_plugins plugin_names;
  let module H = Plugin.Helper (struct let loc = loc end) in
  let names = Names.({
      catamorphism = new Names.catamorphism (involved_type_names descrs);
      transformer = new Names.transformer loc type_parameters;
    })
  in
  let is_polymorphic_variant =
    match description with
    | `PolymorphicVariant _ -> true
    | _ -> false
  in
  let properties = {
    inh_t = <:ctyp< ' $names.Names.transformer#inh$ >>;
    syn_t = <:ctyp< ' $names.Names.transformer#syn$ >>;
    transformer_parameters = names.Names.transformer#parameters;
    syn_t_of_parameter = (fun parameter -> <:ctyp< ' $names.Names.transformer#syn_for parameter$ >>);
    inh_t_of_parameter = (fun parameter -> <:ctyp< ' $names.Names.transformer#inh_for parameter$ >>);
  }
  in
  let type_descriptor  = {
    is_polymorphic_variant = is_polymorphic_variant;
    parameters = type_parameters;
    name = type_name;
    default_properties = properties;
  }
  in
  let parameter_transform_ctyps = make_parameter_transform_ctyps loc names in
  let parameter_transforms_obj = create_parameter_transforms_obj loc names in
  let parameter_transforms_obj_ctyp =
    H.T.obj (combine names.Names.transformer#methods_of_transforms_obj parameter_transform_ctyps) ~is_open_type:false
  in
  let type_instance_ctyp = H.T.app (H.T.id type_name :: map H.T.var type_parameters) in
  let type_transform =
    H.T.arrow [H.T.var names.Names.transformer#inh; type_instance_ctyp; H.T.var names.Names.transformer#syn]
  in
  let gt_record_ctyp =
    let transformer = H.T.app (H.T.class_t [class_tt type_name] :: map H.T.var names.Names.transformer#parameters) in
    let generic_catamorphism = H.T.arrow (parameter_transform_ctyps @ [transformer; type_transform]) in
    let gt_record = H.T.acc [H.T.id "GT"; H.T.id "t"] in
    H.T.app [gt_record; generic_catamorphism]
  in
  let method_sig_for_catamorphism =
    let catamorphism_with_binded_transformer = H.T.arrow (parameter_transform_ctyps @ [type_transform]) in
    <:class_sig_item< method $lid: tmethod type_name$ : $catamorphism_with_binded_transformer$ >>
  in
  let is_one_of_processed_mut_rec_types type_name = mem_assoc type_name descrs in
  let plugin_classes_generator = get_plugin_classes_generator loc names descrs type_descriptor in
(* ===--------------------------------------------------------------------=== *)
  let case_descriptions = type_case_descriptions description in
  let plugin_properties_and_generators = apply_plugins loc type_descriptor plugin_names in
  case_descriptions
  |> iter (fun case ->
      plugin_properties_and_generators
      |> iter (add_derived_member loc
                                  plugin_classes_generator
                                  is_one_of_processed_mut_rec_types
                                  type_descriptor
                                  case)
  );
  let catamorphism_match_cases =
    case_descriptions
    |> map (match_case_for loc
                            names
                            plugin_names
                            is_one_of_processed_mut_rec_types
                            is_polymorphic_variant)
  in
  let base_types =
    case_descriptions
    |> map (base_types_for loc)
    |> flatten
  in
  let (methods, methods_sig, methods_sig_t) =
    case_descriptions
    |> map (class_items loc
                        properties
                        type_instance_ctyp
                        parameter_transforms_obj_ctyp
                        names.Names.transformer)
    |> split3
  in
(* ===--------------------------------------------------------------------=== *)
  let cata_metarg_names =
    (map names.Names.catamorphism#transform_for type_parameters) @ [names.Names.catamorphism#transformer]
  in
  let cata_arg_names =
    cata_metarg_names @ [names.Names.catamorphism#initial_inh; names.Names.catamorphism#subject]
  in
  let subject = H.E.id names.Names.catamorphism#subject in
  let local_defs_and_then expr =
    let local_defs = [
        H.P.id names.Names.transformer#self, H.E.app (H.E.id (cata type_name) :: map H.E.id cata_metarg_names);
        H.P.id names.Names.transformer#parameter_transforms_obj, parameter_transforms_obj;
      ]
    in
    match local_defs with
    | [] -> expr
    | _  -> H.E.letrec local_defs expr
  in
  let is_abbrev = not is_polymorphic_variant && length base_types = 1 in
  let proto_class_type = <:class_type< object $list: methods_sig_t @ [method_sig_for_catamorphism]$ end >> in
  let class_expr =
    let this = names.Names.transformer#generator#generate "this" in
    let body =
      let args = map names.Names.catamorphism#transform_for type_parameters in
      H.E.func (map H.P.id args) (H.E.app ((H.E.acc (map H.E.id ["GT"; "transform"])) :: map H.E.id (type_name :: args@[this])))
    in
    let met = <:class_str_item< method $lid:tmethod type_name$ = $body$ >> in
    <:class_expr< object ($H.P.id this$) $list:methods@[met]$ end >>
  in
  let class_type = <:class_type< object $list: methods_sig @ [method_sig_for_catamorphism]$ end >> in
  let transformer_class_info class_name class_definition =
    class_info loc ~is_virtual:true class_name names.Names.transformer#parameters class_definition
  in
(*TODO:  let metaclass_decl = metaclass loc type_name type_parameters case_descriptions in *)
  let class_type_def = <:str_item< class type $list: [transformer_class_info (class_tt type_name) proto_class_type]$ >> in
  let class_type_decl = <:sig_item< class type $list: [transformer_class_info (class_tt type_name) proto_class_type]$ >> in
  let class_def  = <:str_item< class $list: [transformer_class_info (class_t type_name) class_expr]$ >> in
  let class_decl = <:sig_item< class $list: [transformer_class_info (class_t type_name) class_type]$ >> in
  let body =
    if is_abbrev
    then
      let ((_, expr), _) = hdtl loc catamorphism_match_cases in
      expr
    else
      let when_guard_expr = VaVal None in
      local_defs_and_then (H.E.match_e subject (map (insert2_2 when_guard_expr) catamorphism_match_cases))
  in
  ( ( H.P.constr (H.P.id type_name) gt_record_ctyp
    , H.E.record [(<:patt< GT.gcata >>, H.E.id (cata type_name))]
    )
  , ( H.P.id (cata type_name)
    , H.E.func (map H.P.id cata_arg_names) body
    )
  , <:sig_item< value $type_name$ : $gt_record_ctyp$ >>
  , ( class_type_def
    , class_type_decl
    )
  , begin
      let (env, protos, defs, edecls, pdecls, decls) =
        plugin_properties_and_generators
        |> map (get_derived_classes loc
                                    plugin_classes_generator
                                    type_descriptor)
        |> split6
      in
      ( class_def
      , flatten env @ protos
      , defs
      , class_decl :: flatten edecls @ pdecls @ decls
      )
    end
  , () (*TODO: metaclass_decl*)
  )


(** Process by type_decl_to_description function type declarations only for which it have been requested by user.
 *  See comment to generate function for details.
 *)
let make_descrs mut_rec_type_decls : (type_name * (parameter list * [> (* description *) ] * plugin_name list)) list =
  fold_right (fun (loc, type_decl, request) acc ->
    match request with
    | Some plugin_names ->
        let (type_name, type_parameters, description) = type_decl_to_description loc type_decl in
        (type_name, (type_parameters, description, plugin_names)) :: acc
    | None -> acc
  ) mut_rec_type_decls []


let open_polymorphic_variant_type loc type_decl =
  let module H = Plugin.Helper (struct let loc = loc end) in
  match type_decl.tdDef with
  | <:ctyp< [ = $list: constructors$ ] >> ->
      let type_name = type_open_t (name_of_type_decl loc type_decl) in
      let parameters = parameters_of_type_decl loc type_decl in
      let self = (name_generator parameters)#generate "self" in [
        { type_decl with
          tdNam = VaVal (loc, VaVal type_name);
          tdPrm = VaVal (map (fun param -> VaVal (Some param), None) (self :: parameters));
          tdDef = H.T.var self;
          tdCon = VaVal [H.T.var self, <:ctyp< [> $list: constructors$ ]>>];
        };
      ]
  | _ -> []


(** mut_rec_type_decls argument is a group of mutual recursive type declarations, in which each element is original
 *  OCaml type declaration and an optional list of plugin names.
 *  If list is present (and maybe empty), the framework will generate a generic traversal function and an abstract
 *  transformer class and auxiliary class types.
 *  If it's not, type declaration will be ignored by the framework.
 *  If list is present and non-empty, corresponding plugins code will be generated as well.
 *)
let generate loc (mut_rec_type_decls : (loc * type_decl * plugin_name list option) list) =
  let module H = Plugin.Helper (struct let loc = loc end) in
  let type_decls = map snd3 mut_rec_type_decls in
  let descrs = make_descrs mut_rec_type_decls in
  let per_mut_rec_type_definitions =
    descrs
    |> map (fun (type_name, (type_parameters, description, plugin_names)) ->
        generate_definitions_for_single_type loc descrs type_name type_parameters description plugin_names)
  in
  let names, defs, decls, classes, derived_classes, metaclasses = split6 per_mut_rec_type_definitions in
  let metaclasses = (*TODO*)[] in
  let pnames, tnames = split names in
  let class_defs, class_decls = split classes in
  let derived_class_defs, derived_class_decls =
    let class_defs, protos, defs, class_decls = split4 derived_classes in
    class_defs @ (flatten protos) @ (flatten defs), flatten class_decls
  in
  let cata_def = <:str_item< value $list: [H.P.tuple pnames, H.E.letrec defs (H.E.tuple tnames)]$ >> in
  let open_polymorphic_variant_types = flatten (map (open_polymorphic_variant_type loc) type_decls) in
  let type_def = <:str_item< type $list: type_decls @ open_polymorphic_variant_types$ >> in
  let type_decl = <:sig_item< type $list: type_decls @ open_polymorphic_variant_types$ >> in
  <:str_item< declare $list: type_def :: class_defs @ [cata_def] @ metaclasses @ derived_class_defs$ end >>,
  <:sig_item< declare $list: type_decl :: class_decls @ decls @ derived_class_decls$ end >>
