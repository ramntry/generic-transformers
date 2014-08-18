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

let split3 l =
  List.fold_right
    (fun (a, b, c) (x, y, z) -> a::x, b::y, c::z) l ([], [], [])

let split4 l =
  List.fold_right
    (fun (a, b, c, d) (x, y, z, t) -> a::x, b::y, c::z, d::t) l ([], [], [], [])

let split5 l =
  List.fold_right
    (fun (a, b, c, d, e) (x, y, z, t, h) -> a::x, b::y, c::z, d::t, e::h) l ([], [], [], [], [])

let split6 l =
  List.fold_right
    (fun (a, b, c, d, e, f) (x, y, z, t, h, i) -> a::x, b::y, c::z, d::t, e::h, f::i) l ([], [], [], [], [], [])

let apply_to2 arg1 arg2 func = func arg1 arg2

let snd3 (_, elem2, _) = elem2

let ctyp_of_qname loc qname =
  let module H = Plugin.Helper (struct let loc = loc end) in H.T.acc (map H.T.id qname)

let ctyp_of_instance loc args qname =
  let module H = Plugin.Helper (struct let loc = loc end) in
  H.T.app (qname :: args)

let from_option_with_error loc = function
| Some v -> v
| _ -> oops loc "empty option (should not happen)"

(* Everywhere
 *     'parameter' stands for type parameter of some type (or class, or class type etc).
 *     'type' - currently being processed type declaration or its name etc.
 *     'type_decl' - Camlp5 record representing OCaml type declaration.
 *)

let name_of_type_decl loc type_decl =
  from_vaval loc (snd (from_vaval loc type_decl.tdNam))

let parameters_of_type_decl loc type_decl =
  from_vaval loc type_decl.tdPrm
  |> map (fun (type_variable, _covariant_flags) ->
      match from_vaval loc type_variable with
      | Some type_parameter -> type_parameter
      | None -> oops loc "wildcard type parameters not supported"
      )

let type_decl_to_description loc td =
  let type_name = name_of_type_decl loc td in
  let type_parameters = parameters_of_type_decl loc td in
  let convert =
    let convert_concrete typ =
      let rec inner = function
      | <:ctyp< ( $list:typs$ ) >> as typ -> Tuple (typ, map inner typs)
      | <:ctyp< ' $a$ >> as typ -> Variable (typ, a)
      | <:ctyp< $t$ $a$ >> as typ ->
          (match inner t, inner a with
           | _, Arbitrary _ -> Arbitrary typ
           | Instance (_, targs, tname), a -> Instance (typ, targs@[a], tname)
           | _ -> Arbitrary typ
          )
      | <:ctyp< $q$ . $t$ >> as typ ->
          (match inner q, inner t with
           | Instance (_, [], q), Instance (_, [], t) -> Instance (typ, [], q@t)
           | _ -> Arbitrary typ
          )
      | (<:ctyp< $uid:n$ >> | <:ctyp< $lid:n$ >>) as typ -> Instance (typ, [], [n]) | td-> Arbitrary td
      in
      let rec replace = function
      | Tuple (t, typs) -> Tuple (t, map replace typs)
      | Instance (t, params, qname) as orig when qname = [type_name] ->
         (try
           let params =
             map (function
                  | Variable (_, a) -> a
                  | _ -> invalid_arg "Not a variable"
                 )
                 params
           in
           if params = type_parameters then Self (t, type_parameters, qname) else orig
          with Invalid_argument "Not a variable" -> orig
         )
      | x -> x
      in
      replace (inner typ)
    in
    function
    | <:ctyp< [ $list:const$ ] >> | <:ctyp< $_$ == $priv:_$ [ $list:const$ ] >> ->
        let const = map (fun (loc, name, args, d) ->
                           match d with
                           | None -> `Constructor (from_vaval loc name, map convert_concrete (from_vaval loc args))
                           | _    -> oops loc "unsupported constructor declaration"
                        )
                    const
        in
        `Variant const

    | <:ctyp< { $list:fields$ } >> | <:ctyp< $_$ == $priv:_$ { $list:fields$ } >> ->
        let fields = map (fun (_, name, mut, typ) -> name, mut, convert_concrete typ) fields in
        `Record fields

    | <:ctyp< ( $list:typs$ ) >> -> `Tuple (map convert_concrete typs)

    | <:ctyp< [ = $list:variants$ ] >> ->
        let wow ()   = oops loc "unsupported polymorphic variant type constructor declaration" in
        let variants =
          map (function
               | <:poly_variant< $typ$ >> ->
                  (match convert_concrete typ with
                   | Arbitrary _ -> wow ()
                   | typ -> `Type typ
                  )
               | <:poly_variant< ` $c$ >> -> `Constructor (c, [])
               | <:poly_variant< ` $c$ of $list:typs$ >> ->
                   let typs =
                     flatten (
                       map (function
                            | <:ctyp< ( $list:typs$ ) >> -> map convert_concrete typs
                            | typ -> [convert_concrete typ]
                           )
                           typs
                     )
                   in
                   `Constructor (c, typs)
               | _ -> wow ()
              )
            variants
        in
        `PolymorphicVariant variants

    | typ -> (
        match convert_concrete typ with
        | Arbitrary _ -> oops loc "unsupported type"
        | typ         -> `Variant [match typ with Variable (t, _) -> `Tuple [Tuple (<:ctyp< ($list:[t]$) >>, [typ])] | _ -> `Type typ]
        )
  in
  (type_name, type_parameters, convert td.tdDef)

let make_descrs mut_rec_type_decls =
  mut_rec_type_decls
  |> map (fun (loc, type_decl, request) ->
    match request with
    | Some plugin_names ->
        let (type_name, type_parameters, description) = type_decl_to_description loc type_decl in
        [(type_name, (type_parameters, description, plugin_names))]
    | None -> []
    )
  |> flatten

(** mut_rec_type_decls argument is a group of mutual recursive type declarations, in which each element is original
 *  OCaml type declaration and an optional list of plugin names.
 *  If list is present (and maybe empty), the framework will generate a generic traversal function and an abstract
 *  transformer class and auxiliary class types.
 *  If it's not, type declaration will be ignored by the framework.
 *  If list is present and non-empty, corresponding plugins code will be generated as well.
 *)
let generate loc (mut_rec_type_decls : (loc * type_decl * plugin_name list option) list) =
  let module H = Plugin.Helper (struct let loc = loc end) in
  let descrs = make_descrs mut_rec_type_decls in
  let get_gcata = function
    | [name] when mem_assoc name descrs -> H.E.id (cata name)
    | qname ->
        let typename = H.E.acc (map H.E.id qname) in
        <:expr< $typename$.GT.gcata >>
  in
  let is_mut_rec type_name = mem_assoc type_name descrs in
  let reserved_names =
    fold_left
      (fun acc (n, (_, d, _)) ->
         match d with
         | `PolymorphicVariant comps->
             fold_left
               (fun acc t ->
                  match t with
                  | `Type (Instance (_, _, [n])) -> n :: acc
                  | _ -> acc
               )
               acc
               comps
         | _ -> acc
      )
      (map fst descrs)
      descrs
  in
  let g = name_generator reserved_names in
  let trans = g#generate "trans" in
  let farg =
    let module M = Plugin.StringMap in
    let m = ref M.empty in
    (fun a ->
       let p = farg a in
       try M.find p !m with
         Not_found ->
           let n = g#generate p in
           m := M.add p n !m;
           n
    )
  in
  let subj = g#generate "subj" in
  let acc = g#generate "inh" in
  let generic_cata = <:patt< GT.gcata >> in
  let defs =
    map (fun (type_name, (type_parameters, description, plugin_names)) ->
      Plugin.load_plugins plugin_names;
      let is_polyvar =
        match description with
        | `PolymorphicVariant _ -> true
        | _ -> false
      in
      let generator = name_generator type_parameters in
      let attribute_parameters = type_parameters |> map (fun type_parameter ->
          type_parameter,
          (generator#generate (inh_parameter type_parameter), generator#generate (syn_parameter type_parameter)))
      in
      let attribute_parameters_of type_parameter =
        try assoc type_parameter attribute_parameters
        with Not_found -> oops loc "type variable image not found (should not happen)"
      in
      let inh_parameter_of type_parameter = fst (attribute_parameters_of type_parameter) in
      let syn_parameter_of type_parameter = snd (attribute_parameters_of type_parameter) in
      let inh = generator#generate "inh" in
      let syn = generator#generate "syn" in
      let transformer_parameters =
        (attribute_parameters |> map (fun (param, (inh_param, syn_param)) -> [param; inh_param; syn_param]) |> flatten)
        @ [inh; syn]
      in
      let type_descriptor  = {
        is_polyvar = is_polyvar;
        parameters = type_parameters;
        name = type_name;
        default_properties = {
          inh_t = H.T.var inh;
          syn_t = H.T.var syn;
          transformer_parameters = transformer_parameters;
          syn_t_of_parameter = (fun type_parameter -> H.T.var (syn_parameter_of type_parameter));
          inh_t_of_parameter = (fun type_parameter -> H.T.var (inh_parameter_of type_parameter));
        };
      }
      in
      let tpo_name = generator#generate "tpo" in
      let self_name = generator#generate "self" in
      let tpo =
        H.E.obj None (map (fun param ->
          <:class_str_item< method $lid: param$ = $H.E.id (farg param)$ >>) type_parameters)
      in
      let tpf = map (fun param ->
        H.T.arrow (map H.T.var [inh_parameter_of param; param; syn_parameter_of param])) type_parameters in
      let tpt = H.T.obj (combine type_parameters tpf) false in
      let catype =
        let typ = H.T.app (H.T.id type_name :: map H.T.var type_parameters) in
        let gt = H.T.acc [H.T.id "GT"; H.T.id "t"] in
        let ft = H.T.arrow [H.T.var inh; typ; H.T.var syn] in
        let trt = H.T.app (H.T.class_t [class_tt type_name] :: map H.T.var transformer_parameters) in
        H.T.app [gt; H.T.arrow (tpf @ [trt; ft])]
      in
      let metargs = (map farg type_parameters) @ [trans] in
      let args = metargs @ [acc; subj] in
      let get_type_handler, get_local_defs, get_type_methods =
        let method_decls = ref [type_name, (H.E.id type_name, (type_parameters, H.T.app (H.T.id type_name :: map H.T.var type_parameters)))] in
        let method_defs  = ref [] in
        let get_type_handler (ctyp, args, qname) =
          if type_parameters = args && qname = [type_name]
          then H.E.id self_name
          else
            let compound_name =
              let b = Buffer.create 64 in
              let u =
                let a = ref true in
                (fun () -> if not !a then Buffer.add_string b "_"; a := false)
              in
              let s = Buffer.add_string b in
              let filler args qname =
                iter (fun name -> u (); s name) args;
                iter (fun name -> u (); s name) qname
              in
              filler args qname;
              Buffer.contents b
            in
            let name =
              try fst (assoc compound_name !method_decls) with
                Not_found ->
                  let args = fold_left (fun args name -> if mem name args then args else name :: args) [] args in
                  let body = H.E.app ((H.E.method_call (H.E.id trans) (tmethod compound_name)) ::
                                      map (fun a -> H.E.id (farg a)) args)
                  in
                  let impl = H.P.id compound_name, body in
                  let name = H.E.id compound_name in
                  method_decls := (compound_name, (name, (args, ctyp))) :: !method_decls;
                  method_defs  := impl :: !method_defs;
                  name
            in
            name
        in
        get_type_handler,
        (fun () -> !method_defs),
        (fun () ->
          (!method_decls |> map (fun (name, (_, (args, t))) ->
           let targs   = map (fun a -> H.T.arrow [H.T.var (inh_parameter_of a); H.T.var a; H.T.var (syn_parameter_of a)]) args in
           let msig    = H.T.arrow (targs @ [H.T.var inh; t; H.T.var syn]) in
           <:class_str_item< method virtual $lid:tmethod name$ : $msig$ >>,
           <:class_sig_item< method $lid:tmethod name$ : $msig$ >>)))
      in
      let add_derived_member, get_derived_classes =
        let mut_rec = length descrs > 1 in
        let obj_magic = <:expr< Obj.magic >> in
        let module M =
          struct

            type t = {
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

            module M = Plugin.StringMap

            let m = ref M.empty

            let get trait =
              try M.find trait !m
              with Not_found ->
                let g    = name_generator reserved_names in
                let this = g#generate "this" in
                let env  = g#generate "env"  in
                let self = g#generate "self" in
                let cn   = g#generate ("c_" ^ type_name) in
                let vals, inits, methods, env_methods = split4 (
                  map
                    (fun (t, (args, _, _)) ->
                      let ct      = if type_name = t then cn else g#generate ("c_" ^ t) in
                      let proto_t = trait_proto_t t trait in
                      let mt      = tmethod t             in
                      let args          = map g#generate args in
                      let attribute_parameters = map (fun param ->
                        param, (g#generate (inh_parameter param), g#generate (syn_parameter param))) args
                      in
                      let type_descriptor  = {
                        is_polyvar = false;
                        parameters = args;
                        name = t;
                        default_properties = {
                          inh_t = H.T.var inh;
                          syn_t = H.T.var syn;
                          transformer_parameters = args;
                          syn_t_of_parameter = (fun type_parameter -> H.T.var (snd (assoc type_parameter attribute_parameters)));
                          inh_t_of_parameter = (fun type_parameter -> H.T.var (fst (assoc type_parameter attribute_parameters)));
                        };
                      }
                      in
                      let prop, _ = (from_option_with_error loc (Plugin.get trait)) loc type_descriptor in
                      let typ     = H.T.app (H.T.id t :: map H.T.var args) in
                      let inh_t   = prop.Plugin.inh_t in
                      let targs = map (fun a ->
                        H.T.arrow [prop.Plugin.inh_t_of_parameter a; H.T.var a; prop.Plugin.syn_t_of_parameter a]) type_descriptor.parameters
                      in
                      let mtype   = H.T.arrow (targs @ [inh_t; typ; prop.Plugin.syn_t]) in
                      <:class_str_item< value mutable $lid:ct$ = $H.E.app [obj_magic; H.E.unit]$ >>,
                      (H.E.assign (H.E.id ct) (H.E.app [H.E.new_e [proto_t]; H.E.id self])),
                      <:class_str_item< method $mt$ : $mtype$ = $H.E.method_call (H.E.id ct) mt$ >>,
                      <:class_sig_item< method $tmethod t$ : $mtype$ >>
                    )
                    (remove_assoc type_name descrs)
                 )
                in
                let items =
                  let prop, _ = (from_option_with_error loc (Plugin.get trait)) loc type_descriptor in
                  let this    = H.E.coerce (H.E.id this) (H.T.app (H.T.id (trait_t type_name trait)::map H.T.var prop.Plugin.transformer_parameters)) in
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
                 in_cluster  = mut_rec;
                 self_name   = cn;
               }

            let put trait t = m := M.add trait t !m

          end
        in
        (fun case (trait, (prop, generator)) ->
          let p       = from_option_with_error loc (Plugin.get trait) in
          let context = M.get trait                   in
          let g       = context.M.gen#copy            in
          let branch met_name met_args gen =
            let rec env = {
              Plugin.inh      = g#generate "inh";
              Plugin.subj     = g#generate "subj";
              Plugin.new_name = (fun s -> g#generate s);
              Plugin.trait    =
                (fun s t ->
                   if s = trait
                   then
                     let rec inner = function
                     | Variable (_, a) -> H.E.gt_tp (H.E.id env.Plugin.subj) a
                     | Instance (_, args, qname) ->
                         let args = map inner args in
                         (match qname with
                          | [t] when is_mut_rec t && t <> type_name ->
                              H.E.app ((H.E.method_call (H.E.app [H.E.lid "!"; H.E.id context.M.env]) (tmethod t)) :: args)
                          | _  ->
                              let tobj =
                                match qname with
                                | [t] when t = type_name -> H.E.id "this"
                                | _ -> H.E.new_e (map_last loc (fun name -> trait_t name trait) qname)
                              in
                              H.E.app ([H.E.acc (map H.E.id ["GT"; "transform"]); H.E.acc (map H.E.id qname)] @ args @ [tobj])
                         )
                     | Self _ -> H.E.gt_f (H.E.id env.Plugin.subj)
                     | _ -> invalid_arg "Unsupported type"
                     in (try Some (inner t) with Invalid_argument "Unsupported type" -> None)
                   else None
                )
            }
            in
            let m_def =
              let body = H.E.func (map H.P.id ([env.Plugin.inh; env.Plugin.subj] @ met_args)) (gen env) in
              <:class_str_item< method $lid:met_name$ = $body$ >>
            in
            {context with M.proto_items = m_def :: context.M.proto_items}
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
                let type_descriptor = {
                  is_polyvar = is_polyvar;
                  parameters = args;
                  name = name;
                  default_properties = prop;
                }
                in
                let prop = fst (p loc type_descriptor) in
                let i_def, _ = Plugin.generate_inherit false loc qname_proto (Some (H.E.id context.M.self, H.T.id "unit")) type_descriptor prop in
                let i_impl, _ = Plugin.generate_inherit false loc qname None type_descriptor prop in
                let i_def_proto, _ = Plugin.generate_inherit false loc qname_proto (Some (H.E.id context.M.env, H.T.id "unit")) type_descriptor prop in
                let _ , i_env = Plugin.generate_inherit false loc env_tt None type_descriptor prop in
                {context with M.defaults = i_impl :: context.M.defaults;
                 M.items = i_def :: context.M.items;
                 M.proto_items = i_def_proto :: context.M.proto_items;
                 M.env_sig     = i_env :: context.M.env_sig
                }
            | _ -> oops loc "unsupported case (infernal error)"
          in
          M.put trait context
        ),
        (fun (trait, p) ->
           let context = M.get trait in
           let i_def, _ = Plugin.generate_inherit true  loc [class_t  type_name] None type_descriptor (fst p) in
           let _ , i_decl = Plugin.generate_inherit true  loc [class_tt type_name] None type_descriptor (fst p) in
           let p_def, _ =
             Plugin.generate_inherit false loc [trait_proto_t type_name trait] (Some (H.E.id context.M.self, H.T.id "unit")) type_descriptor (fst p)
           in
           let cproto = <:class_expr< object ($H.P.id context.M.this$) $list:i_def::context.M.proto_items$ end >> in
           let ce =
             let ce = <:class_expr< object ($H.P.id context.M.this$) $list:i_def::p_def::context.M.defaults@context.M.items$ end >> in
             <:class_expr< let $flag:false$ $list:[H.P.id context.M.self, H.E.app [obj_magic; H.E.app [H.E.id "ref"; H.E.unit]]]$ in $ce$ >>
           in
           let env_t = <:class_type< object $list:context.M.env_sig$ end >> in
           let class_targs = map H.T.var (fst p).transformer_parameters in
           let cproto_t =
             <:class_type< [ $H.T.app [H.T.id "ref"; H.T.app (H.T.id (env_tt type_name trait) :: class_targs)]$ ] -> object $list:[i_decl]$ end >>
           in
           let ct =
             let ct =
               match class_targs with
               | [] -> <:class_type< $id:env_tt type_name trait$ >>
               | _  -> <:class_type< $id:env_tt type_name trait$ [ $list:class_targs$ ] >>
             in
             let env_inh = <:class_sig_item< inherit $ct$ >> in
             <:class_type< object $list:[i_decl; env_inh]$ end >>
           in
           Plugin.generate_classes loc trait type_descriptor p (context.M.this, context.M.env, env_t, cproto, ce, cproto_t, ct)
        )
      in
      let case_branch patt met_name names types =
        let met_sig  =
          let make_a x y z = H.T.app [<:ctyp< GT.a >>; x; y; z; tpt] in
          let rec make_typ = function
          | Arbitrary t | Instance (t, _, _) -> t
          | Variable (t, name) -> make_a (H.T.var (inh_parameter_of name)) t (H.T.var (syn_parameter_of name))
          | Self     (t, _, _) -> make_a (H.T.var inh) t (H.T.var syn)
          | Tuple    (t, typs) -> H.T.tuple (map make_typ typs)
          in
          let typs = [H.T.var inh;
                      make_a (H.T.var inh) (H.T.app (H.T.id type_name :: map H.T.var type_parameters)) (H.T.var syn)
                     ] @
                     (map make_typ types)
          in
          H.T.arrow (typs @ [H.T.var syn])
        in
        let expr =
          let met = H.E.method_call (H.E.id trans) met_name in
          let garg f x =
            H.E.app [<:expr< GT.make >>; f; x; H.E.id tpo_name]
          in
          H.E.app (
            [met; H.E.id acc; garg (H.E.id self_name) (H.E.id subj)] @
            (map (fun (typ, x) ->
                    let rec augmented = function
                    | Arbitrary _ | Instance _ -> false
                    | Self      _ | Variable _ -> true
                    | Tuple (_, typs) -> exists augmented typs
                    in
                    let rec augment id = function
                    | Arbitrary _ | Instance _ ->  H.E.id id
                    | Variable (_, name)       -> garg (H.E.id (farg name)) (H.E.id id)
                    | Self     (typ, args, t)  ->
                        let name = get_type_handler (typ, args, t) in
                        garg name (H.E.id id)
                    | Tuple    (_, typs) as typ ->
                        if augmented typ
                        then
                          let generator  = generator#copy in
                          let components = mapi (fun i _ -> generator#generate (sprintf "e%d" i)) typs in
                          H.E.let_nrec
                            [H.P.tuple (map H.P.id components), H.E.id id]
                            (H.E.tuple (map (fun (name, typ) -> augment name typ) (combine components typs)))
                        else H.E.id id
                    in
                    augment x typ
                 )
                 (combine types names)
            )
          )
        in
        (patt, VaVal None, expr),
        [<:class_str_item< method virtual $lid:met_name$ : $met_sig$ >>],
        [<:class_sig_item< method virtual $lid:met_name$ : $met_sig$ >>],
        [<:class_sig_item< method $lid:met_name$ : $met_sig$ >>],
        []
      in
      let derived : (plugin_name * (properties * generator)) list =
        let plugin_processors = plugin_names |> map Plugin.get |> map (from_option_with_error loc) in
        let properties_and_generators = plugin_processors |> map (apply_to2 loc type_descriptor) in
        combine plugin_names properties_and_generators
      in
      let match_cases = (
        match description with
        | (`Variant constructors | `PolymorphicVariant constructors) -> constructors
        | (`Tuple _ | `Record _) as tuple_or_record -> [tuple_or_record]
        )
        |>
        map (
          function
          | `Tuple elements as case ->
              iter (add_derived_member case) derived;
              let args = mapi (fun i a -> sprintf "p%d" i) elements in
              let patt = H.P.tuple (map H.P.id args) in
              case_branch patt vmethod args elements

          | `Record fields as case ->
              iter (add_derived_member case) derived;
              let names, _, types = split3 fields in
              let args = map (fun a -> generator#generate a) names in
              let patt = H.P.record (map (fun (n, a) -> H.P.id n, H.P.id a) (combine names args)) in
              case_branch patt vmethod args types

          | `Constructor (cname, cargs) as case ->
              iter (add_derived_member case) derived;
              let args = mapi (fun i a -> sprintf "p%d" i) cargs in
              let patt = H.P.app ((if is_polyvar then H.P.variant else H.P.id) cname :: map H.P.id args) in
              case_branch patt (cmethod cname) args cargs

          | `Type (Instance (_, args, qname)) as case ->
              let args = map (function Variable (_, a) -> a | _ -> oops loc "unsupported case (non-variable in instance)") args in (* TODO *)
              iter (add_derived_member case) derived;
              let targs = flatten (map (fun a -> [a; inh_parameter_of a; syn_parameter_of a]) args) @ [inh; syn] in
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
              let expr =
                H.E.app (
                  (get_gcata qname) ::
                  (map (fun a -> H.E.id (farg a)) args @ [H.E.id trans; H.E.id acc; H.E.id subj])
               )
              in
              (H.P.alias (H.P.type_p qname) (H.P.id subj), VaVal None, expr),
              [<:class_str_item< inherit $ce$ >>],
              [<:class_sig_item< inherit $ct class_t$  >>],
              [<:class_sig_item< inherit $ct class_tt$ >>],
              [args, qname]

          | _ -> oops loc "unsupported case (internal error)"
        )
      in
      let subj = H.E.id subj in
      let local_defs_and_then expr =
        let local_defs =
          get_local_defs () @
          [H.P.id self_name, H.E.app (H.E.id (cata type_name) :: map H.E.id metargs);
           H.P.id tpo_name, tpo
          ]
        in
        match local_defs with
        | [] -> expr
        | _  -> H.E.letrec local_defs expr
      in
      let cases, methods, methods_sig, methods_sig_t, base_types = split5 match_cases in
      let type_methods, type_methods_sig = split (get_type_methods ()) in
      let base_types = flatten base_types in
      let is_abbrev = not is_polyvar && length base_types = 1 in
      let methods = flatten methods in
      let methods_sig = flatten methods_sig in
      let methods_sig_t = flatten methods_sig_t in
      (* proto_class_type -> meta_class_type *)
      let proto_class_type = <:class_type< object $list: methods_sig_t @ type_methods_sig$ end >> in
      let class_expr =
        let this = generator#generate "this" in
        let body =
          let args = map farg type_parameters in
          H.E.func (map H.P.id args) (H.E.app ((H.E.acc (map H.E.id ["GT"; "transform"])) :: map H.E.id (type_name :: args@[this])))
        in
        let met = <:class_str_item< method $lid:tmethod type_name$ = $body$ >> in
        <:class_expr< object ($H.P.id this$) $list:methods@[met]$ end >>
      in
      let class_type = <:class_type< object $list: methods_sig @ type_methods_sig$ end >> in
      let class_info ~is_virtual class_name class_definition = {
        ciLoc = loc;
        ciVir = Ploc.VaVal is_virtual;
        ciPrm = (loc, Ploc.VaVal (map (fun a -> Ploc.VaVal (Some a), None) transformer_parameters));
        ciNam = Ploc.VaVal class_name;
        ciExp = class_definition;
      }
      in
      (*
        let meta_class_def  = ... meta_class_type
        let meta_class_decl = ... meta_class_type

      *)
      let type_class_def  = <:str_item< class type $list: [class_info ~is_virtual:true (class_tt type_name) proto_class_type]$ >> in
      let type_class_decl = <:sig_item< class type $list: [class_info ~is_virtual:true (class_tt type_name) proto_class_type]$ >> in
      let class_def  = <:str_item< class $list: [class_info ~is_virtual:true (class_t type_name) class_expr]$ >> in
      let class_decl = <:sig_item< class $list: [class_info ~is_virtual:true (class_t type_name) class_type]$ >> in
      let body =
        if is_abbrev
        then let (_, _, expr), _ = hdtl loc cases in expr
        else local_defs_and_then (H.E.match_e subj cases)
      in
      (H.P.constr (H.P.id type_name) catype, H.E.record [generic_cata, H.E.id (cata type_name)]),
      (H.P.id (cata type_name), (H.E.func (map H.P.id args) body)),
      <:sig_item< value $type_name$ : $catype$ >>,
      (type_class_def, type_class_decl),
      (let env, protos, defs, edecls, pdecls, decls = split6 (map get_derived_classes derived) in
       class_def, (flatten env)@protos, defs, class_decl::(flatten edecls)@pdecls@decls)
    )
    descrs
  in
  let open_type td =
    match td.tdDef with
    | <:ctyp< [ = $list:lcons$ ] >> ->
        let from_vaval x = from_vaval loc x in
        let name      = type_open_t (from_vaval (snd (from_vaval td.tdNam))) in
        let args      = map (function (VaVal (Some name), _) -> name | _ -> oops loc "unsupported case (internal error)") (from_vaval td.tdPrm) in
        let gen       = name_generator args in
        let self      = gen#generate "self" in
        [{td with tdNam = VaVal (loc, VaVal name);
                  tdPrm = VaVal (map (fun name -> VaVal (Some name), None) (self::args));
                  tdDef = H.T.var self;
                  tdCon = VaVal [H.T.var self, <:ctyp< [> $list:lcons$ ]>>]
         }
        ]
    | _ -> []
  in
  let tuples, defs, decls, classes, derived_classes = split5 defs in
  let pnames, tnames = split tuples in
  let class_defs, class_decls = split classes in
  let derived_class_defs, derived_class_decls =
    let class_defs, protos, defs, class_decls = split4 derived_classes in
    class_defs @ (flatten protos) @ (flatten defs), flatten class_decls
  in
  let cata_def = <:str_item< value $list: [H.P.tuple pnames, H.E.letrec defs (H.E.tuple tnames)]$ >> in
  let type_decls = map snd3 mut_rec_type_decls in
  let open_t = flatten (map open_type type_decls) in
  let type_def = <:str_item< type $list: type_decls @ open_t$ >> in
  let type_decl = <:sig_item< type $list: type_decls @ open_t$ >> in
  <:str_item< declare $list: type_def :: class_defs @ [cata_def] @ derived_class_defs$ end >>,
  <:sig_item< declare $list: type_decl :: class_decls @ decls @ derived_class_decls$ end >>
