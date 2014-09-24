(**************************************************************************
 *  Copyright (C) 2012-2013
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

open Pcaml
open MLast
open Ploc
open Dynlink
open List
open Printf

type parameter = string
type type_name = string
type qualified_name = string list
type plugin_name = string

type typ  =
  | Arbitrary of ctyp
  | Variable  of ctyp * string
  | Self      of ctyp * parameter list * qualified_name
  | Tuple     of ctyp * typ list
  | Instance  of ctyp * typ list * qualified_name

let ctyp_of = function
  | Arbitrary t
  | Variable (t, _)
  | Self     (t, _, _)
  | Instance (t, _, _)
  | Tuple    (t, _) -> t

exception Generic_extension of string

let oops loc str = Ploc.raise loc (Generic_extension str)

let from_vaval loc = function
  | VaVal v -> v
  | _ -> oops loc "could not get VaVal _ (should not happen)"

let hdtl loc = function
  | h::t -> (h, t)
  | _    -> oops loc "empty list (should not happen)"

let map_last loc f l =
  let h, tl = hdtl loc (rev l) in
  rev (f h :: tl)

exception Bad_plugin of string

let rec name_generator reserved_names =
  let module S = Set.Make (String) in
  let s = ref (fold_right S.add reserved_names S.empty) in
  object(self)
    method copy = name_generator (S.elements !s)
    method generate prompt =
      if S.mem prompt !s
      then self#generate (prompt ^ "_")
      else (
        s := S.add prompt !s;
        prompt
      )
  end

let cata type_name = type_name ^ "_gcata"
let syn_parameter type_parameter = type_parameter ^ "_syn"
let inh_parameter type_parameter = type_parameter ^ "_inh"
let parameter_transform parameter = "transform_" ^ parameter
let tname         name      = "t" ^ name
let cmethod       c         = "c_" ^ c
let vmethod                 = "value"
let tmethod       t         = "t_" ^ t
let class_t       name      = name ^ "_t"
let class_tt      name      = name ^ "_tt"
let trait_t       typ trait = class_t (if trait <> "" then sprintf "%s_%s" trait typ else typ)
let trait_proto_t typ trait = sprintf "%s_proto_%s" trait typ
let env_tt        typ trait = trait ^ "_" ^ typ ^ "_env_tt"
let tags_t        typ       = typ ^ "_tags"
let type_open_t   typ       = typ ^ "_open"

let load_path = ref []

let () =
  Pcaml.add_option "-L"
    (Arg.String (fun dir -> load_path := !load_path @ [dir]))
    "<dir> Add <dir> to the list of include directories."

type properties = {
  inh_t : ctyp;
  syn_t : ctyp;
  transformer_parameters : parameter list;
  inh_t_of_parameter : parameter -> ctyp;
  syn_t_of_parameter : parameter -> ctyp;
}

type type_descriptor = {
  is_polymorphic_variant : bool;
  parameters : parameter list;
  name : type_name;
  default_properties : properties;
}

type env = {
  inh : string;
  subject : string;
  new_name : string -> string;
  trait : plugin_name -> typ -> expr option;
}

class virtual plugin_generator =
  object
    method header     = ([] : str_item list)
    method header_sig = ([] : sig_item list)
    method virtual constructor : env -> string -> (string * typ) list -> expr
    method virtual tuple       : env -> (string * typ) list -> expr
    method virtual record      : env -> (string * (string * bool * typ)) list -> expr
  end

type processor = loc -> type_descriptor -> properties * plugin_generator

module Helper (L : sig val loc : loc end) =
  struct

    open L

    let id lid uid s =
      if String.length s = 0
      then invalid_arg "Plugin.Helper.id: empty string"
      else (if s.[0] = Char.uppercase s.[0] then uid else lid) s

    let qname acc id = function
    | []    -> invalid_arg "Plugin.Helper.qname: empty string list"
    | h::tl -> fold_left (fun q n -> acc q (id n)) (id h) tl

    module T =
      struct

        let lid         = (fun s -> <:ctyp< $lid:s$ >>)
        let uid         = (fun s -> <:ctyp< $uid:s$ >>)
        let id          = id lid uid
        let acc         = qname (fun x y -> <:ctyp< $x$ . $y$ >>) (fun x -> x)
        let qname       = qname (fun x y -> <:ctyp< $x$ . $y$ >>) id
        let alias t1 t2 = <:ctyp< $t1$ as $t2$ >>
        let wildcard    = <:ctyp< _ >>

        let app = function
        | []    -> invalid_arg "Plugin.Helper.T.app: empty expression list"
        | h::tl -> fold_left (fun a e -> <:ctyp< $a$ $e$ >>) h tl

        let arrow = function
        | [] -> invalid_arg "Plugin.Helper.T.arrow: empty expression list"
        | ll -> let h, tl = hdtl loc (rev ll) in fold_right (fun e a -> <:ctyp< $e$ -> $a$ >>) (rev tl) h

        let class_t   qname      = <:ctyp< # $list:qname$ >>
        let label     s t        = <:ctyp< ~$s$: $t$ >>
        let manifest  t1 priv t2 = <:ctyp< $t1$ == $priv:priv$ $t2$ >>

        let obj (methods : (string * ctyp) list) ~is_open_type =
          <:ctyp< < $list: methods$ $flag: is_open_type$ > >>

        let opt_label s t        = <:ctyp< ?$s$: $t$ >>
        let package   mt         = <:ctyp< (module $mt$) >>
        let polymorph lst t      = <:ctyp< ! $list:lst$ . $t$ >>
        let var       s          = <:ctyp< '$s$ >>
        let record    lst        = <:ctyp< { $list:lst$ } >>
        let sum       lst        = <:ctyp< [ $list:lst$ ] >>
        let tuple     lst        = <:ctyp< ( $list:lst$ ) >>

        let pv_constr s = function
        | []   -> <:poly_variant< ` $s$ >>
        | args -> <:poly_variant< ` $s$ of $list:args$ >>

        let pv_and_constr       s args = <:poly_variant< ` $s$ of & $list:args$ >>
        let pv_type             t      = <:poly_variant< $t$ >>
        let eq_variant          lpv    = <:ctyp< [ = $list:lpv$ ] >>
        let more_variant        lpv    = <:ctyp< [ > $list:lpv$ ] >>
        let less_variant        lpv    = <:ctyp< [ < $list:lpv$ ] >>
        let less_constr_variant lpv ls = <:ctyp< [ < $list:lpv$ > $list:ls$ ] >>

      end

    module P =
      struct

        let lid         = (fun s -> <:patt< $lid:s$ >>)
        let uid         = (fun s -> <:patt< $uid:s$ >>)
        let id          = id lid uid
        let acc         = qname (fun x y -> <:patt< $x$ . $y$ >>) (fun x -> x)
        let qname       = qname (fun x y -> <:patt< $x$ . $y$ >>) id
        let alias t1 t2 = <:patt< ($t1$ as $t2$ ) >>
        let wildcard    = <:patt< _ >>

        let app = function
        | []    -> invalid_arg "Plugin.Helper.P.app: empty expression list"
        | h::tl -> fold_left (fun e a -> <:patt< $e$ $a$ >>) h tl

        let array      lp    = <:patt< [| $list:lp$ |] >>
        let char       s     = <:patt< $chr:s$ >>
        let float      s     = <:patt< $flo:s$ >>
        let int        s     = <:patt< $int:s$ >>
        let int32      s     = <:patt< $int32:s$ >>
        let int64      s     = <:patt< $int64:s$ >>
        let nativeint  s     = <:patt< $nativeint:s$ >>
        let label      p1 p2 = <:patt< ~{$p1$ $opt:p2$} >>
        let lazy_p     p     = <:patt< lazy $p$ >>
        let newtype    s     = <:patt< (type $lid:s$) >>
        let opt_label  p oe  = <:patt< ?{$p$ $opt:oe$} >>
        let or_p       p1 p2 = <:patt< $p1$ | $p2$ >>
        let record     lpp   = <:patt< { $list:lpp$ } >>
        let range      p1 p2 = <:patt< $p1$ .. $p2$ >>
        let str        s     = <:patt< $str:s$ >>
        let tuple      lp    = <:patt< ($list:lp$) >>
        let constr     p t   = <:patt< ($p$ : $t$) >>
        let type_p     ls    = <:patt< # $list:ls$ >>
        let module_unp s     = function None -> <:patt< (module $uid:s$) >> | Some mt -> <:patt< (module $uid:s$ : $mt$) >>
        let variant    s     = <:patt< ` $s$ >>

      end

    module E =
      struct

        let lid   = (fun s -> <:expr< $lid:s$ >>)
        let uid   = (fun s -> <:expr< $uid:s$ >>)
        let id    = id lid uid
        let acc   = qname (fun x y -> <:expr< $x$ . $y$ >>) (fun x -> x)
        let qname = qname (fun x y -> <:expr< $x$ . $y$ >>) id

        let app   = function
        | []    -> invalid_arg "Plugin.Helper.E.app: empty expression list"
        | h::tl -> fold_left (fun a e -> <:expr< $a$ $e$ >>) h tl

        let abstr       list       = <:expr< fun [ $list:list$ ] >>
        let func        args body  = fold_right
                                       (fun arg expr -> <:expr< fun [ $list:[arg, VaVal None, expr]$ ] >>)
                                       args
                                       body
        let aelem       a i        = <:expr< $a$ . ( $i$ ) >>
        let belem       a i        = <:expr< $a$ . { $i$ } >>
        let array       list       = <:expr< [| $list:list$ |] >>
        let assrt       e          = <:expr< assert $e$ >>
        let assign      x y        = <:expr< $x$ := $y$ >>
        let char        s          = <:expr< $chr:s$ >>
        let coerce      e t        = <:expr< ( $e$ :> $t$ ) >>
        let float       s          = <:expr< $flo:s$ >>
        let for_to      i l u list = <:expr< for $lid:i$ = $l$ to     $u$ do { $list:list$ } >>
        let for_downto  i l u list = <:expr< for $lid:i$ = $l$ downto $u$ do { $list:list$ } >>
        let if_then     c t e      = <:expr< if $c$ then $t$ else $e$ >>
        let int         s          = <:expr< $int:s$ >>
        let int32       s          = <:expr< $int32:s$ >>
        let int64       s          = <:expr< $int64:s$ >>
        let nat         s          = <:expr< $nativeint:s$ >>
        let label       p e        = <:expr< ~{$p$ $opt:e$} >>
        let lazy_e      e          = <:expr< lazy $e$ >>
        let letrec      pe e       = <:expr< let rec $list:pe$ in $e$ >>
        let let_nrec    pe e       = <:expr< let $list:pe$ in $e$ >>
        let let_module  s me e     = <:expr< let module $uid:s$ = $me$ in $e$ >>
        let match_e     e pe       = <:expr< match $e$ with [ $list:pe$ ] >>
        let new_e       list       = <:expr< new $list:list$ >>
        let obj ?self_pattern list_of_items = <:expr< object $opt: self_pattern$ $list: list_of_items$ end >>
        let opt_label   p oe       = <:expr< ?{ $p$ $opt:oe$ } >>
        let override    list       = <:expr< {< $list:list$ >} >>
        let module_e    me         = <:expr< ( module $me$ ) >>
        let module_t    me t       = <:expr< ( module $me$ : $t$ ) >>
        let record      list       = <:expr< { $list:list$ } >>
        let record_with e list     = <:expr< { ($e$) with $list:list$} >>
        let seq         list       = <:expr< do { $list:list$ } >>
        let method_selection e m        = <:expr< $e$ # $m$ >>
        let selem       s i        = <:expr< $s$ . [$i$] >>
        let str         s          = <:expr< $str:s$ >>
        let try_e       e list     = <:expr< try $e$ with [ $list:list$ ] >>
        let tuple       list       = <:expr< ( $list:list$ ) >>
        let constr      e t        = <:expr< ( $e$ : $t$ ) >>
        let variant     s          = <:expr< ` $s$ >>
        let while_e     e list     = <:expr< while $e$ do { $list:list$ } >>
        let unit                   = <:expr< () >>

        let gt_field f e = acc [e; uid "GT"; lid f]
        let gt_f         = gt_field "f"
        let gt_x         = gt_field "x"
        let gt_fx        = gt_field "fx"
        let gt_tp e p    = method_selection (gt_field "t" e) p

      end
  end

let generate_classes loc trait descr (prop, generator) (this, env, env_t, b_proto_def, b_def, b_proto_decl, b_decl) =
  let class_targs = prop.transformer_parameters in
  let def n b = {
    ciLoc = loc;
    ciVir = Ploc.VaVal false;
    ciPrm = (loc, Ploc.VaVal (map (fun a -> Ploc.VaVal (Some a), None) class_targs));
    ciNam = Ploc.VaVal n;
    ciExp = b
  }
  in
  let ce =
    let p = <:patt< $lid:env$ >> in
    <:class_expr< fun $p$ -> $b_proto_def$ >>
  in
  generator#header @ [<:str_item< class type $list:[def (env_tt descr.name trait) env_t]$ >>],
  <:str_item< class $list:[def (trait_proto_t descr.name trait) ce]$ >>,
  <:str_item< class $list:[def (trait_t descr.name trait) b_def]$ >>,
  generator#header_sig @ [<:sig_item< class type $list:[def (env_tt descr.name trait) env_t]$ >>],
  <:sig_item< class $list:[def (trait_proto_t descr.name trait) b_proto_decl]$ >>,
  <:sig_item< class $list:[def (trait_t descr.name trait) b_decl]$ >>

let generate_inherit base_class loc qname arg descr prop =
  let args =
    if base_class
    then
      flatten (map (fun a -> [<:ctyp< ' $a$ >>; prop.inh_t_of_parameter a; prop.syn_t_of_parameter a]) descr.parameters) @
      [prop.inh_t; prop.syn_t]
    else map (fun a -> <:ctyp< ' $a$ >>) prop.transformer_parameters
  in
  let ce =
    let ce = match args with [] -> <:class_expr< $list:qname$ >> | _ -> <:class_expr< [ $list:args$ ] $list:qname$ >> in
    match arg with
    | None -> ce
    | Some (e, _) -> <:class_expr< $ce$ $e$ >>
  in
  let ct =
    let h, t = hdtl loc qname in
    let ct   =
      fold_left
        (fun t id -> let id = <:class_type< $id:id$ >> in <:class_type< $t$ . $id$ >>)
        <:class_type< $id:h$ >>
      t
    in
    let ct = match args with [] -> ct | _ -> <:class_type< $ct$ [ $list:args$ ] >> in
    match arg with
    | None -> ct
    | Some (_, t) -> <:class_type< [ $t$ ] -> $ct$ >>
  in
  <:class_str_item< inherit $ce$ >>,
  <:class_sig_item< inherit $ct$ >>

module StringMap =
  struct
    type 'value t = (string * 'value) list

    let empty = []
    let add key value t = (key, value) :: t
    let mem = mem_assoc
    let find = assoc

    let option_find key t =
      try
        Some (find key t)
      with Not_found -> None
  end

let plugin_processors : processor StringMap.t ref = ref StringMap.empty

let register name processor =
  if not (StringMap.mem name !plugin_processors)
  then plugin_processors := StringMap.add name processor !plugin_processors

let get name =
  if (StringMap.mem name !plugin_processors)
  then Some (StringMap.find name !plugin_processors)
  else None

let load_plugins plugin_names =
  let load_one name =
    match get name with
    | None ->
        let filename = name ^ ".cmo" in
        let ok =
          fold_left
            (fun ok path ->
              if not ok then
                let fullname = Filename.concat path filename in
                try
                  loadfile fullname;
                  true
                with
                | Error (File_not_found _) -> false
                | Error err -> Pervasives.raise (Bad_plugin (error_message err))
              else ok
            )
            false
            !load_path
        in
        if not ok
        then Pervasives.raise (Bad_plugin (sprintf "Plugin \"%s\" bytecode file not found" name))
        else begin
          match get name with
          | None   -> Pervasives.raise (Bad_plugin (sprintf "Plugin \"%s\" was not properly initialized" name))
          | Some _ -> ()
        end
    | Some _ -> ()
  in
  iter load_one plugin_names
