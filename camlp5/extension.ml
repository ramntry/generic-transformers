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

let from_option ~default = function
  | Some v -> v
  | None -> default

EXTEND
  GLOBAL: sig_item str_item class_expr expr ctyp type_decl;

  class_expr: BEFORE "simple" [[
    "["; ct = ctyp; ","; ctcl = LIST1 ctyp SEP ","; "]"; ci = class_longident ->
      <:class_expr< [ $list:(ct :: ctcl)$ ] $list:ci$ >>
  | "["; ct = ctyp; "]"; ci = class_longident ->
      <:class_expr< [ $ct$ ] $list:ci$ >>
  | ci = class_longident -> <:class_expr< $list:ci$ >>
  ]];

  expr: LEVEL "expr1" [[
    "unfold"; "("; tname = LIDENT; ")" -> <:expr< $lid: tname ^ "_ana'"$ >>
  ]];

  expr: LEVEL "expr1" [[
    "unfold'"; "("; tname = LIDENT; ")" -> <:expr< $lid: tname ^ "_ana"$ >>
  ]];

  expr: BEFORE "simple" [
   LEFTA [ "new"; i = V class_longident "list" -> <:expr< new $_list:i$ >> ]
  ];

  ctyp: BEFORE "simple" [[
    "#"; id = V class_longident "list" -> <:ctyp< # $_list:id$ >>
  ]];

  class_longident: [[
    "@"; ci=qname; t=OPT trait ->
      let n, q = Plugin.hdtl loc (rev ci) in
      rev ((match t with None -> Plugin.class_t n | Some t -> Plugin.trait_t t n)::q)

  | "+"; ci=qname; t=trait ->
      let n, q = Plugin.hdtl loc (rev ci) in
      rev ((Plugin.trait_proto_t t n) :: q)

  | ci=qname -> ci
  ]];

  qname: [[
    n = LIDENT              -> [n]
  | m = UIDENT; "."; q=SELF -> m :: q
  ]];

  trait: [[
    "["; id = LIDENT; "]" ->
      id
  ]];

  str_item: LEVEL "top" [[
    "@"; "type"; mut_rec_type_decls = LIST1 type_decl_with_escape_or_deriving SEP "and" ->
      fst (Core.generate loc mut_rec_type_decls)
  ]];

  sig_item: LEVEL "top" [[
    "@"; "type"; mut_rec_type_decls = LIST1 type_decl_with_escape_or_deriving SEP "and" ->
      snd (Core.generate loc mut_rec_type_decls)
  ]];

type_decl_with_escape_or_deriving: [[
  (** An escape declaration for non-supported cases. Will be ignored by the framework. *)
    "["; type_declaration = type_decl; "]" ->
      (loc, type_declaration, None)

  (** An ordinary type declaration. If list of plugin names is empty only a generic traversal function and an abstract
   *  transformer class and auxiliary class types will be generated, otherwise the plugins code as well *)
  | type_declaration = type_decl; maybe_plugin_names = OPT with_annotation ->
      (loc, type_declaration, Some (from_option ~default:[] maybe_plugin_names))
  ]];

  with_annotation: [[
    "with"; plugin_names = LIST1 LIDENT SEP "," ->
      plugin_names
  ]];

END;
