open GT

@type lam =
  | Var of string
  | App of lam * lam
  | Lam of string * lam
  with show, foldl

module StringSet = Set.Make (String)

class vars_transformer = object inherit [StringSet.t] @foldl[lam]
  method c_Var acc _ var_name = StringSet.add var_name acc
end

let vars : lam -> StringSet.t =
  transform(lam) (new vars_transformer) StringSet.empty

class free_vars_transformer = object inherit vars_transformer
  method c_Lam acc _ var_name body =
    let lam_free_vars = StringSet.remove var_name (body.fx StringSet.empty) in
    StringSet.union acc lam_free_vars
end

let free_vars : lam -> StringSet.t =
  transform(lam) (new free_vars_transformer) StringSet.empty
;;

(* subst function is not defined in main article *)
(*
type context = string -> string
type mtype = context -> (context, lam, lam, < >) a -> lam

class virtual reducer = object (this) inherit [context, lam] @lam
  method virtual arg : mtype
  method virtual subst_arg : mtype
  method head : mtype = fun context term -> term.fx context

  method c_Var _ self _ = self.x

  method c_App context self left right =
    match this#head context left with
    | Lam (var_name, body) ->
        self.f context
               (subst (*???*) context var_name (this#subst_arg context right) body)
    | other ->
        let reduced = self.f context other in
        App (reduced, this#arg context right)
end
*)


@type var =
  [ `Var of string
  ]

class ['v] var_eval_transformer = object inherit [string -> 'v, 'v] @var
  method c_Var env _ var_name = env var_name
end

@type 'e arith =
  [ `Add of 'e * 'e
  | `Mul of 'e * 'e
  ]

class ['e, 'inh] arith_eval_transformer = object
  inherit ['e, 'inh, int, 'inh, int] @arith

  method c_Add inh _ left right = left.fx inh + right.fx inh
  method c_Mul inh _ left right = left.fx inh * right.fx inh
end

@type 'e expr =
  [ var
  | 'e arith
  ]

class ['e] expr_eval_transformer = object
  inherit ['e, string -> int, int, string -> int, int] @expr
  inherit [int] var_eval_transformer
  inherit ['e, string -> int] arith_eval_transformer
end

let rec eval env expression =
  transform(expr) eval (new expr_eval_transformer) env expression


let test_expr = `Add (`Mul (`Var "x",
                            `Var "y"),
                      `Add (`Var "x",
                            `Var "z"))
let test_env = function
  | "x" -> 10
  | "y" -> 20
  | "z" -> 30
  | _ -> failwith "test_env: variable not found"

let test_expected = 240
let test_actual = eval test_env test_expr

let my_assert : bool -> unit = fun assertion ->
  if not assertion then
    print_endline "[FAIL]"

let () =
  my_assert (test_actual = test_expected)
