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

class ['e, 'inh] arith_eval_transformer = object inherit ['e, 'inh, int, 'inh, int] @arith
  method c_Add inh _ left right = left.fx inh + right.fx inh
  method c_Mul inh _ left right = left.fx inh * right.fx inh
end
