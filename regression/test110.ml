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
