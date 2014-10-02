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


module ByHand = struct

module StringSet = Set.Make (String)

let lam_fold self acc = function
  | Var _ -> acc
  | App (func, arg) -> self (self acc func) arg
  | Lam (_, body) -> self acc body

let open_vars self acc = function
  | Var var_name -> StringSet.add var_name acc
  | other -> lam_fold self acc other

let vars : lam -> StringSet.t =
  let rec vars_acc acc term = open_vars vars_acc acc term in
  vars_acc StringSet.empty

let open_free_vars self acc = function
  | Lam (var_name, body) ->
      let lam_free_vars = StringSet.remove var_name (self StringSet.empty body) in
      StringSet.union acc lam_free_vars
  | other -> open_vars self acc other

let free_vars : lam -> StringSet.t =
  let rec free_vars_acc acc term = open_free_vars free_vars_acc acc term in
  free_vars_acc StringSet.empty

end

let test_term =
  Lam ("x",
       App (Lam ("y",
                 Var "y"),
            Var "z"))

let string_set_of_list xs = List.fold_right StringSet.add xs StringSet.empty

let my_assert : bool -> unit = fun assertion ->
  if not assertion then
    print_endline "[FAIL]"

let vars_expected = ["y"; "z"]
let free_vars_expected = ["z"]

let () =
  my_assert (StringSet.elements (vars test_term) = vars_expected);
  my_assert (StringSet.elements (free_vars test_term) = free_vars_expected);
  my_assert (StringSet.elements (ByHand.vars test_term) = vars_expected);
  my_assert (StringSet.elements (ByHand.free_vars test_term) = free_vars_expected);
