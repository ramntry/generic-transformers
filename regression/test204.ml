type token =
  | Comma
  | OpenParenth
  | CloseParenth
  | LowerName of string
  | UpperName of string

@type 'a lst =
  | Nil
  | Cons of 'a * 'a lst

@type 'el expr =
  | Var of string
  | Constr of string * 'el
  | Call of string * 'el

@type ('sl, 'el) def =
  | FDef of string * 'sl * 'el expr
  | GDef of string * string * 'sl * 'el expr

let pass = fun x -> x

let parenth_list_parser item_parser stream =
  let until_close = lst_ana' item_parser (fun item -> function
    | (Comma | OpenParenth) :: xs -> `Cons (item xs, pass)
    | CloseParenth :: xs -> `Nil
  ) in
  let (lst, CloseParenth :: rest) = until_close stream in
  (lst, rest)

let rec expr_parser stream =
  expr_ana' (parenth_list_parser expr_parser) (fun el -> function
    | UpperName constr_name :: xs -> `Constr (constr_name, el xs)
    | LowerName func_name :: OpenParenth :: xs -> `Call (func_name, el (OpenParenth :: xs))
    | LowerName var_name :: xs -> `Var var_name
  ) stream

(*
let name_parser (Id name :: rest) = (Name name, rest)


let test_parenth_var_list () =
  let stream = [OpenParenth; Id "x"; Comma; Id "y"; CloseParenth] in
  let expected = Cons (Name "x", Cons ( Name "y", Nil)) in
  let (actual, _) = parenth_list_parser name_parser stream in
  if actual <> expected
  then Printf.printf "[FAIL]\n"

let () =
  test_parenth_var_list ()
*)
