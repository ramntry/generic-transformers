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

type expr' = expr' lst expr

@type ('sl, 'el) def =
  | FDef of string * 'sl * 'el expr
  | GDef of string * string * 'sl * 'el expr

type def' = (string lst, expr' lst) def

let pass = fun x -> x
let pass' r = fun x -> (r, x)


let parenth_list_parser item_parser stream =
  let until_close = lst_ana' item_parser (fun item -> function
    | OpenParenth :: CloseParenth :: xs -> `Nil
    | CloseParenth :: xs -> `Nil
    | (Comma | OpenParenth) :: xs -> `Cons (item xs, pass)
  ) in
  match until_close stream  with
  | (l, (OpenParenth :: CloseParenth :: rest | CloseParenth :: rest)) -> (l, rest)

let rec expr_parser stream =
  expr_ana' (parenth_list_parser expr_parser) (fun el -> function
    | UpperName constr_name :: xs -> `Constr ((constr_name, xs), fun _ -> el xs)
    | LowerName func_name :: OpenParenth :: xs ->
        `Call ((func_name, OpenParenth :: xs), fun ys -> el ys)
    | LowerName var_name :: xs -> `Var (var_name, xs)
  ) stream

let var_list_parser = parenth_list_parser (fun (LowerName var_name) :: xs -> (var_name, xs))

let def_parser =
  def_ana' var_list_parser (parenth_list_parser expr_parser) (fun sl el -> function
    | LowerName func_name :: OpenParenth :: UpperName constr_name :: xs ->
        `GDef ((func_name, xs), pass' constr_name, sl, fun CloseParenth :: ys -> expr_parser ys)
    | LowerName func_name :: xs -> `FDef ((func_name, xs), sl, expr_parser)
  )

let program_parser stream = fst (parenth_list_parser def_parser stream) (* 27 LOC *)


let expr_stream =
  [ UpperName "Cons"; OpenParenth;
      UpperName "S"; OpenParenth; UpperName "Z"; OpenParenth; CloseParenth; CloseParenth; Comma;
    UpperName "Cons"; OpenParenth;
      LowerName "f"; OpenParenth; LowerName "x"; Comma; LowerName "y"; Comma; LowerName "z"; CloseParenth; Comma;
      UpperName "Nil"; OpenParenth; CloseParenth;
    CloseParenth; CloseParenth
  ]

let expr_expected : expr' =
  Constr ("Cons", Cons (
    Constr ("S", Cons(Constr ("Z", Nil), Nil)), Cons (
  Constr ("Cons", Cons (
    Call ("f", Cons (Var "x", Cons (Var "y", Cons (Var "z", Nil)))), Cons (
  Constr ("Nil", Nil), Nil))), Nil)))

let fdef_stream =
  [ LowerName "f"; OpenParenth; LowerName "x"; Comma; LowerName "y"; Comma; LowerName "z"; CloseParenth;
  ] @ expr_stream

let gdef_stream =
  [ LowerName "g"; OpenParenth; UpperName "S"; OpenParenth; LowerName "x"; CloseParenth; CloseParenth;
  ] @ expr_stream

let program_stream =
  [ OpenParenth ] @ fdef_stream @ [ Comma ] @ gdef_stream @ [ CloseParenth ]

let expr_parser_test () =
  let actual = expr_parser expr_stream |> fst in
  if actual <> expr_expected
  then Printf.printf "[FAIL]\n"

let program_expected : def' lst =
  let fdef = FDef ("f", Cons ("x", Cons ("y", Cons ("z", Nil))), expr_expected) in
  let gdef = GDef ("g", "S", Cons ("x", Nil), expr_expected) in
  Cons (fdef, Cons (gdef, Nil))

let program_parser_test () =
  let actual = program_parser program_stream in
  if actual <> program_expected
  then Printf.printf "[FAIL]\n"

let () =
  expr_parser_test ();
  program_parser_test ()
