type token =
  | Comma
  | OpenP
  | CloseP
  | LName of string
  | UName of string

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


let parenth_list_parser item_parser (OpenP :: stream) =
  let until_close = lst_ana' item_parser (fun item -> function
    | CloseP :: _ -> `Nil
    | Comma :: xs | xs -> `Cons (item xs, pass)
  ) in
  let (l, CloseP :: rest) = until_close stream in
  (l, rest)

let rec expr_parser stream =
  expr_ana' (parenth_list_parser expr_parser) (fun el -> function
    | UName constr_name :: xs -> `Constr ((constr_name, xs), fun _ -> el xs)
    | LName func_name :: OpenP :: xs -> `Call ((func_name, OpenP :: xs), fun ys -> el ys)
    | LName var_name :: xs -> `Var (var_name, xs)
  ) stream

let def_parser =
  let var_list_parser = parenth_list_parser (fun (LName var_name) :: xs -> (var_name, xs)) in
  def_ana' var_list_parser (parenth_list_parser expr_parser) (fun sl el -> function
    | LName func_name :: OpenP :: UName constr_name :: xs ->
        `GDef ((func_name, xs), pass' constr_name, sl, fun CloseP :: ys -> expr_parser ys)
    | LName func_name :: xs -> `FDef ((func_name, xs), sl, expr_parser))

let program_parser stream = fst (parenth_list_parser def_parser stream) (* 23 LOC *)


let parenth_list_parser2 item_parser (OpenP :: stream) =
  let rec until_close = function
    | CloseP :: xs -> (Nil, xs)
    | Comma :: xs | xs ->
        let (head, rest) = item_parser xs in
        let (tail, rest') = until_close rest in
        (Cons (head, tail), rest')
  in
  until_close stream

let rec expr_parser2 stream =
  let expr_list_parser = parenth_list_parser2 expr_parser2 in
  match stream with
  | UName constr_name :: xs ->
      let (args, rest) = expr_list_parser xs in
      (Constr (constr_name, args), rest)
  | LName func_name :: OpenP :: xs ->
      let (args, rest) = expr_list_parser (OpenP :: xs) in
      (Call (func_name, args), rest)
  | LName var_name :: xs -> (Var var_name, xs)

let def_parser2 stream =
  let var_list_parser = parenth_list_parser2 (fun (LName var_name) :: xs -> (var_name, xs)) in
  match stream with
    | LName func_name :: OpenP :: UName constr_name :: xs ->
        let (args, CloseP :: rest) = var_list_parser xs in
        let (expr, rest') = expr_parser2 rest in
        (GDef (func_name, constr_name, args, expr), rest')
    | LName func_name :: xs ->
        let (args, rest) = var_list_parser xs in
        let (expr, rest') = expr_parser2 rest in
        (FDef (func_name, args, expr), rest')

let program_parser2 stream = fst (parenth_list_parser2 def_parser2 stream) (* 34 LOC *)


let expr_stream =
  [ UName "Cons"; OpenP;
      UName "S"; OpenP; UName "Z"; OpenP; CloseP; CloseP; Comma;
    UName "Cons"; OpenP;
      LName "f"; OpenP; LName "x"; Comma; LName "y"; Comma; LName "z"; CloseP; Comma;
      UName "Nil"; OpenP; CloseP;
    CloseP; CloseP
  ]

let expr_expected : expr' =
  Constr ("Cons", Cons (
    Constr ("S", Cons(Constr ("Z", Nil), Nil)), Cons (
  Constr ("Cons", Cons (
    Call ("f", Cons (Var "x", Cons (Var "y", Cons (Var "z", Nil)))), Cons (
  Constr ("Nil", Nil), Nil))), Nil)))

let fdef_stream =
  [ LName "f"; OpenP; LName "x"; Comma; LName "y"; Comma; LName "z"; CloseP;
  ] @ expr_stream

let gdef_stream =
  [ LName "g"; OpenP; UName "S"; OpenP; LName "x"; CloseP; CloseP;
  ] @ expr_stream

let program_stream =
  [ OpenP ] @ fdef_stream @ [ Comma ] @ gdef_stream @ [ CloseP ]

let expr_parser_test pexpr =
  let actual = pexpr expr_stream |> fst in
  if actual <> expr_expected
  then Printf.printf "[FAIL]\n"

let program_expected : def' lst =
  let fdef = FDef ("f", Cons ("x", Cons ("y", Cons ("z", Nil))), expr_expected) in
  let gdef = GDef ("g", "S", Cons ("x", Nil), expr_expected) in
  Cons (fdef, Cons (gdef, Nil))

let program_parser_test pparser =
  let actual = pparser program_stream in
  if actual <> program_expected
  then Printf.printf "[FAIL]\n"

let () =
  expr_parser_test expr_parser;
  expr_parser_test expr_parser2;
  program_parser_test program_parser;
  program_parser_test program_parser2
