@type 'a lst =
  | Nil
  | Cons of 'a * 'a lst

let custom_lst_ana = lst_ana (fun n -> (n, n)) (fun item -> function 0 -> `Nil | n -> `Cons (item n, fun _ -> n - 1))

let () =
  let expected = Cons (3, Cons (2, Cons (1, Nil))) in
  let actual = custom_lst_ana 3 in
  if actual <> expected then Printf.printf "[FAIL]\n"
