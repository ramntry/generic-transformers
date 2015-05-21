@type 'a lst =
  | Nil
  | Cons of 'a * 'a lst

let step item = function
  | 0 -> `Nil
  | n -> `Cons (item n, n - 1)

let step2 = step (ana (step (fun n -> n)))

let () =
  let actual = ana step2 3 in
  let expected = Cons (Cons (3, Cons (2, Cons (1, Nil)))
               , Cons (Cons (2, Cons (1, Nil))
               , Cons (Cons (1, Nil)
               , Nil)))
  in
  if actual <> expected
  then Printf.printf "[FAIL]\n"
