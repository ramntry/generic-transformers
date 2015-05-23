@type 'a lst =
  | Nil
  | Cons of 'a * 'a lst

@type 'a bst =
  | Null
  | Node of 'a * 'a bst * 'a bst

let range =
  lst_ana'
    (fun k -> (k, k))
    (fun item -> function
      | 0 -> `Nil
      | k -> `Cons (item k, fun _ -> k - 1))

let range2 =
  bst_ana
    range
    (fun item -> function
      | 0 -> `Null
      | 1 -> `Null
      | k -> `Node (item k, (fun _ -> k - 1), (fun _ -> k - 2)))

let test () =
  let rec from_list = function
    | [] -> Nil
    | x :: xs -> Cons (x, from_list xs)
  in
  let expected =
    Node (from_list [4; 3; 2; 1]
      , Node (from_list [3; 2; 1]
        , Node (from_list [2; 1]
          , Node (from_list [1], Null, Null)
          , Null)
        , Node (from_list [1], Null, Null))
      , Node (from_list [2; 1]
        , Node (from_list [1], Null, Null)
        , Null))
  in
  let actual = range2 4 in
  if actual <> expected
  then Printf.printf "[FAIL]\n"
