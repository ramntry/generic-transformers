open GT

@type 'a bst =
  | Null
  | Node of 'a * 'a bst * 'a bst

let bst_step = fun _ -> function
  | ([], _) -> `Null
  | (x :: xs, max) ->
      if x > max
      then `Null
      else `Node ((x, (xs, x)), pass, fun (tail, _) -> (tail, max))

let custom_bst_ana preorder = unfold'(bst) () bst_step (preorder, max_int)

let () =
  let arg = [5; 3; 4; 7; 6; 8] in
  let expected = Node (5, Node (3, Null, Node (4, Null, Null)),
                          Node (7, Node (6, Null, Null), Node (8, Null, Null)))
  in
  let actual =  custom_bst_ana arg in
  if actual <> expected then Printf.printf "[FAIL]\n"
