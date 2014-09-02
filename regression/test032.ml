open GT

@type test = string with show, map, foldl, foldr, eq, compare

let () =
  Printf.printf "%s\n" (transform(test) (new @show[test]) () "abc")
