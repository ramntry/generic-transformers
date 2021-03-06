@type a = [`A of GT.int | `B of GT.string] with show, eq, compare
@type b = [`C of GT.int | `D of GT.string] with show, eq, compare
@type c = [a | b] with show, eq, compare
 
let _ =
  let x = `A 3 in
  let y = `D "2" in
  Printf.printf "%s\n" (GT.transform(a) (new @show[a]) () x);
  Printf.printf "%s\n" (GT.transform(b) (new @show[b]) () y);
  Printf.printf "%s\n" (GT.transform(c) (new @show[c]) () x);
  Printf.printf "%s\n" (GT.transform(c) (new @show[c]) () y);
  Printf.printf "%b\n" (GT.transform(a) (new @eq[a]) x x);
  Printf.printf "%b\n" (GT.transform(b) (new @eq[b]) y y);
  Printf.printf "%b\n" (GT.transform(c) (new @eq[c]) x x);
  Printf.printf "%b\n" (GT.transform(c) (new @eq[c]) y y);
  Printf.printf "%b\n" (GT.transform(c) (new @eq[c]) x y)
