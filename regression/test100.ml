@type ('a, 'b) t1 = Constructor of 'a * 'b with map
@type ('a, 'b) t2 = ('a, 'b) t1

let test =
  GT.transform(t1) (fun a -> a) (fun b -> b) @map
