@type ('a1, 'a2) t1 =
  | Constr1 of 'a1
  | Constr2 of 'a2

@type ('b1, 'b2) t2 = ('b2, 'b1) t1
