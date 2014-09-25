@type ('a1, 'a2, 'a3) t1 =
  | Constr1 of 'a1
  | Constr2 of 'a2
  | Constr3 of 'a3

@type 'b1 t2 = ('b1, int, 'b1 list) t1
