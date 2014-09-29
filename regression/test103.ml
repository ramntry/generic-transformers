@type 'a t1 =
  | Constr1 of 'a
  with show

@type 'b t2 = 'b t1
