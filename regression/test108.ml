@type ('a1, 'a2, 'a3, 'a4) t1 =
  | Constr1 of 'a1
  | Constr2 of 'a2
  | Constr3 of 'a3
  | Constr4 of 'a4
  | ConstrRec of ('a1, 'a2, 'a3, 'a4) t1
  with show, eq, compare, foldl, foldr, map

@type ('b1, 'b2) t2 = ('b1, 'b2, 'b1 list, 'b1 * 'b2) t1
@type 'c t3 = ('c, 'c * 'c) t2

(*
type 'c t3 = ( 'c
             , 'c * 'c
             , 'c list
             , 'c * ('c * 'c)
             ) t1
*)
