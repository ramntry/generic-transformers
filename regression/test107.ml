@type ('alpha1, 'alpha2, 'alpha3, 'alpha4) t1 =
  | Constr1 of 'alpha1
  | Constr2 of 'alpha2
  | Constr3 of 'alpha3
  | Constr4 of 'alpha4
  | ConstrRec of ('alpha1, 'alpha2, 'alpha3, 'alpha4) t1

@type ('beta1, 'beta2) t2 = ('beta1, int, 'beta1 list, 'beta1 * 'beta2) t1
