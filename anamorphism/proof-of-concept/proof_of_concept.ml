(**
 * Lists
 *)

(* user code *)

(* тип "список" t, определённый пользователем *)
type 'a lst =
  | Nil
  | Cons of 'a * 'a lst

(* autogenerated code *)

(* тип "состояние" state
 * Тип имеет один дополнительный параметр 'seed; тип образуется путём замены всех
 * 1. вариантов на одноимённые полиморфные варианты
 * 2. первых рекурсивных вхождений аргументов конструкторов типа t параметром 'seed
 * 3. последующих рекурсивных вхождений типа t типом 'seed -> 'seed,
 *)
type ('a, 'seed) lst_state = [
  | `Nil
  | `Cons of 'a * 'seed
]

(* анаморфизм параметризован пользователькой функцией step и представляет собой
 * преобразователь типа 'seed -> t
 * Функция step должна отобразить 'seed в state, то есть, выполнить развёртку на один
 * уровень, остальную часть развёртки выполняет фреймворк.
 *)
let lst_ana (step : 'seed -> ('a, 'seed) lst_state) (seed : 'seed) : 'a lst =
  let rec lst_unfold s =
    match (step s) with
    | `Nil -> (Nil, s)
    | `Cons (head, tail_seed) ->
        let (tail, after_tail) = lst_unfold tail_seed in
        (Cons(head, tail), after_tail)
  in
  fst (lst_unfold seed)

(* user code *)
let custom_lst_ana = lst_ana (function 0 -> `Nil | n -> `Cons (n, n - 1))          (* 1 line *)
(* реализация, не использующая фреймворк *)
let rec byhand_lst_ana = function 0 -> Nil | n -> Cons (n, byhand_lst_ana (n - 1)) (* 1 line, slightly longer *)


let lst_test () =
  let arg = 3 in
  let expected = Cons (3, Cons (2, Cons (1, Nil))) in
  let actual =  custom_lst_ana arg in
  let actual_byhand = byhand_lst_ana arg in
  Printf.printf "%b (%b)\n" (actual = expected) (actual_byhand = expected)


(**
 * BSTs
 *)

(* user code *)

(* пользовательский тип бинарного дерева поиска *)
type 'a bst =
  | Null
  | Node of 'a * 'a bst * 'a bst

(* autogenerated code *)

(* Если конструктор типа в списке своих аргументов содержит больше одного рекурсивного вхождения этого типа,
 * seed'ы, начиная со второго, могут зависить не только от значения seed родительской вершины,
 * но и от результатов развертки предыдущих рекурсивных вхождений. Значение state, возвращаемое
 * функцией step, должно содержать для каждого такого вхождения не 'seed, а функцию 'seed -> 'seed.
 * Фреймворк для получения соответствующего значения seed вызывает такую функцию с остаточным
 * после развертки всех предыдущих рекурсивных вхождений значением seed. Таким образом, эффективно
 * развёртка одного узла имеет тип 'seed -> t * 'seed, причем если развертка произошла по конструктору,
 * не содержающему рекурсивных вхождений t (листу), то seed не изменяется.
*)
type ('a, 'seed) bst_state = [
  | `Null
  | `Node of 'a * 'seed * ('seed -> 'seed)
]

let bst_ana (step : 'seed -> ('a, 'seed) bst_state) seed =
  let rec bst_unfold s =
    match (step s) with
    | `Null -> (Null, s)
    | `Node (root, left, right) ->
        let (left_bst, after_left) = bst_unfold left in
        let (right_bst, after_right) = bst_unfold (right after_left) in
        (Node (root, left_bst, right_bst), after_right)

  in
  fst (bst_unfold seed)

(* user code *)
(** пример: развёртка бинарного дерева поиска из preorder-обхода этого дерева за линейное время.
 *  В качестве seed используется кортеж 'a list * 'a, где список соответствует
 *  остатку preorder-обхода, а одиночный элемент - максимальному значению, до которого
 *  (не включительно) можно использовать элементы из обхода для построения текущего поддерева.
 *)
let bst_step = function
  | ([], _) -> `Null
  | (x :: xs, max) ->
      if x > max
      then `Null
      else `Node (x, (xs, x), fun (tail, _) -> (tail, max))

let custom_bst_ana preorder = bst_ana bst_step (preorder, max_int) (* 7 lines *)

(* реализация, не использующая фреймворк *)
let byhand_bst_ana preorder =
  let rec unfold = function
    | ([], _) -> (Null, [])
    | (x :: xs, max) ->
        if x > max
        then (Null, x :: xs)
        else
          let (left, after_left) = unfold (xs, x) in
          let (right, after_right) = unfold (after_left, max) in
          (Node (x, left, right), after_right)
  in
  fst (unfold (preorder, max_int))                                (* 12 lines, more complex and obscure *)

let bst_test () =
  let arg = [5; 3; 4; 7; 6; 8] in
  let expected = Node (5, Node (3, Null, Node (4, Null, Null)),
                          Node (7, Node (6, Null, Null), Node (8, Null, Null)))
  in
  let actual =  custom_bst_ana arg in
  let actual_byhand = byhand_bst_ana arg in
  Printf.printf "%b (%b)\n" (actual = expected) (actual_byhand = expected)

let () =
  lst_test ();
  bst_test ()
