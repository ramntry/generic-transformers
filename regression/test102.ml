open GT

@type ('a, 'b, 'c) my_list =
  | Nil
  | ConsA of 'a * ('a, 'b, 'c) my_list
  | ConsB of 'b * ('a, 'b, 'c) my_list
  | ConsC of 'c * ('a, 'b, 'c) my_list
  with show
