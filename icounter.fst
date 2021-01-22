module Icounter

open FStar.List.Tot

module L = FStar.List.Tot

module H = History

type operation =
  | Inc : nat -> operation

type trace = list operation

val apply_op : operation -> s1:H.state -> s2:H.state {s2 >= s1} 
let apply_op op s = 
  match op with
  | Inc n -> s + n

val apply_tr : t:trace -> s1:H.state -> s2:H.state {s2 >= s1}
let rec apply_tr t s =
  match t with
  | [] -> s
  | op::ops -> apply_tr ops (apply_op op s)


