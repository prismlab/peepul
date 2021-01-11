module History

open FStar.List.Tot

module Vc = Vector_clock

type state = nat

type ntree = | Ntree: v:nat -> children:list ntree -> ntree

let rec size1 t = fold_left (fun acc ch -> size1 ch + acc) 1 (Ntree?.children t)

let rec size2 trees acc = 
  match trees with
  | [] -> acc
  | (Ntree _ ts1)::ts2 -> size2 (ts1 @ ts2) (acc + 1)

type history =
| History : clock:Vc.t
          -> state:state
          -> children:list history
          -> history

let rec size (History _ _ children) = fold_left (fun acc ch -> size ch + acc) 1 children

val wellformed: h:history -> bool 
let rec wellformed (History clock state children) = 
  let n = length clock in
  for_all (fun child -> 
    let child_clock = History?.clock child in
    wellformed child &&
    length child_clock = length clock &&
    Vc.hb clock child_clock) children


