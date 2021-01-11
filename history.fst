module History

open FStar.List.Tot

module Vc = Vector_clock

type state = nat

type ntree = | Ntree: v:nat -> children:list ntree -> ntree

type history =
| History : clock:Vc.t
          -> state:state
          -> children:list history
          -> history

let rec wellformed (h:history) : Tot bool (decreases %[h]) =
  let History clock _ ch = h in
  wellformed' clock ch
and wellformed' parent_clock children : Tot bool (decreases %[children]) =
  match children with
  | [] -> true
  | x::xs ->
     let clock = History?.clock x in
     length clock = length parent_clock &&
     Vc.hb parent_clock clock &&
     wellformed x &&
     wellformed' parent_clock xs
