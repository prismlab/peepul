module Icounter

open FStar.List.Tot

module M = Mrdt

type operation =
  | Inc : nat -> operation

type state = nat

val apply_op : state -> operation -> state
let apply_op s (Inc n) = s + n

instance _ : M.mrdt state operation = {
  M.apply_op = apply_op
}

open History

let _ = assert (hbeq (History 1 [([Inc 1;Inc 1], (History 3 [([Inc 1],(History 4 []))]))]) 
                     (History 3 [([Inc 1],(History 4 []))]))

let _ = assert (hb (History 1 [([Inc 1;Inc 1], (History 3 [([Inc 1],(History 4 []))]))]) 
                   (History 4 []))

let _ = assert (History 1 [([Inc 1;Inc 1], (History 3 [([Inc 1],(History 4 []))]))] = 
                History 1 [([Inc 1;Inc 1], (History 3 [([Inc 1],(History 4 []))]))])

let h : history nat operation = History 1 [([Inc 1;Inc 2], (History 4 [([Inc 1],(History 5 []))]))]

let _ = assert (wellformed h)
