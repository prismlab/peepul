module History

open FStar.Tactics
module T = FStar.Tactics
open FStar.Tactics.Typeclasses

module L = FStar.List.Tot

module M = Mrdt

val apply_trace : #s:eqtype -> #o:eqtype -> {| M.mrdt s o |} -> s -> t:list o -> Tot s (decreases %[t]) 
let rec apply_trace s t =
  match t with
  | [] -> s
  | op::ops -> apply_trace (M.apply_op s op) ops

type history (s:eqtype) (o:eqtype) =
 | History  : state:s
            -> children:list (list o * history s o)
            -> history s o

val size : #s:eqtype -> #o:eqtype -> h:history s o -> Tot nat (decreases %[h])
val size' : #s:eqtype -> #o:eqtype -> l:list (list o * history s o) -> Tot nat (decreases %[l])
let rec size h =
    let History  _ ch = h in
    1 + size' ch
and size' l =
    match l with
    | [] -> 0
    | (tr,x)::xs -> size x + size' xs

val hb : #s:eqtype -> #o:eqtype -> h1:history s o -> h2:history s o -> Tot bool (decreases (size h1))
let rec hb (History s ch) h2 = 
  match ch with
  | [] -> false
  | (_,x)::xs -> x = h2 || hb x h2 || hb (History s xs) h2

(* h1 --hb--> h2 <==> hbeq h1 h2 = true *)
val hbeq : #s:eqtype -> #o:eqtype -> h1:history s o -> h2:history s o -> bool
let hbeq h1 h2 = h1 = h2 || hb h1 h2

val concurrent : #s:eqtype -> #o:eqtype -> h1:history s o -> h2:history s o -> bool
let concurrent h1 h2 = not (hb h1 h2 || hb h2 h1 || h1 = h2)

val concurrent_commutative : #s:eqtype -> #o:eqtype 
                           -> h1:history s o
                           -> h2:history s o{concurrent h1 h2}
                           -> Lemma (ensures (concurrent h2 h1))
let concurrent_commutative h1 h2 = ()

val wellformed : #s:eqtype -> #o:eqtype -> {| M.mrdt s o |} -> h:history s o -> Tot bool (decreases (size h))
let rec wellformed (History s ch) =
  match ch with
  | [] -> true
  | (tr,h)::xs ->
      apply_trace s tr = History?.state h &&
      wellformed h &&
      wellformed (History s xs)

val hbeq_reflexive : #s:eqtype -> #o:eqtype -> h:history s o
                   -> Lemma (ensures (hbeq h h))
let hbeq_reflexive h = ()

val lemma1 : #s:eqtype -> #o:eqtype -> {| M.mrdt s o |} -> h:history s o{wellformed h}
           -> Lemma (ensures (forall h'. hbeq h h' ==> wellformed h'))  (decreases (size h))
let rec lemma1 (History s ch) = 
  match ch with
  | [] -> ()
  | (_,x)::xs -> 
     lemma1 x; 
     lemma1 (History s xs)
