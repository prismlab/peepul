module History

open FStar.Tactics
module T = FStar.Tactics
open FStar.Tactics.Typeclasses
  
module L = FStar.List.Tot

module I = Icounter

module M = Mrdt

type state = nat

type history  =
 | History  : state:state
            -> children:list (I.trace * history)
            -> history

val size : h:history -> Tot nat (decreases %[h])
val size' : l:list (I.trace * history) -> Tot nat (decreases %[l])
let rec size h =
    let History  _ ch = h in
    1 + size' ch
and size'  l = 
    match l with
    | [] -> 0
    | (tr,x)::xs -> size x + size' xs

val hb : h1:history -> h2:history -> Tot bool (decreases (size h1))
let rec hb (History s ch) h2 = 
  match ch with
  | [] -> false
  | (_,x)::xs -> x = h2 || hb x h2 || hb (History s xs) h2

(* h1 --hb--> h2 <==> hbeq h1 h2 = true *)
val hbeq : h1:history -> h2:history -> bool
let hbeq h1 h2 = h1 = h2 || hb h1 h2

val concurrent : h1:history -> h2:history -> bool
let concurrent h1 h2 = not (hb h1 h2 || hb h2 h1 || h1 = h2)

val concurrent_commutative : h1:history
                           -> h2:history{concurrent h1 h2}
                           -> Lemma (ensures (concurrent h2 h1))
let concurrent_commutative h1 h2 = ()

val wellformed : h:history -> Tot bool (decreases h)
val wellformed' : s:state -> l:list (I.trace * history) -> h:history -> Tot bool (decreases l)
let rec wellformed h =
  let History state ch = h in
  wellformed' state ch h
and wellformed' par_state children par_history =
  match children with
  | [] -> true
  | (tr,x)::xs -> 
         hb par_history x &&
         M.apply_tr par_state tr = (History?.state x) &&
         wellformed x &&
         wellformed' par_state xs par_history

let _ = assert (hbeq  (History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))]) (History 3 [([I.Inc 1],(History 4 []))]));()

let _ = assert (hb (History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))]) (History 4 []));()

let _ = assert ((History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))])  = (History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))]));()

let _ = assert (wellformed (History 1 [([I.Inc 1;I.Inc 2], (History 4 [([I.Inc 1],(History 5 []))]))]));()


val hbeq_reflexive : h:history
                     -> Lemma (ensures (hbeq h h))
let hbeq_reflexive h = ()

val lemma1 : h:history {wellformed h}
           -> Lemma (ensures (forall h'. hbeq h h' ==> wellformed h'))  (decreases (size h))
let rec lemma1 (History s ch) = 
  match ch with
  | [] -> ()
  | (_,x)::xs -> 
     lemma1 x; 
     lemma1 (History s xs)
