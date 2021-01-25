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

(*Returns true if h1 happens before h2*)
val hb : h1:history -> h2:history -> Tot bool (decreases %[h1]) 
val hb' : l:list (I.trace * history) -> s:state  -> h2:history -> Tot bool (decreases %[l])

let rec hb h1 h2 =
  let History s ch = h1 in 
  hb' ch s h2 
and hb' children par_state h2 =
  match children with
  | [] -> false
  | (tr,x)::xs -> x = h2 ||
                hb x h2 ||
                hb' xs par_state h2
  

val eq : h1:history -> h2:history -> Tot bool (decreases %[h1]) 
let eq h1 h2 = (h1 = h2)

(*Returns true if h1 happens before or equal to h2*)
val hbeq : h1:history -> h2:history -> Tot bool (decreases %[h1])
let hbeq h1 h2 = hb h1 h2 || eq h1 h2

val concurrent : h1:history -> h2:history -> Tot bool (decreases %[h1])
let concurrent h1 h2 = not (hbeq h1 h2 || hbeq h2 h1)
          
val concurrent_commutative : h1:history
                             -> h2:history{concurrent h1 h2}
                             -> Lemma (ensures (concurrent h2 h1))
let concurrent_commutative h1 h2 = ()


val size : h:history -> Tot nat (decreases %[h])
val size' : l:list (I.trace * history) -> Tot nat (decreases %[l])
let rec size h =
    let History  _ ch = h in
    1 + size' ch
and size'  l = 
    match l with
    | [] -> 0
    | (tr,x)::xs -> size x + size' xs


(*Returns true if all the children of a parent node are concurrent*)
val concur_ch : l:list(I.trace * history) -> Tot bool (decreases %[l])
val concur_ch' : child:history -> l:list(I.trace * history) -> Tot bool (decreases %[l])
let rec concur_ch l = 
match l with 
  |[] -> true
  |(tr,x)::xs -> concur_ch' x xs && concur_ch xs
and concur_ch' x ch =
match ch with
  |[] -> true
  |(tr,y)::xs -> concurrent x y && concur_ch' x xs


val wellformed : h:history -> Tot bool (decreases h)
val wellformed' : s:state -> l:list (I.trace * history) -> h:history -> Tot bool (decreases l)
let rec wellformed h =
  let History state ch = h in
 (* concur_ch #n ch &&      //not necessary// *)
  wellformed' state ch h
and wellformed' par_state children par_history =
  match children with
  | [] -> true
  | (tr,ch_history)::xs -> 
         let ch_state = History?.state ch_history in
         hb par_history ch_history &&
         ch_state = M.apply_tr par_state tr &&
         wellformed ch_history &&
         wellformed' par_state xs par_history
    


let _ = assert (hbeq  (History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))]) (History 3 [([I.Inc 1],(History 4 []))]));()

let _ = assert (hb (History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))]) (History 4 []));()

let _ = assert (eq (History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))]) (History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))]));()

let _ = assert (wellformed (History 1 [([I.Inc 1;I.Inc 2], (History 4 [([I.Inc 1],(History 5 []))]))]));()


val hbeq_reflexive : h:history
                     -> Lemma (ensures (hbeq h h))
let hbeq_reflexive h = ()



val lemma1 : h:history {wellformed h}
             -> Lemma (ensures (forall h'. hbeq h h' ==> wellformed h'))  (decreases (size h))
                       
let rec lemma1 (History s ch) = match ch with
 | [] -> ()
 | (tr,x)::xs -> lemma1 x; lemma1 (History s xs)
          
