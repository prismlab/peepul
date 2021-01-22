module History

module L = FStar.List.Tot

module I = Icounter

type state = nat

type history (n:nat) =
| History : state:state
            -> children:list (I.trace * history n)
            -> history n


val hbeq : #n:nat -> h1:history n -> h2:history n -> Tot bool (decreases %[h1]) 
val hbeq' : #n:nat -> l:list (I.trace * history n) -> h2:history n -> Tot bool (decreases %[l])
let rec hbeq #n h1 h2 =
  let History s ch = h1 in 
  h1 = h2 || hbeq' #n ch h2 
and hbeq' #n children h2 =
  match children with
  |[] -> false
  |(tr,x)::xs -> hbeq #n x h2 || hbeq' #n xs h2
  

val eq : #n:nat -> h1:history n -> h2:history n -> Tot bool (decreases %[h1]) 
let eq #n h1 h2 = (h1 = h2)

val hb : #n:nat -> h1:history n -> h2:history n -> Tot bool (decreases %[h1])
let hb #n h1 h2 = hbeq h1 h2 && not(eq h1 h2)
          

val size : #n:nat -> h:history n -> Tot nat (decreases %[h])
val size' : #n:nat -> l:list (I.trace * history n) -> Tot nat (decreases %[l])
let rec size #n h =
    let History  _ ch = h in
    1 + size' ch
and size' #n l = 
    match l with
    | [] -> 0
    | (tr,x)::xs -> size x + size' xs
    

val wellformed : #n:nat -> h:history n -> Tot bool (decreases %[h])
val wellformed' : #n:nat -> s:state -> l:list (I.trace * history n) -> h:history n -> Tot bool (decreases %[l])
let rec wellformed #n h =
  let History state ch = h in
  wellformed' state ch h
and wellformed' #n parent_state children parent_history =
  match children with
  |[] -> true
  |(tr,child_history)::xs -> 
    let state = History?.state child_history in
    state = I.apply_tr tr parent_state &&
    hb parent_history child_history &&
    wellformed child_history &&
    wellformed' parent_state xs parent_history

val test : #n:nat -> Tot unit
let test #n = assert (hbeq #n (History 1 [([I.Inc;I.Inc], (History 3 [([I.Inc],(History 4 []))]))]) (History 3 [([I.Inc],(History 4 []))]));()

val test1 : #n:nat -> Tot unit
let test1 #n = assert (hb #n (History 1 [([I.Inc;I.Inc], (History 3 [([I.Inc],(History 4 []))]))]) (History 4 []));()

val test2 : #n:nat -> Tot unit
let test2 #n = assert (eq #n (History 1 [([I.Inc;I.Inc], (History 3 [([I.Inc],(History 4 []))]))]) (History 1 [([I.Inc;I.Inc], (History 3 [([I.Inc],(History 4 []))]))]));()




