module History

module L = FStar.List.Tot

module I = Icounter

type state = nat

type history (n:nat) =
| History : state:state
            -> children:list (I.trace * history n)
            -> history n

(*Returns true if h1 happens before h2*)
val hb : #n:nat -> h1:history n -> h2:history n -> Tot bool (decreases %[h1]) 
val hb' : #n:nat -> l:list (I.trace * history n) -> s:state -> h2:history n -> Tot bool (decreases %[l])
let rec hb #n h1 h2 =
  let History s ch = h1 in 
  hb' #n ch s h2 
and hb' #n children par_state h2 =
  match children with
  | [] -> false
  | (tr,x)::xs -> x = h2 ||
                hb #n x h2 ||
                hb' #n xs par_state h2
  

val eq : #n:nat -> h1:history n -> h2:history n -> Tot bool (decreases %[h1]) 
let eq #n h1 h2 = (h1 = h2)

(*Returns true if h1 happens before or equal to h2*)
val hbeq : #n:nat -> h1:history n -> h2:history n -> Tot bool (decreases %[h1])
let hbeq #n h1 h2 = hb h1 h2 || eq h1 h2

val concurrent : #n:nat -> h1:history n -> h2:history n -> Tot bool (decreases %[h1])
let concurrent #n h1 h2 = not (hbeq h1 h2 || hbeq h2 h1)
          
val concurrent_commutative : #n:nat 
                             -> h1:history n 
                             -> h2:history n{concurrent h1 h2}
                             -> Lemma (ensures (concurrent h2 h1))
let concurrent_commutative #n h1 h2 = ()


val size : #n:nat -> h:history n -> Tot nat (decreases %[h])
val size' : #n:nat -> l:list (I.trace * history n) -> Tot nat (decreases %[l])
let rec size #n h =
    let History  _ ch = h in
    1 + size' ch
and size' #n l = 
    match l with
    | [] -> 0
    | (tr,x)::xs -> size x + size' xs


(*Returns true if all the children of a parent node are concurrent*)
val concur_ch : #n:nat -> l:list(I.trace * history n) -> Tot bool (decreases %[l])
val concur_ch' : #n:nat -> child:history n -> l:list(I.trace * history n) -> Tot bool (decreases %[l])
let rec concur_ch #n l = 
match l with 
  |[] -> true
  |(tr,x)::xs -> concur_ch' x xs && concur_ch xs
and concur_ch' #n x ch =
match ch with
  |[] -> true
  |(tr,y)::xs -> concurrent x y && concur_ch' x xs


val wellformed : #n:nat -> h:history n -> Tot bool (decreases h)
val wellformed' : #n:nat -> s:state -> l:list (I.trace * history n) -> h:history n -> Tot bool (decreases l)
let rec wellformed #n h =
  let History state ch = h in
  concur_ch #n ch &&
  wellformed' state ch h
and wellformed' #n par_state children par_history =
  match children with
  | [] -> true
  | (tr,ch_history)::xs -> 
         let ch_state = History?.state ch_history in
         hb par_history ch_history &&
         ch_state = I.apply_tr tr par_state &&
         wellformed ch_history &&
         wellformed' par_state xs par_history
    

val test : #n:nat -> Tot unit
let test #n = assert (hbeq #n (History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))]) (History 3 [([I.Inc 1],(History 4 []))]));()

val test1 : #n:nat -> Tot unit
let test1 #n = assert (hb #n (History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))]) (History 4 []));()

val test2 : #n:nat -> Tot unit
let test2 #n = assert (eq #n (History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))]) (History 1 [([I.Inc 1;I.Inc 1], (History 3 [([I.Inc 1],(History 4 []))]))]));()


val hbeq_reflexive : #n:nat 
                     -> h:history n 
                     -> Lemma (ensures (hbeq h h))
let hbeq_reflexive #n h = ()


val lemma1 : #n:nat 
             -> h:history n{wellformed h}
             -> Lemma (ensures (forall h'. hb h h' ==> wellformed h'))  (decreases (size h))
                       
let rec lemma1 #n (History s ch) = match ch with
 | [] -> ()
 | (tr,x)::xs -> lemma1 x; lemma1 (History s xs)
          
